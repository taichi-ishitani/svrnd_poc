//! The tvip-axi constraints, written down with the svrand API the way xezim
//! would lower them. Each case is solved N times; every solution is checked
//! with the independent evaluator.
//!
//! usage: tvip [item|delay|config|all] [N] [seed]

use std::collections::BTreeMap;
use std::time::Instant;

use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use svrand::build::*;
use svrand::{
    ArraySize, BinOp::*, Bits, Expr, FuncEval, FuncId, Item, NoFuncs, Problem, Solution, UnOp,
    VarRef,
};

// ---------------------------------------------------------------- helpers

fn and(a: Expr, b: Expr) -> Expr {
    bin(LogAnd, a, b)
}
fn or(a: Expr, b: Expr) -> Expr {
    bin(LogOr, a, b)
}
fn eq(a: Expr, b: Expr) -> Expr {
    bin(Eq, a, b)
}
fn ne(a: Expr, b: Expr) -> Expr {
    bin(Ne, a, b)
}
fn ge(a: Expr, b: Expr) -> Expr {
    bin(Ge, a, b)
}
fn le(a: Expr, b: Expr) -> Expr {
    bin(Le, a, b)
}
fn gt(a: Expr, b: Expr) -> Expr {
    bin(Gt, a, b)
}
/// An unsized based literal (`'h1000`): 32-bit unsigned.
fn based(v: i64) -> Expr {
    c(32, false, v)
}
/// A sized unsigned literal (`64'h…`).
fn sized(w: u32, v: u64) -> Expr {
    Expr::Const(Bits::from_u64(w, false, v))
}

/// The delay configuration as the item sees it (state, after its own
/// `post_randomize`).
#[derive(Clone, Copy)]
struct Delay {
    min: i64,
    mid: [i64; 2],
    max: i64,
    wz: i64,
    ws: i64,
    wl: i64,
}

const ZERO_DELAY: Delay = Delay {
    min: 0,
    mid: [0, 0],
    max: 0,
    wz: 1,
    ws: 1,
    wl: 1,
};
const SAMPLE_DELAY: Delay = Delay {
    min: 0,
    mid: [3, 6],
    max: 10,
    wz: 6,
    ws: 3,
    wl: 1,
};

/// `tvip_delay_constraint(DELAY, CONFIGURATION)`; the configuration fields
/// are state, so they arrive as constants.
fn delay_constraint(d: Expr, cfg: Delay) -> Item {
    let tvip_inside =
        |x: &Expr, lo: i64, hi: i64| and(ge(x.clone(), int(lo)), le(x.clone(), int(hi)));
    if_else(
        gt(int(cfg.max), int(cfg.min)),
        vec![
            item(or(
                tvip_inside(&d, cfg.min, cfg.mid[0]),
                tvip_inside(&d, cfg.mid[1], cfg.max),
            )),
            if_else(
                eq(int(cfg.min), int(0)),
                vec![dist(
                    d.clone(),
                    vec![
                        each(val(int(0)), int(cfg.wz)),
                        spread(range(int(1), int(cfg.mid[0])), int(cfg.ws)),
                        spread(range(int(cfg.mid[1]), int(cfg.max)), int(cfg.wl)),
                    ],
                )],
                vec![dist(
                    d.clone(),
                    vec![
                        spread(range(int(cfg.min), int(cfg.mid[0])), int(cfg.ws)),
                        spread(range(int(cfg.mid[1]), int(cfg.max)), int(cfg.wl)),
                    ],
                )],
            ),
        ],
        vec![item(eq(d, int(cfg.min)))],
    )
}

// ------------------------------------------------- tvip_axi_master_item

const AXI4: i64 = 0;
const WRITE: i64 = 0;
const READ: i64 = 1;

struct ItemVars {
    access_type: svrand::VarId,
    id: svrand::VarId,
    address: svrand::VarId,
    burst_length: svrand::VarId,
    burst_size: svrand::VarId,
    need_response: svrand::VarId,
    start_delay: svrand::VarId,
    data: svrand::ArrayId,
    strobe: svrand::ArrayId,
    write_data_delay: svrand::ArrayId,
}

/// `tvip_axi_master_item` as `do_basic_write_read_access` randomizes its
/// `index`-th write item, with the sample configuration:
/// AXI4, id 8 / address 64 / data 64 bits, max burst 256, qos [2:9],
/// request start / write data delays enabled, bready delay 0.
fn master_write_item(index: i64) -> (Problem, ItemVars) {
    let mut p = Problem::new();
    // §18.4: rand_mode(0) members (response, response_delay,
    // address_ready_delay, write_data_ready_delay) are state and not
    // declared; their constraint blocks are off (pre_randomize).
    let access_type = p.var("access_type", 32, true);
    let id = p.var("id", 32, false);
    let address = p.var("address", 64, false);
    let burst_length = p.var("burst_length", 32, true);
    let burst_size = p.var("burst_size", 32, true);
    let burst_type = p.var("burst_type", 2, false);
    let memory_type = p.var("memory_type", 32, true);
    let _protection = p.var("protection", 3, false);
    let qos = p.var("qos", 4, false);
    let data = p.array("data", 1024, false, ArraySize::Dynamic { max: 256 });
    let strobe = p.array("strobe", 128, false, ArraySize::Dynamic { max: 256 });
    let start_delay = p.var("start_delay", 32, true);
    let write_data_delay = p.array(
        "write_data_delay",
        32,
        true,
        ArraySize::Dynamic { max: 256 },
    );
    let response_ready_delay = p.array(
        "response_ready_delay",
        32,
        true,
        ArraySize::Dynamic { max: 256 },
    );
    let need_response = p.var("need_response", 1, false);

    let (id_width, address_width, data_width, strobe_width) = (8, 64, 64, 8);
    let protocol = int(AXI4);
    let is_axi4 = || eq(protocol.clone(), int(AXI4));
    let is_write = || eq(var(access_type), int(WRITE));
    let is_read = || eq(var(access_type), int(READ));

    // §6.19.3: a rand enum takes only its members.
    p.constraint(
        0,
        vec![
            item(inside(var(access_type), vec![val(int(0)), val(int(1))])),
            item(inside(var(burst_type), vec![range(int(0), int(2))])),
            item(inside(var(memory_type), vec![range(int(0), int(11))])),
        ],
    );
    // c_valid_id / c_valid_address
    p.constraint(1, vec![item(eq(bin(Shr, var(id), int(id_width)), int(0)))]);
    p.constraint(
        2,
        vec![item(eq(bin(Shr, var(address), int(address_width)), int(0)))],
    );
    // c_valid_burst_length
    p.constraint(
        3,
        vec![if_else(
            is_axi4(),
            vec![item(inside(
                var(burst_length),
                vec![range(int(1), int(256))],
            ))],
            vec![item(eq(var(burst_length), int(1)))],
        )],
    );
    // c_valid_burst_size
    p.constraint(
        4,
        vec![if_else(
            is_axi4(),
            vec![
                item(inside(
                    var(burst_size),
                    [1, 2, 4, 8, 16, 32, 64, 128]
                        .iter()
                        .map(|&v| val(int(v)))
                        .collect(),
                )),
                item(le(bin(Mul, int(8), var(burst_size)), int(data_width))),
            ],
            vec![item(eq(bin(Mul, int(8), var(burst_size)), int(data_width)))],
        )],
    );
    // c_4kb_boundary:
    //   ((address & tvip_axi_address'('h1000 - burst_size)) +
    //    (burst_length * burst_size)) <= 4096
    p.constraint(
        5,
        vec![item(le(
            bin(
                Add,
                bin(
                    BitAnd,
                    var(address),
                    cast(64, false, bin(Sub, based(0x1000), var(burst_size))),
                ),
                bin(Mul, var(burst_length), var(burst_size)),
            ),
            int(4096),
        ))],
    );
    // c_valid_memory_type
    p.constraint(
        6,
        vec![if_(
            eq(protocol.clone(), int(1)),
            vec![item(eq(var(memory_type), int(0)))],
        )],
    );
    // c_valid_qos
    p.constraint(7, vec![item(inside(var(qos), vec![range(int(2), int(9))]))]);
    // c_valid_write_data
    let i = p.loop_var();
    p.constraint(
        8,
        vec![
            item(bin(Implies, is_write(), eq(size(data), var(burst_length)))),
            item(bin(Implies, is_read(), eq(size(data), int(0)))),
            foreach(
                data,
                i,
                vec![item(eq(
                    bin(Shr, elem(data, lp(i)), int(data_width)),
                    int(0),
                ))],
            ),
        ],
    );
    p.solve_before(vec![VarRef::Var(access_type)], vec![VarRef::Array(data)]);
    p.solve_before(vec![VarRef::Var(burst_length)], vec![VarRef::Array(data)]);
    // c_valid_strobe
    let i = p.loop_var();
    p.constraint(
        9,
        vec![
            item(bin(
                Implies,
                is_write(),
                eq(size(strobe), var(burst_length)),
            )),
            item(bin(Implies, is_read(), eq(size(strobe), int(0)))),
            foreach(
                strobe,
                i,
                vec![item(eq(
                    bin(Shr, elem(strobe, lp(i)), int(strobe_width)),
                    int(0),
                ))],
            ),
        ],
    );
    p.solve_before(vec![VarRef::Var(access_type)], vec![VarRef::Array(strobe)]);
    p.solve_before(vec![VarRef::Var(burst_length)], vec![VarRef::Array(strobe)]);
    // c_address_start_delay
    p.constraint(10, vec![delay_constraint(var(start_delay), SAMPLE_DELAY)]);
    // c_write_data_delay
    let i = p.loop_var();
    p.constraint(
        11,
        vec![
            if_else(
                is_write(),
                vec![item(eq(size(write_data_delay), var(burst_length)))],
                vec![item(eq(size(write_data_delay), int(0)))],
            ),
            foreach(
                write_data_delay,
                i,
                vec![delay_constraint(
                    elem(write_data_delay, lp(i)),
                    SAMPLE_DELAY,
                )],
            ),
        ],
    );
    p.solve_before(
        vec![VarRef::Var(access_type), VarRef::Var(burst_length)],
        vec![VarRef::Array(write_data_delay)],
    );
    // c_response_ready_delay
    let i = p.loop_var();
    p.constraint(
        12,
        vec![
            if_else(
                is_write(),
                vec![item(eq(size(response_ready_delay), int(1)))],
                vec![item(eq(size(response_ready_delay), var(burst_length)))],
            ),
            foreach(
                response_ready_delay,
                i,
                vec![if_else(
                    is_write(),
                    vec![delay_constraint(
                        elem(response_ready_delay, lp(i)),
                        ZERO_DELAY,
                    )],
                    vec![delay_constraint(
                        elem(response_ready_delay, lp(i)),
                        ZERO_DELAY,
                    )],
                )],
            ),
        ],
    );
    // c_default_need_response (tvip_axi_master_item)
    p.constraint(13, vec![soft(item(eq(var(need_response), int(0))))]);
    // The inline `with` of do_basic_write_read_access ranks highest.
    let lo = bin(
        Sub,
        bin(
            Mul,
            sized(64, 0x0001_0000_0000_0000),
            bin(Add, int(index), int(0)),
        ),
        int(0),
    );
    let hi = bin(
        Sub,
        bin(
            Mul,
            sized(64, 0x0001_0000_0000_0000),
            bin(Add, int(index), int(1)),
        ),
        int(1),
    );
    p.constraint(
        100,
        vec![
            item(eq(var(access_type), int(WRITE))),
            item(ge(var(address), lo)),
            item(le(var(address), hi.clone())),
            item(le(
                bin(
                    Add,
                    var(address),
                    bin(Mul, var(burst_size), var(burst_length)),
                ),
                hi,
            )),
        ],
    );
    (
        p,
        ItemVars {
            access_type,
            id,
            address,
            burst_length,
            burst_size,
            need_response,
            start_delay,
            data,
            strobe,
            write_data_delay,
        },
    )
}

// --------------------------------------------- tvip_delay_configuration

const GET_MIN: FuncId = FuncId(0);
const GET_MAX: FuncId = FuncId(1);
const GET_DELTA: FuncId = FuncId(2);

/// The class's `get_min_delay` / `get_max_delay` / `get_delay_delta`.
struct DelayFuncs;

impl FuncEval for DelayFuncs {
    fn call(&mut self, f: FuncId, a: &[Bits]) -> Bits {
        let v = |i: usize| a[i].to_i64().unwrap();
        let min = |m: i64| if m >= 0 { m } else { 0 };
        let max = |x: i64, m: i64| if x >= 0 { x } else { min(m) };
        let r = match f {
            GET_MIN => min(v(0)),
            GET_MAX => max(v(0), v(1)),
            _ => max(v(0), v(1)) - min(v(1)),
        };
        Bits::from_i64(32, true, r)
    }
}

struct DelayVars {
    min: svrand::VarId,
    max: svrand::VarId,
    mid: svrand::ArrayId,
    wz: svrand::VarId,
    ws: svrand::VarId,
    wl: svrand::VarId,
}

/// `tvip_delay_configuration` as the object named `pre` (`""` at the top),
/// its blocks ranked from `prio`. The caller flattens a sub-object into the
/// problem: its members become variables `pre.member`.
fn add_delay_cfg(p: &mut Problem, pre: &str, prio: u32) -> DelayVars {
    let n = |m: &str| format!("{pre}{m}");
    let min = p.var(&n("min_delay"), 32, true);
    let mid = p.array(&n("mid_delay"), 32, true, ArraySize::Fixed(2));
    let max = p.var(&n("max_delay"), 32, true);
    let wz = p.var(&n("weight_zero_delay"), 32, true);
    let ws = p.var(&n("weight_short_delay"), 32, true);
    let wl = p.var(&n("weight_long_delay"), 32, true);
    // The methods only read their arguments, so one FuncId each serves every
    // instance; a method reading its object would get an id per receiver.
    let get_min = |x: Expr| call(GET_MIN, 32, true, vec![x]);
    let get_max = |x: Expr, m: Expr| call(GET_MAX, 32, true, vec![x, m]);
    let get_delta = |x: Expr, m: Expr| call(GET_DELTA, 32, true, vec![x, m]);
    let mid_ = |i: i64| elem(mid, int(i));

    p.constraint(
        prio,
        vec![
            item(ge(var(min), int(-1))),
            item(ge(var(max), int(-1))),
            item(ge(var(max), var(min))),
        ],
    );
    p.constraint(
        prio + 1,
        vec![
            soft(item(eq(var(min), int(-1)))),
            soft(item(eq(var(max), int(-1)))),
        ],
    );
    p.constraint(
        prio + 2,
        vec![
            item(or(eq(mid_(0), int(-1)), ge(mid_(0), get_min(var(min))))),
            item(or(
                eq(mid_(1), int(-1)),
                le(mid_(1), get_max(var(max), var(min))),
            )),
            item(le(mid_(0), mid_(1))),
            if_(
                ge(get_delta(var(max), var(min)), int(1)),
                vec![if_(
                    eq(get_min(var(min)), int(0)),
                    vec![item(gt(mid_(0), int(0)))],
                )],
            ),
        ],
    );
    p.solve_before(
        vec![VarRef::Var(min), VarRef::Var(max)],
        vec![VarRef::Array(mid)],
    );
    p.constraint(
        prio + 3,
        vec![
            soft(item(eq(mid_(0), int(-1)))),
            soft(item(eq(mid_(1), int(-1)))),
        ],
    );
    p.constraint(
        prio + 4,
        vec![if_else(
            gt(get_min(var(min)), int(0)),
            vec![
                item(eq(var(wz), int(0))),
                item(ge(var(ws), int(-1))),
                item(ge(var(wl), int(-1))),
            ],
            vec![
                item(ge(var(wz), int(-1))),
                item(ge(var(ws), int(-1))),
                item(ge(var(wl), int(-1))),
            ],
        )],
    );
    p.solve_before(vec![VarRef::Var(min)], vec![VarRef::Var(wz)]);
    p.constraint(
        prio + 5,
        vec![
            soft(item(eq(var(wz), int(-1)))),
            soft(item(eq(var(ws), int(-1)))),
            soft(item(eq(var(wl), int(-1)))),
        ],
    );
    DelayVars {
        min,
        max,
        mid,
        wz,
        ws,
        wl,
    }
}

/// `tvip_delay_configuration`, with the sample's
/// `c_request_start_delay` (min 0, max 10, weights 6/3/1) when `sample`.
fn delay_configuration(sample: bool) -> (Problem, DelayVars) {
    let mut p = Problem::new();
    let v = add_delay_cfg(&mut p, "", 0);
    if sample {
        // The enclosing configuration's constraint is a hard one.
        p.constraint(100, sample_delay_bounds(&v));
    }
    (p, v)
}

/// The sample configuration's `min 0 / max 10 / weights 6, 3, 1`.
fn sample_delay_bounds(v: &DelayVars) -> Vec<Item> {
    vec![
        item(eq(var(v.min), int(0))),
        item(eq(var(v.max), int(10))),
        item(eq(var(v.wz), int(6))),
        item(eq(var(v.ws), int(3))),
        item(eq(var(v.wl), int(1))),
    ]
}

// ------------------------------------------------ tvip_axi_configuration

struct ConfigVars {
    protocol: svrand::VarId,
    id_width: svrand::VarId,
    data_width: svrand::VarId,
    strobe_width: svrand::VarId,
    qos_range: svrand::ArrayId,
    response_ordering: svrand::VarId,
    outstanding: svrand::VarId,
    interleave: svrand::VarId,
    reset_by_agent: svrand::VarId,
    address_width: svrand::VarId,
    max_burst_length: svrand::VarId,
    weights: Vec<svrand::VarId>,
    /// request_start, write_data, response_start, response, awready,
    /// wready, bready, arready, rready.
    delays: Vec<DelayVars>,
}

const DELAY_NAMES: [&str; 9] = [
    "request_start_delay",
    "write_data_delay",
    "response_start_delay",
    "response_delay",
    "awready_delay",
    "wready_delay",
    "bready_delay",
    "arready_delay",
    "rready_delay",
];

/// `tvip_axi_configuration` as the object `pre`, its blocks ranked from
/// `prio` and its nine rand `tvip_delay_configuration` members below them
/// (§18.5.14.1: an object's constraints outrank its members').
fn add_axi_cfg(p: &mut Problem, pre: &str, prio: u32) -> ConfigVars {
    let n = |m: &str| format!("{pre}{m}");
    let delays: Vec<DelayVars> = DELAY_NAMES
        .iter()
        .enumerate()
        .map(|(i, d)| add_delay_cfg(p, &format!("{pre}{d}."), prio - 100 + 6 * i as u32))
        .collect();
    let protocol = p.var(&n("protocol"), 32, true);
    let id_width = p.var(&n("id_width"), 32, true);
    let address_width = p.var(&n("address_width"), 32, true);
    let max_burst_length = p.var(&n("max_burst_length"), 32, true);
    let data_width = p.var(&n("data_width"), 32, true);
    let strobe_width = p.var(&n("strobe_width"), 32, true);
    let qos_range = p.array(&n("qos_range"), 32, true, ArraySize::Fixed(2));
    let response_ordering = p.var(&n("response_ordering"), 32, true);
    let outstanding = p.var(&n("outstanding_responses"), 32, true);
    let interleave = p.var(&n("enable_response_interleaving"), 1, false);
    let min_il = p.var(&n("min_interleave_size"), 32, true);
    let max_il = p.var(&n("max_interleave_size"), 32, true);
    let weights: Vec<_> = ["okay", "exokay", "slave_error", "decode_error"]
        .iter()
        .map(|w| p.var(&n(&format!("response_weight_{w}")), 32, true))
        .collect();
    for r in ["awready", "wready", "bready", "arready", "rready"] {
        p.var(&n(&format!("default_{r}")), 1, false);
    }
    let reset_by_agent = p.var(&n("reset_by_agent"), 1, false);
    let lite = || eq(var(protocol), int(1));
    let i = p.loop_var();

    p.constraint(
        prio,
        vec![
            item(inside(var(protocol), vec![val(int(0)), val(int(1))])),
            item(inside(
                var(response_ordering),
                vec![val(int(0)), val(int(1))],
            )),
        ],
    );
    p.constraint(prio + 1, vec![soft(item(eq(var(protocol), int(AXI4))))]);
    p.constraint(
        prio + 2,
        vec![item(inside(var(id_width), vec![range(int(0), int(32))]))],
    );
    p.constraint(
        prio + 3,
        vec![if_(lite(), vec![soft(item(eq(var(id_width), int(0))))])],
    );
    p.solve_before(vec![VarRef::Var(protocol)], vec![VarRef::Var(id_width)]);
    p.constraint(
        prio + 4,
        vec![item(inside(
            var(address_width),
            vec![range(int(1), int(64))],
        ))],
    );
    p.constraint(
        prio + 5,
        vec![
            item(inside(var(max_burst_length), vec![range(int(1), int(256))])),
            if_(lite(), vec![item(eq(var(max_burst_length), int(1)))]),
        ],
    );
    p.solve_before(
        vec![VarRef::Var(protocol)],
        vec![VarRef::Var(max_burst_length)],
    );
    p.constraint(
        prio + 6,
        vec![
            item(inside(
                var(data_width),
                [8, 16, 32, 64, 128, 256, 512, 1024]
                    .iter()
                    .map(|&v| val(int(v)))
                    .collect(),
            )),
            if_(
                lite(),
                vec![item(inside(
                    var(data_width),
                    vec![val(int(32)), val(int(64))],
                ))],
            ),
        ],
    );
    p.solve_before(vec![VarRef::Var(protocol)], vec![VarRef::Var(data_width)]);
    p.constraint(
        prio + 7,
        vec![item(eq(
            var(strobe_width),
            bin(Div, var(data_width), int(8)),
        ))],
    );
    p.solve_before(
        vec![VarRef::Var(data_width)],
        vec![VarRef::Var(strobe_width)],
    );
    p.constraint(
        prio + 8,
        vec![if_else(
            lite(),
            vec![
                item(eq(elem(qos_range, int(0)), int(0))),
                item(eq(elem(qos_range, int(1)), int(0))),
            ],
            vec![
                item(le(elem(qos_range, int(0)), elem(qos_range, int(1)))),
                foreach(
                    qos_range,
                    i,
                    vec![item(inside(
                        elem(qos_range, lp(i)),
                        vec![val(int(-1)), range(int(0), int(15))],
                    ))],
                ),
            ],
        )],
    );
    p.solve_before(vec![VarRef::Var(protocol)], vec![VarRef::Array(qos_range)]);
    let j = p.loop_var();
    p.constraint(
        prio + 9,
        vec![foreach(
            qos_range,
            j,
            vec![soft(item(eq(elem(qos_range, lp(j)), int(-1))))],
        )],
    );
    p.constraint(
        prio + 10,
        vec![if_(lite(), vec![item(eq(var(response_ordering), int(0)))])],
    );
    p.solve_before(
        vec![VarRef::Var(protocol)],
        vec![VarRef::Var(response_ordering)],
    );
    p.constraint(
        prio + 11,
        vec![soft(item(eq(var(response_ordering), int(1))))],
    );
    p.constraint(prio + 12, vec![item(ge(var(outstanding), int(0)))]);
    p.constraint(prio + 13, vec![soft(item(eq(var(outstanding), int(0))))]);
    p.constraint(prio + 14, vec![soft(item(eq(var(interleave), int(0))))]);
    p.constraint(
        prio + 15,
        vec![
            item(ge(var(min_il), int(0))),
            item(ge(var(max_il), int(0))),
            item(ge(var(max_il), var(min_il))),
        ],
    );
    p.constraint(
        prio + 16,
        vec![
            soft(item(eq(var(min_il), int(0)))),
            soft(item(eq(var(max_il), int(0)))),
        ],
    );
    p.constraint(
        prio + 17,
        weights.iter().map(|&w| item(ge(var(w), int(-1)))).collect(),
    );
    p.constraint(
        prio + 18,
        weights
            .iter()
            .map(|&w| soft(item(eq(var(w), int(-1)))))
            .collect(),
    );
    p.constraint(prio + 19, vec![soft(item(eq(var(reset_by_agent), int(1))))]);
    ConfigVars {
        protocol,
        id_width,
        data_width,
        strobe_width,
        qos_range,
        response_ordering,
        outstanding,
        interleave,
        reset_by_agent,
        address_width,
        max_burst_length,
        weights,
        delays,
    }
}

/// `c_axi_basic` of the sample configuration for one `axi_cfg`.
fn axi_basic(v: &ConfigVars) -> Vec<Item> {
    vec![
        item(eq(var(v.id_width), int(8))),
        item(eq(var(v.address_width), int(64))),
        item(eq(var(v.max_burst_length), int(256))),
        item(eq(var(v.data_width), int(64))),
        item(ne(elem(v.qos_range, int(0)), int(-1))),
        item(ne(elem(v.qos_range, int(1)), int(-1))),
    ]
}

/// `tvip_axi_configuration` alone (its delay members included) with the
/// sample's `c_axi_basic`.
fn axi_configuration() -> (Problem, ConfigVars) {
    let mut p = Problem::new();
    let v = add_axi_cfg(&mut p, "", 1000);
    p.constraint(5000, axi_basic(&v));
    (p, v)
}

/// `tvip_axi_sample_configuration::randomize()`: `axi_cfg[0]` (master) and
/// `axi_cfg[1]` (slave), each with its nine delay members — one problem,
/// the members flattened. `enable` is every `enable_*` switch (state, set
/// from the command line in `pre_randomize`).
fn sample_configuration(enable: bool) -> (Problem, [ConfigVars; 2]) {
    let mut p = Problem::new();
    let c0 = add_axi_cfg(&mut p, "axi_cfg[0].", 1000);
    let c1 = add_axi_cfg(&mut p, "axi_cfg[1].", 2000);
    let on = || int(enable as i64);
    let d = |c: &ConfigVars, name: &str| {
        DELAY_NAMES
            .iter()
            .position(|n| *n == name)
            .map(|i| sample_delay_bounds(&c.delays[i]))
            .unwrap()
    };
    p.constraint(
        5000,
        axi_basic(&c0).into_iter().chain(axi_basic(&c1)).collect(),
    );
    p.constraint(5001, vec![if_(on(), d(&c0, "request_start_delay"))]);
    p.constraint(5002, vec![if_(on(), d(&c0, "write_data_delay"))]);
    p.constraint(
        5003,
        vec![
            item(eq(var(c1.weights[0]), int(6))),
            item(eq(var(c1.weights[1]), int(2))),
            item(eq(var(c1.weights[2]), int(1))),
            item(eq(var(c1.weights[3]), int(1))),
        ],
    );
    p.constraint(5004, vec![if_(on(), d(&c1, "response_start_delay"))]);
    p.constraint(5005, vec![if_(on(), d(&c1, "response_delay"))]);
    let mut ready = Vec::new();
    for (c, n) in [
        (&c1, "awready_delay"),
        (&c1, "wready_delay"),
        (&c0, "bready_delay"),
        (&c1, "arready_delay"),
        (&c0, "rready_delay"),
    ] {
        ready.extend(d(c, n));
    }
    p.constraint(5006, vec![if_(on(), ready)]);
    p.constraint(
        5007,
        vec![if_else(
            on(),
            vec![
                item(eq(var(c1.response_ordering), int(1))),
                item(inside(var(c1.outstanding), vec![range(int(2), int(5))])),
            ],
            vec![item(eq(var(c1.response_ordering), int(0)))],
        )],
    );
    p.constraint(
        5008,
        vec![if_else(
            on(),
            vec![item(eq(var(c1.interleave), int(1)))],
            vec![item(eq(var(c1.interleave), int(0)))],
        )],
    );
    (p, [c0, c1])
}

// --------------------------------------------------- tvip_axi_slave_item

struct SlaveVars {
    data: svrand::ArrayId,
    response: svrand::ArrayId,
    start_delay: svrand::VarId,
    response_delay: svrand::ArrayId,
    address_ready_delay: svrand::VarId,
    write_data_ready_delay: svrand::ArrayId,
    need_response: svrand::VarId,
}

/// `tvip_axi_slave_item` as the default slave sequence randomizes it, for a
/// request already received (access type, burst length are state). The
/// slave configuration after its `post_randomize`: weights 6/2/1/1, delays
/// sample (`delay`) or zero.
fn slave_item(write: bool, burst_length: i64, delay: Delay) -> (Problem, SlaveVars) {
    let mut p = Problem::new();
    // pre_randomize: access_type, id, address, burst_*, protection, qos,
    // strobe, write_data_delay, response_ready_delay are state; data is rand
    // only for a read.
    let _memory_type = p.var("memory_type", 32, true);
    let data = p.array("data", 1024, false, ArraySize::Dynamic { max: 256 });
    let response = p.array("response", 2, false, ArraySize::Dynamic { max: 256 });
    let start_delay = p.var("start_delay", 32, true);
    let response_delay = p.array("response_delay", 32, true, ArraySize::Dynamic { max: 256 });
    let address_ready_delay = p.var("address_ready_delay", 32, true);
    let write_data_ready_delay = p.array(
        "write_data_ready_delay",
        32,
        true,
        ArraySize::Dynamic { max: 256 },
    );
    let need_response = p.var("need_response", 1, false);
    let is_write = || int(write as i64);
    let bl = || int(burst_length);

    p.constraint(
        0,
        vec![item(inside(
            var(_memory_type),
            vec![range(int(0), int(11))],
        ))],
    );
    // c_valid_read_data is on only for a read; for a write, data is state
    // (empty here).
    let i = p.loop_var();
    if write {
        p.constraint(1, vec![item(eq(size(data), int(0)))]);
    } else {
        p.constraint(
            1,
            vec![
                item(eq(size(data), bl())),
                foreach(
                    data,
                    i,
                    vec![item(eq(bin(Shr, elem(data, lp(i)), int(64)), int(0)))],
                ),
            ],
        );
    }
    // c_valid_response
    let i = p.loop_var();
    p.constraint(
        2,
        vec![
            item(bin(Implies, is_write(), eq(size(response), int(1)))),
            item(bin(
                Implies,
                un(UnOp::LogNot, is_write()),
                eq(size(response), bl()),
            )),
            foreach(
                response,
                i,
                vec![dist(
                    elem(response, lp(i)),
                    vec![
                        each(val(int(0)), int(6)),
                        each(val(int(1)), int(2)),
                        each(val(int(2)), int(1)),
                        each(val(int(3)), int(1)),
                    ],
                )],
            ),
        ],
    );
    // c_address_ready_delay (awready / arready: both `delay` here)
    p.constraint(
        3,
        vec![if_else(
            is_write(),
            vec![delay_constraint(var(address_ready_delay), delay)],
            vec![delay_constraint(var(address_ready_delay), delay)],
        )],
    );
    // c_write_data_ready_delay
    let i = p.loop_var();
    p.constraint(
        4,
        vec![
            if_else(
                is_write(),
                vec![item(eq(size(write_data_ready_delay), bl()))],
                vec![item(eq(size(write_data_ready_delay), int(0)))],
            ),
            foreach(
                write_data_ready_delay,
                i,
                vec![delay_constraint(elem(write_data_ready_delay, lp(i)), delay)],
            ),
        ],
    );
    // c_response_start_delay
    p.constraint(5, vec![delay_constraint(var(start_delay), delay)]);
    // c_response_delay
    let i = p.loop_var();
    p.constraint(
        6,
        vec![
            if_else(
                is_write(),
                vec![item(eq(size(response_delay), int(1)))],
                vec![item(eq(size(response_delay), bl()))],
            ),
            foreach(
                response_delay,
                i,
                vec![delay_constraint(elem(response_delay, lp(i)), delay)],
            ),
        ],
    );
    // c_default_need_response (tvip_axi_slave_item)
    p.constraint(7, vec![soft(item(eq(var(need_response), int(1))))]);
    (
        p,
        SlaveVars {
            data,
            response,
            start_delay,
            response_delay,
            address_ready_delay,
            write_data_ready_delay,
            need_response,
        },
    )
}

// --------------------------------------------- std::randomize in the driver

/// `randomize_ready_delay`: `std::randomize(delay) with
/// { tvip_delay_constraint(delay, cfg) }` — a local variable.
fn ready_delay(cfg: Delay) -> (Problem, svrand::VarId) {
    let mut p = Problem::new();
    let d = p.var("delay", 32, true);
    p.constraint(0, vec![delay_constraint(var(d), cfg)]);
    (p, d)
}

/// `randomize_response_size`: `std::randomize(size) with { size inside
/// {[1:remaining]}; if ((min > 0) && (remaining >= min)) size >= min; if
/// (max > 0) size <= max; }` — the locals are state.
fn response_size(remaining: i64, min: i64, max: i64) -> (Problem, svrand::VarId) {
    let mut p = Problem::new();
    let s = p.var("size", 32, true);
    p.constraint(
        0,
        vec![
            item(inside(var(s), vec![range(int(1), int(remaining))])),
            if_(
                and(gt(int(min), int(0)), ge(int(remaining), int(min))),
                vec![item(ge(var(s), int(min)))],
            ),
            if_(gt(int(max), int(0)), vec![item(le(var(s), int(max)))]),
        ],
    );
    (p, s)
}

// ------------------------------------------------------------------ runner

struct Run {
    n: usize,
    ok: usize,
    checks: u64,
    rebuilds: u64,
    solver_ms: f64,
    wall_ms: f64,
    max_wall_ms: f64,
}

fn run(
    name: &str,
    n: usize,
    seed: u64,
    p: &Problem,
    funcs: &mut dyn FuncEval,
    mut each: impl FnMut(&Solution),
) {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut r = Run {
        n,
        ok: 0,
        checks: 0,
        rebuilds: 0,
        solver_ms: 0.0,
        wall_ms: 0.0,
        max_wall_ms: 0.0,
    };
    for k in 0..n {
        let t = Instant::now();
        match p.solve(&mut rng, funcs) {
            Ok((sol, st)) => {
                let ms = t.elapsed().as_secs_f64() * 1e3;
                r.wall_ms += ms;
                r.max_wall_ms = r.max_wall_ms.max(ms);
                r.checks += u64::from(st.checks);
                r.rebuilds = r.rebuilds.max(st.sat_vars as u64);
                r.solver_ms += st.solver_time.as_secs_f64() * 1e3;
                match p.verify(&sol, funcs) {
                    Ok(()) => r.ok += 1,
                    Err(m) => println!("  [{name} #{k}] VIOLATION: {m}"),
                }
                each(&sol);
            }
            Err(e) => println!("  [{name} #{k}] solve failed: {e:?}"),
        }
    }
    println!(
        "{name}: {}/{} verified, {:.1} checks/solve, {} SAT vars, {:.0} ms/solve (solver {:.0} ms, max {:.0} ms)",
        r.ok,
        r.n,
        r.checks as f64 / r.n as f64,
        r.rebuilds,
        r.wall_ms / r.n as f64,
        r.solver_ms / r.n as f64,
        r.max_wall_ms
    );
}

fn hist(name: &str, h: &BTreeMap<String, usize>) {
    let s: Vec<String> = h.iter().map(|(k, v)| format!("{k}:{v}")).collect();
    println!("  {name}: {}", s.join(" "));
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let which = args.get(1).map_or("all", String::as_str);
    let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10);
    let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1);

    if which == "item" || which == "all" {
        let (p, v) = master_write_item(3);
        let mut lens: BTreeMap<String, usize> = BTreeMap::new();
        let mut sizes: BTreeMap<String, usize> = BTreeMap::new();
        let mut delays: BTreeMap<String, usize> = BTreeMap::new();
        let mut need: BTreeMap<String, usize> = BTreeMap::new();
        let mut first = true;
        run("tvip_axi_master_item", n, seed, &p, &mut NoFuncs, |s| {
            let bl = s.var(v.burst_length).to_i64().unwrap();
            let bucket = match bl {
                1 => "1",
                2..=4 => "2-4",
                5..=16 => "5-16",
                17..=64 => "17-64",
                _ => "65-256",
            };
            *lens.entry(bucket.to_string()).or_default() += 1;
            *sizes.entry(s.var(v.burst_size).to_string()).or_default() += 1;
            for d in std::iter::once(s.var(v.start_delay)).chain(s.array(v.write_data_delay)) {
                let x = d.to_i64().unwrap();
                let b = match x {
                    0 => "0",
                    1..=3 => "1-3",
                    6..=10 => "6-10",
                    _ => "other",
                };
                *delays.entry(b.to_string()).or_default() += 1;
            }
            *need.entry(s.var(v.need_response).to_string()).or_default() += 1;
            if first {
                first = false;
                println!(
                    "  sample: access_type={} id={} address={} burst_length={} burst_size={}",
                    s.var(v.access_type),
                    s.var(v.id),
                    s.var(v.address),
                    s.var(v.burst_length),
                    s.var(v.burst_size)
                );
                println!(
                    "          data[0]={} strobe[0]={}",
                    s.array(v.data)[0],
                    s.array(v.strobe)[0]
                );
            }
        });
        hist("burst_length", &lens);
        hist("burst_size", &sizes);
        hist("delays (dist 0:=6, [1:3]:/3, [6:10]:/1)", &delays);
        hist("need_response (soft == 0)", &need);
    }
    if which == "delay" || which == "all" {
        for sample in [false, true] {
            let (p, v) = delay_configuration(sample);
            let mut seen: BTreeMap<String, usize> = BTreeMap::new();
            let name = if sample {
                "tvip_delay_configuration (sample)"
            } else {
                "tvip_delay_configuration (default)"
            };
            run(name, n, seed, &p, &mut DelayFuncs, |s| {
                let mid = s.array(v.mid);
                let k = format!(
                    "min={} max={} mid=[{},{}] wz={}",
                    s.var(v.min),
                    s.var(v.max),
                    mid[0],
                    mid[1],
                    s.var(v.wz)
                );
                *seen.entry(k).or_default() += 1;
            });
            for (k, c) in seen.iter().take(6) {
                println!("  {k} x{c}");
            }
        }
    }
    if which == "config" || which == "all" {
        let (p, v) = axi_configuration();
        let mut seen: BTreeMap<String, usize> = BTreeMap::new();
        run(
            "tvip_axi_configuration",
            n,
            seed,
            &p,
            &mut DelayFuncs,
            |s| {
                let q = s.array(v.qos_range);
                let k = format!(
                    "protocol={} id_width={} data_width={} strobe_width={} ordering={} reset_by_agent={} qos=[{},{}]",
                    s.var(v.protocol),
                    s.var(v.id_width),
                    s.var(v.data_width),
                    s.var(v.strobe_width),
                    s.var(v.response_ordering),
                    s.var(v.reset_by_agent),
                    q[0],
                    q[1]
                );
                *seen.entry(k).or_default() += 1;
            },
        );
        for (k, c) in seen.iter().take(4) {
            println!("  {k} x{c}");
        }
    }
    if which == "sample" || which == "all" {
        for enable in [false, true] {
            let (p, [c0, c1]) = sample_configuration(enable);
            let name = format!("tvip_axi_sample_configuration (enable_*={})", enable as u8);
            let mut first = true;
            run(&name, n, seed, &p, &mut DelayFuncs, |s| {
                if first {
                    first = false;
                    for (c, tag) in [(&c0, "axi_cfg[0]"), (&c1, "axi_cfg[1]")] {
                        let rs = &c.delays[0];
                        let mid = s.array(rs.mid);
                        println!(
                            "  {tag}: ordering={} outstanding={} interleave={} weights={:?} request_start_delay: min={} max={} mid=[{},{}] w={}/{}/{}",
                            s.var(c.response_ordering),
                            s.var(c.outstanding),
                            s.var(c.interleave),
                            c.weights
                                .iter()
                                .map(|w| s.var(*w).to_string())
                                .collect::<Vec<_>>(),
                            s.var(rs.min),
                            s.var(rs.max),
                            mid[0],
                            mid[1],
                            s.var(rs.wz),
                            s.var(rs.ws),
                            s.var(rs.wl)
                        );
                    }
                }
            });
        }
    }
    if which == "slave" || which == "all" {
        for (write, delay, tag) in [
            (false, SAMPLE_DELAY, "read, sample delays"),
            (true, SAMPLE_DELAY, "write, sample delays"),
            (false, ZERO_DELAY, "read, zero delays"),
        ] {
            let bl = 16;
            let (p, v) = slave_item(write, bl, delay);
            let mut resp: BTreeMap<String, usize> = BTreeMap::new();
            let mut sizes = String::new();
            let mut need: BTreeMap<String, usize> = BTreeMap::new();
            let mut first = true;
            run(
                &format!("tvip_axi_slave_item ({tag}, burst_length={bl})"),
                n,
                seed,
                &p,
                &mut NoFuncs,
                |s| {
                    for r in s.array(v.response) {
                        *resp.entry(r.to_string()).or_default() += 1;
                    }
                    *need.entry(s.var(v.need_response).to_string()).or_default() += 1;
                    if first {
                        first = false;
                        sizes = format!(
                            "data={} response={} response_delay={} write_data_ready_delay={} start_delay={} address_ready_delay={}",
                            s.array(v.data).len(),
                            s.array(v.response).len(),
                            s.array(v.response_delay).len(),
                            s.array(v.write_data_ready_delay).len(),
                            s.var(v.start_delay),
                            s.var(v.address_ready_delay)
                        );
                    }
                },
            );
            println!("  sizes: {sizes}");
            hist(
                "response (dist OKAY:=6 EXOKAY:=2 SLVERR:=1 DECERR:=1)",
                &resp,
            );
            hist("need_response (soft == 1)", &need);
        }
    }
    if which == "stdrand" || which == "all" {
        let (p, d) = ready_delay(SAMPLE_DELAY);
        let mut h: BTreeMap<String, usize> = BTreeMap::new();
        run(
            "std::randomize(delay) (randomize_ready_delay)",
            n * 10,
            seed,
            &p,
            &mut NoFuncs,
            |s| {
                let x = s.var(d).to_i64().unwrap();
                let b = match x {
                    0 => "0",
                    1..=3 => "1-3",
                    6..=10 => "6-10",
                    _ => "other",
                };
                *h.entry(b.to_string()).or_default() += 1;
            },
        );
        hist("delay (dist 0:=6, [1:3]:/3, [6:10]:/1)", &h);
        for (rem, min, max) in [(13, 2, 4), (1, 2, 4), (13, 0, 0)] {
            let (p, sz) = response_size(rem, min, max);
            let mut h: BTreeMap<i64, usize> = BTreeMap::new();
            run(
                &format!("std::randomize(size) (remaining={rem} min={min} max={max})"),
                n * 10,
                seed,
                &p,
                &mut NoFuncs,
                |s| {
                    *h.entry(s.var(sz).to_i64().unwrap()).or_default() += 1;
                },
            );
            println!("  size: {h:?}");
        }
    }
}
