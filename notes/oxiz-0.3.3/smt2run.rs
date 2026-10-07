fn main() {
    let path = std::env::args().nth(1).unwrap();
    let script = std::fs::read_to_string(path).unwrap();
    let mut ctx = oxiz::solver::Context::new();
    match ctx.execute_script(&script) {
        Ok(out) => println!("{}", out.join(" ")),
        Err(e) => println!("error: {e:?}"),
    }
}
