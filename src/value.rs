//! Two-state values of any width.

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};

/// A two-state packed value: `width` bits, held as an unsigned integer below
/// `2**width`. `signed` is the type's signedness; it only changes how the bits
/// are read (`to_bigint`), never the bits themselves.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Bits {
    width: u32,
    signed: bool,
    val: BigUint,
}

pub(crate) fn mask(width: u32) -> BigUint {
    (BigUint::one() << width) - BigUint::one()
}

impl Bits {
    /// `val` is reduced modulo `2**width`.
    pub fn new(width: u32, signed: bool, val: BigUint) -> Self {
        assert!(width > 0, "zero-width value");
        Bits {
            width,
            signed,
            val: val & mask(width),
        }
    }

    /// Two's complement of `v` in `width` bits.
    pub fn from_bigint(width: u32, signed: bool, v: &BigInt) -> Self {
        let m = BigInt::one() << width;
        let r = ((v % &m) + &m) % &m;
        Bits::new(width, signed, r.to_biguint().unwrap())
    }

    pub fn from_i64(width: u32, signed: bool, v: i64) -> Self {
        Bits::from_bigint(width, signed, &BigInt::from(v))
    }

    pub fn from_u64(width: u32, signed: bool, v: u64) -> Self {
        Bits::new(width, signed, BigUint::from(v))
    }

    pub fn width(&self) -> u32 {
        self.width
    }

    pub fn signed(&self) -> bool {
        self.signed
    }

    /// The bits as an unsigned integer.
    pub fn bits(&self) -> &BigUint {
        &self.val
    }

    /// The value the bits denote under the type's signedness.
    pub fn to_bigint(&self) -> BigInt {
        let u = BigInt::from_biguint(Sign::Plus, self.val.clone());
        if self.signed && self.val.bit(u64::from(self.width - 1)) {
            u - (BigInt::one() << self.width)
        } else {
            u
        }
    }

    pub fn to_i64(&self) -> Option<i64> {
        i64::try_from(self.to_bigint()).ok()
    }

    pub fn is_zero(&self) -> bool {
        self.val.is_zero()
    }
}

impl std::fmt::Display for Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.signed {
            write!(f, "{}", self.to_bigint())
        } else {
            write!(f, "'h{:x}", self.val)
        }
    }
}
