pub mod literals;

pub use num_bigint;
pub use num_bigint::BigInt;
use num_bigint::{BigUint, ParseBigIntError, ToBigInt, ToBigUint};
pub use num_complex;
pub use num_complex::Complex64;
pub use num_rational;
use num_rational::{BigRational, Rational64};
pub use num_traits;
use num_traits::checked_pow;
pub use num_traits::{Num, One, Pow, Signed, ToPrimitive, Zero};
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Int {
    SmallInt(i64),
    BigInt(BigInt),
}

impl Int {
    pub fn true_div(&self, rhs: &Self) -> Option<f64> {
        let (left, right) = match (self, rhs) {
            (Int::SmallInt(left), Int::SmallInt(right)) => {
                if let Some(value) = Rational64::new(*left, *right).to_f64() {
                    return Some(value);
                }
                (&BigInt::from(*left), &BigInt::from(*right))
            }
            (Int::SmallInt(left), Int::BigInt(right)) => (&BigInt::from(*left), right),
            (Int::BigInt(left), Int::SmallInt(right)) => (left, &BigInt::from(*right)),
            (Int::BigInt(left), Int::BigInt(right)) => (left, right),
        };

        let Some(value) = BigRational::new(left.clone(), right.clone()).to_f64() else {
            return None;
        };

        Some(value)
    }
}

macro_rules! impl_int_binop_method {
    ($rhs_ty:ty, $method:ident, $checked:ident, $op:tt) => {
        fn $method(self, rhs: $rhs_ty) -> Self::Output {
            match (&self, &rhs) {
                (Int::SmallInt(left), Int::SmallInt(right)) => {
                    if let Some(result) = left.$checked(*right) {
                        Int::SmallInt(result)
                    } else {
                        Int::BigInt(BigInt::from(*left) $op right)
                    }
                }
                (Int::SmallInt(left), Int::BigInt(right)) => {
                    Int::BigInt(BigInt::from(*left) $op right)
                }
                (Int::BigInt(left), Int::SmallInt(right)) => {
                    Int::BigInt(left $op right)
                }
                (Int::BigInt(left), Int::BigInt(right)) => {
                    Int::BigInt(left $op right)
                }
            }
        }
    };
    (infallible: $rhs_ty:ty, $method:ident, $op:tt) => {
        fn $method(self, rhs: $rhs_ty) -> Self::Output {
            match (&self, &rhs) {
                (Int::SmallInt(left), Int::SmallInt(right)) => {
                    Int::SmallInt(left $op right)
                }
                (Int::SmallInt(left), Int::BigInt(right)) => {
                    Int::BigInt(BigInt::from(*left) $op right)
                }
                (Int::BigInt(left), Int::SmallInt(right)) => {
                    Int::BigInt(left $op BigInt::from(*right))
                }
                (Int::BigInt(left), Int::BigInt(right)) => {
                    Int::BigInt(left $op right)
                }
            }
        }
    };
    (shift: $rhs_ty:ty, $method:ident, $checked:ident, $op:tt) => {
        fn $method(self, rhs: $rhs_ty) -> Self::Output {
            match &self {
                Int::SmallInt(left) => {
                    if let Some(result) = u32::try_from(rhs.clone())
                        .ok()
                        .and_then(|right| left.$checked(right))
                    {
                        Int::SmallInt(result)
                    } else {
                        Int::BigInt(BigInt::from(*left) $op rhs)
                    }
                }
                Int::BigInt(left) => Int::BigInt(left $op rhs),
            }
        }
    };
    (pow_usize: $rhs_ty:ty) => {
        fn pow(self, rhs: $rhs_ty) -> Self::Output {
            match &self {
                Int::SmallInt(n) => {
                    if let Some(result) = checked_pow(*n, rhs.clone()) {
                        Int::SmallInt(result)
                    } else {
                        Int::BigInt(Pow::pow(BigInt::from(*n), rhs))
                    }
                }
                Int::BigInt(n) => Int::BigInt(Pow::pow(n, rhs)),
            }
        }
    };
    (pow_biguint: $rhs_ty:ty) => {
        fn pow(self, rhs: $rhs_ty) -> Self::Output {
            match &self {
                Int::SmallInt(n) => Int::BigInt(Pow::pow(BigInt::from(*n), rhs)),
                Int::BigInt(n) => Int::BigInt(Pow::pow(n, rhs)),
            }
        }
    }
}

macro_rules! impl_int_binop {
    ($trait:ident, $method:ident, $checked:ident, $op:tt) => {
        impl $trait<Int> for Int {
            type Output = Int;

            impl_int_binop_method!(Int, $method, $checked, $op);
        }
        impl $trait<Int> for &Int {
            type Output = Int;

            impl_int_binop_method!(Int, $method, $checked, $op);
        }
        impl $trait<&Int> for Int {
            type Output = Int;

            impl_int_binop_method!(&Int, $method, $checked, $op);
        }
        impl $trait<&Int> for &Int {
            type Output = Int;

            impl_int_binop_method!(&Int, $method, $checked, $op);
        }
    };
    (infallible: $trait:ident, $method:ident, $op:tt) => {
        impl $trait<Int> for Int {
            type Output = Int;

            impl_int_binop_method!(infallible: Int, $method, $op);
        }
        impl $trait<Int> for &Int {
            type Output = Int;

            impl_int_binop_method!(infallible: Int, $method, $op);
        }
        impl $trait<&Int> for Int {
            type Output = Int;

            impl_int_binop_method!(infallible: &Int, $method, $op);
        }
        impl $trait<&Int> for &Int {
            type Output = Int;

            impl_int_binop_method!(infallible: &Int, $method, $op);
        }
    };
    (shift: $trait:ident<$rhs_ty:ty>, $method:ident, $checked:ident, $op:tt) => {
        impl $trait<$rhs_ty> for Int {
            type Output = Int;

            impl_int_binop_method!(shift: $rhs_ty, $method, $checked, $op);
        }
        impl $trait<$rhs_ty> for &Int {
            type Output = Int;

            impl_int_binop_method!(shift: $rhs_ty, $method, $checked, $op);
        }
        impl $trait<&$rhs_ty> for Int {
            type Output = Int;

            impl_int_binop_method!(shift: &$rhs_ty, $method, $checked, $op);
        }
        impl $trait<&$rhs_ty> for &Int {
            type Output = Int;

            impl_int_binop_method!(shift: &$rhs_ty, $method, $checked, $op);
        }
    };
    (pow: $implementation:tt, $rhs_ty:ty) => {
        impl Pow<$rhs_ty> for Int {
            type Output = Int;

            impl_int_binop_method!($implementation: $rhs_ty);
        }
        impl Pow<$rhs_ty> for &Int {
            type Output = Int;

            impl_int_binop_method!($implementation: $rhs_ty);
        }
        impl Pow<&$rhs_ty> for Int {
            type Output = Int;

            impl_int_binop_method!($implementation: &$rhs_ty);
        }
        impl Pow<&$rhs_ty> for &Int {
            type Output = Int;

            impl_int_binop_method!($implementation: &$rhs_ty);
        }
    }
}

impl_int_binop!(Add, add, checked_add, +);
impl_int_binop!(Sub, sub, checked_sub, -);
impl_int_binop!(Mul, mul, checked_mul, *);
impl_int_binop!(Div, div, checked_div, /);
impl_int_binop!(Rem, rem, checked_rem, %);
impl_int_binop!(shift: Shl<usize>, shl, checked_shl, <<);
impl_int_binop!(shift: Shl<isize>, shl, checked_shl, <<);
impl_int_binop!(shift: Shr<usize>, shr, checked_shr, >>);
impl_int_binop!(shift: Shr<isize>, shr, checked_shr, >>);
impl_int_binop!(infallible: BitOr,  bitor,  |);
impl_int_binop!(infallible: BitXor, bitxor, ^);
impl_int_binop!(infallible: BitAnd, bitand, &);
impl_int_binop!(pow: pow_usize, usize);
impl_int_binop!(pow: pow_biguint, BigUint);

macro_rules! impl_int_shift_method {
    ($rhs_ty:ty, $method:ident) => {
        fn $method(self, other: $rhs_ty) -> Self::Output {
            if let Some(small_other) = other.to_usize() {
                Some(self.$method(small_other))
            } else if let Some(small_other) = other.to_isize() {
                Some(self.$method(small_other))
            } else {
                None
            }
        }
    };
}

impl Shl<Self> for Int {
    type Output = Option<Int>;

    impl_int_shift_method!(Self, shl);
}

impl Shl<Self> for &Int {
    type Output = Option<Int>;

    impl_int_shift_method!(Self, shl);
}

impl Shl<&Self> for Int {
    type Output = Option<Int>;

    impl_int_shift_method!(&Self, shl);
}

impl Shl<&Self> for &Int {
    type Output = Option<Int>;

    impl_int_shift_method!(&Self, shl);
}

impl Shr<Self> for Int {
    type Output = Option<Int>;

    impl_int_shift_method!(Self, shr);
}

impl Shr<Self> for &Int {
    type Output = Option<Int>;

    impl_int_shift_method!(Self, shr);
}

impl Shr<&Self> for Int {
    type Output = Option<Int>;

    impl_int_shift_method!(&Self, shr);
}

impl Shr<&Self> for &Int {
    type Output = Option<Int>;

    impl_int_shift_method!(&Self, shr);
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum PowOutput {
    Int(Int),
    Float(f64),
}

macro_rules! impl_int_pow_method {
    ($rhs_ty:ty) => {
        fn pow(self, other: $rhs_ty) -> Self::Output {
            if let Some(small_other) = other.to_usize() {
                Some(PowOutput::Int(self.pow(small_other)))
            } else if let Some(big_other) = other.to_biguint() {
                Some(PowOutput::Int(self.pow(big_other)))
            } else if let (Some(self_float), Some(other_float)) = (self.to_f64(), other.to_f64()) {
                Some(PowOutput::Float(self_float.pow(other_float)))
            } else {
                None
            }
        }
    };
}

impl Pow<Self> for Int {
    type Output = Option<PowOutput>;

    impl_int_pow_method!(Self);
}

impl Pow<Self> for &Int {
    type Output = Option<PowOutput>;

    impl_int_pow_method!(Self);
}

impl Pow<&Self> for Int {
    type Output = Option<PowOutput>;

    impl_int_pow_method!(&Self);
}

impl Pow<&Self> for &Int {
    type Output = Option<PowOutput>;

    impl_int_pow_method!(&Self);
}

macro_rules! impl_int_neg_method {
    () => {
        fn neg(self) -> Self::Output {
            match &self {
                Int::SmallInt(n) => {
                    if let Some(result) = n.checked_neg() {
                        Int::SmallInt(result)
                    } else {
                        Int::BigInt(-BigInt::from(*n))
                    }
                }
                Int::BigInt(n) => Int::BigInt(-n),
            }
        }
    };
}

impl Neg for Int {
    type Output = Int;

    impl_int_neg_method!();
}

impl Neg for &Int {
    type Output = Int;

    impl_int_neg_method!();
}

macro_rules! impl_int_not_method {
    () => {
        fn not(self) -> Self::Output {
            match self {
                Int::SmallInt(n) => Int::SmallInt(!n),
                Int::BigInt(n) => Int::BigInt(!n),
            }
        }
    };
}

impl Not for Int {
    type Output = Int;

    impl_int_not_method!();
}

impl Not for &Int {
    type Output = Int;

    impl_int_not_method!();
}

macro_rules! impl_int_to_primitive {
    ($($method:ident -> $ty:ty),* $(,)?) => {
        $(
            fn $method(&self) -> Option<$ty> {
                match self {
                    Int::SmallInt(n) => n.$method(),
                    Int::BigInt(n) => n.$method(),
                }
            }
        )*
    };
}

impl ToPrimitive for Int {
    impl_int_to_primitive!(
        to_isize -> isize,
        to_i8 -> i8,
        to_i16 -> i16,
        to_i32 -> i32,
        to_i64 -> i64,
        to_i128 -> i128,
        to_usize -> usize,
        to_u8 -> u8,
        to_u16 -> u16,
        to_u32 -> u32,
        to_u64 -> u64,
        to_u128 -> u128,
        to_f32 -> f32,
        to_f64 -> f64,
    );
}

impl ToBigInt for Int {
    fn to_bigint(&self) -> Option<BigInt> {
        match self {
            Int::SmallInt(n) => n.to_bigint(),
            Int::BigInt(n) => n.to_bigint(),
        }
    }
}

impl ToBigUint for Int {
    fn to_biguint(&self) -> Option<BigUint> {
        match self {
            Int::SmallInt(n) => n.to_biguint(),
            Int::BigInt(n) => n.to_biguint(),
        }
    }
}

impl Num for Int {
    type FromStrRadixErr = ParseBigIntError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Ok(if let Ok(n) = i64::from_str_radix(str, radix) {
            Int::SmallInt(n)
        } else {
            Int::BigInt(BigInt::from_str_radix(str, radix)?)
        })
    }
}

impl Zero for Int {
    fn zero() -> Self {
        Int::SmallInt(0)
    }

    fn is_zero(&self) -> bool {
        match self {
            Int::SmallInt(n) => *n == 0,
            Int::BigInt(n) => *n == BigInt::ZERO,
        }
    }
}

impl One for Int {
    fn one() -> Self {
        Int::SmallInt(1)
    }
}

impl Signed for Int {
    fn abs(&self) -> Self {
        match self {
            Int::SmallInt(n) => Int::SmallInt(n.abs()),
            Int::BigInt(n) => Int::BigInt(n.abs()),
        }
    }

    fn abs_sub(&self, other: &Self) -> Self {
        if *self <= *other {
            Self::zero()
        } else {
            self - other
        }
    }

    fn signum(&self) -> Self {
        match self {
            Int::SmallInt(n) => Int::SmallInt(n.signum()),
            Int::BigInt(n) => Int::BigInt(n.signum()),
        }
    }

    fn is_positive(&self) -> bool {
        match self {
            Int::SmallInt(n) => n.is_positive(),
            Int::BigInt(n) => n.is_positive(),
        }
    }

    fn is_negative(&self) -> bool {
        match self {
            Int::SmallInt(n) => n.is_negative(),
            Int::BigInt(n) => n.is_negative(),
        }
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Int::SmallInt(n) => write!(f, "{}", n),
            Int::BigInt(n) => write!(f, "{}", n),
        }
    }
}
