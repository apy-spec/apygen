use crate::{BigInt, Complex64, Int, ToPrimitive};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter, Write};
use std::hash::Hash;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralInt {
    pub value: Int,
}

impl LiteralInt {
    pub fn new(value: Int) -> Self {
        Self { value }
    }

    pub fn to_literal_float(&self) -> Option<LiteralFloat> {
        Some(LiteralFloat::new(self.value.to_f64()?))
    }

    pub fn to_literal_complex(&self) -> Option<LiteralComplex> {
        Some(LiteralComplex::new(Complex64::new(
            self.value.to_f64()?,
            0.0,
        )))
    }
}

impl From<i64> for LiteralInt {
    fn from(value: i64) -> Self {
        Self::new(Int::SmallInt(value))
    }
}

impl From<BigInt> for LiteralInt {
    fn from(value: BigInt) -> Self {
        Self::new(Int::BigInt(value))
    }
}

impl Display for LiteralInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralBool {
    pub value: bool,
}

impl Display for LiteralBool {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.value {
            write!(f, "True")
        } else {
            write!(f, "False")
        }
    }
}

#[derive(Debug, Clone)]
pub struct LiteralFloat {
    pub value: f64,
}

impl LiteralFloat {
    pub fn new(value: f64) -> Self {
        LiteralFloat { value }
    }

    pub fn to_literal_complex(&self) -> Option<LiteralComplex> {
        Some(LiteralComplex {
            value: Complex64::new(self.value, 0.0),
        })
    }
}

// LiteralFloat is metadata about a float literal so we can implement Eq, Ord and Hash.
impl PartialEq<Self> for LiteralFloat {
    fn eq(&self, other: &Self) -> bool {
        if self.value.is_nan() {
            other.value.is_nan()
        } else {
            self.value == other.value
        }
    }
}

impl Eq for LiteralFloat {}

impl PartialOrd<Self> for LiteralFloat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LiteralFloat {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.value < other.value {
            Ordering::Less
        } else if self.value > other.value {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

impl Hash for LiteralFloat {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.to_bits().hash(state);
    }
}

impl Display for LiteralFloat {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone)]
pub struct LiteralComplex {
    pub value: Complex64,
}

impl LiteralComplex {
    pub fn new(value: Complex64) -> Self {
        Self { value }
    }
}

// LiteralComplex is metadata about a complex literal so we can implement Eq, Ord and Hash.
impl PartialEq for LiteralComplex {
    fn eq(&self, other: &Self) -> bool {
        LiteralFloat::new(self.value.re) == LiteralFloat::new(other.value.re)
            && LiteralFloat::new(self.value.im) == LiteralFloat::new(other.value.im)
    }
}

impl Eq for LiteralComplex {}

impl PartialOrd for LiteralComplex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LiteralComplex {
    fn cmp(&self, other: &Self) -> Ordering {
        match LiteralFloat::new(self.value.re).cmp(&LiteralFloat::new(other.value.re)) {
            Ordering::Equal => {
                LiteralFloat::new(self.value.im).cmp(&LiteralFloat::new(other.value.im))
            }
            ordering => ordering,
        }
    }
}

impl Hash for LiteralComplex {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.re.to_bits().hash(state);
        self.value.im.to_bits().hash(state);
    }
}

impl Display for LiteralComplex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralStr {
    pub value: Arc<String>,
}

impl LiteralStr {
    pub fn new(value: Arc<String>) -> Self {
        Self { value }
    }
}

impl From<&str> for LiteralStr {
    fn from(value: &str) -> Self {
        Self::new(Arc::new(value.to_owned()))
    }
}

impl Display for LiteralStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralBytes {
    pub value: Arc<Vec<u8>>,
}

impl LiteralBytes {
    pub fn new(value: Arc<Vec<u8>>) -> Self {
        Self { value }
    }
}

impl Display for LiteralBytes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("b\"")?;
        for element in self.value.as_ref() {
            if element.is_ascii_alphanumeric() {
                f.write_char(*element as char)?;
            } else {
                write!(f, "\\x{:02X}", element)?;
            }
        }
        f.write_str("\"")
    }
}
