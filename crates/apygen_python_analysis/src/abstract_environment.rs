use crate::analysis::lattice::ContextualLattice;
use crate::analysis::namespace::{Location, NamespaceLocation, Namespaces};
use crate::constraints::QualifiedLocation;
pub use apy::OneOrMany;
pub use apy::v1::{GenericKind, Identifier, ParameterKind, ParseIdentifierError, QualifiedName};
use apygen_analysis::lattice::{Lattice, OrdLattice};
use imbl;
pub use num_bigint::BigInt;
use num_bigint::BigUint;
use num_complex::Complex64;
use num_traits::{Pow, ToPrimitive, checked_pow};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};
use std::sync::Arc;
use thiserror::Error;

pub const BUILTINS_MODULE: &str = "builtins";
pub const TYPES_MODULE: &str = "types";
pub const TYPING_MODULE: &str = "typing";
pub const TYPING_EXTENSIONS_MODULE: &str = "typing_extensions";
pub const ABC_MODULE: &str = "abc";
pub const DEPTH_LIMIT: usize = 20;
pub const WIDTH_LIMIT: usize = 20;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Source {
    #[default]
    Inferred,
    Specified,
}

impl OrdLattice for Source {}

impl Display for Source {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Sourced<T: Clone> {
    pub data: T,
    pub source: Source,
}

impl<T: Clone> Sourced<T> {
    pub fn new(data: T, source: Source) -> Self {
        Sourced { data, source }
    }

    pub fn inferred(data: T) -> Self {
        Sourced::new(data, Source::Inferred)
    }

    pub fn specified(data: T) -> Self {
        Sourced::new(data, Source::Specified)
    }

    pub fn map<U: Clone>(self, f: impl FnOnce(T) -> U) -> Sourced<U> {
        Sourced {
            data: f(self.data),
            source: self.source,
        }
    }
}

impl<T: Clone + Lattice> Lattice for Sourced<T> {
    fn includes(&self, other: &Self) -> bool {
        match (&self.source, &other.source) {
            (Source::Specified, Source::Specified) => self.data.includes(&other.data),
            (Source::Inferred, Source::Inferred) => self.data.includes(&other.data),
            (Source::Inferred, Source::Specified) => false,
            (Source::Specified, Source::Inferred) => true,
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (&self.source, &other.source) {
            (Source::Specified, Source::Specified) => Sourced {
                data: self.data.join(&other.data),
                source: Source::Specified,
            },
            (Source::Inferred, Source::Inferred) => Sourced {
                data: self.data.join(&other.data),
                source: Source::Inferred,
            },
            (Source::Inferred, Source::Specified) => other.clone(),
            (Source::Specified, Source::Inferred) => self.clone(),
        }
    }
}

impl<C, T: ContextualLattice<C> + Clone> ContextualLattice<C> for Sourced<T> {
    type Error = T::Error;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error> {
        match (&self.source, &other.source) {
            (Source::Specified, Source::Specified) => self.data.includes(context, &other.data),
            (Source::Inferred, Source::Inferred) => self.data.includes(context, &other.data),
            (Source::Inferred, Source::Specified) => Ok(false),
            (Source::Specified, Source::Inferred) => Ok(true),
        }
    }

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error> {
        match (&self.source, &other.source) {
            (Source::Specified, Source::Specified) => Ok(Sourced {
                data: self.data.join(context, &other.data)?,
                source: Source::Specified,
            }),
            (Source::Inferred, Source::Inferred) => Ok(Sourced {
                data: self.data.join(context, &other.data)?,
                source: Source::Inferred,
            }),
            (Source::Inferred, Source::Specified) => Ok(other.clone()),
            (Source::Specified, Source::Inferred) => Ok(self.clone()),
        }
    }
}

impl<T: Clone + Display> Display for Sourced<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sourced(data={}, source={})", self.data, self.source)
    }
}

fn iter_depth<'a, S: StructuralDepth + 'a>(iter: impl Iterator<Item = &'a S>) -> usize {
    iter.map(|item| item.depth()).max().unwrap_or(0)
}

pub trait StructuralDepth {
    fn depth(&self) -> usize;
}

impl<S: StructuralDepth> StructuralDepth for Arc<S> {
    fn depth(&self) -> usize {
        self.as_ref().depth()
    }
}

impl<S: StructuralDepth> StructuralDepth for Option<S> {
    fn depth(&self) -> usize {
        match self {
            None => 0,
            Some(value) => value.depth(),
        }
    }
}

impl<S: StructuralDepth> StructuralDepth for imbl::Vector<S> {
    fn depth(&self) -> usize {
        iter_depth(self.iter())
    }
}

impl<S: StructuralDepth + Ord> StructuralDepth for imbl::OrdSet<S> {
    fn depth(&self) -> usize {
        iter_depth(self.iter())
    }
}

fn iter_width<'a, S: StructuralWidth + 'a>(iter: impl Iterator<Item = &'a S>) -> usize {
    iter.map(|item| item.width()).sum()
}

pub trait StructuralWidth {
    fn width(&self) -> usize;
}

impl<S: StructuralWidth> StructuralWidth for Arc<S> {
    fn width(&self) -> usize {
        self.as_ref().width()
    }
}

impl<S: StructuralWidth> StructuralWidth for Option<S> {
    fn width(&self) -> usize {
        match self {
            None => 0,
            Some(value) => value.width(),
        }
    }
}

impl<S: StructuralWidth> StructuralWidth for imbl::Vector<S> {
    fn width(&self) -> usize {
        iter_width(self.iter())
    }
}

impl<S: StructuralWidth + Ord> StructuralWidth for imbl::OrdSet<S> {
    fn width(&self) -> usize {
        iter_width(self.iter())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Parameter {
    pub name: Arc<Identifier>,

    pub kind: ParameterKind,

    pub is_optional: bool,

    pub deprecation: Deprecation,
}

impl StructuralDepth for Parameter {
    fn depth(&self) -> usize {
        1
    }
}

impl StructuralWidth for Parameter {
    fn width(&self) -> usize {
        1
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericType {
    pub name: Arc<Identifier>,

    pub location: Location<QualifiedName>,

    pub kind: GenericKind,

    pub bound: Arc<Type>,

    pub constraints: imbl::Vector<Arc<Type>>,

    pub default: Option<Arc<Type>>,

    pub is_covariant: bool,

    pub is_contravariant: bool,
}

impl StructuralDepth for GenericType {
    fn depth(&self) -> usize {
        1 + self
            .bound
            .depth()
            .max(self.constraints.depth())
            .max(self.default.depth())
    }
}

impl StructuralWidth for GenericType {
    fn width(&self) -> usize {
        self.bound.width() + self.constraints.width() + self.default.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExceptionOrigin {
    Unknown,
    Raised(Location<QualifiedName>),
    Specified,
    Propagated(NamespaceLocation<QualifiedName>),
}

impl Display for ExceptionOrigin {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ExceptionOrigin::Unknown => write!(f, "Unknown"),
            ExceptionOrigin::Raised(location) => write!(f, "Raised({location})"),
            ExceptionOrigin::Specified => write!(f, "Specified"),
            ExceptionOrigin::Propagated(namespace_location) => {
                write!(f, "Propagated({namespace_location})")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Exception {
    pub exception_type: Arc<Type>,

    pub origin: ExceptionOrigin,
}

impl Exception {
    pub fn new(exception_type: Arc<Type>, origin: ExceptionOrigin) -> Self {
        Exception {
            exception_type,
            origin,
        }
    }

    pub fn any() -> Self {
        Exception::new(Arc::new(Type::Any), ExceptionOrigin::Unknown)
    }

    pub fn builtins(name: &str, origin: ExceptionOrigin) -> Self {
        Exception::new(
            Arc::new(Type::Instance(TypeInstance::builtins(name))),
            origin,
        )
    }

    pub fn type_error(origin: ExceptionOrigin) -> Self {
        Exception::builtins("TypeError", origin)
    }
}

impl Display for Exception {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Exception(type={}, origin={})",
            self.exception_type, self.origin
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionType {
    pub name: Arc<Identifier>,

    pub location: Location<QualifiedName>,

    pub qualified_location: QualifiedLocation,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub parameters: imbl::Vector<Parameter>,

    pub is_async: bool,
}

impl StructuralDepth for FunctionType {
    fn depth(&self) -> usize {
        1 + self
            .parameters
            .depth()
            .max(iter_depth(self.generics.values()))
    }
}

impl StructuralWidth for FunctionType {
    fn width(&self) -> usize {
        self.parameters.width() + iter_width(self.generics.values())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OverloadedFunctionType {
    pub overloads: imbl::Vector<LiteralFunction>,
    pub target: Option<LiteralFunction>,
}

impl OverloadedFunctionType {
    pub fn add_overload(&self, overload: LiteralFunction) -> Self {
        let mut overloads = self.overloads.clone();
        overloads.push_back(overload);
        OverloadedFunctionType {
            overloads,
            target: self.target.clone(),
        }
    }

    pub fn with_target(&self, target: Option<LiteralFunction>) -> Self {
        OverloadedFunctionType {
            overloads: self.overloads.clone(),
            target,
        }
    }
}

impl StructuralDepth for OverloadedFunctionType {
    fn depth(&self) -> usize {
        1 + self.overloads.depth().max(self.target.depth())
    }
}

impl StructuralWidth for OverloadedFunctionType {
    fn width(&self) -> usize {
        self.overloads.width() + self.target.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeAliasKind {
    Type,
    String,
    Statement,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeAliasType {
    pub name: Arc<Identifier>,

    pub location: Location<QualifiedName>,

    pub alias: Arc<Type>,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub kind: TypeAliasKind,
}

impl StructuralDepth for TypeAliasType {
    fn depth(&self) -> usize {
        1 + self.alias.depth().max(iter_depth(self.generics.values()))
    }
}

impl StructuralWidth for TypeAliasType {
    fn width(&self) -> usize {
        self.alias.width() + iter_width(self.generics.values())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClassType {
    pub name: Arc<Identifier>,

    pub location: Location<QualifiedName>,

    pub qualified_location: QualifiedLocation,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub bases: imbl::Vector<LiteralClass>,

    pub keyword_arguments: imbl::OrdMap<String, Arc<Type>>,

    pub is_abstract: bool,
}

impl StructuralDepth for ClassType {
    fn depth(&self) -> usize {
        1 + iter_depth(self.generics.values())
            .max(self.bases.depth())
            .max(iter_depth(self.keyword_arguments.values()))
    }
}

impl StructuralWidth for ClassType {
    fn width(&self) -> usize {
        iter_width(self.generics.values())
            + self.bases.width()
            + iter_depth(self.keyword_arguments.values())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportedModuleType {
    pub name: Arc<Identifier>,

    pub location: Location<QualifiedName>,

    pub module: Arc<QualifiedName>,

    pub submodules: imbl::OrdSet<Arc<QualifiedName>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LiteralInteger {
    Int(i64),
    BigInt(BigInt),
}

impl LiteralInteger {
    pub fn is_zero(&self) -> bool {
        match self {
            LiteralInteger::Int(n) => *n == 0,
            LiteralInteger::BigInt(n) => n == &BigInt::ZERO,
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            LiteralInteger::Int(n) => *n > 0,
            LiteralInteger::BigInt(n) => n > &BigInt::ZERO,
        }
    }

    pub fn is_negative(&self) -> bool {
        match self {
            LiteralInteger::Int(n) => *n < 0,
            LiteralInteger::BigInt(n) => n < &BigInt::ZERO,
        }
    }

    pub fn to_literal_float(&self) -> Option<LiteralFloat> {
        Some(LiteralFloat::new(self.to_f64()?))
    }
}

macro_rules! impl_literal_integer_binop_method {
    ($rhs_ty:ty, $method:ident, $checked:ident, $op:tt) => {
        fn $method(self, rhs: $rhs_ty) -> Self::Output {
            match (&self, &rhs) {
                (LiteralInteger::Int(left), LiteralInteger::Int(right)) => {
                    if let Some(result) = left.$checked(*right) {
                        LiteralInteger::Int(result)
                    } else {
                        LiteralInteger::BigInt(BigInt::from(*left) $op right)
                    }
                }
                (LiteralInteger::Int(left), LiteralInteger::BigInt(right)) => {
                    LiteralInteger::BigInt(BigInt::from(*left) $op right)
                }
                (LiteralInteger::BigInt(left), LiteralInteger::Int(right)) => {
                    LiteralInteger::BigInt(left $op right)
                }
                (LiteralInteger::BigInt(left), LiteralInteger::BigInt(right)) => {
                    LiteralInteger::BigInt(left $op right)
                }
            }
        }
    };
    (infallible: $rhs_ty:ty, $method:ident, $op:tt) => {
        fn $method(self, rhs: $rhs_ty) -> Self::Output {
            match (&self, &rhs) {
                (LiteralInteger::Int(left), LiteralInteger::Int(right)) => {
                    LiteralInteger::Int(left $op right)
                }
                (LiteralInteger::Int(left), LiteralInteger::BigInt(right)) => {
                    LiteralInteger::BigInt(BigInt::from(*left) $op right)
                }
                (LiteralInteger::BigInt(left), LiteralInteger::Int(right)) => {
                    LiteralInteger::BigInt(left $op BigInt::from(*right))
                }
                (LiteralInteger::BigInt(left), LiteralInteger::BigInt(right)) => {
                    LiteralInteger::BigInt(left $op right)
                }
            }
        }
    };
    (shift: $rhs_ty:ty, $method:ident, $checked:ident, $op:tt) => {
        fn $method(self, rhs: $rhs_ty) -> Self::Output {
            match &self {
                LiteralInteger::Int(left) => {
                    if let Some(result) = u32::try_from(rhs.clone())
                        .ok()
                        .and_then(|right| left.$checked(right))
                    {
                        LiteralInteger::Int(result)
                    } else {
                        LiteralInteger::BigInt(BigInt::from(*left) $op rhs)
                    }
                }
                LiteralInteger::BigInt(left) => LiteralInteger::BigInt(left $op rhs),
            }
        }
    };
    (pow_usize: $rhs_ty:ty) => {
        fn pow(self, rhs: $rhs_ty) -> Self::Output {
            match &self {
                LiteralInteger::Int(n) => {
                    if let Some(result) = checked_pow(*n, rhs.clone()) {
                        LiteralInteger::Int(result)
                    } else {
                        LiteralInteger::BigInt(Pow::pow(BigInt::from(*n), rhs))
                    }
                }
                LiteralInteger::BigInt(n) => LiteralInteger::BigInt(Pow::pow(n, rhs)),
            }
        }
    };
    (pow_biguint: $rhs_ty:ty) => {
        fn pow(self, rhs: $rhs_ty) -> Self::Output {
            match &self {
                LiteralInteger::Int(n) => LiteralInteger::BigInt(Pow::pow(BigInt::from(*n), rhs)),
                LiteralInteger::BigInt(n) => LiteralInteger::BigInt(Pow::pow(n, rhs)),
            }
        }
    }
}

macro_rules! impl_literal_integer_binop {
    ($trait:ident, $method:ident, $checked:ident, $op:tt) => {
        impl $trait<LiteralInteger> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(LiteralInteger, $method, $checked, $op);
        }
        impl $trait<LiteralInteger> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(LiteralInteger, $method, $checked, $op);
        }
        impl $trait<&LiteralInteger> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(&LiteralInteger, $method, $checked, $op);
        }
        impl $trait<&LiteralInteger> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(&LiteralInteger, $method, $checked, $op);
        }
    };
    (infallible: $trait:ident, $method:ident, $op:tt) => {
        impl $trait<LiteralInteger> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(infallible: LiteralInteger, $method, $op);
        }
        impl $trait<LiteralInteger> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(infallible: LiteralInteger, $method, $op);
        }
        impl $trait<&LiteralInteger> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(infallible: &LiteralInteger, $method, $op);
        }
        impl $trait<&LiteralInteger> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(infallible: &LiteralInteger, $method, $op);
        }
    };
    (shift: $trait:ident<$rhs_ty:ty>, $method:ident, $checked:ident, $op:tt) => {
        impl $trait<$rhs_ty> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(shift: $rhs_ty, $method, $checked, $op);
        }
        impl $trait<$rhs_ty> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(shift: $rhs_ty, $method, $checked, $op);
        }
        impl $trait<&$rhs_ty> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(shift: &$rhs_ty, $method, $checked, $op);
        }
        impl $trait<&$rhs_ty> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!(shift: &$rhs_ty, $method, $checked, $op);
        }
    };
    (pow: $implementation:tt, $rhs_ty:ty) => {
        impl Pow<$rhs_ty> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!($implementation: $rhs_ty);
        }
        impl Pow<$rhs_ty> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!($implementation: $rhs_ty);
        }
        impl Pow<&$rhs_ty> for LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!($implementation: &$rhs_ty);
        }
        impl Pow<&$rhs_ty> for &LiteralInteger {
            type Output = LiteralInteger;

            impl_literal_integer_binop_method!($implementation: &$rhs_ty);
        }
    }
}

impl_literal_integer_binop!(Add, add, checked_add, +);
impl_literal_integer_binop!(Sub, sub, checked_sub, -);
impl_literal_integer_binop!(Mul, mul, checked_mul, *);
impl_literal_integer_binop!(Div, div, checked_div, /);
impl_literal_integer_binop!(Rem, rem, checked_rem, %);
impl_literal_integer_binop!(shift: Shl<usize>, shl, checked_shl, <<);
impl_literal_integer_binop!(shift: Shl<isize>, shl, checked_shl, <<);
impl_literal_integer_binop!(shift: Shr<usize>, shr, checked_shr, >>);
impl_literal_integer_binop!(shift: Shr<isize>, shr, checked_shr, >>);
impl_literal_integer_binop!(infallible: BitOr,  bitor,  |);
impl_literal_integer_binop!(infallible: BitXor, bitxor, ^);
impl_literal_integer_binop!(infallible: BitAnd, bitand, &);
impl_literal_integer_binop!(pow: pow_usize, usize);
impl_literal_integer_binop!(pow: pow_biguint, BigUint);

macro_rules! impl_literal_integer_neg_method {
    () => {
        fn neg(self) -> Self::Output {
            match &self {
                LiteralInteger::Int(n) => {
                    if let Some(result) = n.checked_neg() {
                        LiteralInteger::Int(result)
                    } else {
                        LiteralInteger::BigInt(-BigInt::from(*n))
                    }
                }
                LiteralInteger::BigInt(n) => LiteralInteger::BigInt(-n),
            }
        }
    };
}

impl Neg for LiteralInteger {
    type Output = LiteralInteger;

    impl_literal_integer_neg_method!();
}

impl Neg for &LiteralInteger {
    type Output = LiteralInteger;

    impl_literal_integer_neg_method!();
}

macro_rules! impl_literal_integer_not_method {
    () => {
        fn not(self) -> Self::Output {
            match self {
                LiteralInteger::Int(n) => LiteralInteger::Int(!n),
                LiteralInteger::BigInt(n) => LiteralInteger::BigInt(!n),
            }
        }
    };
}

impl Not for LiteralInteger {
    type Output = LiteralInteger;

    impl_literal_integer_not_method!();
}

impl Not for &LiteralInteger {
    type Output = LiteralInteger;

    impl_literal_integer_not_method!();
}

macro_rules! impl_literal_integer_to_primitive {
    ($($method:ident -> $ty:ty),* $(,)?) => {
        $(
            fn $method(&self) -> Option<$ty> {
                match self {
                    LiteralInteger::Int(n) => n.$method(),
                    LiteralInteger::BigInt(n) => n.$method(),
                }
            }
        )*
    };
}

impl ToPrimitive for LiteralInteger {
    impl_literal_integer_to_primitive!(
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

impl Display for LiteralInteger {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralInteger::Int(n) => write!(f, "{}", n),
            LiteralInteger::BigInt(n) => write!(f, "{}", n),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralBoolean {
    pub value: bool,
}

impl Display for LiteralBoolean {
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
pub struct LiteralString {
    pub value: Arc<String>,
}

impl LiteralString {
    pub fn from_str(value: &str) -> Self {
        LiteralString {
            value: Arc::new(value.to_owned()),
        }
    }
}

impl Display for LiteralString {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralBytes {
    pub value: imbl::Vector<u8>,
}

impl Display for LiteralBytes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "b\"")?;
        for (i, element) in self.value.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "\\x{:02X}", element)?;
        }
        write!(f, "\"")?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralList {
    pub value: imbl::Vector<Arc<TypeLiteral>>,
}

impl Display for LiteralList {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, element) in self.value.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", element)?;
        }
        write!(f, "]")
    }
}

impl StructuralDepth for LiteralList {
    fn depth(&self) -> usize {
        1 + self.value.depth()
    }
}

impl StructuralWidth for LiteralList {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralTuple {
    pub value: imbl::Vector<Arc<TypeLiteral>>,
}

impl Display for LiteralTuple {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for element in &self.value {
            write!(f, "{},", element)?;
        }
        write!(f, ")")
    }
}
impl StructuralDepth for LiteralTuple {
    fn depth(&self) -> usize {
        1 + self.value.depth()
    }
}

impl StructuralWidth for LiteralTuple {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeLiteralKey {
    Integer(LiteralInteger),
    Boolean(LiteralBoolean),
    Float(LiteralFloat),
    Complex(LiteralComplex),
    String(LiteralString),
    Bytes(LiteralBytes),

    None,
    Ellipsis,

    Tuple(LiteralTuple),

    Function(LiteralFunction),
    OverloadedFunction(LiteralOverloadedFunction),
    Class(LiteralClass),
    TypeAlias(LiteralTypeAlias),
    Generic(LiteralGeneric),
    ImportedModule(LiteralImportedModule),
}

impl Display for TypeLiteralKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeLiteralKey::Integer(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Boolean(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Float(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Complex(literal) => write!(f, "{}", literal),
            TypeLiteralKey::String(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Bytes(literal) => write!(f, "{}", literal),
            TypeLiteralKey::None => write!(f, "None"),
            TypeLiteralKey::Ellipsis => write!(f, "..."),
            TypeLiteralKey::Tuple(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Function(literal) => write!(f, "{}", literal),
            TypeLiteralKey::OverloadedFunction(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Class(literal) => write!(f, "{}", literal),
            TypeLiteralKey::TypeAlias(literal) => write!(f, "{}", literal),
            TypeLiteralKey::Generic(literal) => write!(f, "{}", literal),
            TypeLiteralKey::ImportedModule(literal) => write!(f, "{}", literal),
        }
    }
}

impl StructuralDepth for TypeLiteralKey {
    fn depth(&self) -> usize {
        match self {
            TypeLiteralKey::Integer(_)
            | TypeLiteralKey::Boolean(_)
            | TypeLiteralKey::Float(_)
            | TypeLiteralKey::Complex(_)
            | TypeLiteralKey::String(_)
            | TypeLiteralKey::Bytes(_)
            | TypeLiteralKey::None
            | TypeLiteralKey::Ellipsis
            | TypeLiteralKey::ImportedModule(_) => 1,
            TypeLiteralKey::Tuple(literal_tuple) => literal_tuple.depth(),
            TypeLiteralKey::Function(literal_function) => literal_function.value.depth(),
            TypeLiteralKey::OverloadedFunction(literal_overloaded_function) => {
                literal_overloaded_function.value.depth()
            }
            TypeLiteralKey::Class(literal_class) => literal_class.value.depth(),
            TypeLiteralKey::TypeAlias(literal_type_alias) => literal_type_alias.value.depth(),
            TypeLiteralKey::Generic(literal_generic) => literal_generic.value.depth(),
        }
    }
}

impl StructuralWidth for TypeLiteralKey {
    fn width(&self) -> usize {
        match self {
            TypeLiteralKey::Integer(_)
            | TypeLiteralKey::Boolean(_)
            | TypeLiteralKey::Float(_)
            | TypeLiteralKey::Complex(_)
            | TypeLiteralKey::String(_)
            | TypeLiteralKey::Bytes(_)
            | TypeLiteralKey::None
            | TypeLiteralKey::Ellipsis
            | TypeLiteralKey::ImportedModule(_) => 1,
            TypeLiteralKey::Tuple(literal_tuple) => literal_tuple.width(),
            TypeLiteralKey::Function(literal_function) => literal_function.value.width(),
            TypeLiteralKey::OverloadedFunction(literal_overloaded_function) => {
                literal_overloaded_function.value.width()
            }
            TypeLiteralKey::Class(literal_class) => literal_class.value.width(),
            TypeLiteralKey::TypeAlias(literal_type_alias) => literal_type_alias.value.width(),
            TypeLiteralKey::Generic(literal_generic) => literal_generic.value.width(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralDict {
    pub values: imbl::Vector<(Arc<TypeLiteralKey>, Arc<TypeLiteral>)>,
}

impl Display for LiteralDict {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, (key, value)) in self.values.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}: {}", key, value)?;
        }
        write!(f, "}}")
    }
}

impl StructuralDepth for LiteralDict {
    fn depth(&self) -> usize {
        1 + self
            .values
            .iter()
            .map(|(k, v)| k.depth().max(v.depth()))
            .max()
            .unwrap_or(0)
    }
}

impl StructuralWidth for LiteralDict {
    fn width(&self) -> usize {
        self.values.iter().map(|(k, v)| k.width() + v.width()).sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralFunction {
    pub value: Arc<FunctionType>,
}

impl Display for LiteralFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "function({})", self.value.qualified_location)
    }
}

impl StructuralDepth for LiteralFunction {
    fn depth(&self) -> usize {
        self.value.depth()
    }
}

impl StructuralWidth for LiteralFunction {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralOverloadedFunction {
    pub value: Arc<OverloadedFunctionType>,
}

impl Display for LiteralOverloadedFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(target) = &self.value.target {
            write!(
                f,
                "overloaded_function({})",
                target.value.qualified_location
            )
        } else {
            write!(f, "overloaded_function")
        }
    }
}

impl StructuralDepth for LiteralOverloadedFunction {
    fn depth(&self) -> usize {
        self.value.depth()
    }
}

impl StructuralWidth for LiteralOverloadedFunction {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralClass {
    pub value: Arc<ClassType>,
}

impl Display for LiteralClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "class({})", self.value.qualified_location)
    }
}

impl StructuralDepth for LiteralClass {
    fn depth(&self) -> usize {
        self.value.depth()
    }
}

impl StructuralWidth for LiteralClass {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralTypeAlias {
    pub value: Arc<TypeAliasType>,
}

impl Display for LiteralTypeAlias {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "type_alias({})", self.value.location)
    }
}

impl StructuralDepth for LiteralTypeAlias {
    fn depth(&self) -> usize {
        self.value.depth()
    }
}

impl StructuralWidth for LiteralTypeAlias {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralGeneric {
    pub value: Arc<GenericType>,
}

impl Display for LiteralGeneric {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "generic({})", self.value.location)
    }
}

impl StructuralDepth for LiteralGeneric {
    fn depth(&self) -> usize {
        self.value.depth()
    }
}

impl StructuralWidth for LiteralGeneric {
    fn width(&self) -> usize {
        self.value.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralImportedModule {
    pub value: Arc<ImportedModuleType>,
}

impl Display for LiteralImportedModule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "import({})", self.value.location)
    }
}

impl StructuralDepth for LiteralImportedModule {
    fn depth(&self) -> usize {
        1
    }
}

impl StructuralWidth for LiteralImportedModule {
    fn width(&self) -> usize {
        1
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeLiteral {
    Integer(LiteralInteger),
    Boolean(LiteralBoolean),
    Float(LiteralFloat),
    Complex(LiteralComplex),
    String(LiteralString),
    Bytes(LiteralBytes),

    None,
    Ellipsis,

    List(LiteralList),
    Tuple(LiteralTuple),
    Dict(LiteralDict),

    Function(LiteralFunction),
    OverloadedFunction(LiteralOverloadedFunction),
    Class(LiteralClass),
    TypeAlias(LiteralTypeAlias),
    Generic(LiteralGeneric),
    ImportedModule(LiteralImportedModule),
}

impl StructuralDepth for TypeLiteral {
    fn depth(&self) -> usize {
        match self {
            TypeLiteral::Integer(_)
            | TypeLiteral::Boolean(_)
            | TypeLiteral::Float(_)
            | TypeLiteral::Complex(_)
            | TypeLiteral::String(_)
            | TypeLiteral::Bytes(_)
            | TypeLiteral::None
            | TypeLiteral::Ellipsis => 0,
            TypeLiteral::List(literal_list) => literal_list.depth(),
            TypeLiteral::Tuple(literal_tuple) => literal_tuple.depth(),
            TypeLiteral::Dict(literal_dict) => literal_dict.depth(),
            TypeLiteral::Function(literal_function) => literal_function.depth(),
            TypeLiteral::OverloadedFunction(literal_overloaded_function) => {
                literal_overloaded_function.depth()
            }
            TypeLiteral::Class(literal_class) => literal_class.depth(),
            TypeLiteral::TypeAlias(literal_type_alias) => literal_type_alias.depth(),
            TypeLiteral::Generic(literal_generic) => literal_generic.depth(),
            TypeLiteral::ImportedModule(literal_imported_module) => literal_imported_module.depth(),
        }
    }
}

impl StructuralWidth for TypeLiteral {
    fn width(&self) -> usize {
        match self {
            TypeLiteral::Integer(_)
            | TypeLiteral::Boolean(_)
            | TypeLiteral::Float(_)
            | TypeLiteral::Complex(_)
            | TypeLiteral::String(_)
            | TypeLiteral::Bytes(_)
            | TypeLiteral::None
            | TypeLiteral::Ellipsis => 1,
            TypeLiteral::List(literal_list) => literal_list.width(),
            TypeLiteral::Tuple(literal_tuple) => literal_tuple.width(),
            TypeLiteral::Dict(literal_dict) => literal_dict.width(),
            TypeLiteral::Function(literal_function) => literal_function.width(),
            TypeLiteral::OverloadedFunction(literal_overloaded_function) => {
                literal_overloaded_function.width()
            }
            TypeLiteral::Class(literal_class) => literal_class.width(),
            TypeLiteral::TypeAlias(literal_type_alias) => literal_type_alias.width(),
            TypeLiteral::Generic(literal_generic) => literal_generic.width(),
            TypeLiteral::ImportedModule(literal_imported_module) => literal_imported_module.width(),
        }
    }
}

impl Display for TypeLiteral {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeLiteral::Integer(literal_integer) => {
                write!(f, "{}", literal_integer)
            }
            TypeLiteral::Boolean(literal_boolean) => {
                write!(f, "{}", literal_boolean)
            }
            TypeLiteral::Float(literal_float) => {
                write!(f, "{}", literal_float)
            }
            TypeLiteral::Complex(literal_complex) => {
                write!(f, "{}", literal_complex)
            }
            TypeLiteral::String(literal_string) => {
                write!(f, "{}", literal_string)
            }
            TypeLiteral::Bytes(literal_bytes) => write!(f, "{}", literal_bytes),
            TypeLiteral::None => write!(f, "None"),
            TypeLiteral::Ellipsis => write!(f, "..."),
            TypeLiteral::List(literal_list) => write!(f, "{}", literal_list),
            TypeLiteral::Tuple(literal_tuple) => write!(f, "{}", literal_tuple),
            TypeLiteral::Dict(literal_dict) => write!(f, "{}", literal_dict),
            TypeLiteral::Function(literal_function) => {
                write!(f, "{}", literal_function)
            }
            TypeLiteral::OverloadedFunction(literal_overloaded_function) => {
                write!(f, "{}", literal_overloaded_function)
            }
            TypeLiteral::Class(literal_class) => {
                write!(f, "{}", literal_class)
            }
            TypeLiteral::TypeAlias(literal_type_alias) => {
                write!(f, "{}", literal_type_alias)
            }
            TypeLiteral::Generic(literal_generic) => {
                write!(f, "{}", literal_generic)
            }
            TypeLiteral::ImportedModule(literal_imported_module) => {
                write!(f, "{}", literal_imported_module)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeInstance {
    pub origin: Location<QualifiedName>,
    pub name: Identifier,
    pub arguments: imbl::Vector<Arc<Type>>,
}

impl TypeInstance {
    pub fn new(origin: Location<QualifiedName>, name: Identifier) -> Self {
        TypeInstance {
            origin,
            name,
            arguments: imbl::Vector::new(),
        }
    }

    pub fn builtins(name: &str) -> Self {
        TypeInstance::new(
            Location::from(QualifiedName::parse(BUILTINS_MODULE)),
            Identifier::parse(name),
        )
    }

    pub fn typing(name: &str) -> Self {
        TypeInstance::new(
            Location::from(QualifiedName::parse(TYPING_MODULE)),
            Identifier::parse(name),
        )
    }

    pub fn builtins_list(element_type: Arc<Type>) -> Self {
        TypeInstance::builtins("list").with_arguments(imbl::vector![element_type])
    }

    pub fn builtins_tuple<I: IntoIterator<Item = Arc<Type>>>(element_types: I) -> Self {
        TypeInstance::builtins("tuple").with_arguments(element_types.into_iter().collect())
    }

    pub fn builtins_dict(key_type: Arc<Type>, value_type: Arc<Type>) -> Self {
        TypeInstance::builtins("dict").with_arguments(imbl::vector![key_type, value_type])
    }

    pub fn with_origin(mut self, origin: Location<QualifiedName>) -> Self {
        self.origin = origin;
        self
    }

    pub fn with_name(mut self, name: Identifier) -> Self {
        self.name = name;
        self
    }

    pub fn with_arguments(mut self, arguments: imbl::Vector<Arc<Type>>) -> Self {
        self.arguments = arguments;
        self
    }
}

impl StructuralDepth for TypeInstance {
    fn depth(&self) -> usize {
        1 + self.arguments.depth()
    }
}

impl StructuralWidth for TypeInstance {
    fn width(&self) -> usize {
        self.arguments.width()
    }
}

impl Display for TypeInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "@({}).{}", self.origin, self.name)?;

        if !self.arguments.is_empty() {
            write!(f, "[")?;
            for (i, argument) in self.arguments.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", argument)?;
            }
            write!(f, "]")?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeInstance2 {
    pub base: Arc<Type>,
    pub arguments: imbl::Vector<Arc<Type>>,
}

impl StructuralDepth for TypeInstance2 {
    fn depth(&self) -> usize {
        self.base.depth().max(self.arguments.depth())
    }
}

impl StructuralWidth for TypeInstance2 {
    fn width(&self) -> usize {
        self.base.width() + self.arguments.width()
    }
}

impl Display for TypeInstance2 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.base)?;

        if !self.arguments.is_empty() {
            write!(f, "[")?;
            for (i, argument) in self.arguments.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", argument)?;
            }
            write!(f, "]")?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeUnion {
    types: imbl::OrdSet<Arc<Type>>,
}

impl TypeUnion {
    pub fn new() -> Self {
        TypeUnion {
            types: imbl::OrdSet::new(),
        }
    }

    pub fn add_type(&mut self, ty: Arc<Type>) {
        match ty.as_ref() {
            Type::Union(inner_types) => {
                for inner_ty in &inner_types.types {
                    self.add_type(inner_ty.clone());
                }
            }
            Type::Never => {}
            _ => {
                self.types.insert(ty);
            }
        };
    }

    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    pub fn contains(&self, ty: &Arc<Type>) -> bool {
        self.types.contains(ty)
    }

    pub fn types(&self) -> &imbl::OrdSet<Arc<Type>> {
        &self.types
    }

    pub fn simplify(self) -> Arc<Type> {
        if self.types.is_empty() {
            Arc::new(Type::Never)
        } else if self.types.len() == 1 {
            self.types
                .into_iter()
                .next()
                .expect("Only one type in the union")
        } else {
            Arc::new(Type::Union(self))
        }
    }
}

impl StructuralDepth for TypeUnion {
    fn depth(&self) -> usize {
        self.types.depth()
    }
}

impl StructuralWidth for TypeUnion {
    fn width(&self) -> usize {
        self.types.width()
    }
}

impl Display for TypeUnion {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Union[{}]",
            self.types
                .iter()
                .map(|ty| ty.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Any,
    Never,
    NoReturn,
    Instance(TypeInstance),
    Instance2(TypeInstance2),
    Union(TypeUnion),
    Intersection(imbl::OrdSet<Arc<Type>>),
    Literal(Arc<TypeLiteral>),
}

impl Type {
    pub fn new_literal(literal: TypeLiteral) -> Self {
        Type::Literal(Arc::new(literal))
    }

    pub fn new_integer_literal(literal_integer: LiteralInteger) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Integer(literal_integer)))
    }

    pub fn new_float_literal(literal_float: LiteralFloat) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Float(literal_float)))
    }

    pub fn new_complex_literal(literal_complex: LiteralComplex) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Complex(literal_complex)))
    }

    pub fn new_string_literal(literal_string: LiteralString) -> Self {
        Type::Literal(Arc::new(TypeLiteral::String(literal_string)))
    }

    pub fn new_bytes_literal(literal_bytes: LiteralBytes) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Bytes(literal_bytes)))
    }

    pub fn new_boolean_literal(literal_boolean: LiteralBoolean) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Boolean(literal_boolean)))
    }

    pub fn new_union<I: IntoIterator<Item = Arc<Type>>>(types: I) -> Self {
        let mut type_union = TypeUnion::new();
        for ty in types {
            type_union.add_type(ty);
        }
        Type::Union(type_union)
    }

    pub fn new_intersection<I: IntoIterator<Item = Type>>(types: I) -> Self {
        Type::Intersection(imbl::OrdSet::from_iter(types.into_iter()))
    }
}

impl Default for Type {
    fn default() -> Self {
        Type::Never
    }
}

impl Lattice for Type {
    fn includes(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        match self {
            Type::Any => true,
            Type::Never => false,
            Type::NoReturn => false,
            Type::Instance { .. } => true,
            Type::Instance2(type_instance2) => true,
            Type::Union(type_union) => {
                if let Type::Union(other_type_union) = other {
                    other_type_union.types().is_subset(type_union.types())
                } else {
                    type_union.contains(&Arc::new(other.clone()))
                }
            }
            Type::Intersection(type_intersection) => {
                if let Type::Intersection(other_type_intersection) = other {
                    type_intersection.is_subset(other_type_intersection)
                } else {
                    other.includes(self)
                }
            }
            Type::Literal(_) => false,
        }
    }

    fn join(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else if self.includes(other) {
            self.clone()
        } else if other.includes(self) {
            other.clone()
        } else {
            let mut type_union = TypeUnion::new();
            type_union.add_type(Arc::new(self.clone()));
            type_union.add_type(Arc::new(other.clone()));
            type_union.simplify().as_ref().clone()
        }
    }
}

impl StructuralDepth for Type {
    fn depth(&self) -> usize {
        match self {
            Type::Any | Type::Never | Type::NoReturn => 1,
            Type::Instance(type_instance) => type_instance.depth(),
            Type::Instance2(type_instance2) => type_instance2.depth(),
            Type::Union(type_union) => type_union.depth(),
            Type::Intersection(type_intersection) => type_intersection.depth(),
            Type::Literal(type_literal) => type_literal.depth(),
        }
    }
}

impl StructuralWidth for Type {
    fn width(&self) -> usize {
        match self {
            Type::Any | Type::Never | Type::NoReturn => 1,
            Type::Instance(type_instance) => type_instance.width(),
            Type::Instance2(type_instance2) => type_instance2.width(),
            Type::Union(type_union) => type_union.width(),
            Type::Intersection(type_intersection) => type_intersection.width(),
            Type::Literal(type_literal) => type_literal.width(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Any => write!(f, "Any"),
            Type::Never => write!(f, "Never"),
            Type::NoReturn => write!(f, "NoReturn"),
            Type::Instance(type_instance) => write!(f, "{}", type_instance),
            Type::Instance2(type_instance2) => write!(f, "{}", type_instance2),
            Type::Union(type_union) => write!(f, "{}", type_union),
            Type::Intersection(_) => write!(f, "Intersection"),
            Type::Literal(type_literal) => write!(f, "{}", type_literal),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub enum Visibility {
    #[default]
    Public,
    Subclass,
    Internal,
}

impl OrdLattice for Visibility {}

impl From<Visibility> for apy::v1::Visibility {
    fn from(visibility: Visibility) -> Self {
        match visibility {
            Visibility::Public => apy::v1::Visibility::Public,
            Visibility::Subclass => apy::v1::Visibility::Subclass,
            Visibility::Internal => apy::v1::Visibility::Internal,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Initialisation {
    #[default]
    Initialised,
    Uninitialised,
}

impl Initialisation {
    pub fn is_initialised(&self) -> bool {
        matches!(self, Initialisation::Initialised)
    }
}

impl OrdLattice for Initialisation {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Mutability {
    #[default]
    Mutable,
    Readonly,
}

impl Mutability {
    pub fn is_readonly(&self) -> bool {
        matches!(self, Mutability::Readonly)
    }
}

impl OrdLattice for Mutability {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Finality {
    #[default]
    NonFinal,
    Final,
}

impl Finality {
    pub fn is_final(&self) -> bool {
        matches!(self, Finality::Final)
    }
}

impl OrdLattice for Finality {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Deprecation {
    #[default]
    NotDeprecated,
    Deprecated,
}

impl Deprecation {
    pub fn is_deprecated(&self) -> bool {
        matches!(self, Deprecation::Deprecated)
    }
}

impl OrdLattice for Deprecation {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalAttribute {
    pub attribute_type: Sourced<Arc<Type>>,

    pub visibility: Sourced<Visibility>,

    pub initialisation: Sourced<Initialisation>,

    pub mutability: Sourced<Mutability>,

    pub finality: Sourced<Finality>,

    pub deprecation: Sourced<Deprecation>,
}

impl LocalAttribute {
    pub fn new(attribute_type: Sourced<Arc<Type>>) -> Self {
        LocalAttribute {
            attribute_type,
            visibility: Sourced::inferred(Visibility::default()),
            initialisation: Sourced::inferred(Initialisation::default()),
            mutability: Sourced::inferred(Mutability::default()),
            finality: Sourced::inferred(Finality::default()),
            deprecation: Sourced::inferred(Deprecation::default()),
        }
    }

    pub fn with_attribute_type(mut self, attribute_type: Sourced<Arc<Type>>) -> Self {
        self.attribute_type = attribute_type;
        self
    }

    pub fn with_visibility(mut self, visibility: Sourced<Visibility>) -> Self {
        self.visibility = visibility;
        self
    }

    pub fn with_initialisation(mut self, initialisation: Sourced<Initialisation>) -> Self {
        self.initialisation = initialisation;
        self
    }

    pub fn with_mutability(mut self, mutability: Sourced<Mutability>) -> Self {
        self.mutability = mutability;
        self
    }

    pub fn with_finality(mut self, finality: Sourced<Finality>) -> Self {
        self.finality = finality;
        self
    }

    pub fn with_deprecation(mut self, deprecation: Sourced<Deprecation>) -> Self {
        self.deprecation = deprecation;
        self
    }
}

impl<C: Namespaces<QualifiedName, AbstractEnvironment>> ContextualLattice<C> for LocalAttribute {
    type Error = GetAttributeError;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error> {
        if self == other {
            return Ok(true);
        }

        Ok(self.attribute_type.includes(&other.attribute_type)
            && self.visibility.includes(&other.visibility)
            && self.initialisation.includes(&other.initialisation)
            && self.mutability.includes(&other.mutability)
            && self.finality.includes(&other.finality)
            && self.deprecation.includes(&other.deprecation))
    }

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error> {
        if self == other {
            return Ok(self.clone());
        }

        let mut attribute_type = self.attribute_type.join(&other.attribute_type);

        if attribute_type.data.depth() > DEPTH_LIMIT {
            attribute_type.data = Arc::new(Type::Any);
        }

        Ok(LocalAttribute {
            attribute_type,
            visibility: self.visibility.join(&other.visibility),
            initialisation: self.initialisation.join(&other.initialisation),
            mutability: self.mutability.join(&other.mutability),
            finality: self.finality.join(&other.finality),
            deprecation: self.deprecation.join(&other.deprecation),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportedAttribute {
    pub name: Identifier,

    pub module: Arc<QualifiedName>,

    pub visibility: Sourced<Visibility>,

    pub deprecation: Sourced<Deprecation>,
}

impl ImportedAttribute {
    pub fn resolve<'a>(
        &'a self,
        namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    ) -> Result<&'a LocalAttribute, GetAttributeError> {
        get_attribute(namespaces, &Location::from(self.module.clone()), &self.name)?
            .resolve(namespaces)
    }

    pub fn as_local(
        &self,
        namespaces: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    ) -> Result<LocalAttribute, GetAttributeError> {
        let mut resolved_attribute = self.resolve(namespaces)?.clone();

        resolved_attribute.visibility = self.visibility.clone();
        resolved_attribute.deprecation = self.deprecation.clone();

        Ok(resolved_attribute)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Attribute {
    Imported(ImportedAttribute),
    Local(LocalAttribute),
}

impl Attribute {
    pub fn resolve<'a>(
        &'a self,
        namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    ) -> Result<&'a LocalAttribute, GetAttributeError> {
        match self {
            Attribute::Imported(imported_attribute) => imported_attribute.resolve(namespaces),
            Attribute::Local(local_attribute) => Ok(local_attribute),
        }
    }

    pub fn as_local(
        &self,
        namespaces: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    ) -> Result<LocalAttribute, GetAttributeError> {
        match self {
            Attribute::Imported(imported_attribute) => imported_attribute.as_local(namespaces),
            Attribute::Local(local_attribute) => Ok(local_attribute.clone()),
        }
    }
}

impl<C: Namespaces<QualifiedName, AbstractEnvironment>> ContextualLattice<C> for Attribute {
    type Error = GetAttributeError;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error> {
        if self == other {
            return Ok(true);
        }

        self.as_local(context)?
            .includes(context, &other.as_local(context)?)
    }

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error> {
        if self == other {
            return Ok(self.clone());
        }

        Ok(match (self, other) {
            (Attribute::Local(self_local_attribute), Attribute::Local(other_local_attribute)) => {
                Attribute::Local(self_local_attribute.join(context, other_local_attribute)?)
            }
            (
                Attribute::Imported(self_imported_attribute),
                Attribute::Imported(other_imported_attribute),
            ) => {
                if self_imported_attribute.name == other_imported_attribute.name
                    && self_imported_attribute.module == other_imported_attribute.module
                {
                    Attribute::Imported(ImportedAttribute {
                        name: self_imported_attribute.name.clone(),
                        module: self_imported_attribute.module.clone(),
                        visibility: self_imported_attribute
                            .visibility
                            .join(&other_imported_attribute.visibility),
                        deprecation: self_imported_attribute
                            .deprecation
                            .join(&other_imported_attribute.deprecation),
                    })
                } else {
                    Attribute::Local(
                        self_imported_attribute
                            .as_local(context)?
                            .join(context, &other_imported_attribute.as_local(context)?)?,
                    )
                }
            }
            (
                Attribute::Local(self_local_attribute),
                Attribute::Imported(other_imported_attribute),
            ) => Attribute::Local(
                self_local_attribute.join(context, &other_imported_attribute.as_local(context)?)?,
            ),
            (
                Attribute::Imported(self_imported_attribute),
                Attribute::Local(other_local_attribute),
            ) => Attribute::Local(
                self_imported_attribute
                    .as_local(context)?
                    .join(context, other_local_attribute)?,
            ),
        })
    }
}

#[derive(Error, Debug)]
pub enum GetAttributeError {
    #[error("the environment location does not exist: `{0:?}`")]
    LocationNotFound(Location<QualifiedName>),
    #[error("the attribute `{identifier}` does not exist at location `{location:?}`")]
    AttributeNotFound {
        location: Location<QualifiedName>,
        identifier: Identifier,
    },
}

pub fn get_attribute<'a>(
    namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &Identifier,
) -> Result<&'a Attribute, GetAttributeError> {
    let Some(abstract_environment) = namespaces.get_abstract_environment(location) else {
        return Err(GetAttributeError::LocationNotFound(location.clone()));
    };

    if let Some(attribute) = abstract_environment.attributes.get(name) {
        return Ok(attribute);
    };

    Err(GetAttributeError::AttributeNotFound {
        location: location.clone(),
        identifier: name.clone(),
    })
}

pub fn resolve_local_attribute<'a>(
    namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: Location<QualifiedName>,
    name: &'a Identifier,
) -> Result<(Location<QualifiedName>, &'a Identifier, &'a LocalAttribute), GetAttributeError> {
    let err = match get_attribute(namespaces, &location, name) {
        Ok(attribute) => {
            return Ok((location, name, attribute.resolve(namespaces)?));
        }
        Err(error) => error,
    };

    if let Some(parent_location) = location.namespace_location.parent_location() {
        return resolve_local_attribute(namespaces, Location::at_exit(parent_location), name);
    }

    let builtins_namespace_location =
        NamespaceLocation::from(Arc::new(QualifiedName::parse(BUILTINS_MODULE)));

    if location.namespace_location != builtins_namespace_location {
        return resolve_local_attribute(
            namespaces,
            Location::at_exit(builtins_namespace_location),
            name,
        );
    }

    Err(err)
}

#[derive(Debug, Clone, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct RaisedExceptions {
    pub exceptions: imbl::OrdSet<Exception>,
}

impl RaisedExceptions {
    pub fn raise(exception: Exception) -> Self {
        RaisedExceptions {
            exceptions: imbl::OrdSet::unit(exception),
        }
    }
}

impl Lattice for RaisedExceptions {
    fn includes(&self, other: &Self) -> bool {
        other.exceptions.is_subset(&self.exceptions)
    }

    fn join(&self, other: &Self) -> Self {
        let mut exceptions = self.exceptions.clone();
        exceptions.extend(other.exceptions.clone());
        RaisedExceptions { exceptions }
    }
}

impl Display for RaisedExceptions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, exception) in self.exceptions.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", exception)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Completeness {
    #[default]
    Total,
    Partial,
}

impl Display for Completeness {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Completeness::Total => write!(f, "Total"),
            Completeness::Partial => write!(f, "Partial"),
        }
    }
}

impl OrdLattice for Completeness {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Pureness {
    #[default]
    Pure,
    Impure,
}

impl Display for Pureness {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Pureness::Pure => write!(f, "Pure"),
            Pureness::Impure => write!(f, "Impure"),
        }
    }
}

impl OrdLattice for Pureness {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Diagnostic {
    InvalidAnnotation { location: Location<QualifiedName> },
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct AbstractEnvironment {
    pub attributes: imbl::HashMap<Arc<Identifier>, Arc<Attribute>>,
    pub returned_value: Option<Sourced<Arc<Type>>>,
    pub raised_exceptions: Sourced<RaisedExceptions>,
    pub completeness: Sourced<Completeness>,
    pub pureness: Sourced<Pureness>,
    pub diagnostics: imbl::HashSet<Diagnostic>,
}

impl AbstractEnvironment {
    pub fn new() -> AbstractEnvironment {
        Self::default()
    }

    pub fn with_attributes(
        mut self,
        attributes: imbl::HashMap<Arc<Identifier>, Arc<Attribute>>,
    ) -> AbstractEnvironment {
        self.attributes = attributes;
        self
    }

    pub fn with_returned_value(mut self, value: Option<Sourced<Arc<Type>>>) -> AbstractEnvironment {
        self.returned_value = value;
        self
    }

    pub fn with_raised_exceptions(
        mut self,
        raised_exceptions: Sourced<RaisedExceptions>,
    ) -> AbstractEnvironment {
        self.raised_exceptions = raised_exceptions;
        self
    }

    pub fn with_completeness(mut self, completeness: Sourced<Completeness>) -> AbstractEnvironment {
        self.completeness = completeness;
        self
    }

    pub fn with_pureness(mut self, pureness: Sourced<Pureness>) -> AbstractEnvironment {
        self.pureness = pureness;
        self
    }

    pub fn with_diagnostics(
        mut self,
        diagnostics: imbl::HashSet<Diagnostic>,
    ) -> AbstractEnvironment {
        self.diagnostics = diagnostics;
        self
    }
}

impl<C: Namespaces<QualifiedName, AbstractEnvironment>> ContextualLattice<C>
    for AbstractEnvironment
{
    type Error = GetAttributeError;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error> {
        for (name, other_attribute) in &other.attributes {
            match self.attributes.get(name) {
                Some(self_attribute) => {
                    if !self_attribute.includes(context, &other_attribute)? {
                        return Ok(false);
                    }
                }
                None => return Ok(false),
            }
        }

        Ok(self.returned_value.includes(&other.returned_value)
            && self.raised_exceptions.includes(&other.raised_exceptions)
            && self.completeness.includes(&other.completeness)
            && self.pureness.includes(&other.pureness)
            && other.diagnostics.is_subset(&self.diagnostics))
    }

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error> {
        let mut attributes = self.attributes.clone();

        for (name, other_attribute) in &other.attributes {
            match attributes.entry(name.clone()) {
                imbl::hashmap::Entry::Occupied(mut entry) => {
                    let self_attribute = entry.get_mut();

                    *self_attribute = self_attribute.join(context, other_attribute)?;
                }
                imbl::hashmap::Entry::Vacant(entry) => {
                    entry.insert(other_attribute.clone());
                }
            }
        }

        let mut diagnostics = self.diagnostics.clone();
        diagnostics.extend(other.diagnostics.clone());

        Ok(AbstractEnvironment {
            attributes,
            returned_value: self.returned_value.join(&other.returned_value),
            raised_exceptions: self.raised_exceptions.join(&other.raised_exceptions),
            completeness: self.completeness.join(&other.completeness),
            pureness: self.pureness.join(&other.pureness),
            diagnostics,
        })
    }
}
