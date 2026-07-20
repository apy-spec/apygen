use crate::analysis::fmt::fmt_display_wrapped;
use crate::analysis::lattice::{Join, LatticeOrd, OrdJoin, OrdLatticeOrd};
use crate::constraints::expressions::{ProgramEntityIdentifier, QualifiedLocation};
use crate::primitives::literals::{
    LiteralBool, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInt, LiteralStr,
};
pub use apy::v1::{GenericKind, Identifier, ParameterKind, ParseIdentifierError, QualifiedName};
pub use apygen_analysis as analysis;
pub use apygen_constraints as constraints;
pub use apygen_primitives as primitives;
pub use imbl;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::sync::Arc;

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

impl OrdJoin for Source {}
impl OrdLatticeOrd for Source {}

impl Display for Source {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Sourced<T> {
    pub data: T,
    pub source: Source,
}

impl<T> Sourced<T> {
    pub fn new(data: T, source: Source) -> Self {
        Sourced { data, source }
    }

    pub fn inferred(data: T) -> Self {
        Sourced::new(data, Source::Inferred)
    }

    pub fn specified(data: T) -> Self {
        Sourced::new(data, Source::Specified)
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Sourced<U> {
        Sourced {
            data: f(self.data),
            source: self.source,
        }
    }
}

impl<T: LatticeOrd + Clone> LatticeOrd for Sourced<T> {
    fn leq(&self, other: &Self) -> bool {
        match (&self.source, &other.source) {
            (Source::Specified, Source::Specified) => self.data.leq(&other.data),
            (Source::Inferred, Source::Inferred) => self.data.leq(&other.data),
            (Source::Inferred, Source::Specified) => true,
            (Source::Specified, Source::Inferred) => false,
        }
    }
}

impl<T: Join + Clone> Join for Sourced<T> {
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
            (Source::Inferred, Source::Specified) => self.clone(),
            (Source::Specified, Source::Inferred) => other.clone(),
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
    Raised(QualifiedLocation),
    Specified,
    Propagated(QualifiedLocation),
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
    pub identifier: ProgramEntityIdentifier,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub parameters: imbl::Vector<Parameter>,

    pub is_async: bool,
}

impl Display for FunctionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "function({})", self.identifier)
    }
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
    pub identifier: ProgramEntityIdentifier,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub bases: imbl::Vector<LiteralClass>,

    pub keyword_arguments: imbl::OrdMap<String, Arc<Type>>,

    pub is_abstract: bool,
}

impl Display for ClassType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "class({})", self.identifier)
    }
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
    pub module: Arc<QualifiedName>,
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
    Integer(LiteralInt),
    Boolean(LiteralBool),
    Float(LiteralFloat),
    Complex(LiteralComplex),
    String(LiteralStr),
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
        self.value.fmt(f)
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
            write!(f, "overloaded_function({})", target.value.identifier)
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
pub struct LiteralMethod {
    pub class: Arc<ClassType>,
    pub arguments: imbl::Vector<Arc<Type>>,
    pub function: Arc<FunctionType>,
}

impl Display for LiteralMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "method({}", self.class)?;
        fmt_display_wrapped(f, self.arguments.iter(), ", ", "[", "]")?;
        write!(f, ", {})", self.function)
    }
}

impl StructuralDepth for LiteralMethod {
    fn depth(&self) -> usize {
        1 + self
            .class
            .depth()
            .max(self.arguments.depth())
            .max(self.function.depth())
    }
}

impl StructuralWidth for LiteralMethod {
    fn width(&self) -> usize {
        self.class.width() + self.arguments.width() + self.function.width()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralClass {
    pub value: Arc<ClassType>,
}

impl Display for LiteralClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
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
        write!(f, "type_alias({})", self.value.alias)
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
        write!(f, "generic({})", self.value.bound)
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
        write!(f, "import({})", self.value.module)
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
    Integer(LiteralInt),
    Boolean(LiteralBool),
    Float(LiteralFloat),
    Complex(LiteralComplex),
    String(LiteralStr),
    Bytes(LiteralBytes),

    None,
    Ellipsis,

    List(LiteralList),
    Tuple(LiteralTuple),
    Dict(LiteralDict),

    Function(LiteralFunction),
    OverloadedFunction(LiteralOverloadedFunction),
    Method(LiteralMethod),
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
            | TypeLiteral::Ellipsis => 1,
            TypeLiteral::List(literal_list) => literal_list.depth(),
            TypeLiteral::Tuple(literal_tuple) => literal_tuple.depth(),
            TypeLiteral::Dict(literal_dict) => literal_dict.depth(),
            TypeLiteral::Function(literal_function) => literal_function.depth(),
            TypeLiteral::OverloadedFunction(literal_overloaded_function) => {
                literal_overloaded_function.depth()
            }
            TypeLiteral::Method(literal_method) => literal_method.depth(),
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
            TypeLiteral::Method(literal_method) => literal_method.width(),
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
            TypeLiteral::Method(literal_method) => {
                write!(f, "{}", literal_method)
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
pub enum Base {
    Class(LiteralClass),
    TypeAlias(LiteralTypeAlias),
    Generic(LiteralGeneric),
}

impl Base {
    pub fn as_type(&self) -> Type {
        match self {
            Base::Class(class) => Type::Literal(Arc::new(TypeLiteral::Class(class.clone()))),
            Base::TypeAlias(type_alias) => {
                Type::Literal(Arc::new(TypeLiteral::TypeAlias(type_alias.clone())))
            }
            Base::Generic(generic) => {
                Type::Literal(Arc::new(TypeLiteral::Generic(generic.clone())))
            }
        }
    }
}

impl Display for Base {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Base::Class(class) => write!(f, "{}", class),
            Base::TypeAlias(type_alias) => write!(f, "{}", type_alias),
            Base::Generic(generic) => write!(f, "{}", generic),
        }
    }
}

impl StructuralDepth for Base {
    fn depth(&self) -> usize {
        match self {
            Base::Class(class) => class.depth(),
            Base::TypeAlias(type_alias) => type_alias.depth(),
            Base::Generic(generic) => generic.depth(),
        }
    }
}

impl StructuralWidth for Base {
    fn width(&self) -> usize {
        match self {
            Base::Class(class) => class.width(),
            Base::TypeAlias(type_alias) => type_alias.width(),
            Base::Generic(generic) => generic.width(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeInstance {
    pub base: Base,
    pub arguments: imbl::Vector<Arc<Type>>,
}

impl StructuralDepth for TypeInstance {
    fn depth(&self) -> usize {
        self.base.depth().max(self.arguments.depth())
    }
}

impl StructuralWidth for TypeInstance {
    fn width(&self) -> usize {
        self.base.width() + self.arguments.width()
    }
}

impl Display for TypeInstance {
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

    pub fn contains(&self, ty: &Type) -> bool {
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
    Union(TypeUnion),
    Intersection(imbl::OrdSet<Arc<Type>>),
    Literal(Arc<TypeLiteral>),
}

impl Type {
    pub fn new_literal(literal: TypeLiteral) -> Self {
        Type::Literal(Arc::new(literal))
    }

    pub fn new_integer_literal(literal_integer: LiteralInt) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Integer(literal_integer)))
    }

    pub fn new_float_literal(literal_float: LiteralFloat) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Float(literal_float)))
    }

    pub fn new_complex_literal(literal_complex: LiteralComplex) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Complex(literal_complex)))
    }

    pub fn new_string_literal(literal_string: LiteralStr) -> Self {
        Type::Literal(Arc::new(TypeLiteral::String(literal_string)))
    }

    pub fn new_bytes_literal(literal_bytes: LiteralBytes) -> Self {
        Type::Literal(Arc::new(TypeLiteral::Bytes(literal_bytes)))
    }

    pub fn new_boolean_literal(literal_boolean: LiteralBool) -> Self {
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

impl Join for Type {
    fn join(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            let mut type_union = TypeUnion::new();
            type_union.add_type(Arc::new(self.clone()));
            type_union.add_type(Arc::new(other.clone()));
            type_union.simplify().as_ref().clone()
        }
    }
}

impl LatticeOrd for Type {
    fn leq(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        match other {
            Type::Any => true,
            Type::Never => false,
            Type::NoReturn => false,
            Type::Instance(_) => true,
            Type::Union(other_type_union) => {
                if let Type::Union(self_type_union) = self {
                    self_type_union.types().leq(other_type_union.types())
                } else {
                    other_type_union.contains(self)
                }
            }
            Type::Intersection(other_type_intersection) => {
                if let Type::Intersection(self_type_intersection) = self {
                    self_type_intersection.leq(other_type_intersection)
                } else {
                    other_type_intersection.contains(self)
                }
            }
            Type::Literal(_) => false,
        }
    }
}

impl StructuralDepth for Type {
    fn depth(&self) -> usize {
        match self {
            Type::Any | Type::Never | Type::NoReturn => 1,
            Type::Instance(type_instance) => type_instance.depth(),
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

impl OrdJoin for Visibility {}
impl OrdLatticeOrd for Visibility {}

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

impl OrdLatticeOrd for Initialisation {}
impl OrdJoin for Initialisation {}

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

impl OrdLatticeOrd for Mutability {}
impl OrdJoin for Mutability {}

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

impl OrdLatticeOrd for Finality {}
impl OrdJoin for Finality {}

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

impl OrdLatticeOrd for Deprecation {}
impl OrdJoin for Deprecation {}

#[derive(Debug, Clone, PartialEq, Eq, Default, PartialOrd, Ord, Join, LatticeOrd)]
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

impl OrdLatticeOrd for Completeness {}
impl OrdJoin for Completeness {}

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

impl OrdLatticeOrd for Pureness {}
impl OrdJoin for Pureness {}
