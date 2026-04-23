use crate::analysis::lattice::Lattice;
use crate::analysis::namespace::{Location, NamespaceLocation, NamespacesContext};
pub use apy::OneOrMany;
pub use apy::v1::{
    GenericKind, Identifier, ParameterKind, ParseIdentifierError, QualifiedName, Visibility,
};
use apygen_analysis::cfg::ProgramPoint;
use imbl;
pub use ordered_float::OrderedFloat;
use std::fmt::{Display, Formatter};
use std::sync::Arc;
use thiserror::Error;

pub const BUILTINS_MODULE: &str = "builtins";
pub const TYPES_MODULE: &str = "types";
pub const TYPING_MODULE: &str = "typing";
pub const TYPING_EXTENSIONS_MODULE: &str = "typing_extensions";
pub const ABC_MODULE: &str = "abc";
pub const DEPTH_LIMIT: usize = 20;

pub fn join_visibility(first: Visibility, second: Visibility) -> Visibility {
    if matches!(first, Visibility::Internal) || matches!(second, Visibility::Internal) {
        Visibility::Internal
    } else if matches!(first, Visibility::Subclass) && matches!(second, Visibility::Subclass) {
        Visibility::Subclass
    } else {
        Visibility::Public
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Parameter {
    pub name: Identifier,

    pub kind: ParameterKind,

    pub parameter_type: Arc<Type>,

    pub is_optional: bool,

    pub is_deprecated: bool,
}

impl StructuralDepth for Parameter {
    fn depth(&self) -> usize {
        self.parameter_type.depth()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericType {
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
        self.bound.depth() + self.constraints.depth() + self.default.depth()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExceptionOrigin {
    Raised,
    Specified,
    Propagated(NamespaceLocation<QualifiedName>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Exception {
    exception_type: Arc<Type>,

    origin: ExceptionOrigin,
}

impl Exception {
    pub fn from_type(exception_type: Type) -> Self {
        Exception {
            exception_type: Arc::new(exception_type),
            origin: ExceptionOrigin::Raised,
        }
    }

    pub fn type_error() -> Self {
        Exception::from_type(Type::Reference(TypeReference::builtins("TypeError")))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionType {
    pub location: Location<QualifiedName>,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub parameters: imbl::Vector<Parameter>,

    pub is_async: bool,
}

impl StructuralDepth for FunctionType {
    fn depth(&self) -> usize {
        1 + self.parameters.depth() + iter_depth(self.generics.values())
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
    pub location: Location<QualifiedName>,

    pub alias: Arc<Type>,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub kind: TypeAliasKind,
}

impl StructuralDepth for TypeAliasType {
    fn depth(&self) -> usize {
        1 + self.alias.depth() + iter_depth(self.generics.values())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClassType {
    pub location: Location<QualifiedName>,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub bases: imbl::Vector<Arc<Type>>,

    pub keyword_arguments: imbl::OrdMap<String, Arc<Type>>,

    pub is_abstract: bool,
}

impl StructuralDepth for ClassType {
    fn depth(&self) -> usize {
        1 + iter_depth(self.generics.values())
            + self.bases.depth()
            + iter_depth(self.keyword_arguments.values())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportedModuleType {
    pub location: Location<QualifiedName>,

    pub module: Arc<QualifiedName>,

    pub submodules: imbl::OrdSet<Arc<QualifiedName>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralInteger {
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralBigInteger {
    pub positive: bool,
    pub value: Arc<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralBoolean {
    pub value: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralFloat {
    pub value: OrderedFloat<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralComplex {
    pub real: OrderedFloat<f64>,
    pub imaginary: OrderedFloat<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralBytes {
    pub value: imbl::Vector<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralList {
    pub value: imbl::Vector<Arc<TypeLiteral>>,
}

impl StructuralDepth for LiteralList {
    fn depth(&self) -> usize {
        1 + self.value.depth()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralTuple {
    pub value: imbl::Vector<Arc<TypeLiteral>>,
}

impl StructuralDepth for LiteralTuple {
    fn depth(&self) -> usize {
        1 + self.value.depth()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralDict {
    pub value: imbl::OrdMap<Arc<TypeLiteral>, Arc<TypeLiteral>>,
}

impl StructuralDepth for LiteralDict {
    fn depth(&self) -> usize {
        1 + iter_depth(self.value.keys()).max(iter_depth(self.value.values()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralFunction {
    pub value: Arc<FunctionType>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralClass {
    pub value: Arc<ClassType>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralTypeAlias {
    pub value: Arc<TypeAliasType>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralGeneric {
    pub value: Arc<GenericType>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralImportedModule {
    pub value: Arc<ImportedModuleType>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeLiteral {
    Integer(LiteralInteger),
    BigInteger(LiteralBigInteger),
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
    Class(LiteralClass),
    TypeAlias(LiteralTypeAlias),
    Generic(LiteralGeneric),
    ImportedModule(LiteralImportedModule),
}

impl StructuralDepth for TypeLiteral {
    fn depth(&self) -> usize {
        match self {
            TypeLiteral::Integer(_)
            | TypeLiteral::BigInteger(_)
            | TypeLiteral::Boolean(_)
            | TypeLiteral::Float(_)
            | TypeLiteral::Complex(_)
            | TypeLiteral::String(_)
            | TypeLiteral::Bytes(_)
            | TypeLiteral::None
            | TypeLiteral::Ellipsis
            | TypeLiteral::ImportedModule(_) => 0,
            TypeLiteral::List(literal_list) => literal_list.depth(),
            TypeLiteral::Tuple(literal_tuple) => literal_tuple.depth(),
            TypeLiteral::Dict(literal_dict) => literal_dict.depth(),
            TypeLiteral::Function(literal_function) => literal_function.value.depth(),
            TypeLiteral::Class(literal_class) => literal_class.value.depth(),
            TypeLiteral::TypeAlias(literal_type_alias) => literal_type_alias.value.depth(),
            TypeLiteral::Generic(literal_generic) => literal_generic.value.depth(),
        }
    }
}

impl Display for TypeLiteral {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeLiteral::Integer(literal_integer) => {
                write!(f, "builtins.Literal[{}]", literal_integer.value)
            }
            TypeLiteral::BigInteger(literal_big_integer) => {
                if literal_big_integer.positive {
                    write!(f, "builtins.Literal[{}]", literal_big_integer.value)
                } else {
                    write!(f, "builtins.Literal[-{}]", literal_big_integer.value)
                }
            }
            TypeLiteral::Boolean(literal_boolean) => {
                write!(f, "builtins.Literal[{}]", literal_boolean.value)
            }
            TypeLiteral::Float(literal_float) => {
                write!(f, "builtins.Literal[{}]", literal_float.value)
            }
            TypeLiteral::Complex(literal_complex) => {
                if literal_complex.imaginary >= OrderedFloat(0.0) {
                    write!(
                        f,
                        "apy_extensions.Literal[{}+{}j]",
                        literal_complex.real, literal_complex.imaginary
                    )
                } else {
                    write!(
                        f,
                        "apy_extensions.Literal[{}{}j]",
                        literal_complex.real, literal_complex.imaginary
                    )
                }
            }
            TypeLiteral::String(literal_string) => {
                write!(f, "builtins.Literal[\"{}\"]", literal_string.value)
            }
            TypeLiteral::Bytes(literal_bytes) => write!(
                f,
                "apy_extensions.Literal[b\"{}\"]",
                String::from_utf8_lossy(&literal_bytes.value.iter().cloned().collect::<Vec<u8>>())
            ),
            TypeLiteral::None => write!(f, "types.NoneType"),
            TypeLiteral::Ellipsis => write!(f, "types.EllipsisType"),
            TypeLiteral::List(literal_list) => write!(
                f,
                "apy_extensions.Literal[[{}]]",
                literal_list
                    .value
                    .iter()
                    .map(|element| element.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TypeLiteral::Tuple(literal_tuple) => write!(
                f,
                "apy_extensions.Literal[({})]",
                literal_tuple
                    .value
                    .iter()
                    .map(|element| element.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TypeLiteral::Dict(literal_dict) => write!(
                f,
                "apy_extensions.Literal[{{{}}}]",
                literal_dict
                    .value
                    .iter()
                    .map(|(key, value)| format!("{}: {}", key, value))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TypeLiteral::Function(_) => {
                write!(f, "types.FunctionType")
            }
            TypeLiteral::Class(_) => {
                write!(f, "builtins.type")
            }
            TypeLiteral::TypeAlias(_) => {
                write!(f, "builtins.type")
            }
            TypeLiteral::Generic(_) => {
                write!(f, "builtins.type")
            }
            TypeLiteral::ImportedModule(_) => {
                write!(f, "types.ModuleType")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeReference {
    pub module: Arc<QualifiedName>,
    pub name: QualifiedName,
    pub arguments: imbl::Vector<Arc<Type>>,
    pub origin: ProgramPoint,
}

impl TypeReference {
    pub fn new(module: Arc<QualifiedName>, name: QualifiedName) -> Self {
        TypeReference {
            module,
            name,
            arguments: imbl::Vector::new(),
            origin: ProgramPoint::Exit,
        }
    }

    pub fn builtins(name: &str) -> Self {
        TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse(name),
        )
    }

    pub fn builtins_list(element_type: Arc<Type>) -> Self {
        TypeReference::builtins("list").with_arguments(imbl::vector![element_type])
    }

    pub fn builtins_tuple<I: IntoIterator<Item = Arc<Type>>>(element_types: I) -> Self {
        TypeReference::builtins("tuple").with_arguments(element_types.into_iter().collect())
    }

    pub fn with_arguments(mut self, arguments: imbl::Vector<Arc<Type>>) -> Self {
        self.arguments = arguments;
        self
    }

    pub fn with_origin(mut self, origin: ProgramPoint) -> Self {
        self.origin = origin;
        self
    }
}

impl StructuralDepth for TypeReference {
    fn depth(&self) -> usize {
        1 + self.arguments.depth()
    }
}

impl Display for TypeReference {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.arguments.is_empty() {
            write!(f, "{}.{}", self.module, self.name)
        } else {
            write!(
                f,
                "{}.{}[{}]",
                self.module,
                self.name,
                self.arguments
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
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
        1 + self.types.depth()
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
    Reference(TypeReference),
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

    pub fn new_big_integer_literal(literal_big_integer: LiteralBigInteger) -> Self {
        Type::Literal(Arc::new(TypeLiteral::BigInteger(literal_big_integer)))
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

    fn includes<'a>(
        &'a self,
        context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
        other: &'a Self,
    ) -> Result<bool, ContextError> {
        if self == other {
            return Ok(true);
        }
        match self {
            Type::Any => Ok(true),
            Type::Never => Ok(false),
            Type::NoReturn => Ok(false),
            Type::Reference { .. } => Ok(true),
            Type::Union(type_union) => Ok(type_union.contains(&Arc::new(other.clone()))),
            Type::Intersection(type_intersection) => {
                if let Type::Intersection(other_type_intersection) = other {
                    Ok(type_intersection.is_subset(other_type_intersection))
                } else {
                    other.includes(context, self)
                }
            }
            Type::Literal(_) => Ok(false),
        }
    }
}

impl StructuralDepth for Type {
    fn depth(&self) -> usize {
        match self {
            Type::Any | Type::Never | Type::NoReturn => 0,
            Type::Reference(type_reference) => type_reference.depth(),
            Type::Union(type_union) => type_union.depth(),
            Type::Intersection(type_intersection) => type_intersection.depth(),
            Type::Literal(type_literal) => type_literal.depth(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Any => write!(f, "Any"),
            Type::Never => write!(f, "Never"),
            Type::NoReturn => write!(f, "NoReturn"),
            Type::Reference(type_reference) => write!(f, "{}", type_reference),
            Type::Union(type_union) => write!(f, "{}", type_union),
            Type::Intersection(_) => write!(f, "Intersection"),
            Type::Literal(type_literal) => write!(f, "{}", type_literal),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalAttribute {
    pub attribute_type: Arc<Type>,

    pub visibility: Visibility,

    pub is_initialised: bool,

    pub is_readonly: bool,

    pub is_final: bool,

    pub is_deprecated: bool,
}

impl LocalAttribute {
    pub fn unknown() -> Self {
        LocalAttribute {
            attribute_type: Arc::new(Type::Any),
            visibility: Visibility::Internal,
            is_initialised: false,
            is_readonly: true,
            is_final: true,
            is_deprecated: true,
        }
    }

    fn includes<'a>(
        &'a self,
        context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
        other: &'a Self,
    ) -> Result<bool, ContextError> {
        self.attribute_type.includes(context, &other.attribute_type)
    }

    pub fn join(&self, other: &LocalAttribute) -> LocalAttribute {
        let mut type_union = TypeUnion::new();

        type_union.add_type(self.attribute_type.clone());
        type_union.add_type(other.attribute_type.clone());

        let ty = type_union.simplify();

        LocalAttribute {
            attribute_type: if ty.depth() > DEPTH_LIMIT {
                Arc::new(Type::Any)
            } else {
                ty
            },
            visibility: join_visibility(self.visibility, other.visibility),
            is_initialised: self.is_initialised && other.is_initialised,
            is_readonly: self.is_readonly || other.is_readonly,
            is_final: self.is_final || other.is_final,
            is_deprecated: self.is_deprecated || other.is_deprecated,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportedAttribute {
    pub name: Identifier,

    pub module: Arc<QualifiedName>,

    pub visibility: Visibility,

    pub is_deprecated: bool,
}

impl ImportedAttribute {
    pub fn resolve<'a>(
        &'a self,
        context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    ) -> Result<&'a LocalAttribute, GetAttributeError> {
        get_attribute(context, &Location::from(self.module.clone()), &self.name)?.resolve(context)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Attribute {
    Local(LocalAttribute),
    Imported(ImportedAttribute),
}

impl Attribute {
    pub fn resolve<'a>(
        &'a self,
        context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    ) -> Result<&'a LocalAttribute, GetAttributeError> {
        match self {
            Attribute::Local(local_attribute) => Ok(local_attribute),
            Attribute::Imported(imported_attribute) => imported_attribute.resolve(context),
        }
    }

    pub fn as_local(
        &self,
        context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    ) -> Result<LocalAttribute, GetAttributeError> {
        match self {
            Attribute::Local(local_attribute) => Ok(local_attribute.clone()),
            Attribute::Imported(imported_attribute) => {
                let mut resolved_attribute = imported_attribute.resolve(context)?.clone();

                resolved_attribute.visibility = imported_attribute.visibility;
                resolved_attribute.is_deprecated = imported_attribute.is_deprecated;

                Ok(resolved_attribute)
            }
        }
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
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &Identifier,
) -> Result<&'a Attribute, GetAttributeError> {
    let Some(abstract_environment) = context.get_abstract_environment(location) else {
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
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &Identifier,
) -> Result<&'a LocalAttribute, GetAttributeError> {
    let err = match get_attribute(context, location, name) {
        Ok(attribute) => return attribute.resolve(context),
        Err(error) => error,
    };

    if let Some(parent_location) = location.namespace_location.parent_location() {
        return resolve_local_attribute(context, &Location::at_exit(parent_location), name);
    }

    let builtins_namespace_location =
        NamespaceLocation::new(Arc::new(QualifiedName::parse(BUILTINS_MODULE)));

    if location.namespace_location != builtins_namespace_location {
        return resolve_local_attribute(
            context,
            &Location::at_exit(builtins_namespace_location),
            name,
        );
    }

    Err(err)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Diagnostic {
    InvalidAnnotation { location: Location<QualifiedName> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbstractEnvironment {
    pub attributes: imbl::HashMap<Arc<Identifier>, Arc<Attribute>>,
    pub returned_value: Arc<Type>,
    pub raised_exceptions: imbl::OrdSet<Exception>,
    pub is_partial: bool,
    pub is_pure: bool,
    pub diagnostics: imbl::HashSet<Diagnostic>,
}

impl AbstractEnvironment {
    pub fn new() -> AbstractEnvironment {
        Self::default()
    }
}

impl Default for AbstractEnvironment {
    fn default() -> Self {
        AbstractEnvironment {
            attributes: imbl::HashMap::new(),
            returned_value: Arc::new(Type::new_literal(TypeLiteral::None)),
            raised_exceptions: imbl::OrdSet::new(),
            is_partial: false,
            is_pure: false,
            diagnostics: imbl::HashSet::new(),
        }
    }
}

#[derive(Debug, Error)]
#[error("failed to get attribute '{identifier}' from context: {error}")]
pub struct ContextError {
    pub identifier: Arc<Identifier>,
    pub error: GetAttributeError,
}

impl Lattice<QualifiedName> for AbstractEnvironment {
    type ContextError = ContextError;

    fn includes(
        &self,
        context: &impl NamespacesContext<QualifiedName, Self>,
        other: &Self,
    ) -> Result<bool, Self::ContextError> {
        for (name, other_attribute) in &other.attributes {
            match self.attributes.get(name) {
                Some(self_attribute) => {
                    if self_attribute == other_attribute {
                        continue;
                    }

                    let self_local_attribute =
                        self_attribute
                            .as_local(context)
                            .map_err(|error| ContextError {
                                identifier: name.clone(),
                                error,
                            })?;
                    let other_local_attribute =
                        other_attribute
                            .as_local(context)
                            .map_err(|error| ContextError {
                                identifier: name.clone(),
                                error,
                            })?;

                    if !self_local_attribute.includes(context, &other_local_attribute)? {
                        return Ok(false);
                    }
                }
                None => return Ok(false),
            }
        }

        Ok(true)
    }

    fn join(
        &self,
        context: &impl NamespacesContext<QualifiedName, Self>,
        other: &Self,
    ) -> Result<Self, Self::ContextError> {
        let mut new_abstract_environment = self.clone();

        for (name, other_attribute) in &other.attributes {
            match new_abstract_environment.attributes.entry(name.clone()) {
                imbl::hashmap::Entry::Occupied(mut entry) => {
                    let entry_attribute = entry.get();

                    if entry_attribute == other_attribute {
                        continue;
                    }

                    let entry_local_attribute =
                        entry_attribute
                            .as_local(context)
                            .map_err(|error| ContextError {
                                identifier: name.clone(),
                                error,
                            })?;
                    let other_local_attribute =
                        other_attribute
                            .as_local(context)
                            .map_err(|error| ContextError {
                                identifier: name.clone(),
                                error,
                            })?;

                    entry.insert(Arc::new(Attribute::Local(
                        entry_local_attribute.join(&other_local_attribute),
                    )));
                }
                imbl::hashmap::Entry::Vacant(entry) => {
                    entry.insert(other_attribute.clone());
                }
            }
        }

        let mut return_type_union = TypeUnion::new();
        return_type_union.add_type(new_abstract_environment.returned_value.clone());
        return_type_union.add_type(other.returned_value.clone());
        new_abstract_environment.returned_value = return_type_union.simplify();

        new_abstract_environment
            .raised_exceptions
            .extend(other.raised_exceptions.clone());
        new_abstract_environment.is_partial |= other.is_partial;
        new_abstract_environment.is_pure &= other.is_pure;
        new_abstract_environment
            .diagnostics
            .extend(other.diagnostics.clone());

        Ok(new_abstract_environment)
    }
}
