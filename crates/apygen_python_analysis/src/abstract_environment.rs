use crate::analysis::lattice::Lattice;
use crate::analysis::namespace::{Location, NamespaceLocation, NamespacesContext};
pub use apy::OneOrMany;
pub use apy::v1::{
    FromInvalidIdentifierError, GenericKind, Identifier, ParameterKind, QualifiedName, Visibility,
};
use imbl;
pub use ordered_float::OrderedFloat;
use std::sync::Arc;
use thiserror::Error;

pub const BUILTINS_MODULE: &str = "builtins";
pub const TYPES_MODULE: &str = "types";
pub const TYPING_MODULE: &str = "typing";
pub const TYPING_EXTENSIONS_MODULE: &str = "typing_extensions";
pub const ABC_MODULE: &str = "abc";

pub fn new_identifier_or_panic(name: &str) -> Identifier {
    Identifier::try_from(name).expect(&format!("Invalid identifier: '{}'", name))
}

pub fn join_visibility(first: Visibility, second: Visibility) -> Visibility {
    if matches!(first, Visibility::Internal) || matches!(second, Visibility::Internal) {
        Visibility::Internal
    } else if matches!(first, Visibility::Subclass) && matches!(second, Visibility::Subclass) {
        Visibility::Subclass
    } else {
        Visibility::Public
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericType {
    pub location: Location<QualifiedName>,

    pub kind: GenericKind,

    pub bound: Arc<Type>,

    pub constraints: Vec<Arc<Type>>,

    pub default: Option<Arc<Type>>,

    pub is_covariant: bool,

    pub is_contravariant: bool,
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
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionType {
    pub location: Location<QualifiedName>,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub parameters: Vec<Parameter>,

    pub is_async: bool,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClassType {
    pub location: Location<QualifiedName>,

    pub generics: imbl::OrdMap<String, GenericType>,

    pub bases: imbl::Vector<Arc<Type>>,

    pub keyword_arguments: imbl::OrdMap<String, Type>,

    pub is_abstract: bool,
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
pub struct LiteralFloat {
    pub value: OrderedFloat<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralComplex {
    pub real: OrderedFloat<f64>,
    pub image: OrderedFloat<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralString {
    pub value: Arc<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralBytes {
    pub value: imbl::Vector<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralBoolean {
    pub value: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralList {
    pub value: imbl::Vector<Arc<TypeLiteral>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralTuple {
    pub value: imbl::Vector<Arc<TypeLiteral>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralDict {
    pub value: imbl::OrdMap<Arc<TypeLiteral>, Arc<TypeLiteral>>,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Any,
    Never,
    NoReturn,
    Reference {
        name: QualifiedName,
        arguments: imbl::Vector<Arc<Type>>,
        origin: Option<Location<QualifiedName>>,
    },
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

    pub fn new_reference(name: QualifiedName, origin: Location<QualifiedName>) -> Self {
        Type::Reference {
            name,
            arguments: imbl::Vector::new(),
            origin: Some(origin),
        }
    }

    pub fn new_absolute_reference(name: QualifiedName) -> Self {
        Self::new_absolute_reference_with_args(name, imbl::Vector::new())
    }

    pub fn new_absolute_reference_with_args(
        name: QualifiedName,
        arguments: imbl::Vector<Arc<Type>>,
    ) -> Self {
        Type::Reference {
            name,
            arguments,
            origin: None,
        }
    }

    pub fn new_builtins_reference(id: &str) -> Self {
        Self::new_absolute_reference(QualifiedName {
            identifiers: OneOrMany::try_from_iter([
                Identifier::try_from(BUILTINS_MODULE).unwrap(),
                Identifier::try_from(id).unwrap(),
            ])
            .unwrap(),
        })
    }

    pub fn new_builtins_reference_with_args(id: &str, arguments: imbl::Vector<Arc<Type>>) -> Self {
        Self::new_absolute_reference_with_args(
            QualifiedName {
                identifiers: OneOrMany::try_from_iter([
                    Identifier::try_from(BUILTINS_MODULE).unwrap(),
                    Identifier::try_from(id).unwrap(),
                ])
                .unwrap(),
            },
            arguments,
        )
    }

    pub fn new_list(element_type: Arc<Type>) -> Self {
        Self::new_builtins_reference_with_args("list", imbl::vector![element_type])
    }

    pub fn new_tuple<I: IntoIterator<Item = Arc<Type>>>(element_types: I) -> Self {
        Self::new_builtins_reference_with_args("tuple", element_types.into_iter().collect())
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

        LocalAttribute {
            attribute_type: type_union.simplify(),
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Attribute {
    Local(LocalAttribute),
    Imported(ImportedAttribute),
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

    let Some(attribute) = abstract_environment.attributes.get(name) else {
        return Err(GetAttributeError::AttributeNotFound {
            location: location.clone(),
            identifier: name.clone(),
        });
    };

    Ok(attribute)
}

pub fn resolve_attribute<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    attribute: &'a Attribute,
) -> Result<&'a LocalAttribute, GetAttributeError> {
    match attribute {
        Attribute::Local(local_attribute) => Ok(local_attribute),
        Attribute::Imported(imported_attribute) => resolve_attribute(
            context,
            get_attribute(
                context,
                &Location::from(imported_attribute.module.clone()),
                &imported_attribute.name,
            )?,
        ),
    }
}

#[derive(Error, Debug)]
pub enum FindTypeError {
    #[error("failed to resolve attribute: {0}")]
    FailedToResolveAttribute(#[from] GetAttributeError),
    #[error("the identifier `{0:?}` is not a namespace")]
    IsNotNamespace(Identifier),
}

fn get_type_attribute<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    identifiers: &[Identifier],
) -> Result<&'a LocalAttribute, FindTypeError> {
    let (identifier, attribute_identifiers) = identifiers
        .split_first()
        .expect("identifiers should not be empty");

    let attribute = get_attribute(context, location, identifier)?;

    let local_attribute = resolve_attribute(context, attribute)?;

    if attribute_identifiers.is_empty() {
        return Ok(local_attribute);
    };

    let Type::Literal(literal_value) = local_attribute.attribute_type.as_ref() else {
        return Err(FindTypeError::IsNotNamespace(identifier.to_owned()));
    };

    match literal_value.as_ref() {
        TypeLiteral::Class(class_type) => {
            get_type_attribute(context, &class_type.value.location, attribute_identifiers)
        }
        TypeLiteral::ImportedModule(module_reference_type) => get_type_attribute(
            context,
            &Location::from(module_reference_type.value.module.clone()),
            attribute_identifiers,
        ),
        _ => Err(FindTypeError::IsNotNamespace(identifier.to_owned())),
    }
}

pub fn get_type<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &QualifiedName,
) -> Result<&'a Type, FindTypeError> {
    Ok(&get_type_attribute(context, location, &name.identifiers)?.attribute_type)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Diagnostic {
    InvalidAnnotation { location: Location<QualifiedName> },
}

#[derive(Debug, Clone, Default)]
pub struct AbstractEnvironment {
    pub attributes: imbl::HashMap<Arc<Identifier>, Arc<Attribute>>,
    pub returned_value: Option<Type>,
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
                        resolve_attribute(context, self_attribute).map_err(|error| {
                            ContextError {
                                identifier: name.clone(),
                                error,
                            }
                        })?;

                    let other_local_attribute = resolve_attribute(context, other_attribute)
                        .map_err(|error| ContextError {
                            identifier: name.clone(),
                            error,
                        })?;

                    if !self_local_attribute.includes(context, other_local_attribute)? {
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
                    if entry.get() == other_attribute {
                        continue;
                    }

                    let entry_local_attribute =
                        resolve_attribute(context, entry.get()).map_err(|error| ContextError {
                            identifier: name.clone(),
                            error,
                        })?;
                    let other_local_attribute = resolve_attribute(context, other_attribute)
                        .map_err(|error| ContextError {
                            identifier: name.clone(),
                            error,
                        })?;

                    entry.insert(Arc::new(Attribute::Local(
                        entry_local_attribute.join(other_local_attribute),
                    )));
                }
                imbl::hashmap::Entry::Vacant(entry) => {
                    entry.insert(other_attribute.clone());
                }
            }
        }

        Ok(new_abstract_environment)
    }
}
