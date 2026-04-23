use crate::abstract_environment::{
    AbstractEnvironment, Attribute, BUILTINS_MODULE, LiteralBigInteger, LiteralBoolean,
    LiteralBytes, LiteralClass, LiteralComplex, LiteralDict, LiteralFloat, LiteralFunction,
    LiteralGeneric, LiteralImportedModule, LiteralInteger, LiteralList, LiteralString,
    LiteralTuple, LiteralTypeAlias, QualifiedName, TYPES_MODULE, TYPING_MODULE, Type, TypeLiteral,
    TypeReference, TypeUnion,
};
use crate::genkill::visibility::visibility_from_module_name;
use apy;
use apygen_analysis::cfg::Cfg;
use apygen_analysis::namespace::{Location, NamespaceLocation, NamespacesContext};
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

pub fn new_literal(arguments: Vec<apy::v1::TypeArgument>) -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Literal"))
        .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE)))
        .with_arguments(arguments)
}

pub fn convert_literal_integer(literal_integer: &LiteralInteger) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Int {
            int: literal_integer.value.to_string(),
        },
    }])
}

pub fn convert_literal_big_integer(
    literal_big_integer: &LiteralBigInteger,
) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Int {
            int: if literal_big_integer.positive {
                literal_big_integer.value.to_string()
            } else {
                format!("-{}", literal_big_integer.value)
            },
        },
    }])
}

pub fn convert_literal_boolean(literal_boolean: &LiteralBoolean) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Bool {
            bool: literal_boolean.value,
        },
    }])
}

pub fn convert_literal_float(literal_float: &LiteralFloat) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Float {
            float: literal_float.value.to_string(),
        },
    }])
}

pub fn convert_literal_complex(literal_complex: &LiteralComplex) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Complex {
            real: literal_complex.real.to_string(),
            imaginary: literal_complex.imaginary.to_string(),
        },
    }])
}

pub fn convert_literal_string(literal_string: &LiteralString) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Str {
            str: literal_string.value.as_ref().clone(),
        },
    }])
}

pub fn convert_literal_bytes(literal_bytes: &LiteralBytes) -> apy::v1::TypeReference {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Bytes {
            bytes: literal_bytes.value.iter().cloned().collect(),
        },
    }])
}

pub fn convert_literal_none() -> apy::v1::PythonValue {
    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::None)
}

pub fn convert_literal_ellipsis() -> apy::v1::PythonValue {
    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::Ellipsis)
}

pub fn convert_literal_list(literal_list: &LiteralList) -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("list"))
}

pub fn convert_literal_tuple(literal_tuple: &LiteralTuple) -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("tuple"))
}

pub fn convert_literal_dict(literal_dict: &LiteralDict) -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("tuple"))
}

pub fn convert_literal_function(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    literal_function: &LiteralFunction,
) -> Option<apy::v1::Function> {
    let abstract_environment = context.get_abstract_environment(&Location::at_exit(
        literal_function.value.location.as_sub_location(),
    ))?;

    let return_type = convert_type(context, &abstract_environment.returned_value)?;

    let mut signature = apy::v1::Signature::new(return_type);

    let mut parameters: Vec<apy::v1::Parameter> = Vec::new();
    for parameter in &literal_function.value.parameters {
        parameters.push(
            apy::v1::Parameter::new(
                parameter.name.clone(),
                parameter.kind,
                convert_type(context, &parameter.parameter_type)?,
            )
            .with_deprecated(parameter.is_deprecated)
            .with_optional(parameter.is_optional),
        )
    }

    signature.parameters = apy::v1::Parameters::try_from(parameters).ok()?;

    let function = apy::v1::Function::new(apy::OneOrMany::one(signature));

    Some(function)
}

pub fn convert_literal_class(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    literal_class: &LiteralClass,
) -> Option<apy::v1::Class> {
    let abstract_environment = context.get_abstract_environment(&Location::at_exit(
        literal_class.value.location.as_sub_location(),
    ))?;

    let return_type = convert_type(context, &abstract_environment.returned_value)?;

    assert!(matches!(return_type, apy::v1::Type::Literal(_)));

    Some(
        apy::v1::Class::new()
            .with_attributes(convert_abstract_environment(context, abstract_environment)?),
    )
}

pub fn convert_literal_type_alias(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    literal_type_alias: &LiteralTypeAlias,
) -> Option<apy::v1::TypeAlias> {
    Some(apy::v1::TypeAlias::new(convert_type(
        context,
        literal_type_alias.value.alias.as_ref(),
    )?))
}

pub fn convert_literal_generic(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    literal_generic: &LiteralGeneric,
) -> Option<apy::v1::Generic> {
    Some(apy::v1::Generic::new(literal_generic.value.kind))
}

pub fn convert_literal_imported_module(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    literal_imported_module: &LiteralImportedModule,
) -> Option<apy::v1::ImportedModule> {
    Some(apy::v1::ImportedModule::new(
        literal_imported_module.value.module.as_ref().clone(),
    ))
}

pub enum ConvertedTypeLiteral {
    TypeReference(apy::v1::TypeReference),
    PythonValue(apy::v1::PythonValue),
    Function(apy::v1::Function),
    Class(apy::v1::Class),
    TypeAlias(apy::v1::TypeAlias),
    Generic(apy::v1::Generic),
    ImportedModule(apy::v1::ImportedModule),
}

pub fn convert_type_literal(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    type_literal: &TypeLiteral,
) -> Option<ConvertedTypeLiteral> {
    Some(match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_integer(literal_integer))
        }
        TypeLiteral::BigInteger(literal_big_integer) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_big_integer(literal_big_integer))
        }
        TypeLiteral::Boolean(literal_boolean) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_boolean(literal_boolean))
        }
        TypeLiteral::Float(literal_float) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_float(literal_float))
        }
        TypeLiteral::Complex(literal_complex) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_complex(literal_complex))
        }
        TypeLiteral::String(literal_string) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_string(literal_string))
        }
        TypeLiteral::Bytes(literal_bytes) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_bytes(literal_bytes))
        }
        TypeLiteral::None => ConvertedTypeLiteral::PythonValue(convert_literal_none()),
        TypeLiteral::Ellipsis => ConvertedTypeLiteral::PythonValue(convert_literal_ellipsis()),
        TypeLiteral::List(literal_list) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_list(&literal_list))
        }
        TypeLiteral::Tuple(literal_tuple) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_tuple(&literal_tuple))
        }
        TypeLiteral::Dict(literal_dict) => {
            ConvertedTypeLiteral::TypeReference(convert_literal_dict(&literal_dict))
        }
        TypeLiteral::Function(literal_function) => {
            ConvertedTypeLiteral::Function(convert_literal_function(context, literal_function)?)
        }
        TypeLiteral::Class(literal_class) => {
            ConvertedTypeLiteral::Class(convert_literal_class(context, literal_class)?)
        }
        TypeLiteral::TypeAlias(literal_type_alias) => ConvertedTypeLiteral::TypeAlias(
            convert_literal_type_alias(context, literal_type_alias)?,
        ),
        TypeLiteral::Generic(literal_generic) => {
            ConvertedTypeLiteral::Generic(convert_literal_generic(context, literal_generic)?)
        }
        TypeLiteral::ImportedModule(literal_imported_module) => {
            ConvertedTypeLiteral::ImportedModule(convert_literal_imported_module(
                context,
                literal_imported_module,
            )?)
        }
    })
}

pub fn convert_type_any() -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Any"))
        .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE)))
}

pub fn convert_type_never() -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Never"))
        .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE)))
}

pub fn convert_type_no_return() -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("NoReturn"))
        .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE)))
}

pub fn convert_type_reference(type_reference: &TypeReference) -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(type_reference.name.clone())
        .with_module(Some(type_reference.module.as_ref().clone()))
}

pub fn convert_type_union(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    type_union: &TypeUnion,
) -> Option<apy::v1::TypeReference> {
    Some(
        apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Union"))
            .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE)))
            .with_arguments(
                type_union
                    .types()
                    .iter()
                    .map(|ty| {
                        Some(apy::v1::TypeArgument::Type(convert_type(
                            context,
                            ty.as_ref(),
                        )?))
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
    )
}

pub fn convert_type_intersection() -> apy::v1::TypeReference {
    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Intersection"))
        .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE)))
}

pub fn convert_type(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    ty: &Type,
) -> Option<apy::v1::Type> {
    Some(apy::v1::Type::Reference(match ty {
        Type::Any => convert_type_any(),
        Type::Never => convert_type_never(),
        Type::NoReturn => convert_type_no_return(),
        Type::Reference(type_reference) => convert_type_reference(type_reference),
        Type::Union(type_union) => convert_type_union(context, type_union)?,
        Type::Intersection(_) => convert_type_intersection(),
        Type::Literal(type_literal) => match convert_type_literal(context, type_literal)? {
            ConvertedTypeLiteral::TypeReference(ty) => ty,
            ConvertedTypeLiteral::PythonValue(python_value) => {
                return match python_value {
                    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::None) => {
                        Some(apy::v1::Type::Literal(apy::v1::TypeLiteral::None))
                    }
                    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::Ellipsis) => {
                        Some(apy::v1::Type::Reference(convert_type_any()))
                    }
                    _ => {
                        unreachable!("Only None and Ellipsis should be converted to Python values")
                    }
                };
            }
            ConvertedTypeLiteral::Function(_) => {
                apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("FunctionType"))
                    .with_module(Some(apy::v1::QualifiedName::parse(TYPES_MODULE)))
            }
            ConvertedTypeLiteral::Class(_) => {
                apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("type"))
                    .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE)))
            }
            ConvertedTypeLiteral::TypeAlias(_) => {
                apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("type"))
                    .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE)))
            }
            ConvertedTypeLiteral::Generic(_) => {
                apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("type"))
                    .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE)))
            }
            ConvertedTypeLiteral::ImportedModule(_) => {
                apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("ModuleType"))
                    .with_module(Some(apy::v1::QualifiedName::parse(TYPES_MODULE)))
            }
        },
    }))
}

pub fn convert_attribute(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    attribute: &Attribute,
) -> Option<apy::v1::Attribute> {
    let local_attribute = attribute.as_local(context).ok()?;

    let ty = match local_attribute.attribute_type.as_ref() {
        Type::Any => apy::v1::Type::Reference(convert_type_any()),
        Type::Never => apy::v1::Type::Reference(convert_type_never()),
        Type::NoReturn => apy::v1::Type::Reference(convert_type_no_return()),
        Type::Reference(type_reference) => {
            apy::v1::Type::Reference(convert_type_reference(type_reference))
        }
        Type::Union(type_union) => {
            apy::v1::Type::Reference(convert_type_union(context, type_union)?)
        }
        Type::Intersection(_) => apy::v1::Type::Reference(convert_type_intersection()),
        Type::Literal(type_literal) => match convert_type_literal(context, type_literal)? {
            ConvertedTypeLiteral::TypeReference(ty) => apy::v1::Type::Reference(ty),
            ConvertedTypeLiteral::PythonValue(type_argument) => match type_argument {
                apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::None) => {
                    apy::v1::Type::Literal(apy::v1::TypeLiteral::None)
                }
                apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::Ellipsis) => {
                    apy::v1::Type::Reference(convert_type_any())
                }
                _ => unreachable!("Only None and Ellipsis should be converted to Python values"),
            },
            ConvertedTypeLiteral::Function(function) => {
                return Some(apy::v1::Attribute::Function(
                    function.with_final(local_attribute.is_final),
                ));
            }
            ConvertedTypeLiteral::Class(class) => {
                return Some(apy::v1::Attribute::Class(
                    class
                        .with_final(local_attribute.is_final)
                        .with_visibility(local_attribute.visibility),
                ));
            }
            ConvertedTypeLiteral::TypeAlias(type_alias) => {
                return Some(apy::v1::Attribute::TypeAlias(
                    type_alias.with_visibility(local_attribute.visibility),
                ));
            }
            ConvertedTypeLiteral::Generic(generic) => {
                return Some(apy::v1::Attribute::Generic(
                    generic.with_visibility(local_attribute.visibility),
                ));
            }
            ConvertedTypeLiteral::ImportedModule(imported_module) => {
                return Some(apy::v1::Attribute::ImportedModule(
                    imported_module.with_visibility(local_attribute.visibility),
                ));
            }
        },
    };

    Some(apy::v1::Attribute::Variable(
        apy::v1::Variable::new(ty)
            .with_final(local_attribute.is_final)
            .with_visibility(local_attribute.visibility)
            .with_deprecated(local_attribute.is_deprecated)
            .with_initialised(local_attribute.is_initialised)
            .with_readonly(local_attribute.is_readonly),
    ))
}

pub fn convert_abstract_environment(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    abstract_environment: &AbstractEnvironment,
) -> Option<BTreeMap<apy::v1::Identifier, apy::OneOrMany<apy::v1::Attribute>>> {
    let mut attributes: BTreeMap<apy::v1::Identifier, apy::OneOrMany<apy::v1::Attribute>> =
        BTreeMap::new();

    for (attribute_name, attribute) in &abstract_environment.attributes {
        attributes.insert(
            attribute_name.as_ref().clone(),
            apy::OneOrMany::one(convert_attribute(context, attribute)?),
        );
    }

    Some(attributes)
}

pub fn convert_module(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    module: &Arc<apy::v1::QualifiedName>,
) -> Option<apy::v1::Module> {
    let namespace_location = NamespaceLocation::new(module.clone());

    let Some(abstract_environment) =
        context.get_abstract_environment(&Location::at_exit(namespace_location))
    else {
        return None;
    };

    Some(
        apy::v1::Module::new(
            apy::v1::ModuleAttributes::try_from(convert_abstract_environment(
                context,
                abstract_environment,
            )?)
            .ok()?,
            apy::v1::ModuleAttributes::new(),
        )
        .with_visibility(visibility_from_module_name(&module)),
    )
}

pub fn convert_apy_v1<'a>(
    context: &(impl NamespacesContext<QualifiedName, AbstractEnvironment> + Sync),
    target_modules: impl IntoParallelIterator<Item = &'a Arc<QualifiedName>>,
) -> apy::v1::ApyV1 {
    apy::v1::ApyV1::new().with_modules(
        target_modules
            .into_par_iter()
            .filter_map(|module| Some((module.as_ref().clone(), convert_module(context, &module)?)))
            .collect(),
    )
}
