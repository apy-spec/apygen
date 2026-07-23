use crate::apy;
use crate::inference::analysis::abstract_state::AbstractState;
use crate::inference::identifiers::{ModuleName, Namespace, QualifiedName};
use crate::inference::primitives::literals::{
    LiteralBool, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInt, LiteralStr,
};
use crate::inference::{
    BUILTINS_MODULE, Base, LiteralClass, LiteralDict, LiteralFunction, LiteralGeneric,
    LiteralImportedModule, LiteralList, LiteralTuple, LiteralTypeAlias, NamespaceEvaluation,
    ProgramEvaluation, RaisedExceptions, TYPES_MODULE, TYPING_MODULE, Type, TypeInstance,
    TypeLiteral, TypeUnion, Visibility,
};
use log::debug;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use std::collections::BTreeMap;
use std::sync::Arc;

pub fn is_dunder_name(name: &str) -> bool {
    name.starts_with("__") && name.ends_with("__")
}

pub fn is_internal_name(name: &str) -> bool {
    name.starts_with("_") && !is_dunder_name(name)
}

pub fn is_internal_mangled_name(name: &str) -> bool {
    name.starts_with("__") && !name.ends_with("__")
}

pub fn visibility_from_name(name: &QualifiedName) -> Visibility {
    if name
        .identifiers
        .iter()
        .any(|component| is_internal_mangled_name(component))
    {
        Visibility::Internal
    } else {
        Visibility::Public
    }
}

pub fn visibility_from_class_name(name: &str) -> Visibility {
    if is_internal_mangled_name(name) {
        Visibility::Internal
    } else if is_internal_name(name) {
        Visibility::Subclass
    } else {
        Visibility::Public
    }
}

pub fn new_literal(arguments: Vec<apy::v1::TypeArgument>) -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(
        apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Literal"))
            .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE))),
    )
    .with_arguments(arguments)
}

pub fn convert_literal_integer(literal_integer: &LiteralInt) -> apy::v1::TypeInstance {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Int {
            int: literal_integer.to_string(),
        },
    }])
}

pub fn convert_literal_boolean(literal_boolean: &LiteralBool) -> apy::v1::TypeInstance {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Bool {
            bool: literal_boolean.value,
        },
    }])
}

pub fn convert_literal_float(literal_float: &LiteralFloat) -> apy::v1::TypeInstance {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Float {
            float: literal_float.value.to_string(),
        },
    }])
}

pub fn convert_literal_complex(literal_complex: &LiteralComplex) -> apy::v1::TypeInstance {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Complex {
            real: literal_complex.value.re.to_string(),
            imaginary: literal_complex.value.im.to_string(),
        },
    }])
}

pub fn convert_literal_string(literal_string: &LiteralStr) -> apy::v1::TypeInstance {
    new_literal(vec![apy::v1::TypeArgument::Value {
        value: apy::v1::PythonValue::Str {
            str: literal_string.value.as_ref().clone(),
        },
    }])
}

pub fn convert_literal_bytes(literal_bytes: &LiteralBytes) -> apy::v1::TypeInstance {
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

pub fn convert_literal_list(literal_list: &LiteralList) -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(apy::v1::TypeReference::new(apy::v1::QualifiedName::parse(
        "list",
    )))
}

pub fn convert_literal_tuple(literal_tuple: &LiteralTuple) -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(apy::v1::TypeReference::new(apy::v1::QualifiedName::parse(
        "tuple",
    )))
}

pub fn convert_literal_dict(literal_dict: &LiteralDict) -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(apy::v1::TypeReference::new(apy::v1::QualifiedName::parse(
        "dict",
    )))
}

pub fn convert_literal_function<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    literal_function: &LiteralFunction,
) -> Option<apy::v1::Function> {
    let evaluation_state = program_evaluation.get(&Namespace::NamedProgramEntity(
        literal_function.value.program_entity.clone(),
    ))?;

    // TODO: add return type

    let mut signature = apy::v1::Signature::new(apy::v1::Type::Instance(convert_type_any()));

    let mut parameters: Vec<apy::v1::Parameter> = Vec::new();
    for parameter in &literal_function.value.parameters {
        parameters.push(
            apy::v1::Parameter::new(
                parameter.name.as_ref().clone(),
                parameter.kind,
                convert_type(program_evaluation, &Arc::new(Type::Any))?,
            )
            .with_deprecated(parameter.deprecation.is_deprecated())
            .with_optional(parameter.is_optional),
        )
    }

    signature.parameters = apy::v1::Parameters::try_from(parameters).ok()?;
    signature.raises = convert_exceptions(
        program_evaluation,
        &evaluation_state.raised_exceptions().as_value()?.data,
    )?;

    let function = apy::v1::Function::new(apy::OneOrMany::one(signature));

    Some(function)
}

pub fn convert_literal_class<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    literal_class: &LiteralClass,
) -> Option<apy::v1::Class> {
    let evaluation_state = program_evaluation.get(&Namespace::NamedProgramEntity(
        literal_class.value.program_entity.clone(),
    ))?;

    // TODO: assert classes should return None

    Some(
        apy::v1::Class::new()
            .with_bases(
                literal_class
                    .value
                    .bases
                    .iter()
                    .map(|base| {
                        apy::v1::Type::Reference(
                            apy::v1::TypeReference::new(QualifiedName::from(
                                base.value.program_entity.name.as_ref().clone(),
                            ))
                            .with_module(Some(
                                base.value
                                    .program_entity
                                    .namespace
                                    .module_name()
                                    .as_ref()
                                    .clone(),
                            )),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
            .with_attributes(convert_abstract_environment(
                program_evaluation,
                evaluation_state,
            )?)
            .with_raises(convert_exceptions(
                program_evaluation,
                &evaluation_state.raised_exceptions().as_value()?.data,
            )?),
    )
}

pub fn convert_literal_type_alias<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    literal_type_alias: &LiteralTypeAlias,
) -> Option<apy::v1::TypeAlias> {
    Some(apy::v1::TypeAlias::new(convert_type(
        program_evaluation,
        literal_type_alias.value.alias.as_ref(),
    )?))
}

pub fn convert_literal_generic<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    literal_generic: &LiteralGeneric,
) -> Option<apy::v1::Generic> {
    Some(apy::v1::Generic::new(literal_generic.value.kind))
}

pub fn convert_literal_imported_module<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    literal_imported_module: &LiteralImportedModule,
) -> Option<apy::v1::ImportedModule> {
    Some(apy::v1::ImportedModule::new(
        literal_imported_module.value.module.as_ref().clone(),
    ))
}

pub enum ConvertedTypeLiteral {
    TypeInstance(apy::v1::TypeInstance),
    PythonValue(apy::v1::PythonValue),
    Function(apy::v1::Function),
    Class(apy::v1::Class),
    TypeAlias(apy::v1::TypeAlias),
    Generic(apy::v1::Generic),
    ImportedModule(apy::v1::ImportedModule),
}

pub fn convert_type_literal<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    type_literal: &TypeLiteral,
) -> Option<ConvertedTypeLiteral> {
    Some(match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_integer(literal_integer))
        }
        TypeLiteral::Boolean(literal_boolean) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_boolean(literal_boolean))
        }
        TypeLiteral::Float(literal_float) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_float(literal_float))
        }
        TypeLiteral::Complex(literal_complex) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_complex(literal_complex))
        }
        TypeLiteral::String(literal_string) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_string(literal_string))
        }
        TypeLiteral::Bytes(literal_bytes) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_bytes(literal_bytes))
        }
        TypeLiteral::None => ConvertedTypeLiteral::PythonValue(convert_literal_none()),
        TypeLiteral::Ellipsis => ConvertedTypeLiteral::PythonValue(convert_literal_ellipsis()),
        TypeLiteral::List(literal_list) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_list(&literal_list))
        }
        TypeLiteral::Tuple(literal_tuple) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_tuple(&literal_tuple))
        }
        TypeLiteral::Dict(literal_dict) => {
            ConvertedTypeLiteral::TypeInstance(convert_literal_dict(&literal_dict))
        }
        TypeLiteral::Function(literal_function) => ConvertedTypeLiteral::Function(
            convert_literal_function(program_evaluation, literal_function)?,
        ),
        TypeLiteral::OverloadedFunction(literal_overloaded_function) => {
            ConvertedTypeLiteral::Function(convert_literal_function(
                program_evaluation,
                literal_overloaded_function.value.target.as_ref()?,
            )?) // TODO: improve the conversion
        }
        TypeLiteral::Method(_) => return None, // TODO: improve the conversion
        TypeLiteral::Class(literal_class) => {
            ConvertedTypeLiteral::Class(convert_literal_class(program_evaluation, literal_class)?)
        }
        TypeLiteral::TypeAlias(literal_type_alias) => ConvertedTypeLiteral::TypeAlias(
            convert_literal_type_alias(program_evaluation, literal_type_alias)?,
        ),
        TypeLiteral::Generic(literal_generic) => ConvertedTypeLiteral::Generic(
            convert_literal_generic(program_evaluation, literal_generic)?,
        ),
        TypeLiteral::ImportedModule(literal_imported_module) => {
            ConvertedTypeLiteral::ImportedModule(convert_literal_imported_module(
                program_evaluation,
                literal_imported_module,
            )?)
        }
    })
}

pub fn convert_type_any() -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(
        apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Any"))
            .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE))),
    )
}

pub fn convert_type_never() -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(
        apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Never"))
            .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE))),
    )
}

pub fn convert_type_no_return() -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(
        apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("NoReturn"))
            .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE))),
    )
}

pub fn convert_type_instance<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    type_instance: &TypeInstance,
) -> Option<apy::v1::TypeInstance> {
    let program_entity = match &type_instance.base {
        Base::Class(literal_class) => &literal_class.value.program_entity,
        Base::TypeAlias(_) => return None,
        Base::Generic(_) => return None,
    };

    let type_reference =
        apy::v1::TypeReference::new(QualifiedName::from(program_entity.name.as_ref().clone()))
            .with_module(Some(
                program_entity.namespace.module_name().as_ref().clone(),
            ));

    Some(
        apy::v1::TypeInstance::new(type_reference).with_arguments(
            type_instance
                .arguments
                .iter()
                .map(|argument| {
                    Some(apy::v1::TypeArgument::Type(convert_type(
                        program_evaluation,
                        argument.as_ref(),
                    )?))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
    )
}

pub fn convert_type_union<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    type_union: &TypeUnion,
) -> Option<apy::v1::TypeInstance> {
    Some(
        apy::v1::TypeInstance::new(
            apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Union"))
                .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE))),
        )
        .with_arguments(
            type_union
                .types
                .iter()
                .map(|ty| {
                    Some(apy::v1::TypeArgument::Type(convert_type(
                        program_evaluation,
                        ty,
                    )?))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
    )
}

pub fn convert_type_intersection() -> apy::v1::TypeInstance {
    apy::v1::TypeInstance::new(
        apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("Intersection"))
            .with_module(Some(apy::v1::QualifiedName::parse(TYPING_MODULE))),
    )
}

pub fn convert_type<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    ty: &Type,
) -> Option<apy::v1::Type> {
    Some(apy::v1::Type::Instance(match ty {
        Type::Any => convert_type_any(),
        Type::Never => convert_type_never(),
        Type::NoReturn => convert_type_no_return(),
        Type::Union(type_union) => convert_type_union(program_evaluation, type_union)?,
        Type::Intersection(_) => convert_type_intersection(),
        Type::Instance(type_instance) => convert_type_instance(program_evaluation, type_instance)?,
        Type::Literal(type_literal) => {
            match convert_type_literal(program_evaluation, type_literal)? {
                ConvertedTypeLiteral::TypeInstance(ty) => ty,
                ConvertedTypeLiteral::PythonValue(python_value) => match python_value {
                    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::None) => {
                        return Some(apy::v1::Type::Literal(apy::v1::TypeLiteral::None));
                    }
                    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::Ellipsis) => {
                        apy::v1::TypeInstance::new(
                            apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("ellipsis"))
                                .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE))),
                        )
                    }
                    _ => {
                        unreachable!("Only None and Ellipsis should be converted to Python values")
                    }
                },
                ConvertedTypeLiteral::Function(_) => apy::v1::TypeInstance::new(
                    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("FunctionType"))
                        .with_module(Some(apy::v1::QualifiedName::parse(TYPES_MODULE))),
                ),
                ConvertedTypeLiteral::Class(_) => apy::v1::TypeInstance::new(
                    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("type"))
                        .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE))),
                ),
                ConvertedTypeLiteral::TypeAlias(_) => apy::v1::TypeInstance::new(
                    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("type"))
                        .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE))),
                ),
                ConvertedTypeLiteral::Generic(_) => apy::v1::TypeInstance::new(
                    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("type"))
                        .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE))),
                ),
                ConvertedTypeLiteral::ImportedModule(_) => apy::v1::TypeInstance::new(
                    apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("ModuleType"))
                        .with_module(Some(apy::v1::QualifiedName::parse(TYPES_MODULE))),
                ),
            }
        }
    }))
}

pub fn convert_exceptions<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    raises: &RaisedExceptions,
) -> Option<Vec<apy::v1::Exception>> {
    raises
        .exceptions
        .iter()
        .map(|exception| {
            convert_type(program_evaluation, exception.exception_type.as_ref())
                .map(apy::v1::Exception::new)
        })
        .collect()
}

pub fn convert_attribute<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    attribute_type: &Type,
) -> Option<apy::v1::Attribute> {
    let ty = match attribute_type {
        Type::Any => apy::v1::Type::Instance(convert_type_any()),
        Type::Never => apy::v1::Type::Instance(convert_type_never()),
        Type::NoReturn => apy::v1::Type::Instance(convert_type_no_return()),
        Type::Instance(type_instance) => {
            apy::v1::Type::Instance(convert_type_instance(program_evaluation, type_instance)?)
        }
        Type::Union(type_union) => {
            apy::v1::Type::Instance(convert_type_union(program_evaluation, type_union)?)
        }
        Type::Intersection(_) => apy::v1::Type::Instance(convert_type_intersection()),
        Type::Literal(type_literal) => {
            match convert_type_literal(program_evaluation, type_literal)? {
                ConvertedTypeLiteral::TypeInstance(ty) => apy::v1::Type::Instance(ty),
                ConvertedTypeLiteral::PythonValue(type_argument) => match type_argument {
                    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::None) => {
                        apy::v1::Type::Literal(apy::v1::TypeLiteral::None)
                    }
                    apy::v1::PythonValue::Other(apy::v1::OtherPythonValue::Ellipsis) => {
                        apy::v1::Type::Reference(
                            apy::v1::TypeReference::new(apy::v1::QualifiedName::parse("ellipsis"))
                                .with_module(Some(apy::v1::QualifiedName::parse(BUILTINS_MODULE))),
                        )
                    }
                    _ => {
                        unreachable!("Only None and Ellipsis should be converted to Python values")
                    }
                },
                ConvertedTypeLiteral::Function(function) => {
                    return Some(apy::v1::Attribute::Function(function));
                }
                ConvertedTypeLiteral::Class(class) => {
                    return Some(apy::v1::Attribute::Class(class));
                }
                ConvertedTypeLiteral::TypeAlias(type_alias) => {
                    return Some(apy::v1::Attribute::TypeAlias(type_alias));
                }
                ConvertedTypeLiteral::Generic(generic) => {
                    return Some(apy::v1::Attribute::Generic(generic));
                }
                ConvertedTypeLiteral::ImportedModule(imported_module) => {
                    return Some(apy::v1::Attribute::ImportedModule(imported_module));
                }
            }
        }
    };

    Some(apy::v1::Attribute::Variable(apy::v1::Variable::new(ty)))
}

pub fn convert_abstract_environment<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    namespace_evaluation: &N,
) -> Option<BTreeMap<apy::v1::Identifier, apy::OneOrMany<apy::v1::Attribute>>> {
    let mut attributes: BTreeMap<apy::v1::Identifier, apy::OneOrMany<apy::v1::Attribute>> =
        BTreeMap::new();

    for (attribute_name, ty) in namespace_evaluation.attributes() {
        let Some(attribute) = convert_attribute(
            program_evaluation,
            &ty.to_value().map(|ty| ty.data).unwrap_or(Type::Any),
        ) else {
            debug!("Skipping attribute {}", attribute_name);
            continue;
        };
        attributes.insert(
            attribute_name.as_ref().clone(),
            apy::OneOrMany::one(attribute),
        );
    }

    Some(attributes)
}

pub fn convert_module<N: NamespaceEvaluation + Clone>(
    program_evaluation: &ProgramEvaluation<N>,
    module: &ModuleName,
) -> Option<apy::v1::Module> {
    let namespace_evaluation = program_evaluation.get(&Namespace::Module(module.clone()))?;

    Some(
        apy::v1::Module::new(
            apy::v1::ModuleAttributes::try_from(convert_abstract_environment(
                program_evaluation,
                namespace_evaluation,
            )?)
            .ok()?,
            apy::v1::ModuleAttributes::new(),
        )
        .with_visibility(visibility_from_name(&module).into()),
    )
}

pub fn convert_apy_v1<'a, N: NamespaceEvaluation + Clone + Send + Sync>(
    program_evaluation: &ProgramEvaluation<N>,
    target_modules: impl IntoParallelIterator<Item = &'a Arc<QualifiedName>>,
) -> apy::v1::ApyV1 {
    apy::v1::ApyV1::new().with_modules(
        target_modules
            .into_par_iter()
            .filter_map(|module_name| {
                Some((
                    module_name.as_ref().clone(),
                    convert_module(program_evaluation, &module_name)?,
                ))
            })
            .collect(),
    )
}
