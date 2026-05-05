use crate::abstract_environment::{
    LiteralString, LiteralTuple, Parameter, Sourced, Type, TypeInstance, TypeLiteral, TypeUnion,
};
use apy::v1::{Identifier, ParameterKind};
use imbl;
use std::collections::BTreeMap;
use std::sync::Arc;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BoundArguments {
    pub variables: BTreeMap<Parameter, Sourced<Arc<Type>>>,
}

impl BoundArguments {
    pub fn new() -> Self {
        Self::default()
    }
}

impl From<&imbl::Vector<Parameter>> for BoundArguments {
    fn from(parameters: &imbl::Vector<Parameter>) -> Self {
        let mut bindings = Self::new();
        for parameter in parameters {
            let ty = match parameter.kind {
                ParameterKind::PositionalOnly
                | ParameterKind::PositionalOrKeyword
                | ParameterKind::KeywordOnly => parameter.parameter_type.clone(),
                ParameterKind::VarPositional => {
                    Arc::new(Type::Instance(TypeInstance::builtins_tuple([
                        parameter.parameter_type.clone(),
                        Arc::new(Type::new_literal(TypeLiteral::Ellipsis)),
                    ])))
                }
                ParameterKind::VarKeyword => Arc::new(Type::Instance(TypeInstance::builtins_dict(
                    Arc::new(Type::Instance(TypeInstance::builtins("str"))),
                    parameter.parameter_type.clone(),
                ))),
            };
            bindings
                .variables
                .insert(parameter.clone(), Sourced::specified(ty));
        }
        bindings
    }
}

#[derive(Error, Debug)]
pub enum BindError {
    #[error("Missing positional argument")]
    MissingPositionalArgument,
    #[error("Missing positional or keyword argument")]
    MissingPositionalOrKeywordArgument,
    #[error("Missing keyword argument")]
    MissingKeywordArgument,
    #[error("Too many positional arguments provided")]
    TooManyPositionalArguments,
    #[error("Unexpected keyword argument provided")]
    UnexpectedKeywordArgument,
    #[error("Multiple values for the same parameter provided")]
    MultipleValuesForParameter,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Arguments {
    pub positional: Vec<Arc<Type>>,
    pub keyword: BTreeMap<Arc<Identifier>, Arc<Type>>,
}

impl Arguments {
    pub fn bind(&self, parameters: &imbl::Vector<Parameter>) -> Result<BoundArguments, BindError> {
        let mut bindings = BoundArguments::new();
        let mut positional_iter = self.positional.iter().cloned();
        for parameter in parameters {
            match parameter.kind {
                ParameterKind::PositionalOnly => {
                    if let Some(argument) = positional_iter.next() {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument));
                    } else {
                        return Err(BindError::MissingPositionalArgument);
                    }
                }
                ParameterKind::PositionalOrKeyword => {
                    if let Some(argument) = positional_iter.next() {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if let Some(argument) = self.keyword.get(&parameter.name) {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else {
                        return Err(BindError::MissingPositionalOrKeywordArgument);
                    }
                }
                ParameterKind::VarPositional => {
                    let mut var_positional_arguments = TypeUnion::new();

                    while let Some(argument) = positional_iter.next() {
                        var_positional_arguments.add_type(argument);
                    }

                    let arguments = if var_positional_arguments.is_empty() {
                        imbl::vector![Arc::new(Type::Literal(Arc::new(TypeLiteral::Tuple(
                            LiteralTuple {
                                value: imbl::Vector::new()
                            }
                        ))))]
                    } else {
                        imbl::vector![var_positional_arguments.simplify()]
                    };

                    let ty = Arc::new(Type::Instance(
                        TypeInstance::builtins("tuple").with_arguments(arguments),
                    ));

                    bindings
                        .variables
                        .insert(parameter.clone(), Sourced::inferred(ty));
                }
                ParameterKind::KeywordOnly => {
                    if bindings.variables.contains_key(&parameter) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    if let Some(argument) = self.keyword.get(&parameter.name) {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else {
                        return Err(BindError::MissingKeywordArgument);
                    }
                }
                ParameterKind::VarKeyword => {
                    if bindings.variables.contains_key(&parameter) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    let mut var_keyword_arguments = TypeUnion::new();

                    for (key, argument) in &self.keyword {
                        if !parameters.iter().any(|p| p.name == *key) {
                            var_keyword_arguments.add_type(argument.clone());
                        }
                    }

                    let str_literal = Arc::new(Type::new_literal(TypeLiteral::String(
                        LiteralString::from_str("str"),
                    )));

                    let arguments = if var_keyword_arguments.is_empty() {
                        imbl::vector![str_literal, Arc::new(Type::Never)]
                    } else {
                        imbl::vector![str_literal, var_keyword_arguments.simplify()]
                    };

                    let ty = Arc::new(Type::Instance(
                        TypeInstance::builtins("dict").with_arguments(arguments),
                    ));

                    bindings
                        .variables
                        .insert(parameter.clone(), Sourced::inferred(ty));
                }
            }
        }

        if positional_iter.next().is_some() {
            return Err(BindError::TooManyPositionalArguments);
        }

        if self.keyword.keys().any(|key| {
            !bindings
                .variables
                .keys()
                .any(|variable| &variable.name == key)
        }) {
            return Err(BindError::UnexpectedKeywordArgument);
        }

        Ok(bindings)
    }
}
