use crate::analysis::fmt::{fmt_display_iterator, fmt_iterator};
use crate::analysis::lattice::Join;
use crate::constraint_graph::expressions::{Parameter, ParameterKind, SmolStr};
use crate::inference::{LiteralTuple, Sourced, Type, TypeLiteral};
use crate::primitives::literals::LiteralStr;
use imbl;
use std::collections::BTreeMap;
use std::fmt::Display;
use std::sync::Arc;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BoundArguments {
    pub variables: BTreeMap<Parameter, Sourced<Type>>,
}

impl BoundArguments {
    pub fn new() -> Self {
        Self::default()
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Arguments {
    pub positional: Vec<Type>,
    pub keyword: BTreeMap<SmolStr, Type>,
}

impl Arguments {
    pub fn new() -> Self {
        Self {
            positional: Vec::new(),
            keyword: BTreeMap::new(),
        }
    }

    pub fn with_self(mut self, self_type: Type) -> Self {
        self.positional.insert(0, self_type);
        self
    }

    pub fn add_positional_argument(mut self, argument: Type) -> Self {
        self.positional.push(argument);
        self
    }

    pub fn add_keyword_argument(mut self, identifier: SmolStr, argument: Type) -> Self {
        self.keyword.insert(identifier, argument);
        self
    }

    pub fn bind(&self, parameters: Vec<Parameter>) -> Result<BoundArguments, BindError> {
        let mut bindings = BoundArguments::new();
        let mut positional_iter = self.positional.iter().cloned();
        for parameter in &parameters {
            match parameter.kind {
                ParameterKind::PositionalOnly => {
                    if let Some(argument) = positional_iter.next() {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument));
                    } else if !parameter.is_optional {
                        return Err(BindError::MissingPositionalArgument);
                    }
                }
                ParameterKind::PositionalOrKeyword => {
                    if let Some(argument) = positional_iter.next() {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if let Some(argument) = self.keyword.get(parameter.name.name()) {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if !parameter.is_optional {
                        return Err(BindError::MissingPositionalOrKeywordArgument);
                    }
                }
                ParameterKind::VarPositional => {
                    let arguments = if self.positional.is_empty() {
                        imbl::vector![Arc::new(Type::Literal(Arc::new(TypeLiteral::Tuple(
                            LiteralTuple {
                                value: imbl::Vector::new()
                            }
                        ))))]
                    } else {
                        let mut var_positional_arguments = Type::Never;

                        while let Some(argument) = positional_iter.next() {
                            var_positional_arguments = var_positional_arguments.join(&argument);
                        }

                        imbl::vector![Arc::new(var_positional_arguments)]
                    };

                    let ty = Type::Any; // TODO: fix

                    bindings
                        .variables
                        .insert(parameter.clone(), Sourced::inferred(ty));
                }
                ParameterKind::KeywordOnly => {
                    if bindings.variables.contains_key(&parameter) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    if let Some(argument) = self.keyword.get(parameter.name.name()) {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if !parameter.is_optional {
                        return Err(BindError::MissingKeywordArgument);
                    }
                }
                ParameterKind::VarKeyword => {
                    if bindings.variables.contains_key(&parameter) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    let mut var_keyword_arguments = Type::Never;

                    for (key, argument) in &self.keyword {
                        if !parameters.iter().any(|p| p.name.name() == key) {
                            var_keyword_arguments = var_keyword_arguments.join(argument);
                        }
                    }

                    let str_literal = Arc::new(Type::new_literal(TypeLiteral::String(
                        LiteralStr::from("str"),
                    )));

                    let arguments = imbl::vector![str_literal, Arc::new(var_keyword_arguments)];

                    let ty = Type::Any; // TODO: fix

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
                .any(|variable| variable.name.name() == key)
        }) {
            return Err(BindError::UnexpectedKeywordArgument);
        }

        Ok(bindings)
    }
}

impl Display for Arguments {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_display_iterator(f, self.positional.iter(), ", ")?;
        if !self.keyword.is_empty() {
            fmt_iterator(f, self.keyword.iter(), ", ", |f, (identifier, ty)| {
                write!(f, "{}={}", identifier, ty)
            })?;
        }
        Ok(())
    }
}
