use crate::abstract_environment::{
    LiteralString, LiteralTuple, Parameter, Type, TypeLiteral, TypeReference, TypeUnion,
};
use crate::genkill::expressions::GenExprResult;
use apy::OneOrMany;
use apy::v1::{Identifier, ParameterKind, QualifiedName};
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

pub mod literal_big_integer;
pub mod literal_boolean;
pub mod literal_bytes;
pub mod literal_complex;
pub mod literal_ellipsis;
pub mod literal_float;
pub mod literal_integer;
pub mod literal_none;
pub mod literal_string;
pub mod type_literal;

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
    pub keyword: HashMap<Identifier, Arc<Type>>,
}

impl Arguments {
    pub fn bind<'a>(
        &self,
        method: bool,
        parameters: &'a Vec<Parameter>,
    ) -> Result<HashMap<&'a Identifier, Arc<Type>>, BindError> {
        let mut bindings: HashMap<&Identifier, Arc<Type>> = HashMap::new();
        let mut positional_iter = self.positional.iter().cloned();
        let mut skip = method;
        for parameter in parameters {
            if skip {
                if self.positional.is_empty() {
                    return Err(BindError::MissingPositionalArgument);
                }
                skip = false;
                continue;
            }
            match parameter.kind {
                ParameterKind::PositionalOnly => {
                    if let Some(argument) = positional_iter.next() {
                        bindings.insert(&parameter.name, argument);
                    } else {
                        return Err(BindError::MissingPositionalArgument);
                    }
                }
                ParameterKind::PositionalOrKeyword => {
                    if let Some(argument) = positional_iter.next() {
                        bindings.insert(&parameter.name, argument.clone());
                    } else if let Some(argument) = self.keyword.get(&parameter.name) {
                        bindings.insert(&parameter.name, argument.clone());
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

                    let ty = Arc::new(Type::Reference(
                        TypeReference::builtins("tuple").with_arguments(arguments),
                    ));

                    bindings.insert(&parameter.name, ty);
                }
                ParameterKind::KeywordOnly => {
                    if bindings.contains_key(&parameter.name) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    if let Some(argument) = self.keyword.get(&parameter.name) {
                        bindings.insert(&parameter.name, argument.clone());
                    } else {
                        return Err(BindError::MissingKeywordArgument);
                    }
                }
                ParameterKind::VarKeyword => {
                    if bindings.contains_key(&parameter.name) {
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

                    let ty = Arc::new(Type::Reference(
                        TypeReference::builtins("dict").with_arguments(arguments),
                    ));

                    bindings.insert(&parameter.name, ty);
                }
            }
        }

        if positional_iter.next().is_some() {
            return Err(BindError::TooManyPositionalArguments);
        }

        if self.keyword.keys().any(|key| !bindings.contains_key(key)) {
            return Err(BindError::UnexpectedKeywordArgument);
        }

        Ok(bindings)
    }
}
