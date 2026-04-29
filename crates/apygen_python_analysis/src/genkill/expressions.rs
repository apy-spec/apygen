pub mod literal_boolean;
pub mod literal_bytes;
pub mod literal_complex;
pub mod literal_ellipsis;
pub mod literal_float;
pub mod literal_integer;
pub mod literal_none;
pub mod literal_string;
pub mod type_literal;

use crate::abstract_environment::{AbstractEnvironment, Exception, LiteralList, LiteralTuple, Type, TypeLiteral, TypeReference, TypeUnion, resolve_local_attribute, Parameter, LiteralString};
use crate::analysis::cfg::nodes;
use crate::analysis::namespace::{Location, NamespacesContext};
use crate::genkill::expressions::type_literal::{as_boolean, call_binary_op, call_unary_op};
use crate::genkill::literals::{
    gen_expr_boolean_literal, gen_expr_bytes_literal, gen_expr_ellipsis_literal,
    gen_expr_none_literal, gen_expr_number_literal, gen_expr_string_literal,
};
use apy::v1::{Identifier, ParameterKind, QualifiedName};
use apygen_analysis::cfg::nodes::{Expr, ExprBinOp, ExprBoolOp, ExprName, ExprUnaryOp};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use thiserror::Error;

pub struct GenExprResult<T> {
    pub value: T,
    pub exceptions: BTreeSet<Exception>,
    pub pure: bool,
    pub partial: bool,
}

impl<T> GenExprResult<T> {
    pub fn new_total_pure_non_raising(value: T) -> Self {
        GenExprResult {
            value,
            exceptions: BTreeSet::new(),
            pure: true,
            partial: false,
        }
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> GenExprResult<U> {
        GenExprResult {
            value: f(self.value),
            exceptions: self.exceptions,
            pure: self.pure,
            partial: self.partial,
        }
    }
}

impl GenExprResult<Type> {
    pub fn raise(exception: Exception) -> Self {
        GenExprResult {
            value: Type::NoReturn,
            exceptions: BTreeSet::from_iter([exception]),
            pure: false,
            partial: false,
        }
    }

    pub fn unknown() -> Self {
        GenExprResult {
            value: Type::Any,
            exceptions: BTreeSet::from_iter([Exception::from_type(Type::Any)]),
            pure: false,
            partial: true,
        }
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

pub fn gen_bool_value(ty: &Type) -> Option<bool> {
    match ty {
        Type::Any => None,
        Type::Never => None,
        Type::NoReturn => None,
        Type::Reference { .. } => None,
        Type::Union(_) => None,
        Type::Intersection(_) => None,
        Type::Literal(literal_value) => as_boolean(literal_value.as_ref()),
    }
}

pub fn gen_expr_collection(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expressions: &Vec<nodes::Expr>,
) -> GenExprResult<impl IntoIterator<Item = Type>> {
    let mut result = GenExprResult::new_total_pure_non_raising(Vec::new());

    for expression in expressions {
        let expression_result = gen_expr(context, environment_location, expression);
        result.value.push(expression_result.value);
        result.exceptions.extend(expression_result.exceptions);
        result.pure &= result.pure;
        result.partial |= result.partial;
    }

    result
}

pub fn gen_expr_list(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_list: &nodes::ExprList,
) -> GenExprResult<Type> {
    // SOUNDNESS: A list can either be literal (if all its elements are literals)
    //            or non-literal (if any of its element is non-literal).
    //            Its creation can be non-pure, partial or raise exceptions
    //            if any of its elements is non-pure, partial or can raise exceptions respectively.
    gen_expr_collection(context, environment_location, &expr_list.elts).map(|list_types_iterator| {
        let mut literal_values: imbl::Vector<Arc<TypeLiteral>> = imbl::Vector::new();
        let mut non_literal_types: Vec<Arc<Type>> = Vec::new();

        for list_type in list_types_iterator {
            match list_type {
                Type::Literal(literal_value) => literal_values.push_back(literal_value),
                non_literal_type => non_literal_types.push(Arc::new(non_literal_type)),
            };
        }

        let value = if non_literal_types.is_empty() {
            Type::new_literal(TypeLiteral::List(LiteralList {
                value: literal_values,
            }))
        } else {
            Type::Reference(TypeReference::builtins_list(Arc::new(Type::new_union(
                literal_values
                    .into_iter()
                    .map(|literal_value| Arc::new(Type::Literal(literal_value)))
                    .chain(non_literal_types.into_iter()),
            ))))
        };

        value
    })
}

pub fn gen_expr_set(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_set: &nodes::ExprSet,
) -> GenExprResult<Type> {
    // SOUNDNESS: A set can either be literal (if all its elements are literals)
    //            or non-literal (if any of its element is non-literal).
    //            Its creation can be non-pure, partial or raise exceptions
    //            if any of its elements is non-pure, partial or can raise exceptions respectively.
    gen_expr_collection(context, environment_location, &expr_set.elts).map(|set_types_iterator| {
        let mut literal_values: imbl::Vector<Arc<TypeLiteral>> = imbl::Vector::new();
        let mut non_literal_types: Vec<Arc<Type>> = Vec::new();

        for list_type in set_types_iterator {
            match list_type {
                Type::Literal(literal_value) => literal_values.push_back(literal_value),
                non_literal_type => non_literal_types.push(Arc::new(non_literal_type)),
            };
        }

        let value = if non_literal_types.is_empty() {
            Type::new_literal(TypeLiteral::List(LiteralList {
                value: literal_values,
            }))
        } else {
            Type::Reference(TypeReference::builtins_list(Arc::new(Type::new_union(
                literal_values
                    .into_iter()
                    .map(|literal_value| Arc::new(Type::Literal(literal_value)))
                    .chain(non_literal_types.into_iter()),
            ))))
        };

        value
    })
}

pub fn gen_expr_tuple(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_tuple: &nodes::ExprTuple,
) -> GenExprResult<Type> {
    // SOUNDNESS: A tuple can either be literal (if all its elements are literals)
    //            or non-literal (if any of its element is non-literal).
    //            Its creation can be non-pure, partial or raise exceptions
    //            if any of its elements is non-pure, partial or can raise exceptions respectively.
    gen_expr_collection(context, environment_location, &expr_tuple.elts).map(
        |tuple_types_iterator| {
            let tuple_types: Vec<Type> = tuple_types_iterator.into_iter().collect();

            let value = if tuple_types.iter().all(|ty| matches!(ty, Type::Literal(_))) {
                let tuple_values = tuple_types
                    .into_iter()
                    .map(|ty| match ty {
                        Type::Literal(literal_value) => literal_value,
                        _ => unreachable!("The if condition ensures that all types are literals"),
                    })
                    .collect();
                Type::new_literal(TypeLiteral::Tuple(LiteralTuple {
                    value: tuple_values,
                }))
            } else {
                Type::Reference(TypeReference::builtins_tuple(
                    tuple_types.into_iter().map(|ty| Arc::new(ty)),
                ))
            };

            value
        },
    )
}

pub fn gen_name(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_name: &ExprName,
) -> GenExprResult<Type> {
    let Ok(identifier) = Identifier::try_parse(expr_name.id.as_ref()) else {
        return GenExprResult::unknown();
    };

    match resolve_local_attribute(context, environment_location, &identifier) {
        Ok(local_attribute) => GenExprResult::new_total_pure_non_raising(
            local_attribute.attribute_type.as_ref().clone(),
        ),
        Err(_) => GenExprResult::unknown(),
    }
}

pub fn gen_bool_op(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_bool_op: &ExprBoolOp,
) -> GenExprResult<Type> {
    let mut expr_iter = expr_bool_op
        .values
        .iter()
        .map(|expr| gen_expr(context, environment_location, expr));

    let mut result = expr_iter
        .next()
        .expect("A boolean operation must have at least one operand");

    for expr_result in expr_iter {
        if let Some(bool) = gen_bool_value(&result.value) {
            if (expr_bool_op.op == nodes::BoolOp::And && !bool)
                || (expr_bool_op.op == nodes::BoolOp::Or && bool)
            {
                break;
            }
            result = expr_result;
        } else {
            let mut type_union = TypeUnion::new();
            type_union.add_type(Arc::new(result.value));
            type_union.add_type(Arc::new(expr_result.value));

            result.value = type_union.simplify().as_ref().clone();
            result.exceptions.extend(expr_result.exceptions);
            result.pure &= expr_result.pure;
            result.partial |= expr_result.partial;
        }
    }

    result
}

pub fn gen_bin_op(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_bin_op: &ExprBinOp,
) -> GenExprResult<Type> {
    let left_result = gen_expr(context, environment_location, &expr_bin_op.left);
    let right_result = gen_expr(context, environment_location, &expr_bin_op.right);

    match (left_result.value, right_result.value) {
        (Type::Literal(left), Type::Literal(right)) => call_binary_op(
            context,
            environment_location,
            left.as_ref(),
            expr_bin_op.op,
            right.as_ref(),
        ),
        _ => GenExprResult::unknown(),
    }
}

pub fn gen_unary_op(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expr_unary_op: &ExprUnaryOp,
) -> GenExprResult<Type> {
    gen_expr(context, environment_location, &expr_unary_op.operand).map(|ty| match ty {
        Type::Any => Type::Any,
        Type::Never => Type::Never,
        Type::NoReturn => Type::NoReturn,
        Type::Reference { .. } => Type::Any,
        Type::Union(_) => Type::Any,
        Type::Intersection(_) => Type::Any,
        Type::Literal(type_literal) => call_unary_op(type_literal.as_ref(), expr_unary_op.op).value,
    })
}

pub fn gen_expr(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    expression: &nodes::Expr,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match expression {
        Expr::BoolOp(expr_bool_op) => {
            return gen_bool_op(context, environment_location, expr_bool_op);
        }
        Expr::Named(_) => return GenExprResult::unknown(),
        Expr::BinOp(expr_bin_op) => return gen_bin_op(context, environment_location, expr_bin_op),
        Expr::UnaryOp(expr_unary_op) => {
            return gen_unary_op(context, environment_location, expr_unary_op);
        }
        Expr::Lambda(_) => return GenExprResult::unknown(),
        Expr::If(_) => return GenExprResult::unknown(),
        Expr::Dict(_) => return GenExprResult::unknown(),
        Expr::Set(expr_set) => return gen_expr_set(context, environment_location, expr_set),
        Expr::ListComp(_) => return GenExprResult::unknown(),
        Expr::SetComp(_) => return GenExprResult::unknown(),
        Expr::DictComp(_) => return GenExprResult::unknown(),
        Expr::Generator(_) => return GenExprResult::unknown(),
        Expr::Await(_) => return GenExprResult::unknown(),
        Expr::Yield(_) => return GenExprResult::unknown(),
        Expr::YieldFrom(_) => return GenExprResult::unknown(),
        Expr::Compare(_) => return GenExprResult::unknown(),
        Expr::Call(_) => return GenExprResult::unknown(),
        Expr::FString(_) => return GenExprResult::unknown(),
        Expr::StringLiteral(expr_string_literal) => gen_expr_string_literal(expr_string_literal),
        Expr::BytesLiteral(expr_bytes_literal) => gen_expr_bytes_literal(expr_bytes_literal),
        Expr::NumberLiteral(expr_number_literal) => gen_expr_number_literal(expr_number_literal),
        Expr::BooleanLiteral(expr_boolean_literal) => {
            gen_expr_boolean_literal(expr_boolean_literal)
        }
        Expr::NoneLiteral(_) => gen_expr_none_literal(),
        Expr::EllipsisLiteral(_) => gen_expr_ellipsis_literal(),
        Expr::Attribute(_) => return GenExprResult::unknown(),
        Expr::Subscript(_) => return GenExprResult::unknown(),
        Expr::Starred(_) => return GenExprResult::unknown(),
        Expr::Name(expr_name) => return gen_name(context, environment_location, expr_name),
        Expr::List(expr_list) => {
            return gen_expr_list(context, environment_location, expr_list);
        }
        Expr::Tuple(expr_tuple) => {
            return gen_expr_tuple(context, environment_location, expr_tuple);
        }
        Expr::Slice(_) => return GenExprResult::unknown(),
        Expr::IpyEscapeCommand(_) => return GenExprResult::unknown(),
    })
}
