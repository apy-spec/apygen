use crate::abstract_environment::{
    AbstractEnvironment, GetAttributeError, LocalAttribute, QualifiedName, TYPING_MODULE, Type,
    TypeInstance, TypeLiteral, TypeUnion, resolve_local_attribute,
};
use crate::analysis::cfg::nodes::{Expr, ExprSubscript, ExprUnaryOp, UnaryOp};
use crate::analysis::namespace::{Location, Namespaces};
use crate::genkill::literals::{
    gen_expr_boolean_literal, gen_expr_bytes_literal, gen_expr_ellipsis_literal,
    gen_expr_none_literal, gen_expr_number_literal, gen_expr_string_literal,
};
use crate::genkill::{ToQualifiedName, ToQualifiedNameError};
use apy::v1::Identifier;
use apygen_analysis::cfg::nodes::{ExprBinOp, Operator};
use std::sync::Arc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum GenAnnotationError {
    #[error("failed to resolve attribute: {0}")]
    FailedToResolveAttribute(#[from] GetAttributeError),
    #[error("the identifier `{0:?}` is not a namespace")]
    IsNotNamespace(Identifier),
    #[error(
        "an error occurred while converting some part of the expression to a qualified name : `{0:?}`"
    )]
    InvalidQualifiedName(#[from] ToQualifiedNameError),
    #[error("the expression is not valid annotation because {reason}")]
    InvalidAnnotation { reason: String },
}

fn get_type_attribute<'a>(
    context: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    identifiers: &'a [Identifier],
) -> Result<(Location<QualifiedName>, &'a Identifier, &'a LocalAttribute), GenAnnotationError> {
    let (attribute_identifier, attribute_identifiers) = identifiers
        .split_first()
        .expect("identifiers should not be empty");

    let (origin, identifier, local_attribute) =
        resolve_local_attribute(context, location.clone(), attribute_identifier)?;

    if attribute_identifiers.is_empty() {
        return Ok((origin, identifier, local_attribute));
    };

    let Type::Literal(literal_value) = local_attribute.attribute_type.data.as_ref() else {
        return Err(GenAnnotationError::IsNotNamespace(identifier.to_owned()));
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
        _ => Err(GenAnnotationError::IsNotNamespace(identifier.to_owned())),
    }
}

pub fn gen_expr_qualified_name(
    context: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    qualified_name: QualifiedName,
) -> Result<Type, GenAnnotationError> {
    let (origin, name, local_attribute) =
        get_type_attribute(context, location, &qualified_name.identifiers)?;

    let Type::Literal(literal_value) = local_attribute.attribute_type.data.as_ref() else {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a literal".to_owned(),
        });
    };

    if !matches!(
        literal_value.as_ref(),
        TypeLiteral::Class(_) | TypeLiteral::TypeAlias(_) | TypeLiteral::Generic(_)
    ) {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a type".to_owned(),
        });
    };

    if origin.namespace_location.module.identifiers.first() != TYPING_MODULE
        || !origin.namespace_location.program_points.is_empty()
    {
        return Ok(Type::Instance(TypeInstance::new(origin, name.clone())));
    }

    match name.as_ref() {
        "Any" => Ok(Type::Any),
        _ => Ok(Type::Instance(TypeInstance::new(origin, name.clone()))),
    }
}

pub fn gen_expr_subscript(
    context: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    expression: &ExprSubscript,
) -> Result<Type, GenAnnotationError> {
    let Type::Instance(mut type_instance) =
        gen_annotation(context, location, expression.value.as_ref())?
    else {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a reference".to_owned(),
        });
    };

    let slice = expression.slice.as_ref();

    match slice {
        Expr::EllipsisLiteral(_) => type_instance
            .arguments
            .push_back(Arc::new(gen_expr_ellipsis_literal())),
        Expr::Tuple(expr_tuple) => {
            for tuple_expression in &expr_tuple.elts {
                type_instance
                    .arguments
                    .push_back(Arc::new(match tuple_expression {
                        Expr::EllipsisLiteral(_) => gen_expr_ellipsis_literal(),
                        _ => gen_annotation(context, location, tuple_expression)?,
                    }));
            }
        }
        _ => type_instance
            .arguments
            .push_back(Arc::new(gen_annotation(context, location, slice)?)),
    };

    Ok(Type::Instance(type_instance))
}

pub fn gen_expr_unary_op(expression: &ExprUnaryOp) -> Result<Type, GenAnnotationError> {
    if !matches!(expression.op, UnaryOp::USub) {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The unary operator is not a negation".to_owned(),
        });
    }

    let number_literal = match expression.operand.as_ref() {
        Expr::NumberLiteral(expr_number_literal) => {
            let Type::Literal(number_literal) = gen_expr_number_literal(&expr_number_literal)
            else {
                unreachable!("gen_expr_number_literal always returns a literal type")
            };
            number_literal
        }
        _ => {
            return Err(GenAnnotationError::InvalidAnnotation {
                reason: "The operand is not a number literal".to_owned(),
            });
        }
    };

    match number_literal.as_ref() {
        TypeLiteral::Integer(literal_integer) => {
            Ok(Type::new_literal(TypeLiteral::Integer(-literal_integer)))
        }
        _ => unreachable!("gen_expr_number_literal always returns a number literal"),
    }
}

pub fn gen_expr_bin_op(
    context: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    expression: &ExprBinOp,
) -> Result<Type, GenAnnotationError> {
    if !matches!(expression.op, Operator::BitOr) {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The binary operator is not a binary or".to_owned(),
        });
    }

    let left_expression = gen_annotation(context, location, expression.left.as_ref())?;
    let right_expression = gen_annotation(context, location, expression.right.as_ref())?;

    let mut ty = TypeUnion::new();
    ty.add_type(Arc::new(left_expression));
    ty.add_type(Arc::new(right_expression));

    Ok(ty.simplify().as_ref().clone())
}

pub fn gen_annotation(
    context: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    expression: &Expr,
) -> Result<Type, GenAnnotationError> {
    Ok(match expression {
        Expr::StringLiteral(expr_string_literal) => gen_expr_string_literal(expr_string_literal),
        Expr::BytesLiteral(expr_bytes_literal) => gen_expr_bytes_literal(expr_bytes_literal),
        Expr::NumberLiteral(expr_number_literal) => gen_expr_number_literal(expr_number_literal),
        Expr::BooleanLiteral(expr_boolean_literal) => {
            gen_expr_boolean_literal(expr_boolean_literal)
        }
        Expr::NoneLiteral(_) => gen_expr_none_literal(),
        Expr::Attribute(expr_attribute) => {
            gen_expr_qualified_name(context, location, expr_attribute.to_qualified_name()?)?
        }
        Expr::Name(expr_name) => {
            gen_expr_qualified_name(context, location, expr_name.to_qualified_name()?)?
        }
        Expr::Subscript(expr_subscript) => gen_expr_subscript(context, location, expr_subscript)?,
        Expr::UnaryOp(expr_unary_op) => gen_expr_unary_op(expr_unary_op)?,
        Expr::BinOp(expr_binary_op) => gen_expr_bin_op(context, location, expr_binary_op)?,
        _ => {
            return Err(GenAnnotationError::InvalidAnnotation {
                reason: "The expression is not a valid annotation".to_owned(),
            });
        }
    })
}
