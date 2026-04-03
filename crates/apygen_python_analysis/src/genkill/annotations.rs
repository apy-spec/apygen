use crate::abstract_environment::{
    AbstractEnvironment, Attribute, Identifier, LiteralBigInteger, LiteralInteger, LocalAttribute,
    QualifiedName, Type, TypeLiteral,
};
use crate::analysis::cfg::nodes::{Expr, ExprSubscript, ExprUnaryOp, UnaryOp};
use crate::analysis::namespace::{Location, NamespacesContext};
use crate::genkill::literals::{
    gen_expr_boolean_literal, gen_expr_bytes_literal, gen_expr_ellipsis_literal,
    gen_expr_none_literal, gen_expr_number_literal, gen_expr_string_literal,
};
use crate::genkill::{ToQualifiedName, ToQualifiedNameError};
use std::sync::Arc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum GetAttributeError {
    #[error("the environment location `{0:?}` does not exist")]
    LocationNotFound(Location<QualifiedName>),
    #[error("the name `{0:?}` does not exist")]
    NameNotFound(Identifier),
    #[error("the attribute `{0:?}` does not exist")]
    AttributeNotFound(Identifier),
    #[error("the identifier `{0:?}` is not a namespace")]
    IsNotNamespace(Identifier),
}

fn get_name<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &Identifier,
) -> Result<&'a Arc<Attribute>, GetAttributeError> {
    let abstract_environment = context
        .get_abstract_environment(location)
        .ok_or_else(|| GetAttributeError::LocationNotFound(location.to_owned()))?;

    abstract_environment
        .attributes
        .get(name)
        .ok_or_else(|| GetAttributeError::NameNotFound(name.to_owned()))
}

pub fn resolve_attribute<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    attribute: &'a Attribute,
) -> Result<&'a LocalAttribute, GetAttributeError> {
    match attribute {
        Attribute::Local(local_attribute) => Ok(local_attribute),
        Attribute::Imported(imported_attribute) => resolve_attribute(
            context,
            get_name(
                context,
                &Location::from(imported_attribute.module.clone()),
                &imported_attribute.name,
            )?,
        ),
    }
}

fn get_attribute<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    identifiers: &[Identifier],
) -> Result<&'a LocalAttribute, GetAttributeError> {
    let (identifier, attribute_identifiers) = identifiers
        .split_first()
        .expect("identifiers should not be empty");

    let name = get_name(context, location, identifier)?;

    let local_attribute = resolve_attribute(context, name)?;

    if attribute_identifiers.is_empty() {
        return Ok(local_attribute);
    };

    let Type::Literal(literal_value) = local_attribute.attribute_type.as_ref() else {
        return Err(GetAttributeError::IsNotNamespace(identifier.to_owned()));
    };

    let result = match literal_value.as_ref() {
        TypeLiteral::Class(class_type) => {
            get_attribute(context, &class_type.value.location, attribute_identifiers)
        }
        TypeLiteral::ImportedModule(module_reference_type) => get_attribute(
            context,
            &Location::from(module_reference_type.value.module.clone()),
            attribute_identifiers,
        ),
        _ => Err(GetAttributeError::IsNotNamespace(identifier.to_owned())),
    };

    match result {
        Err(GetAttributeError::NameNotFound(name)) => {
            Err(GetAttributeError::AttributeNotFound(name))
        }
        result => result,
    }
}

pub fn get_type<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &QualifiedName,
) -> Result<&'a Type, GetAttributeError> {
    Ok(&get_attribute(context, location, &name.identifiers)?.attribute_type)
}

pub fn as_local_attribute(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    attribute: &Attribute,
) -> LocalAttribute {
    match attribute {
        Attribute::Local(local_attribute) => local_attribute.clone(),
        Attribute::Imported(imported_attribute) => match get_name(
            context,
            &Location::from(imported_attribute.module.clone()),
            &imported_attribute.name,
        ) {
            Ok(name) => {
                let mut result = as_local_attribute(context, name);
                result.visibility = imported_attribute.visibility.clone();
                result.is_deprecated = imported_attribute.is_deprecated;
                result
            }
            Err(_) => LocalAttribute::unknown(),
        },
    }
}

#[derive(Error, Debug)]
pub enum GenAnnotationError {
    #[error("an error occurred while finding an attribute : `{0:?}`")]
    Find(#[from] GetAttributeError),
    #[error(
        "an error occurred while converting some part of the expression to a qualified name : `{0:?}`"
    )]
    InvalidQualifiedName(#[from] ToQualifiedNameError),
    #[error("the expression is not valid annotation because {reason}")]
    InvalidAnnotation { reason: String },
}

pub fn gen_expr_qualified_name(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    qualified_name: QualifiedName,
) -> Result<Type, GenAnnotationError> {
    let attribute_type = get_type(context, location, &qualified_name)?;

    let Type::Literal(literal_value) = attribute_type else {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a literal".to_owned(),
        });
    };

    let origin = match literal_value.as_ref() {
        TypeLiteral::Class(class_type) => class_type.value.location.clone(),
        TypeLiteral::TypeAlias(type_alias_type) => type_alias_type.value.location.clone(),
        TypeLiteral::Generic(generic_type) => generic_type.value.location.clone(),
        _ => {
            return Err(GenAnnotationError::InvalidAnnotation {
                reason: "The base is not a type".to_owned(),
            });
        }
    };

    Ok(Type::new_reference(qualified_name, origin))
}

pub fn gen_expr_subscript(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    expression: &ExprSubscript,
) -> Result<Type, GenAnnotationError> {
    let Type::Reference {
        name,
        mut arguments,
        origin,
    } = gen_annotation(context, location, expression.value.as_ref())?
    else {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a reference".to_owned(),
        });
    };

    let slice = expression.slice.as_ref();

    match slice {
        Expr::EllipsisLiteral(_) => arguments.push_back(Arc::new(gen_expr_ellipsis_literal())),
        Expr::Tuple(expr_tuple) => {
            for tuple_expression in &expr_tuple.elts {
                arguments.push_back(Arc::new(match tuple_expression {
                    Expr::EllipsisLiteral(_) => gen_expr_ellipsis_literal(),
                    _ => gen_annotation(context, location, tuple_expression)?,
                }));
            }
        }
        _ => arguments.push_back(Arc::new(gen_annotation(context, location, slice)?)),
    };

    Ok(Type::Reference {
        name,
        arguments,
        origin,
    })
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
        TypeLiteral::Integer(LiteralInteger { value }) => {
            Ok(Type::new_literal(TypeLiteral::Integer(LiteralInteger {
                value: -value,
            })))
        }
        TypeLiteral::BigInteger(LiteralBigInteger { positive, value }) => Ok(Type::new_literal(
            TypeLiteral::BigInteger(LiteralBigInteger {
                positive: !positive,
                value: value.clone(),
            }),
        )),
        _ => unreachable!("gen_expr_number_literal always returns a number literal"),
    }
}

pub fn gen_annotation(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
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
        _ => {
            return Err(GenAnnotationError::InvalidAnnotation {
                reason: "The expression is not a valid annotation".to_owned(),
            });
        }
    })
}
