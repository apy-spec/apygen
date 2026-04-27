use crate::abstract_environment::{
    AbstractEnvironment, Attribute, BUILTINS_MODULE, GetAttributeError, LiteralBigInteger,
    LiteralInteger, LocalAttribute, QualifiedName, TYPING_MODULE, Type, TypeLiteral, TypeReference,
    TypeUnion,
};
use crate::analysis::cfg::nodes::{Expr, ExprSubscript, ExprUnaryOp, UnaryOp};
use crate::analysis::namespace::{Location, NamespacesContext};
use crate::genkill::literals::{
    gen_expr_boolean_literal, gen_expr_bytes_literal, gen_expr_ellipsis_literal,
    gen_expr_none_literal, gen_expr_number_literal, gen_expr_string_literal,
};
use crate::genkill::{ToQualifiedName, ToQualifiedNameError};
use apy::OneOrMany;
use apy::v1::Identifier;
use apygen_analysis::cfg::nodes::{ExprBinOp, Operator};
use apygen_analysis::namespace::NamespaceLocation;
use std::sync::Arc;
use thiserror::Error;

pub fn get_attribute_with_module<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    name: &Identifier,
) -> Result<(&'a Attribute, Arc<QualifiedName>), GetAttributeError> {
    let Some(abstract_environment) = context.get_abstract_environment(location) else {
        return Err(GetAttributeError::LocationNotFound(location.clone()));
    };

    if let Some(attribute) = abstract_environment.attributes.get(name) {
        return Ok((attribute, location.namespace_location.module.clone()));
    };

    let builtins_name = Arc::new(QualifiedName::parse(BUILTINS_MODULE));
    let builtins_namespace_location = NamespaceLocation::new(builtins_name.clone());

    if location.namespace_location != builtins_namespace_location {
        let Some(builtins_abstract_environment) =
            context.get_abstract_environment(&Location::at_exit(builtins_namespace_location))
        else {
            return Err(GetAttributeError::LocationNotFound(location.clone()));
        };

        if let Some(builtins_attribute) = builtins_abstract_environment.attributes.get(name) {
            return Ok((builtins_attribute, builtins_name.clone()));
        };
    }

    Err(GetAttributeError::AttributeNotFound {
        location: location.clone(),
        identifier: name.clone(),
    })
}

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

fn resolve_with_module<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    identifier: &Identifier,
) -> Result<(&'a LocalAttribute, Arc<QualifiedName>), GenAnnotationError> {
    match get_attribute_with_module(context, location, identifier)? {
        (Attribute::Local(local_attribute), module) => Ok((local_attribute, module)),
        (Attribute::Imported(imported_attribute), _) => resolve_with_module(
            context,
            &Location::from(imported_attribute.module.clone()),
            &imported_attribute.name,
        ),
    }
}

fn get_type_attribute<'a>(
    context: &'a impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    identifiers: &[Identifier],
) -> Result<(&'a LocalAttribute, Arc<QualifiedName>, QualifiedName), GenAnnotationError> {
    let (identifier, attribute_identifiers) = identifiers
        .split_first()
        .expect("identifiers should not be empty");

    let (local_attribute, module) = resolve_with_module(context, location, identifier)?;

    if attribute_identifiers.is_empty() {
        return Ok((
            local_attribute,
            module,
            QualifiedName {
                identifiers: OneOrMany::one(identifier.clone()),
            },
        ));
    };

    let Type::Literal(literal_value) = local_attribute.attribute_type.as_ref() else {
        return Err(GenAnnotationError::IsNotNamespace(identifier.to_owned()));
    };

    match literal_value.as_ref() {
        TypeLiteral::Class(class_type) => {
            let (class_local_attribute, class_module, class_name) =
                get_type_attribute(context, &class_type.value.location, attribute_identifiers)?;

            let name = if module != class_module {
                class_name
            } else {
                let mut name = QualifiedName {
                    identifiers: OneOrMany::one(identifier.clone()),
                };
                name.identifiers.extend(class_name.identifiers);
                name
            };

            Ok((class_local_attribute, class_module, name))
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
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    qualified_name: QualifiedName,
) -> Result<Type, GenAnnotationError> {
    let (local_attribute, module, name) =
        get_type_attribute(context, location, &qualified_name.identifiers)?;

    let Type::Literal(literal_value) = local_attribute.attribute_type.as_ref() else {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a literal".to_owned(),
        });
    };

    let origin = match literal_value.as_ref() {
        TypeLiteral::Class(class_type) => class_type.value.location.program_point,
        TypeLiteral::TypeAlias(type_alias_type) => type_alias_type.value.location.program_point,
        TypeLiteral::Generic(generic_type) => generic_type.value.location.program_point,
        _ => {
            return Err(GenAnnotationError::InvalidAnnotation {
                reason: "The base is not a type".to_owned(),
            });
        }
    };

    if module.join() != TYPING_MODULE || name.identifiers.len() != 1 {
        return Ok(Type::Reference(
            TypeReference::new(module, name).with_origin(origin),
        ));
    }

    match name.identifiers.first().as_ref() {
        "Any" => Ok(Type::Any),
        _ => Ok(Type::Reference(
            TypeReference::new(module, name).with_origin(origin),
        )),
    }
}

pub fn gen_expr_subscript(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: &Location<QualifiedName>,
    expression: &ExprSubscript,
) -> Result<Type, GenAnnotationError> {
    let Type::Reference(mut type_reference) =
        gen_annotation(context, location, expression.value.as_ref())?
    else {
        return Err(GenAnnotationError::InvalidAnnotation {
            reason: "The base is not a reference".to_owned(),
        });
    };

    let slice = expression.slice.as_ref();

    match slice {
        Expr::EllipsisLiteral(_) => type_reference
            .arguments
            .push_back(Arc::new(gen_expr_ellipsis_literal())),
        Expr::Tuple(expr_tuple) => {
            for tuple_expression in &expr_tuple.elts {
                type_reference
                    .arguments
                    .push_back(Arc::new(match tuple_expression {
                        Expr::EllipsisLiteral(_) => gen_expr_ellipsis_literal(),
                        _ => gen_annotation(context, location, tuple_expression)?,
                    }));
            }
        }
        _ => type_reference
            .arguments
            .push_back(Arc::new(gen_annotation(context, location, slice)?)),
    };

    Ok(Type::Reference(type_reference))
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
        TypeLiteral::BigInteger(LiteralBigInteger { value }) => Ok(Type::new_literal(
            TypeLiteral::BigInteger(LiteralBigInteger { value: -value }),
        )),
        _ => unreachable!("gen_expr_number_literal always returns a number literal"),
    }
}

pub fn gen_expr_bin_op(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
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
        Expr::BinOp(expr_binary_op) => gen_expr_bin_op(context, location, expr_binary_op)?,
        _ => {
            return Err(GenAnnotationError::InvalidAnnotation {
                reason: "The expression is not a valid annotation".to_owned(),
            });
        }
    })
}
