use crate::abstract_environment::{
    AbstractEnvironment, BUILTINS_MODULE, TYPES_MODULE, TYPING_MODULE, Type, TypeAliasKind,
    TypeLiteral, TypeReference,
};
use crate::genkill::expressions::{GenExprResult, calls};
use apy::v1::QualifiedName;
use apygen_analysis::cfg::nodes;
use apygen_analysis::namespace::{Location, NamespacesContext};
use std::sync::Arc;

pub fn as_boolean(type_literal: &TypeLiteral) -> Option<bool> {
    match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            Some(calls::literal_integer::as_boolean(literal_integer))
        }
        TypeLiteral::BigInteger(literal_big_integer) => {
            Some(calls::literal_big_integer::as_boolean(literal_big_integer))
        }
        TypeLiteral::Boolean(literal_boolean) => {
            Some(calls::literal_boolean::as_boolean(literal_boolean))
        }
        TypeLiteral::Float(literal_float) => Some(calls::literal_float::as_boolean(literal_float)),
        TypeLiteral::Complex(literal_complex) => {
            Some(calls::literal_complex::as_boolean(literal_complex))
        }
        TypeLiteral::String(literal_string) => {
            Some(calls::literal_string::as_boolean(literal_string))
        }
        TypeLiteral::Bytes(literal_bytes) => Some(calls::literal_bytes::as_boolean(literal_bytes)),
        TypeLiteral::None => Some(calls::literal_none::as_boolean()),
        TypeLiteral::Ellipsis => Some(calls::literal_ellipsis::as_boolean()),
        TypeLiteral::List(list) => Some(!list.value.is_empty()),
        TypeLiteral::Tuple(tuple) => Some(!tuple.value.is_empty()),
        TypeLiteral::Dict(dict) => Some(!dict.value.is_empty()),
        TypeLiteral::Function(_) => None,
        TypeLiteral::Class(_) => None,
        TypeLiteral::TypeAlias(_) => None,
        TypeLiteral::Generic(_) => None,
        TypeLiteral::ImportedModule(_) => None,
    }
}

pub fn as_type_reference(type_literal: &TypeLiteral) -> TypeReference {
    match type_literal {
        TypeLiteral::Integer(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("int"),
        ),
        TypeLiteral::BigInteger(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("int"),
        ),
        TypeLiteral::Boolean(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("bool"),
        ),
        TypeLiteral::Float(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("float"),
        ),
        TypeLiteral::Complex(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("complex"),
        ),
        TypeLiteral::String(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("str"),
        ),
        TypeLiteral::Bytes(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("bytes"),
        ),
        TypeLiteral::None => TypeReference::new(
            Arc::new(QualifiedName::parse(TYPES_MODULE)),
            QualifiedName::parse("NoneType"),
        ),
        TypeLiteral::Ellipsis => TypeReference::new(
            Arc::new(QualifiedName::parse(TYPES_MODULE)),
            QualifiedName::parse("EllipsisType"),
        ),
        TypeLiteral::List(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("list"),
        ),
        TypeLiteral::Tuple(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("tuple"),
        ),
        TypeLiteral::Dict(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("dict"),
        ),
        TypeLiteral::Function(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(TYPES_MODULE)),
            QualifiedName::parse("FunctionType"),
        ),
        TypeLiteral::Class(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            QualifiedName::parse("type"),
        ),
        TypeLiteral::TypeAlias(literal_type_alias) => match literal_type_alias.value.kind {
            TypeAliasKind::Type | TypeAliasKind::String => TypeReference::new(
                Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                QualifiedName::parse("type"),
            ),
            TypeAliasKind::Statement => TypeReference::new(
                Arc::new(QualifiedName::parse(TYPING_MODULE)),
                QualifiedName::parse("TypeAliasType"),
            ),
        },
        TypeLiteral::Generic(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(TYPING_MODULE)),
            QualifiedName::parse("TypeVar"),
        ),
        TypeLiteral::ImportedModule(_) => TypeReference::new(
            Arc::new(QualifiedName::parse(TYPES_MODULE)),
            QualifiedName::parse("ModuleType"),
        ),
    }
}

pub fn call_binary_op(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    environment_location: &Location<QualifiedName>,
    left: &TypeLiteral,
    operator: nodes::Operator,
    right: &TypeLiteral,
) -> GenExprResult<Type> {
    match (left, right) {
        (TypeLiteral::Integer(left), TypeLiteral::Integer(right)) => {
            calls::literal_integer::call_binary_op(left, operator, right)
        }
        _ => GenExprResult::unknown(),
    }
}

pub fn call_unary_op(type_literal: &TypeLiteral, operator: nodes::UnaryOp) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            calls::literal_integer::call_unary_op(literal_integer, operator)
        }
        TypeLiteral::BigInteger(literal_big_integer) => {
            calls::literal_big_integer::call_unary_op(literal_big_integer, operator)
        }
        TypeLiteral::Boolean(literal_boolean) => {
            calls::literal_boolean::call_unary_op(literal_boolean, operator)
        }
        TypeLiteral::Float(literal_float) => {
            return calls::literal_float::call_unary_op(literal_float, operator);
        }
        TypeLiteral::Complex(literal_complex) => {
            return calls::literal_complex::call_unary_op(literal_complex, operator);
        }
        TypeLiteral::String(literal_string) => {
            return calls::literal_string::call_unary_op(literal_string, operator);
        }
        TypeLiteral::Bytes(literal_bytes) => {
            return calls::literal_bytes::call_unary_op(literal_bytes, operator);
        }
        TypeLiteral::None => {
            return calls::literal_none::call_unary_op(operator);
        }
        TypeLiteral::Ellipsis => {
            return calls::literal_ellipsis::call_unary_op(operator);
        }
        _ => return GenExprResult::unknown(),
    })
}
