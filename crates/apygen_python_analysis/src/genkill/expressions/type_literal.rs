use crate::abstract_environment::{
    TYPES_MODULE, TYPING_MODULE, TypeAliasKind, TypeInstance, TypeLiteral,
};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions::{self, PyTypeEval};
use apy::v1::{Identifier, QualifiedName};

pub fn as_boolean(type_literal: &TypeLiteral) -> Option<bool> {
    match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            Some(expressions::literal_integer::as_boolean(literal_integer))
        }
        TypeLiteral::Boolean(literal_boolean) => {
            Some(expressions::literal_boolean::as_boolean(literal_boolean))
        }
        TypeLiteral::Float(literal_float) => {
            Some(expressions::literal_float::as_boolean(literal_float))
        }
        TypeLiteral::Complex(literal_complex) => {
            Some(expressions::literal_complex::as_boolean(literal_complex))
        }
        TypeLiteral::String(literal_string) => {
            Some(expressions::literal_string::as_boolean(literal_string))
        }
        TypeLiteral::Bytes(literal_bytes) => {
            Some(expressions::literal_bytes::as_boolean(literal_bytes))
        }
        TypeLiteral::None => Some(expressions::literal_none::as_boolean()),
        TypeLiteral::Ellipsis => Some(expressions::literal_ellipsis::as_boolean()),
        TypeLiteral::List(list) => Some(!list.value.is_empty()),
        TypeLiteral::Tuple(tuple) => Some(!tuple.value.is_empty()),
        TypeLiteral::Dict(dict) => Some(!dict.values.is_empty()),
        TypeLiteral::Function(_) => None,
        TypeLiteral::OverloadedFunction(_) => None,
        TypeLiteral::Method(_) => None,
        TypeLiteral::Class(_) => None,
        TypeLiteral::TypeAlias(_) => None,
        TypeLiteral::Generic(_) => None,
        TypeLiteral::ImportedModule(_) => None,
    }
}
pub fn call_binary_op(
    left: &TypeLiteral,
    operator: BinaryOperator,
    right: &TypeLiteral,
) -> PyTypeEval {
    match (left, right) {
        (TypeLiteral::Integer(left), TypeLiteral::Integer(right)) => {
            expressions::literal_integer::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Boolean(left), TypeLiteral::Boolean(right)) => {
            expressions::literal_boolean::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Float(left), TypeLiteral::Integer(right)) => {
            if let Some(right_float) = right.to_literal_float() {
                expressions::literal_float::call_binary_op(left, operator, &right_float)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Integer(left), TypeLiteral::Float(right)) => {
            if let Some(left_float) = left.to_literal_float() {
                expressions::literal_float::call_binary_op(&left_float, operator, right)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Float(left), TypeLiteral::Float(right)) => {
            expressions::literal_float::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Complex(left), TypeLiteral::Float(right)) => {
            if let Some(right_complex) = right.to_literal_complex() {
                expressions::literal_complex::call_binary_op(left, operator, &right_complex)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Float(left), TypeLiteral::Complex(right)) => {
            if let Some(left_complex) = left.to_literal_complex() {
                expressions::literal_complex::call_binary_op(&left_complex, operator, right)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Complex(left), TypeLiteral::Complex(right)) => {
            expressions::literal_complex::call_binary_op(left, operator, right)
        }
        (TypeLiteral::String(left), TypeLiteral::String(right)) => {
            expressions::literal_string::call_binary_op(left, operator, right)
        }
        (TypeLiteral::String(left), TypeLiteral::Integer(right)) => {
            expressions::literal_string::repeat_string(left, right)
        }
        (TypeLiteral::Integer(left), TypeLiteral::String(right)) => {
            expressions::literal_string::repeat_string(right, left)
        }
        (TypeLiteral::Bytes(left), TypeLiteral::Bytes(right)) => {
            expressions::literal_bytes::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Bytes(left), TypeLiteral::Integer(right)) => {
            expressions::literal_bytes::repeat_bytes(left, right)
        }
        (TypeLiteral::Integer(left), TypeLiteral::Bytes(right)) => {
            expressions::literal_bytes::repeat_bytes(right, left)
        }
        _ => PyTypeEval::unknown(),
    }
}

pub fn call_unary_op(type_literal: &TypeLiteral, operator: UnaryOperator) -> PyTypeEval {
    PyTypeEval::with_default_effects(match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            expressions::literal_integer::call_unary_op(literal_integer, operator)
        }
        TypeLiteral::Boolean(literal_boolean) => {
            expressions::literal_boolean::call_unary_op(literal_boolean, operator)
        }
        TypeLiteral::Float(literal_float) => {
            return expressions::literal_float::call_unary_op(literal_float, operator);
        }
        TypeLiteral::Complex(literal_complex) => {
            return expressions::literal_complex::call_unary_op(literal_complex, operator);
        }
        TypeLiteral::String(literal_string) => {
            return expressions::literal_string::call_unary_op(literal_string, operator);
        }
        TypeLiteral::Bytes(literal_bytes) => {
            return expressions::literal_bytes::call_unary_op(literal_bytes, operator);
        }
        TypeLiteral::None => {
            return expressions::literal_none::call_unary_op(operator);
        }
        TypeLiteral::Ellipsis => {
            return expressions::literal_ellipsis::call_unary_op(operator);
        }
        _ => return PyTypeEval::unknown(),
    })
}
