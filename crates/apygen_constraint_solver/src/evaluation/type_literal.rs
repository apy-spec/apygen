use crate::EvaluationState;
use crate::analysis::abstract_state::AbstractState;
use crate::constraint_graph::expressions::{BinaryOperator, UnaryOperator};
use crate::evaluation::{self, PyTypeEval};
use crate::identifiers::Namespace;
use crate::inference::{Sourced, TypeLiteral};

pub fn as_boolean(type_literal: &TypeLiteral) -> Option<bool> {
    match type_literal {
        TypeLiteral::Integer(literal_integer) => {
            Some(evaluation::literal_integer::as_boolean(literal_integer))
        }
        TypeLiteral::Boolean(literal_boolean) => {
            Some(evaluation::literal_boolean::as_boolean(literal_boolean))
        }
        TypeLiteral::Float(literal_float) => {
            Some(evaluation::literal_float::as_boolean(literal_float))
        }
        TypeLiteral::Complex(literal_complex) => {
            Some(evaluation::literal_complex::as_boolean(literal_complex))
        }
        TypeLiteral::String(literal_string) => {
            Some(evaluation::literal_string::as_boolean(literal_string))
        }
        TypeLiteral::Bytes(literal_bytes) => {
            Some(evaluation::literal_bytes::as_boolean(literal_bytes))
        }
        TypeLiteral::None => Some(evaluation::literal_none::as_boolean()),
        TypeLiteral::Ellipsis => Some(evaluation::literal_ellipsis::as_boolean()),
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
pub fn call_binary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    left: &TypeLiteral,
    operator: BinaryOperator,
    right: &TypeLiteral,
) -> PyTypeEval<S> {
    match (left, right) {
        (TypeLiteral::Integer(left), TypeLiteral::Integer(right)) => {
            evaluation::literal_integer::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Boolean(left), TypeLiteral::Boolean(right)) => {
            evaluation::literal_boolean::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Float(left), TypeLiteral::Integer(right)) => {
            if let Some(right_float) = right.to_literal_float() {
                evaluation::literal_float::call_binary_op(left, operator, &right_float)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Integer(left), TypeLiteral::Float(right)) => {
            if let Some(left_float) = left.to_literal_float() {
                evaluation::literal_float::call_binary_op(&left_float, operator, right)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Float(left), TypeLiteral::Float(right)) => {
            evaluation::literal_float::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Complex(left), TypeLiteral::Float(right)) => {
            if let Some(right_complex) = right.to_literal_complex() {
                evaluation::literal_complex::call_binary_op(left, operator, &right_complex)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Float(left), TypeLiteral::Complex(right)) => {
            if let Some(left_complex) = left.to_literal_complex() {
                evaluation::literal_complex::call_binary_op(&left_complex, operator, right)
            } else {
                PyTypeEval::unknown()
            }
        }
        (TypeLiteral::Complex(left), TypeLiteral::Complex(right)) => {
            evaluation::literal_complex::call_binary_op(left, operator, right)
        }
        (TypeLiteral::String(left), TypeLiteral::String(right)) => {
            evaluation::literal_string::call_binary_op(left, operator, right)
        }
        (TypeLiteral::String(left), TypeLiteral::Integer(right)) => {
            evaluation::literal_string::repeat_string(left, right)
        }
        (TypeLiteral::Integer(left), TypeLiteral::String(right)) => {
            evaluation::literal_string::repeat_string(right, left)
        }
        (TypeLiteral::Bytes(left), TypeLiteral::Bytes(right)) => {
            evaluation::literal_bytes::call_binary_op(left, operator, right)
        }
        (TypeLiteral::Bytes(left), TypeLiteral::Integer(right)) => {
            evaluation::literal_bytes::repeat_bytes(left, right)
        }
        (TypeLiteral::Integer(left), TypeLiteral::Bytes(right)) => {
            evaluation::literal_bytes::repeat_bytes(right, left)
        }
        _ => PyTypeEval::unknown(),
    }
}

pub fn call_unary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    type_literal: &TypeLiteral,
    operator: UnaryOperator,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(match type_literal {
        TypeLiteral::Integer(literal_integer) => Sourced::inferred(
            evaluation::literal_integer::call_unary_op(literal_integer, operator),
        ),
        TypeLiteral::Boolean(literal_boolean) => Sourced::inferred(
            evaluation::literal_boolean::call_unary_op(literal_boolean, operator),
        ),
        TypeLiteral::Float(literal_float) => {
            return evaluation::literal_float::call_unary_op(literal_float, operator);
        }
        TypeLiteral::Complex(literal_complex) => {
            return evaluation::literal_complex::call_unary_op(literal_complex, operator);
        }
        TypeLiteral::String(literal_string) => {
            return evaluation::literal_string::call_unary_op(literal_string, operator);
        }
        TypeLiteral::Bytes(literal_bytes) => {
            return evaluation::literal_bytes::call_unary_op(literal_bytes, operator);
        }
        TypeLiteral::None => {
            return evaluation::literal_none::call_unary_op(operator);
        }
        TypeLiteral::Ellipsis => {
            return evaluation::literal_ellipsis::call_unary_op(operator);
        }
        _ => return PyTypeEval::unknown(),
    })
}
