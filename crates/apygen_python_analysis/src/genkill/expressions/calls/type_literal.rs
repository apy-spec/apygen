use crate::abstract_environment::{Type, TypeLiteral};
use crate::genkill::expressions::{GenExprResult, calls};
use apygen_analysis::cfg::nodes;

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
