use crate::abstract_environment::{
    LiteralBigInteger, LiteralBoolean, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInteger,
    LiteralString, OrderedFloat, Type, TypeLiteral,
};
use crate::analysis::cfg::nodes::{
    ExprBooleanLiteral, ExprBytesLiteral, ExprNumberLiteral, ExprStringLiteral, Number,
};
use std::sync::Arc;

pub fn gen_expr_string_literal(expression: &ExprStringLiteral) -> Type {
    Type::new_literal(TypeLiteral::String(LiteralString {
        value: Arc::new(expression.value.to_str().to_owned()),
    }))
}

pub fn gen_expr_bytes_literal(expression: &ExprBytesLiteral) -> Type {
    Type::new_literal(TypeLiteral::Bytes(LiteralBytes {
        value: expression
            .value
            .iter()
            .flat_map(|part| part.as_slice().iter().copied())
            .collect(),
    }))
}

pub fn gen_expr_number_literal(expression: &ExprNumberLiteral) -> Type {
    match &expression.value {
        Number::Int(int) => Type::new_literal(match int.as_i64() {
            Some(value) => TypeLiteral::Integer(LiteralInteger { value }),
            None => TypeLiteral::BigInteger(LiteralBigInteger {
                positive: true,
                value: Arc::new(int.to_string()),
            }),
        }),
        Number::Float(float) => Type::new_literal(TypeLiteral::Float(LiteralFloat {
            value: OrderedFloat(*float),
        })),
        Number::Complex { real, imag } => Type::new_literal(TypeLiteral::Complex(LiteralComplex {
            real: OrderedFloat(*real),
            image: OrderedFloat(*imag),
        })),
    }
}

pub fn gen_expr_boolean_literal(expression: &ExprBooleanLiteral) -> Type {
    Type::new_literal(TypeLiteral::Boolean(LiteralBoolean {
        value: expression.value,
    }))
}

pub fn gen_expr_none_literal() -> Type {
    Type::new_literal(TypeLiteral::None)
}

pub fn gen_expr_ellipsis_literal() -> Type {
    Type::new_literal(TypeLiteral::Ellipsis)
}
