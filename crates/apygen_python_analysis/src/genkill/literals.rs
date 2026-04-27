use crate::abstract_environment::{
    LiteralBigInteger, LiteralBoolean, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInteger,
    LiteralString, OrderedFloat, Type, TypeLiteral,
};
use crate::analysis::cfg::nodes::{
    ExprBooleanLiteral, ExprBytesLiteral, ExprNumberLiteral, ExprStringLiteral, Number,
};
use num_bigint::BigInt;
use num_traits::Num;
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
                value: {
                    let base = int.to_string();

                    if base.starts_with("0x") || base.starts_with("0X") {
                        BigInt::from_str_radix(&base[2..], 16).unwrap()
                    } else if base.starts_with("0o") || base.starts_with("0O") {
                        BigInt::from_str_radix(&base[2..], 8).unwrap()
                    } else if base.starts_with("0b") || base.starts_with("0B") {
                        BigInt::from_str_radix(&base[2..], 2).unwrap()
                    } else {
                        BigInt::from_str_radix(&base, 10).unwrap()
                    }
                },
            }),
        }),
        Number::Float(float) => Type::new_literal(TypeLiteral::Float(LiteralFloat {
            value: OrderedFloat(*float),
        })),
        Number::Complex { real, imag } => Type::new_literal(TypeLiteral::Complex(LiteralComplex {
            real: OrderedFloat(*real),
            imaginary: OrderedFloat(*imag),
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
