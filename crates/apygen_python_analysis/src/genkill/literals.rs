use std::sync::Arc;
use crate::analysis::cfg::nodes::{
    ExprBooleanLiteral, ExprBytesLiteral, ExprNumberLiteral, ExprStringLiteral, Number,
};
use crate::abstract_environment::{LiteralValue, OrderedFloat, Type};

pub fn gen_expr_string_literal(expression: &ExprStringLiteral) -> Type {
    Type::new_literal(LiteralValue::StringLiteral(
        Arc::new(expression.value.to_str().to_owned()),
    ))
}

pub fn gen_expr_bytes_literal(expression: &ExprBytesLiteral) -> Type {
    Type::new_literal(LiteralValue::BytesLiteral(
        expression
            .value
            .iter()
            .flat_map(|part| part.as_slice().iter().copied())
            .collect(),
    ))
}

pub fn gen_expr_number_literal(expression: &ExprNumberLiteral) -> Type {
    match &expression.value {
        Number::Int(int) => Type::new_literal(match int.as_i64() {
            Some(value) => LiteralValue::IntegerLiteral(value),
            None => LiteralValue::BigIntegerLiteral {
                positive: true,
                value: Arc::new(int.to_string()),
            },
        }),
        Number::Float(float) => Type::new_literal(LiteralValue::FloatLiteral(OrderedFloat(*float))),
        Number::Complex { real, imag } => Type::new_literal(LiteralValue::ComplexLiteral {
            real: OrderedFloat(*real),
            image: OrderedFloat(*imag),
        }),
    }
}

pub fn gen_expr_boolean_literal(expression: &ExprBooleanLiteral) -> Type {
    Type::new_literal(LiteralValue::BooleanLiteral(expression.value))
}

pub fn gen_expr_none_literal() -> Type {
    Type::new_literal(LiteralValue::NoneLiteral)
}

pub fn gen_expr_ellipsis_literal() -> Type {
    Type::new_literal(LiteralValue::EllipsisLiteral)
}
