use crate::abstract_environment::{LiteralBoolean, LiteralBytes, LiteralString, Type, TypeLiteral};
use crate::cfg::ast::{ExprBooleanLiteral, ExprBytesLiteral, ExprStringLiteral};
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
