use crate::abstract_environment::{Exception, LiteralBoolean, LiteralInteger, LiteralString, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_traits::ToPrimitive;
use std::sync::Arc;

pub fn as_boolean(literal_string: &LiteralString) -> bool {
    !literal_string.value.is_empty()
}

pub fn call_dunder_bool(literal_string: &LiteralString) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_string),
    })
}

pub fn call_not(literal_string: &LiteralString) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_string),
    })
}

pub fn call_unary_op(
    literal_string: &LiteralString,
    operator: nodes::UnaryOp,
) -> GenExprResult<Type> {
    match operator {
        nodes::UnaryOp::Invert | nodes::UnaryOp::UAdd | nodes::UnaryOp::USub => {
            GenExprResult::raise(Exception::type_error())
        }
        nodes::UnaryOp::Not => GenExprResult::new(call_not(literal_string)),
    }
}

pub fn call_binary_op(
    left: &LiteralString,
    operator: nodes::Operator,
    right: &LiteralString,
) -> GenExprResult<Type> {
    GenExprResult::new(match operator {
        nodes::Operator::Add => Type::new_string_literal({
            let mut value = String::new();
            value.push_str(left.value.as_str());
            value.push_str(right.value.as_str());
            LiteralString {
                value: Arc::new(value),
            }
        }),
        _ => return GenExprResult::raise(Exception::type_error()),
    })
}

pub fn repeat_string(string: &LiteralString, repetitions: &LiteralInteger) -> GenExprResult<Type> {
    if let Some(repetitions) = repetitions.to_usize() {
        GenExprResult::new(Type::new_string_literal(LiteralString {
            value: Arc::new(string.value.repeat(repetitions)),
        }))
    } else {
        GenExprResult::unknown()
    }
}
