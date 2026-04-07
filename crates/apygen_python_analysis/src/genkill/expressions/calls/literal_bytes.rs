use crate::abstract_environment::{Exception, LiteralBoolean, LiteralBytes, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;

pub fn as_boolean(literal_bytes: &LiteralBytes) -> bool {
    !literal_bytes.value.is_empty()
}

pub fn call_dunder_bool(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_bytes),
    })
}

pub fn call_not(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_bytes),
    })
}

pub fn call_unary_op(
    literal_bytes: &LiteralBytes,
    operator: nodes::UnaryOp,
) -> GenExprResult<Type> {
    match operator {
        nodes::UnaryOp::Invert | nodes::UnaryOp::UAdd | nodes::UnaryOp::USub => {
            GenExprResult::raise(Exception::type_error())
        }
        nodes::UnaryOp::Not => GenExprResult::new_total_pure_non_raising(call_not(literal_bytes)),
    }
}
