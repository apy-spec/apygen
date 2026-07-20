use crate::inference::{Exception, Type};
use crate::genkill::expressions::PyTypeEval;
use crate::primitives::literals::LiteralBool;
use apygen_constraints::expressions::UnaryOperator;

pub fn as_boolean() -> bool {
    false
}

pub fn call_dunder_bool() -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(),
    })
}

pub fn call_not() -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: !as_boolean(),
    })
}

pub fn call_unary_op(operator: UnaryOperator) -> PyTypeEval {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::any()) // TODO: fix
        }
        UnaryOperator::Not => PyTypeEval::with_default_effects(call_not()),
    }
}
