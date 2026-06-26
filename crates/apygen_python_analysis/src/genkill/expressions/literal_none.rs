use crate::abstract_environment::{Exception, ExceptionOrigin, LiteralBoolean, Type};
use crate::genkill::expressions::PyTypeEval;
use crate::constraints::UnaryOperator;

pub fn as_boolean() -> bool {
    false
}

pub fn call_dunder_bool() -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(),
    })
}

pub fn call_not() -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(),
    })
}

pub fn call_unary_op(operator: UnaryOperator) -> PyTypeEval {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Unknown))
        }
        UnaryOperator::Not => PyTypeEval::with_default_effects(call_not()),
    }
}
