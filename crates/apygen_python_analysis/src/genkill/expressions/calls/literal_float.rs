use crate::abstract_environment::{Exception, LiteralBoolean, LiteralFloat, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;

pub fn as_boolean(literal_float: &LiteralFloat) -> bool {
    literal_float.value != 0.0
}

pub fn call_dunder_bool(literal_float: &LiteralFloat) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_float),
    })
}

pub fn call_not(literal_float: &LiteralFloat) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_float),
    })
}

pub fn call_dunder_pos(literal_float: &LiteralFloat) -> Type {
    Type::new_float_literal(LiteralFloat {
        value: literal_float.value,
    })
}

pub fn call_dunder_neg(literal_float: &LiteralFloat) -> Type {
    Type::new_float_literal(LiteralFloat {
        value: -literal_float.value,
    })
}

pub fn call_unary_op(
    literal_float: &LiteralFloat,
    operator: nodes::UnaryOp,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match operator {
        nodes::UnaryOp::Invert => {
            return GenExprResult::raise(Exception::type_error());
        }
        nodes::UnaryOp::Not => call_not(literal_float),
        nodes::UnaryOp::UAdd => call_dunder_pos(literal_float),
        nodes::UnaryOp::USub => call_dunder_neg(literal_float),
    })
}
