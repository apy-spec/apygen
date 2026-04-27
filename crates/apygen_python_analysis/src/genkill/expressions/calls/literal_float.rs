use crate::abstract_environment::{Exception, LiteralBoolean, LiteralFloat, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_traits::Pow;
use ordered_float::OrderedFloat;

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

pub fn call_binary_op(
    left: &LiteralFloat,
    operator: nodes::Operator,
    right: &LiteralFloat,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match operator {
        nodes::Operator::Add => Type::new_float_literal(LiteralFloat {
            value: left.value + right.value,
        }),
        nodes::Operator::Sub => Type::new_float_literal(LiteralFloat {
            value: left.value - right.value,
        }),
        nodes::Operator::Mult => Type::new_float_literal(LiteralFloat {
            value: left.value * right.value,
        }),
        nodes::Operator::Pow => Type::new_float_literal(LiteralFloat {
            value: left.value.pow(right.value),
        }),
        nodes::Operator::Div => {
            if right.value == 0.0 {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_float_literal(LiteralFloat {
                value: left.value / right.value,
            })
        }
        nodes::Operator::FloorDiv => {
            if right.value == 0.0 {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_float_literal(LiteralFloat {
                value: OrderedFloat((left.value / right.value).floor()),
            })
        }
        nodes::Operator::Mod => {
            if right.value == 0.0 {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_float_literal(LiteralFloat {
                value: left.value % right.value,
            })
        }
        nodes::Operator::MatMult
        | nodes::Operator::LShift
        | nodes::Operator::RShift
        | nodes::Operator::BitOr
        | nodes::Operator::BitXor
        | nodes::Operator::BitAnd => return GenExprResult::raise(Exception::type_error()),
    })
}
