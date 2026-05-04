use crate::abstract_environment::{Exception, LiteralBoolean, LiteralBytes, LiteralInteger, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_traits::ToPrimitive;

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
        nodes::UnaryOp::Not => GenExprResult::new(call_not(literal_bytes)),
    }
}

pub fn call_binary_op(
    left: &LiteralBytes,
    operator: nodes::Operator,
    right: &LiteralBytes,
) -> GenExprResult<Type> {
    GenExprResult::new(match operator {
        nodes::Operator::Add => Type::new_bytes_literal(LiteralBytes {
            value: left
                .value
                .iter()
                .chain(right.value.iter())
                .cloned()
                .collect(),
        }),
        _ => return GenExprResult::raise(Exception::type_error()),
    })
}

pub fn repeat_bytes(bytes: &LiteralBytes, repetitions: &LiteralInteger) -> GenExprResult<Type> {
    if let Some(repetitions) = repetitions.to_usize() {
        GenExprResult::new(Type::new_bytes_literal(LiteralBytes {
            value: imbl::Vector::from_iter(
                (0..repetitions).flat_map(|_| bytes.value.iter().cloned()),
            ),
        }))
    } else {
        GenExprResult::unknown()
    }
}
