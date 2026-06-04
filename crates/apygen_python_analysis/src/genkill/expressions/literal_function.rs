use crate::abstract_environment::{Exception, LiteralFunction, Type, TypeLiteral};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::{PyEffects, PyTypeEval};
use crate::worklist::{WorklistContext, add_call, add_dependent};
use apy::v1::QualifiedName;
use apygen_analysis::namespace::{Location, Namespaces};

pub fn as_literal_functions(ty: &Type) -> Vec<LiteralFunction> {
    match ty {
        Type::Union(type_union) => type_union
            .types()
            .iter()
            .flat_map(|union_ty| as_literal_functions(union_ty))
            .collect(),
        Type::Literal(type_literal) => {
            let TypeLiteral::Function(function_type) = type_literal.as_ref() else {
                return Vec::new();
            };
            vec![function_type.clone()]
        }
        _ => Vec::new(),
    }
}

pub fn call(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    literal_function: &LiteralFunction,
    arguments: &Arguments,
) -> PyTypeEval {
    let Ok(bindings) = arguments.bind(&literal_function.value.parameters) else {
        return PyTypeEval::raise(Exception::builtins("TypeError"));
    };

    let result = if let Some(environment) =
        context
            .namespaces
            .get_abstract_environment(&Location::at_exit(
                literal_function.value.location.as_sub_location(),
            )) {
        PyTypeEval::new(
            environment
                .returned_value
                .as_ref()
                .map(|value| value.data.as_ref().clone())
                .unwrap_or(Type::new_literal(TypeLiteral::None)),
            PyEffects {
                exceptions: environment.raised_exceptions.data.clone(),
                pureness: environment.pureness.data,
                completeness: environment.completeness.data,
            },
        )
    } else {
        PyTypeEval::unknown()
    };

    add_call(
        &mut context.calls,
        &context.namespaces,
        literal_function.value.location.as_sub_location(),
        bindings,
    );

    add_dependent(
        &mut context.dependents,
        literal_function.value.location.as_sub_location(),
        environment_location.namespace_location.clone(),
    );

    result
}
