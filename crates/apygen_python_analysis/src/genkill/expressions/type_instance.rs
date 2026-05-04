use crate::abstract_environment::{
    AbstractEnvironment, Exception, FunctionType, GetAttributeError, Type, TypeInstance,
    TypeLiteral, get_attribute,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::GenExprResult;
use crate::worklist::WorklistContext;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::cfg::nodes::Operator;
use apygen_analysis::namespace::{Location, NamespaceLocation, Namespaces};
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum GetInstanceEnvironmentError {
    #[error("failed to get attribute namespace: {0}")]
    GetAttributeError(#[from] GetAttributeError),
    #[error("the attribute is not a namespace")]
    DoesNotHaveNamespace,
}

pub fn get_instance_environment<'a>(
    context: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    type_instance: &TypeInstance,
) -> Result<&'a AbstractEnvironment, GetInstanceEnvironmentError> {
    let local_attribute =
        get_attribute(context, &type_instance.origin, &type_instance.name)?.resolve(context)?;

    let Type::Literal(type_literal) = local_attribute.attribute_type.data.as_ref() else {
        return Err(GetInstanceEnvironmentError::DoesNotHaveNamespace);
    };

    let location = match type_literal.as_ref() {
        TypeLiteral::Class(class_type) => {
            Location::at_exit(class_type.value.location.as_sub_location())
        }
        TypeLiteral::ImportedModule(module_reference_type) => Location::at_exit(
            NamespaceLocation::new(module_reference_type.value.module.clone()),
        ),
        _ => return Err(GetInstanceEnvironmentError::DoesNotHaveNamespace),
    };

    context
        .get_abstract_environment(&location)
        .ok_or(GetInstanceEnvironmentError::DoesNotHaveNamespace)
}

pub fn get_functions(ty: &Type) -> Vec<&FunctionType> {
    match ty {
        Type::Union(type_union) => type_union
            .types()
            .iter()
            .flat_map(|union_ty| get_functions(union_ty))
            .collect(),
        Type::Literal(type_literal) => {
            let TypeLiteral::Function(function_type) = type_literal.as_ref() else {
                return Vec::new();
            };
            vec![&function_type.value]
        }
        _ => Vec::new(),
    }
}

pub fn get_methods<'a>(
    namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    type_instance: &TypeInstance,
    method_name: &Identifier,
) -> Vec<&'a FunctionType> {
    let Ok(environment) = get_instance_environment(namespaces, type_instance) else {
        return Vec::new();
    };

    let Some(attribute) = environment.attributes.get(method_name) else {
        return Vec::new();
    };

    let Ok(local_attribute) = attribute.resolve(namespaces) else {
        return Vec::new();
    };

    get_functions(local_attribute.attribute_type.data.as_ref())
}

pub fn call_method(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    type_instance: &TypeInstance,
    method_name: &Identifier,
    positional: Vec<Arc<Type>>,
    keyword: HashMap<Arc<Identifier>, Arc<Type>>,
) -> GenExprResult<Type> {
    let methods = get_methods(&context.namespaces, type_instance, method_name);

    if methods.is_empty() {
        return GenExprResult::raise(Exception::builtins("AttributeError"));
    }

    let arguments = Arguments {
        positional: std::iter::once(Arc::new(Type::Instance(type_instance.clone())))
            .chain(positional.into_iter())
            .collect(),
        keyword,
    };

    let mut result = GenExprResult::never();
    for method in methods {
        if let Ok(bindings) = arguments.bind(&method.parameters) {
            if let Some(environment) = context
                .namespaces
                .get_abstract_environment(&Location::at_exit(method.location.as_sub_location()))
            {
                result = result.union(
                    &context.namespaces,
                    GenExprResult {
                        value: environment.returned_value.data.as_ref().clone(),
                        exceptions: environment.raised_exceptions.data.clone(),
                        pureness: environment.pureness.data,
                        completeness: environment.completeness.data,
                    },
                );
            } else {
                result = GenExprResult::unknown();
            }

            context
                .calls
                .insert(method.location.as_sub_location(), bindings);
            context
                .dependents
                .entry(method.location.as_sub_location())
                .or_default()
                .insert(environment_location.namespace_location.clone());
        } else {
            result = result.union(
                &context.namespaces,
                GenExprResult::raise(Exception::builtins("TypeError")),
            );
        }
    }

    result
}

pub fn call_operator(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    left: &TypeInstance,
    operator_name: &str,
    right: &TypeInstance,
) -> GenExprResult<Type> {
    let normal_call = call_method(
        context,
        environment_location,
        left,
        &Identifier::parse(&format!("__{operator_name}__")),
        vec![Arc::new(Type::Instance(right.clone()))],
        HashMap::new(),
    );
    let reverse_call = call_method(
        context,
        environment_location,
        right,
        &Identifier::parse(&format!("__r{operator_name}__")),
        vec![Arc::new(Type::Instance(left.clone()))],
        HashMap::new(),
    );

    normal_call.union(&context.namespaces, reverse_call)
}

/// References:
/// - https://docs.python.org/3/reference/datamodel.html#emulating-numeric-types
pub fn call_binary_op(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    left: &TypeInstance,
    operator: Operator,
    right: &TypeInstance,
) -> GenExprResult<Type> {
    match operator {
        Operator::Add => call_operator(context, environment_location, left, "add", right),
        Operator::Sub => call_operator(context, environment_location, left, "sub", right),
        Operator::Mult => call_operator(context, environment_location, left, "mul", right),
        Operator::MatMult => call_operator(context, environment_location, left, "matmul", right),
        Operator::Div => call_operator(context, environment_location, left, "truediv", right),
        Operator::Mod => call_operator(context, environment_location, left, "mod", right),
        Operator::Pow => call_operator(context, environment_location, left, "pow", right),
        Operator::LShift => call_operator(context, environment_location, left, "lshift", right),
        Operator::RShift => call_operator(context, environment_location, left, "rshift", right),
        Operator::BitOr => call_operator(context, environment_location, left, "or", right),
        Operator::BitXor => call_operator(context, environment_location, left, "xor", right),
        Operator::BitAnd => call_operator(context, environment_location, left, "and", right),
        Operator::FloorDiv => call_operator(context, environment_location, left, "floordiv", right),
    }
}
