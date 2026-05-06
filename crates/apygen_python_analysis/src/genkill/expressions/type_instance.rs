use crate::abstract_environment::{
    AbstractEnvironment, Exception, FunctionType, GetAttributeError, Type, TypeInstance,
    TypeLiteral, get_attribute,
};
use crate::genkill::calls::{Arguments, BoundArguments};
use crate::genkill::expressions::GenExprResult;
use crate::worklist::{Dependents, WorklistContext, add_call, add_dependent};
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::cfg::nodes::Operator;
use apygen_analysis::namespace::{Location, NamespaceLocation, Namespaces};
use std::collections::{BTreeMap, HashMap};
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

pub fn call_function(
    namespaces: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<NamespaceLocation<QualifiedName>, Dependents>,
    calls: &mut HashMap<NamespaceLocation<QualifiedName>, BoundArguments>,
    environment_location: &Location<QualifiedName>,
    function_type: &FunctionType,
    arguments: &Arguments,
) -> GenExprResult<Type> {
    let Ok(bindings) = arguments.bind(&function_type.parameters) else {
        return GenExprResult::raise(Exception::builtins("TypeError"));
    };

    let result = if let Some(environment) = namespaces
        .get_abstract_environment(&Location::at_exit(function_type.location.as_sub_location()))
    {
        GenExprResult {
            value: environment
                .returned_value
                .as_ref()
                .map(|value| value.data.as_ref().clone())
                .unwrap_or(Type::new_literal(TypeLiteral::None)),
            exceptions: environment.raised_exceptions.data.clone(),
            pureness: environment.pureness.data,
            completeness: environment.completeness.data,
        }
    } else {
        GenExprResult::unknown()
    };

    add_call(
        calls,
        namespaces,
        function_type.location.as_sub_location(),
        bindings,
    );

    add_dependent(
        dependents,
        function_type.location.as_sub_location(),
        environment_location.namespace_location.clone(),
    );

    result
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
    keyword: BTreeMap<Arc<Identifier>, Arc<Type>>,
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
        let call_result = call_function(
            &context.namespaces,
            &mut context.dependents,
            &mut context.calls,
            environment_location,
            method,
            &arguments,
        );
        result = result.union(&context.namespaces, call_result);
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
        BTreeMap::new(),
    );
    let reverse_call = call_method(
        context,
        environment_location,
        right,
        &Identifier::parse(&format!("__r{operator_name}__")),
        vec![Arc::new(Type::Instance(left.clone()))],
        BTreeMap::new(),
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
    let method_name = match operator {
        Operator::Add => "add",
        Operator::Sub => "sub",
        Operator::Mult => "mul",
        Operator::MatMult => "matmul",
        Operator::Div => "truediv",
        Operator::Mod => "mod",
        Operator::Pow => "pow",
        Operator::LShift => "lshift",
        Operator::RShift => "rshift",
        Operator::BitOr => "or",
        Operator::BitXor => "xor",
        Operator::BitAnd => "and",
        Operator::FloorDiv => "floordiv",
    };

    call_operator(context, environment_location, left, method_name, right)
}
