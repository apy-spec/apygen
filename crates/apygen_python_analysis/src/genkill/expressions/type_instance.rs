use crate::abstract_environment::{
    AbstractEnvironment, Exception, GetAttributeError, Type, TypeInstance, TypeLiteral,
    get_attribute,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::{GenExprResult, literal_class, literal_function};
use crate::worklist::WorklistContext;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::namespace::{Location, NamespaceLocation, Namespaces};
use std::collections::BTreeMap;
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

pub fn call_method(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    type_instance: &TypeInstance,
    method_name: &Identifier,
    positional: Vec<Arc<Type>>,
    keyword: BTreeMap<Arc<Identifier>, Arc<Type>>,
) -> GenExprResult<Type> {
    let methods = get_instance_environment(&context.namespaces, type_instance)
        .map(|environment| {
            literal_class::get_methods(&context.namespaces, environment, method_name)
        })
        .unwrap_or(Vec::new());

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
        let call_result =
            literal_function::call(context, environment_location, &method, &arguments);
        result = result.union(&context.namespaces, call_result);
    }

    result
}
