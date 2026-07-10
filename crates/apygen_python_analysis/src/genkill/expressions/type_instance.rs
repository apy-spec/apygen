use crate::abstract_environment::{
    AbstractEnvironment, Attribute, Exception, ExceptionOrigin, GetAttributeError, Type,
    TypeInstance, TypeLiteral, get_attribute,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::literal_class::{
    attribute_as_literal_functions, resolve_class_attribute,
};
use crate::genkill::expressions::{PyTypeEval, literal_function};
use crate::worklist::WorklistContext;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::lattice::Join;
use apygen_analysis::namespace::{Location, Namespaces};
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

pub fn get_instance_attribute<'a>(
    namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    type_instance: &TypeInstance,
    name: &Identifier,
) -> Result<&'a Attribute, GetInstanceEnvironmentError> {
    let local_attribute = get_attribute(namespaces, &type_instance.origin, &type_instance.name)?
        .resolve(namespaces)?;

    let Type::Literal(type_literal) = local_attribute.attribute_type.data.as_ref() else {
        return Err(GetInstanceEnvironmentError::DoesNotHaveNamespace);
    };

    Ok(match type_literal.as_ref() {
        TypeLiteral::Class(literal_class) => {
            let Some(attribute) = resolve_class_attribute(namespaces, literal_class, &name) else {
                return Err(GetInstanceEnvironmentError::DoesNotHaveNamespace); // TODO: use a better error
            };
            attribute
        }
        TypeLiteral::ImportedModule(module_reference_type) => get_attribute(
            namespaces,
            &Location::from(module_reference_type.value.module.clone()),
            &name,
        )?,
        _ => return Err(GetInstanceEnvironmentError::DoesNotHaveNamespace),
    })
}

pub fn call_method(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    type_instance: &TypeInstance,
    method_name: &Identifier,
    positional: Vec<Arc<Type>>,
    keyword: BTreeMap<Arc<Identifier>, Arc<Type>>,
) -> PyTypeEval {
    let methods = get_instance_attribute(&context.namespaces, type_instance, method_name)
        .map(|attribute| attribute_as_literal_functions(&context.namespaces, &attribute))
        .unwrap_or(Vec::new());

    if methods.is_empty() {
        return PyTypeEval::raise(Exception::builtins(
            "AttributeError",
            ExceptionOrigin::Raised(environment_location.clone()),
        ));
    }

    let arguments = Arguments {
        positional: std::iter::once(Arc::new(Type::Instance(type_instance.clone())))
            .chain(positional.into_iter())
            .collect(),
        keyword,
    };

    let mut result = PyTypeEval::never();
    for method in methods {
        let call_result =
            literal_function::call(context, environment_location, &method, &arguments);
        result = result.join(&call_result);
    }

    result
}
