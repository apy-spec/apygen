use crate::abstract_environment::{
    AbstractEnvironment, Exception, LiteralClass, LiteralFunction, Type, TypeInstance, TypeLiteral,
    resolve_local_attribute,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::{
    GenExprResult, literal_boolean, literal_bytes, literal_ellipsis, literal_function,
    literal_integer, literal_none,
};
use crate::worklist::WorklistContext;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::{Location, Namespaces};

pub fn get_methods<'a>(
    namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    environment: &AbstractEnvironment,
    method_name: &Identifier,
) -> Vec<LiteralFunction> {
    let Some(attribute) = environment.attributes.get(method_name) else {
        return Vec::new();
    };

    let Ok(local_attribute) = attribute.resolve(namespaces) else {
        return Vec::new();
    };

    literal_function::as_literal_functions(local_attribute.attribute_type.data.as_ref())
}

pub fn call_literal(
    type_instance: &TypeInstance,
    arguments: &Arguments,
) -> Option<GenExprResult<Type>> {
    let identifiers = &type_instance.origin.namespace_location.module.identifiers;

    if identifiers.len() != 1 {
        return None;
    }

    match (identifiers.first().as_ref(), type_instance.name.as_ref()) {
        ("builtins", "int") => match arguments.positional.get(0).map(|arg| arg.as_ref()) {
            Some(Type::Literal(type_literal))
                if arguments.positional.len() == 1 && arguments.keyword.is_empty() =>
            {
                match type_literal.as_ref() {
                    TypeLiteral::Integer(literal_integer) => Some(GenExprResult::new(
                        literal_integer::call_dunder_int(literal_integer),
                    )),
                    TypeLiteral::Boolean(literal_boolean) => Some(GenExprResult::new(
                        literal_boolean::call_dunder_int(literal_boolean),
                    )),
                    _ => None,
                }
            }
            _ => None,
        },
        ("builtins", "bool") => match arguments.positional.get(0).map(|arg| arg.as_ref()) {
            Some(Type::Literal(type_literal))
                if arguments.positional.len() == 1 && arguments.keyword.is_empty() =>
            {
                match type_literal.as_ref() {
                    TypeLiteral::Integer(literal_integer) => Some(GenExprResult::new(
                        literal_integer::call_dunder_bool(literal_integer),
                    )),
                    TypeLiteral::Boolean(literal_boolean) => Some(GenExprResult::new(
                        literal_boolean::call_dunder_bool(literal_boolean),
                    )),
                    TypeLiteral::Bytes(literal_bytes) => Some(GenExprResult::new(
                        literal_bytes::call_dunder_bool(literal_bytes),
                    )),
                    TypeLiteral::Ellipsis => {
                        Some(GenExprResult::new(literal_ellipsis::call_dunder_bool()))
                    }
                    TypeLiteral::None => Some(GenExprResult::new(literal_none::call_dunder_bool())),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

pub fn call(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    name: &Identifier,
    literal_class: &LiteralClass,
    arguments: &Arguments,
) -> GenExprResult<Type> {
    let mut found_init = true;
    let mut found_new = true;
    let Ok((origin, _)) =
        resolve_local_attribute(&context.namespaces, environment_location.clone(), name)
    else {
        return GenExprResult::unknown();
    };

    let type_instance = TypeInstance::new(origin.clone(), name.clone());

    if let Some(result) = call_literal(&type_instance, arguments) {
        return result;
    }

    let mut result = GenExprResult::new(Type::Instance(type_instance));
    for (method_name, found) in [("__new__", &mut found_new), ("__init__", &mut found_init)] {
        let Some(environment) = context
            .namespaces
            .get_abstract_environment(&Location::at_exit(
                literal_class.value.location.as_sub_location(),
            ))
        else {
            return GenExprResult::unknown();
        };

        let methods = get_methods(
            &context.namespaces,
            environment,
            &Identifier::parse(method_name),
        );

        if methods.is_empty() {
            *found = false;
            continue;
        }

        for method in methods {
            let method_result =
                literal_function::call(context, environment_location, &method, arguments);
            result.exceptions = result.exceptions.join(&method_result.exceptions);
            result.pureness = result.pureness.join(&method_result.pureness);
            result.completeness = result.completeness.join(&method_result.completeness);
        }
    }

    if !found_new && !found_init {
        result = GenExprResult::raise(Exception::builtins("TypeError"));
    }

    result
}
