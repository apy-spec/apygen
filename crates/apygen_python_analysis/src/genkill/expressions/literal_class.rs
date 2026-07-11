use crate::abstract_environment::{
    AbstractEnvironment, Attribute, Exception, ExceptionOrigin, LiteralClass, LiteralFunction,
    Type, TypeInstance, TypeLiteral, resolve_local_attribute,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::{
    PyTypeEval, literal_boolean, literal_bytes, literal_ellipsis, literal_float, literal_function,
    literal_integer, literal_none, literal_string,
};
use crate::worklist::WorklistContext;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::namespace::{Location, Namespaces};
use std::collections::VecDeque;

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

pub fn call_literal(type_instance: &TypeInstance, arguments: &Arguments) -> Option<PyTypeEval> {
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
                    TypeLiteral::Integer(literal_integer) => {
                        Some(PyTypeEval::with_default_effects(
                            literal_integer::call_dunder_int(literal_integer),
                        ))
                    }
                    TypeLiteral::Boolean(literal_boolean) => {
                        Some(PyTypeEval::with_default_effects(
                            literal_boolean::call_dunder_int(literal_boolean),
                        ))
                    }
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
                    TypeLiteral::Integer(literal_integer) => {
                        Some(PyTypeEval::with_default_effects(
                            literal_integer::call_dunder_bool(literal_integer),
                        ))
                    }
                    TypeLiteral::Float(literal_float) => Some(PyTypeEval::with_default_effects(
                        literal_float::call_dunder_bool(literal_float),
                    )),
                    TypeLiteral::Boolean(literal_boolean) => {
                        Some(PyTypeEval::with_default_effects(
                            literal_boolean::call_dunder_bool(literal_boolean),
                        ))
                    }
                    TypeLiteral::Bytes(literal_bytes) => Some(PyTypeEval::with_default_effects(
                        literal_bytes::call_dunder_bool(literal_bytes),
                    )),
                    TypeLiteral::String(literal_string) => Some(PyTypeEval::with_default_effects(
                        literal_string::call_dunder_bool(literal_string),
                    )),
                    TypeLiteral::Ellipsis => Some(PyTypeEval::with_default_effects(
                        literal_ellipsis::call_dunder_bool(),
                    )),
                    TypeLiteral::None => Some(PyTypeEval::with_default_effects(
                        literal_none::call_dunder_bool(),
                    )),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// References:
/// - https://docs.python.org/3/glossary.html#term-method-resolution-order
/// - https://docs.python.org/3/howto/mro.html
pub fn method_resolution_order(literal_class: &LiteralClass) -> Option<VecDeque<&LiteralClass>> {
    let mut class_bases = VecDeque::from_iter(&literal_class.value.bases);

    let mut class_bases_mro = class_bases
        .iter()
        .map(|base| method_resolution_order(base))
        .collect::<Option<Vec<_>>>()?;
    let mut class = VecDeque::from_iter([literal_class]);

    let mut sequences = VecDeque::new();
    sequences.push_back(&mut class);
    for class_base_mro in &mut class_bases_mro {
        sequences.push_back(class_base_mro);
    }
    sequences.push_back(&mut class_bases);

    let mut mro: VecDeque<&LiteralClass> = VecDeque::new();
    loop {
        let mut candidate: Option<&LiteralClass> = None;
        let mut all_empty = true;

        for sequence in &sequences {
            let Some(class_candidate) = sequence.front() else {
                continue;
            };

            all_empty = false;

            if !sequences.iter().any(|sequence| {
                sequence.len() >= 1 && sequence.range(1..).any(|class| class == class_candidate)
            }) {
                candidate = Some(class_candidate);
                break;
            }
        }

        if all_empty {
            break;
        }

        let head = candidate?;

        mro.push_back(head);

        for sequence in &mut sequences {
            let Some(sequence_head) = sequence.front() else {
                continue;
            };
            if sequence_head == &head {
                sequence.pop_front();
            }
        }
    }

    Some(mro)
}

pub fn resolve_class_attribute<'a>(
    namespaces: &'a impl Namespaces<QualifiedName, AbstractEnvironment>,
    literal_class: &LiteralClass,
    name: &Identifier,
) -> Option<&'a Attribute> {
    for class in method_resolution_order(literal_class)? {
        let Some(environment) = namespaces
            .get_abstract_environment(&Location::at_exit(class.value.location.as_sub_location()))
        else {
            continue;
        };

        let Some(attribute) = environment.attributes.get(name) else {
            continue;
        };

        return Some(attribute);
    }

    None
}

pub fn attribute_as_literal_functions(
    namespaces: &impl Namespaces<QualifiedName, AbstractEnvironment>,
    attribute: &Attribute,
) -> Vec<LiteralFunction> {
    let Ok(local_attribute) = attribute.resolve(namespaces) else {
        return Vec::new();
    };

    literal_function::as_literal_functions(local_attribute.attribute_type.data.as_ref())
}

pub fn call(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    name: &Identifier,
    literal_class: &LiteralClass,
    arguments: &Arguments,
) -> PyTypeEval {
    let mut found_init = true;
    let mut found_new = true;
    let Ok((origin, _, _)) =
        resolve_local_attribute(&context.namespaces, environment_location.clone(), name)
    else {
        return PyTypeEval::unknown();
    };

    let type_instance = TypeInstance::new(origin.clone(), name.clone());

    if let Some(ty) = call_literal(&type_instance, arguments) {
        return ty;
    }

    let mut ty = PyTypeEval::with_default_effects(Type::Instance(type_instance));
    for (method_name, found) in [
        (Identifier::parse("__new__"), &mut found_new),
        (Identifier::parse("__init__"), &mut found_init),
    ] {
        let Some(attribute) =
            resolve_class_attribute(&context.namespaces, literal_class, &method_name)
        else {
            continue;
        };

        let methods = attribute_as_literal_functions(&context.namespaces, &attribute);

        if methods.is_empty() {
            *found = false;
            continue;
        }

        for method in methods {
            ty.effects.consume(literal_function::call(
                context,
                environment_location,
                &method,
                arguments,
            ));
        }
    }

    if !found_new && !found_init {
        ty = PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Raised(
            environment_location.clone(),
        )));
    }

    ty
}

#[cfg(test)]
mod tests {
    use crate::abstract_environment::{
        AbstractEnvironment, Attribute, ClassType, LiteralClass, LocalAttribute, Sourced, Type,
        TypeLiteral,
    };
    use crate::constraints::QualifiedLocation;
    use crate::genkill::expressions::literal_class::method_resolution_order;
    use apy::v1::{Identifier, QualifiedName};
    use apygen_analysis::cfg::ProgramPoint;
    use apygen_analysis::namespace::{
        Location, Namespace, NamespaceLocation, NamespaceLocations, Namespaces,
    };
    use imbl::OrdMap;
    use std::collections::{HashMap, VecDeque};
    use std::sync::Arc;

    fn create_namespace_location() -> NamespaceLocation<QualifiedName> {
        NamespaceLocation::from(Arc::new(QualifiedName::parse("test_module")))
    }

    fn get_class<'a>(
        abstract_environment: &'a AbstractEnvironment,
        name: &str,
    ) -> &'a LiteralClass {
        let attribute = abstract_environment
            .attributes
            .get(&Identifier::parse(name))
            .expect("Attribute not found");

        let Attribute::Local(local_attribute) = attribute.as_ref() else {
            panic!("Attribute should be local");
        };

        let Type::Literal(type_literal) = local_attribute.attribute_type.data.as_ref() else {
            panic!("Attribute type should be literal");
        };

        let TypeLiteral::Class(literal_class) = type_literal.as_ref() else {
            panic!("Attribute type literal should be a class");
        };

        literal_class
    }

    fn create_namespaces(
        namespace_location: NamespaceLocation<QualifiedName>,
        classes: Vec<(&str, Vec<&str>)>,
    ) -> NamespaceLocations<QualifiedName, AbstractEnvironment> {
        let mut namespace = Namespace::default();

        let mut previous_point = ProgramPoint::Entry;
        let mut current_point_id: usize = 0;

        namespace
            .abstract_environments
            .insert(previous_point, AbstractEnvironment::new());

        for (name, bases) in classes {
            let mut current_environment = namespace
                .abstract_environments
                .get(&previous_point)
                .cloned()
                .unwrap_or_default();

            let current_point = ProgramPoint::Point(current_point_id);
            let identifier = Arc::new(Identifier::parse(name));
            current_environment.attributes.insert(
                identifier.clone(),
                Arc::new(Attribute::Local(LocalAttribute::new(Sourced::inferred(
                    Arc::new(Type::Literal(Arc::new(TypeLiteral::Class(LiteralClass {
                        value: Arc::new(ClassType {
                            name: identifier,
                            location: Location {
                                namespace_location: namespace_location.clone(),
                                program_point: current_point,
                            },
                            qualified_location: QualifiedLocation::new(
                                namespace_location.module.clone(),
                                Default::default(),
                            ),
                            generics: OrdMap::new(),
                            bases: bases
                                .iter()
                                .map(|base| get_class(&current_environment, base).clone())
                                .collect(),
                            keyword_arguments: OrdMap::new(),
                            is_abstract: false,
                        }),
                    })))),
                )))),
            );

            namespace
                .abstract_environments
                .insert(current_point, current_environment);
            previous_point = current_point;
            current_point_id = current_point_id + 1;
        }

        namespace.abstract_environments.insert(
            ProgramPoint::Exit,
            namespace
                .abstract_environments
                .get(&previous_point)
                .cloned()
                .unwrap_or_default(),
        );

        NamespaceLocations {
            locations: HashMap::from_iter([(namespace_location, namespace)]),
        }
    }

    fn get_class_location<'a>(
        namespaces: &'a NamespaceLocations<QualifiedName, AbstractEnvironment>,
        namespace_location: NamespaceLocation<QualifiedName>,
        name: &'a str,
    ) -> Location<QualifiedName> {
        let abstract_environment = namespaces
            .get_abstract_environment(&Location::at_exit(namespace_location))
            .expect("Namespace not found");
        get_class(abstract_environment, name).value.location.clone()
    }

    fn create_target_base<'a>(
        namespaces: &'a NamespaceLocations<QualifiedName, AbstractEnvironment>,
        namespace_location: NamespaceLocation<QualifiedName>,
        name: &'a str,
    ) -> &'a LiteralClass {
        let abstract_environment = namespaces
            .get_abstract_environment(&Location::at_exit(namespace_location.clone()))
            .expect("Namespace not found");

        get_class(abstract_environment, name)
    }

    fn assert_eq_mro(
        namespaces: &NamespaceLocations<QualifiedName, AbstractEnvironment>,
        namespace_location: &NamespaceLocation<QualifiedName>,
        actual_mro: VecDeque<&LiteralClass>,
        expected_mro: Vec<(Location<QualifiedName>, Vec<&str>)>,
    ) {
        for (actual_class, (expected_location, expected_bases)) in
            actual_mro.iter().zip(expected_mro.iter())
        {
            assert_eq!(&actual_class.value.location, expected_location);
            assert_eq!(
                actual_class.value.bases,
                expected_bases
                    .iter()
                    .map(
                        |base| create_target_base(namespaces, namespace_location.clone(), base)
                            .clone()
                    )
                    .collect()
            );
        }

        assert_eq!(actual_mro.len(), expected_mro.len());
    }

    #[test]
    fn test_linear_mro() {
        let namespace_location = create_namespace_location();

        let namespaces = create_namespaces(
            namespace_location.clone(),
            vec![("A", vec![]), ("B", vec!["A"]), ("C", vec!["B"])],
        );

        let class_c = create_target_base(&namespaces, namespace_location.clone(), "C");

        let class_c_mro = method_resolution_order(&class_c).expect("Failed to compute MRO");

        assert_eq_mro(
            &namespaces,
            &namespace_location,
            class_c_mro,
            vec![
                (
                    get_class_location(&namespaces, namespace_location.clone(), "C"),
                    vec!["B"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "B"),
                    vec!["A"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "A"),
                    vec![],
                ),
            ],
        );

        let class_b = create_target_base(&namespaces, namespace_location.clone(), "B");

        let class_b_mro = method_resolution_order(&class_b).expect("Failed to compute MRO");

        assert_eq_mro(
            &namespaces,
            &namespace_location,
            class_b_mro,
            vec![
                (
                    get_class_location(&namespaces, namespace_location.clone(), "B"),
                    vec!["A"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "A"),
                    vec![],
                ),
            ],
        );

        let class_a = create_target_base(&namespaces, namespace_location.clone(), "A");

        let class_a_mro = method_resolution_order(&class_a).expect("Failed to compute MRO");

        assert_eq_mro(
            &namespaces,
            &namespace_location,
            class_a_mro,
            vec![(
                get_class_location(&namespaces, namespace_location.clone(), "A"),
                vec![],
            )],
        );
    }

    #[test]
    fn test_impossible_mro() {
        let namespace_location = create_namespace_location();

        let namespaces = create_namespaces(
            namespace_location.clone(),
            vec![
                ("O", vec![]),
                ("X", vec!["O"]),
                ("Y", vec!["O"]),
                ("A", vec!["X", "Y"]),
                ("B", vec!["Y", "X"]),
                ("C", vec!["A", "B"]),
            ],
        );

        let class_c = create_target_base(&namespaces, namespace_location.clone(), "C");

        let class_c_mro = method_resolution_order(&class_c);

        assert_eq!(class_c_mro, None);

        let class_b = create_target_base(&namespaces, namespace_location.clone(), "B");

        let class_b_mro = method_resolution_order(&class_b).expect("Failed to compute MRO");

        assert_eq_mro(
            &namespaces,
            &namespace_location,
            class_b_mro,
            vec![
                (
                    get_class_location(&namespaces, namespace_location.clone(), "B"),
                    vec!["Y", "X"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "Y"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "X"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "O"),
                    vec![],
                ),
            ],
        );

        let class_a = create_target_base(&namespaces, namespace_location.clone(), "A");

        let class_a_mro = method_resolution_order(class_a).expect("Failed to compute MRO");

        assert_eq_mro(
            &namespaces,
            &namespace_location,
            class_a_mro,
            vec![
                (
                    get_class_location(&namespaces, namespace_location.clone(), "A"),
                    vec!["X", "Y"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "X"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "Y"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "O"),
                    vec![],
                ),
            ],
        );
    }

    #[test]
    fn test_difficult_mro() {
        let namespace_location = create_namespace_location();

        let namespaces = create_namespaces(
            namespace_location.clone(),
            vec![
                ("O", vec![]),
                ("F", vec!["O"]),
                ("E", vec!["O"]),
                ("D", vec!["O"]),
                ("C", vec!["D", "F"]),
                ("B", vec!["D", "E"]),
                ("A", vec!["B", "C"]),
            ],
        );

        let class_a = create_target_base(&namespaces, namespace_location.clone(), "A");

        let class_a_mro = method_resolution_order(class_a).expect("Failed to compute MRO");

        assert_eq_mro(
            &namespaces,
            &namespace_location,
            class_a_mro,
            vec![
                (
                    get_class_location(&namespaces, namespace_location.clone(), "A"),
                    vec!["B", "C"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "B"),
                    vec!["D", "E"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "C"),
                    vec!["D", "F"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "D"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "E"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "F"),
                    vec!["O"],
                ),
                (
                    get_class_location(&namespaces, namespace_location.clone(), "O"),
                    vec![],
                ),
            ],
        );
    }
}
