use crate::inference::LiteralClass;
use std::collections::VecDeque;

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

#[cfg(test)]
mod tests {
    use crate::expressions::literal_class::method_resolution_order;
    use crate::identifiers::NamedQualifiedLocation;
    use crate::inference::{ClassType, LiteralClass};
    use apy::v1::{Identifier, QualifiedName};
    use apygen_constraint_graph::expressions::{Location, Namespace};
    use std::collections::VecDeque;
    use std::sync::Arc;

    fn create_classes(classes: &[(&str, Vec<&str>)]) -> imbl::OrdMap<String, LiteralClass> {
        let namespace = Arc::new(Namespace::Module(Arc::new(QualifiedName::parse(
            "test_module",
        ))));

        let mut literal_classes: imbl::OrdMap<String, LiteralClass> = imbl::OrdMap::new();

        for (line, (name, bases)) in classes.iter().enumerate() {
            let identifier = Arc::new(Identifier::parse(name));
            literal_classes.insert(
                identifier.as_ref().as_ref().to_owned(),
                LiteralClass {
                    value: Arc::new(ClassType {
                        program_entity: NamedQualifiedLocation::new(
                            identifier,
                            Location::new(line, 0),
                            namespace.clone(),
                        ),
                        generics: imbl::OrdMap::new(),
                        bases: bases
                            .iter()
                            .filter_map(|base| Some(literal_classes.get(*base)?.clone()))
                            .collect(),
                        keyword_arguments: imbl::OrdMap::new(),
                        is_abstract: false,
                    }),
                },
            );
        }

        literal_classes
    }

    fn assert_eq_mro(actual_mro: Option<VecDeque<&LiteralClass>>, expected_mro: &[&str]) {
        let Some(actual_mro) = actual_mro else {
            panic!("Expected MRO {:?}, but got None", expected_mro);
        };
        assert_eq!(
            actual_mro
                .iter()
                .map(|literal_class| literal_class.value.program_entity.name.as_ref().as_ref())
                .collect::<Vec<_>>(),
            expected_mro
        );
    }

    #[test]
    fn test_linear_mro() {
        let classes = create_classes(&[("A", vec![]), ("B", vec!["A"]), ("C", vec!["B"])]);

        let class_c_mro = method_resolution_order(&classes["C"]);
        assert_eq_mro(class_c_mro, &["C", "B", "A"]);

        let class_b_mro = method_resolution_order(&classes["B"]);
        assert_eq_mro(class_b_mro, &["B", "A"]);

        let class_a_mro = method_resolution_order(&classes["A"]);
        assert_eq_mro(class_a_mro, &["A"]);
    }

    #[test]
    fn test_impossible_mro() {
        let classes = create_classes(&[
            ("O", vec![]),
            ("X", vec!["O"]),
            ("Y", vec!["O"]),
            ("A", vec!["X", "Y"]),
            ("B", vec!["Y", "X"]),
            ("C", vec!["A", "B"]),
        ]);

        let class_c_mro = method_resolution_order(&classes["C"]);
        assert_eq!(class_c_mro, None);

        let class_b_mro = method_resolution_order(&classes["B"]);
        assert_eq_mro(class_b_mro, &["B", "Y", "X", "O"]);

        let class_a_mro = method_resolution_order(&classes["A"]);
        assert_eq_mro(class_a_mro, &["A", "X", "Y", "O"]);
    }

    #[test]
    fn test_difficult_mro() {
        let classes = create_classes(&[
            ("O", vec![]),
            ("F", vec!["O"]),
            ("E", vec!["O"]),
            ("D", vec!["O"]),
            ("C", vec!["D", "F"]),
            ("B", vec!["D", "E"]),
            ("A", vec!["B", "C"]),
        ]);

        let class_a_mro = method_resolution_order(&classes["A"]);
        assert_eq_mro(class_a_mro, &["A", "B", "C", "D", "E", "F", "O"]);
    }
}
