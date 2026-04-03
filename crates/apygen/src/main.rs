use apy;
use apy::Value;
use apy::v1::{PythonValue, QualifiedName, TypeArgument};
use apygen_python_analysis::abstract_environment::{
    AbstractEnvironment, Attribute, Type, TypeLiteral,
};
use apygen_python_analysis::analysis::namespace::{
    Location, NamespaceLocation, Namespaces, NamespacesContext,
};
use apygen_python_analysis::finder::filesystem::{AbsolutePathBuf, Filesystem, LocalFilesystem};
use apygen_python_analysis::finder::pathfinder::{FileLoader, ModuleSpec, PathFinder};
use apygen_python_analysis::genkill::visibility::visibility_from_module_name;
use apygen_python_analysis::worklist::cfg_worklist;
use rayon::prelude::*;
use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::path::PathBuf;
use std::sync::Arc;

fn add_attributes(
    namespaces: &Namespaces<apy::v1::QualifiedName, AbstractEnvironment>,
    namespace_location: NamespaceLocation<apy::v1::QualifiedName>,
    abstract_environment: &AbstractEnvironment,
) -> BTreeMap<apy::v1::Identifier, apy::OneOrMany<apy::v1::Attribute>> {
    let mut attributes: BTreeMap<apy::v1::Identifier, apy::OneOrMany<apy::v1::Attribute>> =
        BTreeMap::new();

    for (name, attribute) in &abstract_environment.attributes {
        let apy_attribute = match attribute.as_ref() {
            Attribute::Local(local_attribute) => match local_attribute.attribute_type.as_ref() {
                Type::Literal(literal_value) => match literal_value.as_ref() {
                    TypeLiteral::List(list_literal) => {
                        apy::v1::Attribute::Variable(apy::v1::Variable {
                            variable_type: apy::v1::Type {
                                id: QualifiedName::try_from("list").unwrap(),
                                history_index: 0,
                                arguments: Vec::new(),
                                extensions: Default::default(),
                            },
                            description: "".to_owned(),
                            is_initialised: true,
                            is_readonly: false,
                            visibility: local_attribute.visibility,
                            is_deprecated: local_attribute.is_deprecated,
                            extensions: BTreeMap::new(),
                            is_final: false,
                        })
                    }
                    TypeLiteral::Tuple(list_literal) => {
                        apy::v1::Attribute::Variable(apy::v1::Variable {
                            variable_type: apy::v1::Type {
                                id: QualifiedName::try_from("tuple").unwrap(),
                                history_index: 0,
                                arguments: Vec::new(),
                                extensions: Default::default(),
                            },
                            description: "".to_owned(),
                            is_initialised: true,
                            is_readonly: false,
                            visibility: local_attribute.visibility,
                            is_deprecated: local_attribute.is_deprecated,
                            extensions: BTreeMap::new(),
                            is_final: false,
                        })
                    }
                    TypeLiteral::String(string_literal) => {
                        apy::v1::Attribute::Variable(apy::v1::Variable {
                            variable_type: apy::v1::Type {
                                id: QualifiedName::try_from("Literal").unwrap(),
                                history_index: 0,
                                arguments: Vec::from_iter([TypeArgument::Value {
                                    value: PythonValue::Str {
                                        str: string_literal.value.as_ref().clone(),
                                    },
                                }]),
                                extensions: Default::default(),
                            },
                            description: "".to_owned(),
                            is_initialised: true,
                            is_readonly: false,
                            visibility: local_attribute.visibility,
                            is_deprecated: local_attribute.is_deprecated,
                            extensions: BTreeMap::new(),
                            is_final: false,
                        })
                    }
                    TypeLiteral::Integer(integer) => {
                        apy::v1::Attribute::Variable(apy::v1::Variable {
                            variable_type: apy::v1::Type {
                                id: QualifiedName::try_from("Literal").unwrap(),
                                history_index: 0,
                                arguments: Vec::from_iter([TypeArgument::Value {
                                    value: PythonValue::Int {
                                        int: integer.value.to_string(),
                                    },
                                }]),
                                extensions: Default::default(),
                            },
                            description: "".to_owned(),
                            is_initialised: true,
                            is_readonly: false,
                            visibility: local_attribute.visibility,
                            is_deprecated: local_attribute.is_deprecated,
                            extensions: BTreeMap::new(),
                            is_final: false,
                        })
                    }
                    TypeLiteral::ImportedModule(module_reference) => {
                        apy::v1::Attribute::ImportedModule(apy::v1::ImportedModule {
                            module: module_reference.value.module.as_ref().clone(),
                            is_deprecated: local_attribute.is_deprecated,
                            visibility: local_attribute.visibility,
                            extensions: BTreeMap::new(),
                        })
                    }
                    TypeLiteral::Function(function_type) => {
                        apy::v1::Attribute::Function(apy::v1::Function {
                            signature: apy::OneOrMany::one(apy::v1::Signature {
                                parameters: apy::v1::Parameters::new(),
                                generics: BTreeMap::new(),
                                visibility: local_attribute.visibility,
                                is_deprecated: local_attribute.is_deprecated,
                                is_partial: false,
                                raises: Vec::new(),
                                summary: String::new(),
                                return_type: apy::v1::Type::new(
                                    apy::v1::QualifiedName::try_from("Any").unwrap(),
                                ),
                                description: String::new(),
                                is_pure: false,
                                extensions: {
                                    let mut variables: Vec<Value> = Vec::new();
                                    if let Some(env) = namespaces.get_abstract_environment(
                                        &Location::at_exit(namespace_location.sub_location(
                                            function_type.value.location.program_point.id(),
                                        )),
                                    ) {
                                        for variable_name in env.attributes.keys() {
                                            variables
                                                .push(Value::String(variable_name.to_string()));
                                        }
                                    }
                                    BTreeMap::from_iter([(
                                        "variables".to_string(),
                                        Value::Array(variables),
                                    )])
                                },
                            }),
                            is_async: false,
                            is_overriding: false,
                            is_abstract: false,
                            is_final: false,
                            extensions: BTreeMap::new(),
                        })
                    }
                    TypeLiteral::Class(class_type) => {
                        let Some(class_abstract_environment) =
                            namespaces.get_abstract_environment(&Location::at_exit(
                                class_type
                                    .value
                                    .location
                                    .namespace_location
                                    .sub_location(class_type.value.location.program_point.id()),
                            ))
                        else {
                            continue;
                        };
                        apy::v1::Attribute::Class(apy::v1::Class {
                            summary: "".to_string(),
                            description: "".to_string(),
                            generics: Default::default(),
                            bases: vec![],
                            keyword_arguments: Default::default(),
                            visibility: Default::default(),
                            is_abstract: false,
                            is_final: false,
                            is_deprecated: false,
                            raises: vec![],
                            is_partial: false,
                            attributes: add_attributes(
                                namespaces,
                                namespace_location.clone(),
                                class_abstract_environment,
                            ),
                            typing_attributes: Default::default(),
                            extensions: Default::default(),
                        })
                    }
                    _ => continue,
                },
                Type::Reference { name, .. } => apy::v1::Attribute::Variable(apy::v1::Variable {
                    variable_type: apy::v1::Type {
                        id: name.clone(),
                        history_index: 0,
                        arguments: Vec::new(),
                        extensions: Default::default(),
                    },
                    description: "".to_owned(),
                    is_initialised: false,
                    is_readonly: false,
                    visibility: local_attribute.visibility,
                    is_deprecated: local_attribute.is_deprecated,
                    extensions: BTreeMap::new(),
                    is_final: false,
                }),
                _ => continue,
            },
            Attribute::Imported(imported_attribute) => {
                apy::v1::Attribute::ImportedAttribute(apy::v1::ImportedAttribute {
                    attribute: imported_attribute.name.clone(),
                    module: imported_attribute.module.as_ref().clone(),
                    is_deprecated: imported_attribute.is_deprecated,
                    visibility: imported_attribute.visibility,
                    extensions: BTreeMap::new(),
                })
            }
        };

        attributes.insert(name.as_ref().clone(), apy::OneOrMany::one(apy_attribute));
    }

    attributes
}

fn is_inside(module_spec: &ModuleSpec<impl Filesystem>, dir: &AbsolutePathBuf) -> bool {
    if module_spec.is_package() {
        module_spec
            .submodule_search_locations
            .iter()
            .any(|location| location.starts_with(dir))
    } else {
        match &module_spec.file_loader {
            FileLoader::SourceFileLoader { path, .. } => path.starts_with(dir),
            FileLoader::ExtensionFileLoader { path, .. } => path.starts_with(dir),
            FileLoader::NamespaceLoader => false,
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let python_paths = vec![];
    let working_dir = AbsolutePathBuf::try_from(PathBuf::from("."))?;

    let finder = PathFinder::new(Arc::new(LocalFilesystem), python_paths);

    let module_specs = finder.get_all_specs();

    let initial_worklist: HashSet<_> = module_specs
        .par_iter()
        .filter_map(|(qualified_name, module_spec)| {
            if is_inside(module_spec, &working_dir) {
                Some(qualified_name.clone())
            } else {
                None
            }
        })
        .collect();

    let (namespaces, cfgs) = cfg_worklist(module_specs, initial_worklist).unwrap();

    let modules = cfgs
        .into_par_iter()
        .filter_map(|(module, _)| {
            if !module.identifiers.first().starts_with("pynguin") {
                return None;
            }
            let namespace_location = NamespaceLocation::new(module.clone());
            let Some(abstract_environment) = namespaces
                .locations
                .get(&namespace_location)
                .and_then(|data| data.at_exit())
            else {
                return None;
            };

            let apy_module = apy::v1::Module {
                summary: String::new(),
                description: String::new(),
                visibility: visibility_from_module_name(&module),
                raises: Vec::new(),
                is_partial: abstract_environment.is_partial,
                attributes: apy::v1::ModuleAttributes::try_from(add_attributes(
                    &namespaces,
                    namespace_location,
                    abstract_environment,
                ))
                .ok()?,
                typing_attributes: apy::v1::ModuleAttributes::new(),
                extensions: BTreeMap::new(),
            };

            Some((module.as_ref().clone(), apy_module))
        })
        .collect();

    let apy_v1_spec = apy::v1::ApyV1 {
        modules,
        extensions: BTreeMap::new(),
    };

    let apy_spec = apy::Apy::V1(apy_v1_spec);

    apy_spec.to_json_writer(File::create("apy.json")?)?;
    apy_spec.to_yaml_writer(&mut File::create("apy.yaml")?)?;

    Ok(())
}
