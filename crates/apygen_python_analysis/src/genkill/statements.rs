use crate::abstract_environment::{AbstractEnvironment, Attribute, ClassType, Diagnostic, FunctionType, ImportedAttribute, ImportedModuleType, LiteralClass, LiteralFunction, LiteralImportedModule, LocalAttribute, Type, TypeLiteral};
use crate::analysis::cfg::nodes::Stmt;
use crate::analysis::cfg::{Cfg, EdgeData, nodes};
use crate::analysis::namespace::{Location, NamespaceLocation, NamespacesContext};
use crate::genkill::annotations::{gen_annotation, get_type};
use crate::genkill::assignment::AssignmentTarget;
use crate::genkill::expressions::gen_expr;
use crate::genkill::visibility::gen_visibility;
use apy::OneOrMany;
use apy::v1::{FromInvalidQualifiedNameError, Identifier, QualifiedName};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::mpsc::Sender;

pub fn gen_assign(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    location: Location<QualifiedName>,
    stmt_assign: &nodes::StmtAssign,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    let gen_result = gen_expr(context, &location, &stmt_assign.value).map(|ty| Arc::new(ty));

    for target in &stmt_assign.targets {
        let target = AssignmentTarget::try_from(target);

        if let Ok(AssignmentTarget::Name(name)) = target {
            let visibility = gen_visibility(cfgs, &location, &name);

            target_abstract_environment.attributes.insert(
                Arc::new(name),
                Arc::new(Attribute::Local(LocalAttribute {
                    attribute_type: gen_result.value.clone(),
                    is_deprecated: false,
                    is_final: false,
                    is_initialised: false,
                    is_readonly: false,
                    visibility,
                })),
            );
        }
    }

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_return(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    location: Location<QualifiedName>,
    stmt_return: &nodes::StmtReturn,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    if let Some(value) = &stmt_return.value {
        let gen_result = gen_expr(context, &location, value);
        target_abstract_environment.returned_value = Some(gen_result.value);
    } else {
        target_abstract_environment.returned_value = None;
    }

    Ok(HashMap::from_iter([(
        EdgeData::Return,
        target_abstract_environment,
    )]))
}

pub fn gen_ann_assign(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    location: Location<QualifiedName>,
    stmt_ann_assign: &nodes::StmtAnnAssign,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    let expression = match gen_annotation(context, &location, &stmt_ann_assign.annotation) {
        Ok(ty) => ty,
        Err(_) => {
            target_abstract_environment
                .diagnostics
                .insert(Diagnostic::InvalidAnnotation {
                    location: location.clone(),
                });
            Type::Any
        }
    };

    let target = AssignmentTarget::try_from(stmt_ann_assign.target.as_ref());

    if let Ok(AssignmentTarget::Name(name)) = target {
        let visibility = gen_visibility(cfgs, &location, &name);

        target_abstract_environment.attributes.insert(
            Arc::new(name),
            Arc::new(Attribute::Local(LocalAttribute {
                attribute_type: Arc::new(expression),
                is_deprecated: false,
                is_final: false,
                is_initialised: false,
                is_readonly: false,
                visibility,
            })),
        );
    }

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_import(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    import_tx: &Sender<NamespaceLocation<QualifiedName>>,
    location: Location<QualifiedName>,
    stmt_import: &nodes::StmtImport,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    for alias in &stmt_import.names {
        let module = QualifiedName::try_from(alias.name.id.as_ref())?;

        let Ok(name) =
            QualifiedName::try_from(alias.asname.as_ref().unwrap_or(&alias.name).id.as_ref())
        else {
            println!(
                "Invalid import alias: {}",
                alias.asname.as_ref().unwrap_or(&alias.name).id
            );
            continue;
        };

        let mut identifier_iter = module.identifiers.clone().into_iter();

        let root_package = identifier_iter
            .next()
            .expect("OneOrMany always has at least one element");

        let visibility = gen_visibility(cfgs, &location.clone(), &root_package);

        let mut submodules = imbl::OrdSet::new();
        if let Ok(submodule_identifiers) = OneOrMany::try_from_iter(identifier_iter) {
            submodules.insert(Arc::new(QualifiedName {
                identifiers: submodule_identifiers,
            }));
        }

        target_abstract_environment.attributes.insert(
            Arc::new(name.identifiers.last().clone()),
            Arc::new(Attribute::Local(LocalAttribute {
                attribute_type: Arc::new(Type::new_literal(TypeLiteral::ImportedModule(
                    LiteralImportedModule {
                        value: Arc::new(ImportedModuleType {
                            location: location.clone(),
                            module: Arc::new(QualifiedName {
                                identifiers: OneOrMany::one(root_package),
                            }),
                            submodules,
                        }),
                    },
                ))),
                is_deprecated: false,
                is_final: false,
                is_initialised: true,
                is_readonly: false,
                visibility,
            })),
        );

        let module_location = NamespaceLocation::from(module);
        import_tx
            .send(module_location.clone())
            .expect("Should send module location to import channel");
        dependents
            .entry(module_location)
            .or_default()
            .insert(location.namespace_location.clone());
    }

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_import_from(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    import_tx: &Sender<NamespaceLocation<QualifiedName>>,
    location: Location<QualifiedName>,
    stmt_import_from: &nodes::StmtImportFrom,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    let mut level = stmt_import_from.level;
    let mut qualified_name = location.namespace_location.module.as_ref().clone();
    while level > 0 {
        qualified_name.identifiers.pop();
        level -= 1;
    }
    if let Some(module_name) = &stmt_import_from.module {
        let module = QualifiedName::try_from(module_name.id.as_ref())?;
        if stmt_import_from.level == 0 {
            qualified_name = module;
        } else {
            qualified_name.identifiers.extend(module.identifiers);
        }
    }

    let module = Arc::new(qualified_name);

    for alias in &stmt_import_from.names {
        let Ok(name) =
            Identifier::try_from(alias.asname.as_ref().unwrap_or(&alias.name).id.as_ref())
        else {
            continue;
        };

        let visibility = gen_visibility(cfgs, &location, &name);

        match get_type(
            context,
            &Location::from(module.clone()),
            &QualifiedName::try_from(alias.name.id.as_ref())?,
        ) {
            Ok(_) => {
                target_abstract_environment.attributes.insert(
                    Arc::new(name),
                    Arc::new(Attribute::Imported(ImportedAttribute {
                        module: module.clone(),
                        visibility,
                        name: Identifier::try_from(alias.name.id.as_ref())?,
                        is_deprecated: false,
                    })),
                );
            }
            Err(_) => {
                let submodule = {
                    let mut identifiers = module.identifiers.clone();
                    identifiers.push(Identifier::try_from(alias.name.id.as_ref())?);
                    Arc::new(QualifiedName { identifiers })
                };

                if cfgs.contains_key(&submodule) {
                    target_abstract_environment.attributes.insert(
                        Arc::new(name),
                        Arc::new(Attribute::Local(LocalAttribute {
                            attribute_type: Arc::new(Type::new_literal(
                                TypeLiteral::ImportedModule(LiteralImportedModule {
                                    value: Arc::new(ImportedModuleType {
                                        location: location.clone(),
                                        module: submodule.clone(),
                                        submodules: imbl::OrdSet::new(),
                                    }),
                                }),
                            )),
                            is_deprecated: false,
                            is_final: false,
                            is_initialised: true,
                            is_readonly: false,
                            visibility,
                        })),
                    );
                }
            }
        };
    }

    let module_location = NamespaceLocation::from(module);
    import_tx
        .send(module_location.clone())
        .expect("Should send module location to import channel");
    dependents
        .entry(module_location)
        .or_default()
        .insert(location.namespace_location);

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_function_def(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    location: Location<QualifiedName>,
    stmt_function_def: &nodes::StmtFunctionDef,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    let name = Identifier::try_from(stmt_function_def.name.id.as_ref())?;
    let visibility = gen_visibility(cfgs, &location, &name);
    target_abstract_environment.attributes.insert(
        Arc::new(name),
        Arc::new(Attribute::Local(LocalAttribute {
            attribute_type: Arc::new(Type::new_literal(TypeLiteral::Function(LiteralFunction {
                value: Arc::new(FunctionType {
                    location: location.clone(),
                    generics: imbl::OrdMap::new(),
                    is_async: stmt_function_def.is_async,
                    parameters: Vec::new(),
                }),
            }))),
            is_deprecated: false,
            is_final: false,
            is_initialised: true,
            is_readonly: false,
            visibility,
        })),
    );

    dependents
        .entry(location.namespace_location.clone())
        .or_default()
        .insert(
            location
                .namespace_location
                .sub_location(location.program_point.id()),
        );

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_class_def(
    context: &impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    location: Location<QualifiedName>,
    stmt_class_def: &nodes::StmtClassDef,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    let mut target_abstract_environment = context
        .get_abstract_environment(&location)
        .cloned()
        .unwrap_or_default();

    let name = Identifier::try_from(stmt_class_def.name.id.as_ref())?;
    let visibility = gen_visibility(cfgs, &location, &name);
    target_abstract_environment.attributes.insert(
        Arc::new(name),
        Arc::new(Attribute::Local(LocalAttribute {
            attribute_type: Arc::new(Type::new_literal(TypeLiteral::Class(LiteralClass {
                value: Arc::new(ClassType {
                    location: location.clone(),
                    generics: imbl::OrdMap::new(),
                    bases: imbl::Vector::new(),
                    is_abstract: false,
                    keyword_arguments: imbl::OrdMap::new(),
                }),
            }))),
            is_deprecated: false,
            is_final: false,
            is_initialised: true,
            is_readonly: false,
            visibility,
        })),
    );

    dependents
        .entry(location.namespace_location.clone())
        .or_default()
        .insert(
            location
                .namespace_location
                .sub_location(location.program_point.id()),
        );

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_statement(
    context: &mut impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    import_tx: &Sender<NamespaceLocation<QualifiedName>>,
    location: Location<QualifiedName>,
    statement: &Stmt,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, FromInvalidQualifiedNameError> {
    match statement {
        Stmt::AnnAssign(stmt_ann_assign) => {
            gen_ann_assign(context, cfgs, location, &stmt_ann_assign)
        }
        Stmt::Return(stmt_return) => gen_return(context, location, &stmt_return),
        Stmt::Assign(stmt_assign) => gen_assign(context, cfgs, location, &stmt_assign),
        Stmt::Import(stmt_import) => {
            gen_import(context, dependents, cfgs, import_tx, location, &stmt_import)
        }
        Stmt::ImportFrom(stmt_import_from) => gen_import_from(
            context,
            dependents,
            cfgs,
            import_tx,
            location,
            &stmt_import_from,
        ),
        Stmt::FunctionDef(stmt_function_def) => {
            gen_function_def(context, dependents, cfgs, location, &stmt_function_def)
        }
        Stmt::ClassDef(stmt_class_def) => {
            gen_class_def(context, dependents, cfgs, location, &stmt_class_def)
        }
        _ => Ok(HashMap::from_iter([(
            EdgeData::Unconditional,
            context
                .get_abstract_environment(&location)
                .cloned()
                .unwrap_or_default(),
        )])),
    }
}
