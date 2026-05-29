use crate::abstract_environment::{
    AbstractEnvironment, Attribute, ClassType, Deprecation, Diagnostic, Exception, FunctionType,
    ImportedAttribute, ImportedModuleType, LiteralClass, LiteralFunction, LiteralImportedModule,
    LocalAttribute, Parameter, ParameterKind, RaisedExceptions, Sourced, Type, TypeInstance,
    TypeLiteral, get_attribute,
};
use crate::analysis::cfg::nodes::Stmt;
use crate::analysis::cfg::{EdgeData, nodes};
use crate::analysis::namespace::{Location, NamespaceLocation, Namespaces};
use crate::genkill::annotations::gen_annotation;
use crate::genkill::assignment::AssignmentTarget;
use crate::genkill::calls::BoundArguments;
use crate::genkill::expressions::{GenExprResult, gen_expr};
use crate::genkill::visibility::gen_visibility;
use crate::worklist::WorklistContext;
use apy::OneOrMany;
use apy::v1::{Identifier, ParseIdentifierError, ParseQualifiedNameError, QualifiedName};
use apygen_analysis::lattice::NamespacesLattice;
use std::collections::HashMap;
use std::sync::Arc;

pub fn gen_assign(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_assign: &nodes::StmtAssign,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

    let gen_result = gen_expr(context, &location, &stmt_assign.value).map(|ty| Arc::new(ty));

    let mut target_abstract_environments: HashMap<EdgeData, AbstractEnvironment> = HashMap::new();

    if !gen_result.exceptions.exceptions.is_empty() {
        target_abstract_environments.insert(
            EdgeData::UnhandledException,
            target_abstract_environment
                .clone()
                .with_raised_exceptions(Sourced::inferred(gen_result.exceptions)),
        );
    }

    for target in &stmt_assign.targets {
        let target = AssignmentTarget::try_from(target);

        if let Ok(AssignmentTarget::Name(name)) = target {
            let visibility = gen_visibility(context.cfgs, &location.namespace_location, &name);

            target_abstract_environment.attributes.insert(
                Arc::new(name),
                Arc::new(Attribute::Local(
                    LocalAttribute::new(Sourced::inferred(gen_result.value.clone()))
                        .with_visibility(Sourced::inferred(visibility)),
                )),
            );
        }
    }

    target_abstract_environments.insert(EdgeData::Unconditional, target_abstract_environment);

    Ok(target_abstract_environments)
}

pub fn gen_return(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_return: &nodes::StmtReturn,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

    let gen_result = if let Some(value) = &stmt_return.value {
        gen_expr(context, &location, value)
    } else {
        GenExprResult::new(Type::new_literal(TypeLiteral::None))
    };

    let mut target_abstract_environments: HashMap<EdgeData, AbstractEnvironment> = HashMap::new();

    if !gen_result.exceptions.exceptions.is_empty() {
        target_abstract_environments.insert(
            EdgeData::UnhandledException,
            target_abstract_environment
                .clone()
                .with_raised_exceptions(Sourced::inferred(gen_result.exceptions)),
        );
    }

    target_abstract_environment.returned_value = target_abstract_environment
        .returned_value
        .join(
            &context.namespaces,
            &Some(Sourced::inferred(Arc::new(gen_result.value))),
        )
        .unwrap();

    target_abstract_environments.insert(EdgeData::Unconditional, target_abstract_environment);

    Ok(target_abstract_environments)
}

pub fn gen_raise(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_raise: &nodes::StmtRaise,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

    let gen_result = if let Some(value) = &stmt_raise.exc {
        gen_expr(context, &location, value)
    } else {
        GenExprResult::new(Type::Any) // TODO: use the previously raised exception
    };

    if !gen_result.exceptions.exceptions.is_empty() {
        target_abstract_environment
            .raised_exceptions
            .data
            .exceptions
            .extend(gen_result.exceptions.exceptions);
    }

    target_abstract_environment
        .raised_exceptions
        .data
        .exceptions
        .insert(Exception::from_type(gen_result.value));

    Ok(HashMap::from_iter([(
        EdgeData::UnhandledException,
        target_abstract_environment,
    )]))
}

pub fn gen_ann_assign(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_ann_assign: &nodes::StmtAnnAssign,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

    let expression =
        match gen_annotation(&context.namespaces, &location, &stmt_ann_assign.annotation) {
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

    let mut target_abstract_environments: HashMap<EdgeData, AbstractEnvironment> = HashMap::new();

    if let Some(value) = &stmt_ann_assign.value {
        let gen_result = gen_expr(context, &location, value);

        if !gen_result.exceptions.exceptions.is_empty() {
            target_abstract_environments.insert(
                EdgeData::UnhandledException,
                target_abstract_environment
                    .clone()
                    .with_raised_exceptions(Sourced::inferred(gen_result.exceptions)),
            );
        }

        // TODO: compare annotated type with inferred type
    }

    let target = AssignmentTarget::try_from(stmt_ann_assign.target.as_ref());

    if let Ok(AssignmentTarget::Name(name)) = target {
        let visibility = gen_visibility(context.cfgs, &location.namespace_location, &name);

        target_abstract_environment.attributes.insert(
            Arc::new(name),
            Arc::new(Attribute::Local(
                LocalAttribute::new(Sourced::specified(Arc::new(expression)))
                    .with_visibility(Sourced::inferred(visibility)),
            )),
        );
    }

    target_abstract_environments.insert(EdgeData::Unconditional, target_abstract_environment);

    Ok(target_abstract_environments)
}

pub fn gen_import(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_import: &nodes::StmtImport,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

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

        let visibility = gen_visibility(context.cfgs, &location.namespace_location, &root_package);

        let mut submodules = imbl::OrdSet::new();
        if let Ok(submodule_identifiers) = OneOrMany::try_from_iter(identifier_iter) {
            submodules.insert(Arc::new(QualifiedName {
                identifiers: submodule_identifiers,
            }));
        }

        target_abstract_environment.attributes.insert(
            Arc::new(name.identifiers.last().clone()),
            Arc::new(Attribute::Local(
                LocalAttribute::new(Sourced::inferred(Arc::new(Type::new_literal(
                    TypeLiteral::ImportedModule(LiteralImportedModule {
                        value: Arc::new(ImportedModuleType {
                            location: location.clone(),
                            module: Arc::new(QualifiedName {
                                identifiers: OneOrMany::one(root_package),
                            }),
                            submodules,
                        }),
                    }),
                ))))
                .with_visibility(Sourced::inferred(visibility)),
            )),
        );

        let module_location = NamespaceLocation::from(module);
        context.import(module_location.clone());
        context.add_dependent(module_location, location.namespace_location.clone());
    }

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_import_from(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_import_from: &nodes::StmtImportFrom,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

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

    let namespace_location = NamespaceLocation::from(Arc::new(qualified_name));

    for alias in &stmt_import_from.names {
        let Ok(name) =
            Identifier::try_parse(alias.asname.as_ref().unwrap_or(&alias.name).id.as_ref())
        else {
            continue;
        };

        let visibility = gen_visibility(&context.cfgs, &location.namespace_location, &name);
        let identifier = Identifier::try_parse(alias.name.id.as_ref())?;

        match get_attribute(
            &context.namespaces,
            &Location::at_exit(namespace_location.clone()),
            &identifier,
        ) {
            Ok(_) if namespace_location != location.namespace_location => {
                target_abstract_environment.attributes.insert(
                    Arc::new(name),
                    Arc::new(Attribute::Imported(ImportedAttribute {
                        module: namespace_location.module.clone(),
                        visibility: Sourced::inferred(visibility),
                        name: identifier,
                        deprecation: Sourced::inferred(Deprecation::NotDeprecated),
                    })),
                );
            }
            _ => {
                let submodule = {
                    let mut identifiers = namespace_location.module.identifiers.clone();
                    identifiers.push(identifier);
                    Arc::new(QualifiedName { identifiers })
                };

                if context.cfgs.contains_key(&submodule) {
                    target_abstract_environment.attributes.insert(
                        Arc::new(name),
                        Arc::new(Attribute::Local(
                            LocalAttribute::new(Sourced::inferred(Arc::new(Type::new_literal(
                                TypeLiteral::ImportedModule(LiteralImportedModule {
                                    value: Arc::new(ImportedModuleType {
                                        location: location.clone(),
                                        module: submodule.clone(),
                                        submodules: imbl::OrdSet::new(),
                                    }),
                                }),
                            ))))
                            .with_visibility(Sourced::inferred(visibility)),
                        )),
                    );
                }
            }
        };
    }

    context.import(namespace_location.clone());
    context.add_dependent(namespace_location, location.namespace_location);

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_parameter(
    context: &mut WorklistContext,
    location: &Location<QualifiedName>,
    parameter: &nodes::Parameter,
    kind: ParameterKind,
    default: Option<&Box<nodes::Expr>>,
) -> Result<(Parameter, Option<Sourced<Arc<Type>>>), ParseIdentifierError> {
    let annotation_ty = match &parameter.annotation {
        Some(annotation) => gen_annotation(&context.namespaces, location, annotation.as_ref())
            .ok()
            .map(|ty| Sourced::specified(Arc::new(ty))),
        None => None,
    };

    let ty = annotation_ty.or_else(|| {
        default.map(|default| {
            Sourced::inferred(Arc::new(
                gen_expr(context, location, default.as_ref()).value,
            ))
        })
    });

    Ok((
        Parameter {
            name: Arc::new(Identifier::try_parse(parameter.name.id.as_ref())?),
            deprecation: Deprecation::NotDeprecated,
            kind,
            is_optional: default.is_some()
                || matches!(
                    kind,
                    ParameterKind::VarPositional | ParameterKind::VarKeyword
                ),
        },
        ty,
    ))
}

pub fn gen_function_def(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_function_def: &nodes::StmtFunctionDef,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

    let name = Identifier::try_parse(stmt_function_def.name.id.as_ref())?;

    let mut parameters: imbl::Vector<Parameter> = imbl::Vector::new();
    let mut bound_arguments = BoundArguments::new();
    for positional_parameter in &stmt_function_def.parameters.posonlyargs {
        let (parameter, ty) = gen_parameter(
            context,
            &location,
            &positional_parameter.parameter,
            ParameterKind::PositionalOnly,
            positional_parameter.default.as_ref(),
        )?;
        parameters.push_back(parameter.clone());
        bound_arguments.variables.insert(parameter, ty);
    }
    for positional_or_keyword_parameter in &stmt_function_def.parameters.args {
        let (parameter, ty) = gen_parameter(
            context,
            &location,
            &positional_or_keyword_parameter.parameter,
            ParameterKind::PositionalOrKeyword,
            positional_or_keyword_parameter.default.as_ref(),
        )?;
        parameters.push_back(parameter.clone());
        bound_arguments.variables.insert(parameter, ty);
    }
    if let Some(var_positional_parameter) = &stmt_function_def.parameters.vararg {
        let (parameter, ty) = gen_parameter(
            context,
            &location,
            &var_positional_parameter,
            ParameterKind::VarPositional,
            None,
        )?;
        parameters.push_back(parameter.clone());
        bound_arguments.variables.insert(
            parameter,
            ty.map(|ty| {
                ty.map(|ty| {
                    Arc::new(Type::Instance(TypeInstance::builtins_tuple([
                        ty,
                        Arc::new(Type::new_literal(TypeLiteral::Ellipsis)),
                    ])))
                })
            }),
        );
    }
    for keyword_parameter in &stmt_function_def.parameters.kwonlyargs {
        let (parameter, ty) = gen_parameter(
            context,
            &location,
            &keyword_parameter.parameter,
            ParameterKind::KeywordOnly,
            keyword_parameter.default.as_ref(),
        )?;
        parameters.push_back(parameter.clone());
        bound_arguments.variables.insert(parameter, ty);
    }
    if let Some(var_keyword_parameter) = &stmt_function_def.parameters.kwarg {
        let (parameter, ty) = gen_parameter(
            context,
            &location,
            &var_keyword_parameter,
            ParameterKind::VarKeyword,
            None,
        )?;
        parameters.push_back(parameter.clone());
        bound_arguments.variables.insert(
            parameter,
            ty.map(|ty| {
                ty.map(|ty| {
                    Arc::new(Type::Instance(TypeInstance::builtins_dict(
                        Arc::new(Type::Instance(TypeInstance::builtins("str"))),
                        ty,
                    )))
                })
            }),
        );
    }
    context.add_call(location.as_sub_location(), bound_arguments);
    if let Some(return_annotation) = &stmt_function_def.returns {
        if let Ok(ty) = gen_annotation(&context.namespaces, &location, return_annotation) {
            context.add_return(location.as_sub_location(), Arc::new(ty));
        }
    }

    let visibility = gen_visibility(context.cfgs, &location.namespace_location, &name);
    target_abstract_environment.attributes.insert(
        Arc::new(name),
        Arc::new(Attribute::Local(
            LocalAttribute::new(Sourced::inferred(Arc::new(Type::new_literal(
                TypeLiteral::Function(LiteralFunction {
                    value: Arc::new(FunctionType {
                        location: location.clone(),
                        generics: imbl::OrdMap::new(),
                        is_async: stmt_function_def.is_async,
                        parameters,
                    }),
                }),
            ))))
            .with_visibility(Sourced::inferred(visibility)),
        )),
    );

    context.add_dependent(
        location.namespace_location.clone(),
        location.as_sub_location(),
    );

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_class_def(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    stmt_class_def: &nodes::StmtClassDef,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    let mut target_abstract_environment = context.clone_abstract_environment(&location);

    let name = Identifier::try_parse(stmt_class_def.name.id.as_ref())?;
    let visibility = gen_visibility(context.cfgs, &location.namespace_location, &name);
    target_abstract_environment.attributes.insert(
        Arc::new(name),
        Arc::new(Attribute::Local(
            LocalAttribute::new(Sourced::inferred(Arc::new(Type::new_literal(
                TypeLiteral::Class(LiteralClass {
                    value: Arc::new(ClassType {
                        location: location.clone(),
                        generics: imbl::OrdMap::new(),
                        bases: imbl::Vector::new(),
                        is_abstract: false,
                        keyword_arguments: imbl::OrdMap::new(),
                    }),
                }),
            ))))
            .with_visibility(Sourced::inferred(visibility)),
        )),
    );

    context.add_dependent(
        location.namespace_location.clone(),
        location.as_sub_location(),
    );

    Ok(HashMap::from_iter([(
        EdgeData::Unconditional,
        target_abstract_environment,
    )]))
}

pub fn gen_statement<'a>(
    context: &mut WorklistContext,
    location: Location<QualifiedName>,
    statement: &Stmt,
) -> Result<HashMap<EdgeData, AbstractEnvironment>, ParseQualifiedNameError> {
    match statement {
        Stmt::AnnAssign(stmt_ann_assign) => gen_ann_assign(context, location, &stmt_ann_assign),
        Stmt::Return(stmt_return) => gen_return(context, location, &stmt_return),
        Stmt::Raise(stmt_raise) => gen_raise(context, location, &stmt_raise),
        Stmt::Assign(stmt_assign) => gen_assign(context, location, &stmt_assign),
        Stmt::Import(stmt_import) => gen_import(context, location, &stmt_import),
        Stmt::ImportFrom(stmt_import_from) => gen_import_from(context, location, &stmt_import_from),
        Stmt::FunctionDef(stmt_function_def) => {
            gen_function_def(context, location, &stmt_function_def)
        }
        Stmt::ClassDef(stmt_class_def) => gen_class_def(context, location, &stmt_class_def),
        _ => Ok(HashMap::from_iter([(
            EdgeData::Unconditional,
            context
                .namespaces
                .get_abstract_environment(&location)
                .cloned()
                .unwrap_or_default(),
        )])),
    }
}
