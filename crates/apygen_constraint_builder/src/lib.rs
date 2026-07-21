pub use apygen_analysis as analysis;
pub use apygen_cfg as cfg;
pub use apygen_constraint_graph as constraint_graph;
pub use apygen_finder as finder;

use crate::analysis::lattice::{Join, OrdJoin};
use crate::analysis::{DummyAnalysisObserver, GraphAnalyser, analysis};
use crate::cfg::ast;
use crate::cfg::build_cfg;
use crate::cfg::convert_text_size_to_location;
use crate::cfg::parser::parse_module;
use crate::cfg::source_file::LineIndex;
use crate::cfg::text_size::Ranged;
use crate::cfg::{Cfg, CfgEdge, CfgEdgeKind, CfgNode as StmtNode, ProgramPoint};
use crate::constraint_graph::expressions::{
    BinaryOperator, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionFunction, ExpressionImport, ExpressionOverride,
    ExpressionSubscript, ExpressionUnary, ExpressionVariable, KeywordArgument, UnaryOperator,
};
use crate::constraint_graph::identifiers::{
    Identifier, Location, ModuleName, NamedQualifiedLocation, Namespace, OneOrMany,
    ParseIdentifierError, QualifiedName, VariableName,
};
use crate::constraint_graph::primitives::literals::{
    LiteralBool, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInt, LiteralStr,
};
use crate::constraint_graph::primitives::{BigInt, Complex64, Int, Num};
use crate::constraint_graph::{
    Constraint, ConstraintGraph, ConstraintNode, Guard, IncludeConstraint, ModuleDependentGraph,
    ModuleNode, ProgramEntityConstraints, ProgramEntitySpecification, ReturnConstraint,
};
use crate::finder::filesystem::{Error as FilesystemError, Filesystem};
use crate::finder::pathfinder::{FinderSpec, ModuleKind, ModuleSpec, Spec, StubSpec};

use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelBridge;
use rayon::iter::ParallelIterator;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;
use thiserror::Error;

pub const BUILTINS_MODULE: &str = "builtins";

#[derive(Debug, Error)]
pub enum FromAssignmentTargetError {
    #[error("the expression contains an invalid identifier")]
    InvalidIdentifier(#[from] ParseIdentifierError),
    #[error("the expression is not a valid assignment target")]
    InvalidTarget,
}

pub enum AssignmentTarget<'e> {
    Name(Identifier),
    Attribute {
        target: Box<AssignmentTarget<'e>>,
        attr: Identifier,
    },
    Subscript {
        target: Box<AssignmentTarget<'e>>,
        slice: &'e ast::Expr,
    },
    Starred(Box<AssignmentTarget<'e>>),
    Tuple(Vec<AssignmentTarget<'e>>),
    List(Vec<AssignmentTarget<'e>>),
}

impl TryFrom<&ast::ExprName> for AssignmentTarget<'_> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &ast::ExprName) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Name(Identifier::try_parse(
            value.id.as_ref(),
        )?))
    }
}

impl<'e> TryFrom<&'e ast::ExprAttribute> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::ExprAttribute) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Attribute {
            attr: Identifier::try_parse(value.attr.id.as_ref())?,
            target: Box::new(AssignmentTarget::try_from(value.value.as_ref())?),
        })
    }
}

impl<'e> TryFrom<&'e ast::ExprSubscript> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::ExprSubscript) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Subscript {
            slice: &value.slice,
            target: Box::new(AssignmentTarget::try_from(value.value.as_ref())?),
        })
    }
}

impl<'e> TryFrom<&'e ast::ExprStarred> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::ExprStarred) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Starred(Box::new(
            AssignmentTarget::try_from(value.value.as_ref())?,
        )))
    }
}

impl<'e> TryFrom<&'e ast::ExprTuple> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::ExprTuple) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Tuple(
            value
                .elts
                .iter()
                .map(|element| AssignmentTarget::try_from(element))
                .collect::<Result<Vec<AssignmentTarget>, Self::Error>>()?,
        ))
    }
}

impl<'e> TryFrom<&'e ast::ExprList> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::ExprList) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::List(
            value
                .elts
                .iter()
                .map(|element| AssignmentTarget::try_from(element))
                .collect::<Result<Vec<AssignmentTarget>, Self::Error>>()?,
        ))
    }
}

impl<'e> TryFrom<&'e ast::Expr> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::Expr) -> Result<Self, Self::Error> {
        match value {
            ast::Expr::Name(expr_name) => AssignmentTarget::try_from(expr_name),
            ast::Expr::Attribute(expr_attribute) => AssignmentTarget::try_from(expr_attribute),
            ast::Expr::Subscript(expr_subscript) => AssignmentTarget::try_from(expr_subscript),
            ast::Expr::Starred(expr_starred) => AssignmentTarget::try_from(expr_starred),
            ast::Expr::Tuple(expr_tuple) => AssignmentTarget::try_from(expr_tuple),
            ast::Expr::List(expr_list) => AssignmentTarget::try_from(expr_list),
            _ => Err(FromAssignmentTargetError::InvalidTarget),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntity {
    pub namespace: Arc<Namespace>,
    pub cfg_location: Option<Location>,
    pub kind: ProgramEntityKind,
}

impl ProgramEntity {
    pub fn new(
        namespace: Arc<Namespace>,
        cfg_location: Option<Location>,
        kind: ProgramEntityKind,
    ) -> Self {
        Self {
            namespace,
            cfg_location,
            kind,
        }
    }
}

impl Display for ProgramEntity {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}Entity({})", self.kind, self.namespace)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct SubProgramEntityContext {
    pub specification: ProgramEntitySpecification,
    pub variable_locations: imbl::OrdMap<VariableName, imbl::OrdSet<Location>>,
}

impl SubProgramEntityContext {
    pub fn new(
        specification: ProgramEntitySpecification,
        variable_locations: imbl::OrdMap<VariableName, imbl::OrdSet<Location>>,
    ) -> Self {
        Self {
            specification,
            variable_locations,
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReturnStatus {
    #[default]
    NotReturning,
    Returning,
}

impl OrdJoin for ReturnStatus {}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct ProgramEntityAbstractEnvironment {
    pub return_status: ReturnStatus,
    pub current_nodes: imbl::OrdMap<ConstraintNode, imbl::OrdSet<Guard>>,
    pub variable_locations: imbl::OrdMap<VariableName, imbl::OrdSet<Location>>,
    pub nodes: imbl::OrdMap<ConstraintNode, imbl::OrdSet<Constraint>>,
    pub edges: imbl::OrdMap<(ConstraintNode, ConstraintNode), imbl::OrdSet<Guard>>,
    pub imports: imbl::OrdSet<ModuleName>,
    pub sub_program_entities: imbl::OrdMap<ProgramEntity, SubProgramEntityContext>,
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct ProgramEntityAnalysisState {
    pub abstract_states: imbl::OrdMap<ProgramPoint, ProgramEntityAbstractEnvironment>,
}

impl ProgramEntityAnalysisState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn at_exit(&self) -> Option<&ProgramEntityAbstractEnvironment> {
        self.abstract_states.get(&ProgramPoint::Exit)
    }

    pub fn clone_abstract_environment_or_default(
        &self,
        program_point: ProgramPoint,
    ) -> ProgramEntityAbstractEnvironment {
        self.abstract_states
            .get(&program_point)
            .cloned()
            .unwrap_or_default()
    }
}

impl Display for ProgramEntityAnalysisState {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.abstract_states.fmt(f)
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct UsedVariables {
    pub names: imbl::OrdMap<VariableName, imbl::OrdSet<Location>>,
}

impl UsedVariables {
    pub fn new(names: imbl::OrdMap<VariableName, imbl::OrdSet<Location>>) -> Self {
        Self { names }
    }

    pub fn consume<T>(&mut self, eval: ExpressionEval<T>) -> T {
        self.names = self.names.join(&eval.variables.names);
        eval.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionEval<T> {
    pub value: T,
    pub variables: UsedVariables,
}

impl<T> ExpressionEval<T> {
    pub fn new(value: T, variables: UsedVariables) -> Self {
        Self { value, variables }
    }

    pub fn only_value(value: T) -> Self {
        Self::new(value, UsedVariables::default())
    }

    pub fn map(self, f: impl FnOnce(T) -> T) -> Self {
        Self::new(f(self.value), self.variables)
    }

    pub fn merge(self, other: Self, f: impl FnOnce(T, T) -> T) -> Self {
        Self::new(
            f(self.value, other.value),
            self.variables.join(&other.variables),
        )
    }
}

#[derive(Debug, Error)]
pub enum ConstraintsBuilderError {
    #[error("`{name}` at location `{location}` is an invalid Python module")]
    InvalidModule { name: String, location: Location },
    #[error("`{name}` at location `{location}` is an invalid Python identifier")]
    InvalidIdentifier { name: String, location: Location },
    #[error("program point `{program_point}` is invalid")]
    InvalidProgramPoint { program_point: ProgramPoint },
    #[error("invalid bool expression `{expr:?}`")]
    InvalidExprBoolOp { expr: ast::ExprBoolOp },
    #[error("invalid compare expression `{expr:?}`")]
    InvalidExprCompare { expr: ast::ExprCompare },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProgramEntityKind {
    Module,
    Class,
    Function,
}

impl Display for ProgramEntityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Module => f.write_str("Module"),
            Self::Class => f.write_str("Class"),
            Self::Function => f.write_str("Function"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityAbstractParentState<'a> {
    pub state: &'a ProgramEntityAbstractEnvironment,
    pub entity: &'a ProgramEntity,
    pub parent: Option<&'a ProgramEntityAbstractParentState<'a>>,
}

impl<'a> ProgramEntityAbstractParentState<'a> {
    pub fn new(
        state: &'a ProgramEntityAbstractEnvironment,
        entity: &'a ProgramEntity,
        parent: Option<&'a ProgramEntityAbstractParentState<'a>>,
    ) -> Self {
        Self {
            state,
            entity,
            parent,
        }
    }

    pub fn previous_locations<'l>(
        &'l self,
        entity: &'l ProgramEntity,
        variable_name: &VariableName,
    ) -> Option<(&'l Arc<Namespace>, &'l imbl::OrdSet<Location>)> {
        let (qualified_location, variable_locations) = match self.entity.kind {
            ProgramEntityKind::Module | ProgramEntityKind::Function => {
                (&self.entity.namespace, &self.state.variable_locations)
            }
            ProgramEntityKind::Class => (
                &entity.namespace,
                &self
                    .state
                    .sub_program_entities
                    .get(entity)?
                    .variable_locations,
            ),
        };

        if let Some(locations) = variable_locations.get(variable_name) {
            return Some((qualified_location, locations));
        }

        if let Some(parent) = &self.parent {
            return parent.previous_locations(self.entity, variable_name);
        }

        None
    }
}

pub fn drain<K: Clone + Ord, V: Clone>(
    map: &mut imbl::OrdMap<K, V>,
    f: impl Fn(&(K, V)) -> bool,
) -> imbl::OrdMap<K, V> {
    let mut drained = imbl::OrdMap::default();

    *map = map
        .clone()
        .into_iter()
        .filter(|entry| {
            if f(entry) {
                let (key, value) = entry;
                drained.insert(key.clone(), value.clone());
                false
            } else {
                true
            }
        })
        .collect();

    drained
}

pub fn update_join<K: Clone + Ord, V: Clone + Join>(
    map: imbl::OrdMap<K, V>,
    key: K,
    value: V,
) -> imbl::OrdMap<K, V> {
    map.update_with(key, value, |self_value, other_value| {
        self_value.join(&other_value)
    })
}

#[derive(Debug, Clone)]
pub struct ConstraintsBuilder<'a> {
    pub cfg: &'a Cfg<'a>,
    pub line_index: &'a LineIndex,
    pub program_entity: &'a ProgramEntity,
    pub abstract_parent_state: Option<&'a ProgramEntityAbstractParentState<'a>>,
}

impl<'a> ConstraintsBuilder<'a> {
    pub fn new(
        cfg: &'a Cfg<'a>,
        line_index: &'a LineIndex,
        program_entity: &'a ProgramEntity,
        abstract_parent_state: Option<&'a ProgramEntityAbstractParentState<'a>>,
    ) -> ConstraintsBuilder<'a> {
        ConstraintsBuilder {
            cfg,
            line_index,
            program_entity,
            abstract_parent_state,
        }
    }

    pub fn filter_guard(
        &self,
        edge_kinds: &BTreeSet<CfgEdgeKind>,
        guards: &imbl::OrdSet<Guard>,
    ) -> Option<imbl::OrdSet<Guard>> {
        if guards.is_empty() {
            return Some(guards.clone());
        }

        let filtered_guards: imbl::OrdSet<_> = guards
            .iter()
            .filter(|guard| match guard {
                Guard::IsTrue(_) => edge_kinds.contains(&CfgEdgeKind::Conditional(true)),
                Guard::IsFalse(_) => edge_kinds.contains(&CfgEdgeKind::Conditional(false)),
                Guard::Succeed(_) => edge_kinds
                    .iter()
                    .any(|edge_kind| edge_kind.is_normal_flow()),
                Guard::Raise { .. } => edge_kinds
                    .iter()
                    .any(|edge_kind| edge_kind.is_exception_flow()),
            })
            .cloned()
            .collect();

        if filtered_guards.is_empty() {
            None
        } else {
            Some(filtered_guards)
        }
    }

    pub fn previous_locations<'l>(
        &'l self,
        variable_locations: &'l imbl::OrdMap<VariableName, imbl::OrdSet<Location>>,
        variable_name: &VariableName,
    ) -> Option<(&'l Arc<Namespace>, &'l imbl::OrdSet<Location>)> {
        if let Some(previous_locations) = variable_locations.get(variable_name) {
            return Some((&self.program_entity.namespace, previous_locations));
        }

        if let Some(parent) = &self.abstract_parent_state {
            return parent.previous_locations(self.program_entity, variable_name);
        }

        None
    }

    pub fn create_used_variables_constraints(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        used_variables: UsedVariables,
    ) {
        if used_variables.names.is_empty() {
            return;
        }

        let mut constraints = imbl::OrdSet::new();
        let mut previous_expression_variables = imbl::OrdSet::new();
        for (used_variable_name, used_locations) in used_variables.names.as_ref() {
            if let Some((previous_program_entity, previous_locations)) = self
                .previous_locations(&abstract_environment.variable_locations, used_variable_name)
            {
                for previous_location in previous_locations {
                    for used_location in used_locations {
                        let previous_expression_variable = Arc::new(Expression::Variable(
                            ExpressionVariable::new(NamedQualifiedLocation::new(
                                used_variable_name.clone(),
                                previous_location.clone(),
                                previous_program_entity.clone(),
                            )),
                        ));
                        constraints.insert(Constraint::Type(IncludeConstraint::new(
                            previous_expression_variable.clone(),
                            Arc::new(Expression::Variable(ExpressionVariable::new(
                                NamedQualifiedLocation::new(
                                    used_variable_name.clone(),
                                    used_location.clone(),
                                    self.program_entity.namespace.clone(),
                                ),
                            ))),
                        )));
                        previous_expression_variables.insert(previous_expression_variable);
                    }
                }
            } else {
                // TODO: add support for forward references
            }
        }

        if constraints.is_empty() {
            return;
        }

        let mut current_nodes = drain(&mut abstract_environment.current_nodes, |(_, guards)| {
            guards
                .iter()
                .any(|guard| matches!(guard, Guard::Raise { .. }))
        });

        let node = ConstraintNode::Constraint {
            location: Some(location.clone()),
            id: None,
        };
        abstract_environment.nodes.insert(node.clone(), constraints);

        let empty_constraint_node = ConstraintNode::Constraint {
            location: Some(location.clone()),
            id: Some(Arc::new("#empty".to_owned())),
        };
        for (from, guards) in &abstract_environment.current_nodes {
            let from = if guards.is_empty() {
                &from
            } else {
                abstract_environment.edges.insert(
                    (from.clone(), empty_constraint_node.clone()),
                    guards.clone(),
                );
                &empty_constraint_node
            };
            abstract_environment.edges.insert(
                (from.clone(), node.clone()),
                previous_expression_variables
                    .iter()
                    .map(|previous_expression_variable| {
                        Guard::Succeed(previous_expression_variable.clone())
                    })
                    .collect(),
            );
            current_nodes.insert(
                from.clone(),
                previous_expression_variables
                    .iter()
                    .map(|previous_expression_variable| Guard::Raise {
                        expression: previous_expression_variable.clone(),
                        exception: None,
                    })
                    .collect(),
            );
        }

        current_nodes.insert(node, imbl::OrdSet::default());

        abstract_environment.current_nodes = current_nodes;
    }

    pub fn create_include_constraint(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        additional_constraints: imbl::OrdSet<Constraint>,
        left: Arc<Expression>,
        right: Arc<Expression>,
    ) {
        let node = ConstraintNode::Constraint {
            location: Some(location.clone()),
            id: None,
        };

        let constraints = additional_constraints.update(Constraint::Type(IncludeConstraint::new(
            left.clone(),
            right.clone(),
        )));

        abstract_environment.nodes.insert(node.clone(), constraints);

        let mut current_nodes = drain(&mut abstract_environment.current_nodes, |(_, guards)| {
            guards
                .iter()
                .any(|guard| matches!(guard, Guard::Raise { .. }))
        })
        .update(node.clone(), imbl::OrdSet::default());

        if left.is_constant() {
            for (from, guards) in &abstract_environment.current_nodes {
                abstract_environment
                    .edges
                    .insert((from.clone(), node.clone()), guards.clone());
            }

            abstract_environment.current_nodes = current_nodes;
            return;
        }

        let current_empty_constraint = ConstraintNode::Constraint {
            location: Some(location.clone()),
            id: Some(Arc::new("#empty".to_owned())),
        };

        for (from, guards) in &abstract_environment.current_nodes {
            let from = if guards.is_empty() {
                &from
            } else {
                abstract_environment.edges.insert(
                    (from.clone(), current_empty_constraint.clone()),
                    guards.clone(),
                );
                &current_empty_constraint
            };

            abstract_environment.edges.insert(
                (from.clone(), node.clone()),
                imbl::OrdSet::unit(Guard::Succeed(left.clone())),
            );
            current_nodes.insert(
                from.clone(),
                imbl::OrdSet::unit(Guard::Raise {
                    expression: left.clone(),
                    exception: None,
                }),
            );
        }

        abstract_environment.current_nodes = current_nodes;
    }

    pub fn assign_variable(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        variable: VariableName,
        type_expression: Arc<Expression>,
    ) {
        let expression_variable = ExpressionVariable::new(NamedQualifiedLocation::new(
            variable.clone(),
            location.clone(),
            self.program_entity.namespace.clone(),
        ));

        self.create_include_constraint(
            abstract_environment,
            location.clone(),
            imbl::OrdSet::unit(Constraint::DefinedVariable(expression_variable.clone())),
            type_expression,
            Arc::new(Expression::Variable(expression_variable)),
        );

        abstract_environment
            .variable_locations
            .insert(variable, imbl::OrdSet::unit(location));
    }

    pub fn assign_empty_constraint(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        new_guards: imbl::OrdSet<Guard>,
    ) {
        let current_nodes = drain(&mut abstract_environment.current_nodes, |(_, guards)| {
            guards
                .iter()
                .any(|guard| matches!(guard, Guard::Raise { .. }))
        });

        let node = if let Some((from, _)) =
            abstract_environment
                .current_nodes
                .get_min()
                .filter(|(_, guards)| {
                    abstract_environment.current_nodes.len() == 1 && guards.is_empty()
                }) {
            from.clone()
        } else {
            let node = ConstraintNode::Constraint {
                location: Some(location.clone()),
                id: None,
            };

            for (from, guards) in &abstract_environment.current_nodes {
                abstract_environment
                    .edges
                    .insert((from.clone(), node.clone()), guards.clone());
            }

            node
        };

        abstract_environment.current_nodes = current_nodes.update(node, new_guards);
    }

    pub fn gen_module_name(
        &self,
        identifier: &ast::Identifier,
    ) -> Result<ModuleName, ConstraintsBuilderError> {
        match QualifiedName::try_from(identifier.id.as_str()) {
            Ok(module_name) => Ok(Arc::new(module_name)),
            Err(_) => Err(ConstraintsBuilderError::InvalidModule {
                location: self.gen_location(&identifier),
                name: identifier.id.to_owned(),
            }),
        }
    }

    pub fn gen_variable_name(
        &self,
        identifier: &ast::Identifier,
    ) -> Result<VariableName, ConstraintsBuilderError> {
        match Identifier::try_from(identifier.id.as_str()) {
            Ok(identifier_name) => Ok(Arc::new(identifier_name)),
            Err(_) => Err(ConstraintsBuilderError::InvalidIdentifier {
                location: self.gen_location(&identifier),
                name: identifier.id.to_owned(),
            }),
        }
    }

    pub fn gen_location(&self, ranged: &impl Ranged) -> Location {
        let program_point_location =
            convert_text_size_to_location(self.line_index, ranged.start()).unwrap();
        Location::new(program_point_location.line, program_point_location.offset)
    }

    pub fn evaluate_parameter(
        &self,
        namespace: &ProgramEntityAnalysisState,
        parameter: &ast::Parameter,
    ) -> Result<(ExpressionVariable, Option<ExpressionEval<Expression>>), ConstraintsBuilderError>
    {
        let parameter_name = self.gen_variable_name(&parameter.name)?;

        let annotation = if let Some(annotation) = &parameter.annotation {
            Some(
                self.evaluate_expr(&namespace, &annotation)?
                    .map(|expression| {
                        Expression::Annotated(ExpressionAnnotated::new(Arc::new(expression)))
                    }),
            )
        } else {
            None
        };

        Ok((
            ExpressionVariable::new(NamedQualifiedLocation::new(
                parameter_name,
                self.gen_location(parameter),
                self.program_entity.namespace.clone(),
            )),
            annotation,
        ))
    }

    pub fn evaluate_parameter_with_default(
        &self,
        namespace: &ProgramEntityAnalysisState,
        parameter_with_default: &ast::ParameterWithDefault,
    ) -> Result<(ExpressionVariable, Option<ExpressionEval<Expression>>), ConstraintsBuilderError>
    {
        let (parameter_name, annotation_eval_option) =
            self.evaluate_parameter(namespace, &parameter_with_default.parameter)?;

        let parameter_eval_option = if let Some(default) = &parameter_with_default.default {
            let default_eval = self.evaluate_expr(&namespace, &default)?;

            if let Some(annotation_eval) = annotation_eval_option {
                Some(annotation_eval.merge(default_eval, |annotation, default| {
                    Expression::Override(ExpressionOverride::new(
                        Arc::new(annotation),
                        Arc::new(default),
                    ))
                }))
            } else {
                Some(default_eval)
            }
        } else {
            annotation_eval_option
        };

        Ok((parameter_name, parameter_eval_option))
    }

    pub fn gen_parameters(
        &self,
        namespace: &ProgramEntityAnalysisState,
        parameters: &ast::Parameters,
    ) -> Result<
        ExpressionEval<imbl::OrdMap<ExpressionVariable, imbl::OrdSet<Expression>>>,
        ConstraintsBuilderError,
    > {
        let positional_only_parameters = parameters
            .posonlyargs
            .iter()
            .map(|parameter| self.evaluate_parameter_with_default(namespace, &parameter));
        let positional_or_keyword_parameters = parameters
            .args
            .iter()
            .map(|parameter| self.evaluate_parameter(namespace, &parameter.parameter));
        let var_positional_parameters = parameters
            .vararg
            .iter()
            .map(|parameter| self.evaluate_parameter(namespace, &parameter));
        let keyword_only_parameters = parameters
            .kwonlyargs
            .iter()
            .map(|parameter| self.evaluate_parameter_with_default(namespace, &parameter));
        let var_keyword_parameters = parameters
            .kwarg
            .iter()
            .map(|parameter| self.evaluate_parameter(namespace, &parameter));

        let parameter_evals = positional_only_parameters
            .chain(positional_or_keyword_parameters)
            .chain(var_positional_parameters)
            .chain(keyword_only_parameters)
            .chain(var_keyword_parameters)
            .collect::<Result<Vec<(ExpressionVariable, Option<ExpressionEval<Expression>>)>, _>>(
            )?;

        let mut used_variables = UsedVariables::default();

        let mut arguments = imbl::OrdMap::default();

        for (variable_name, parameter_eval_option) in parameter_evals {
            let parameter_type_expression = if let Some(parameter_eval) = parameter_eval_option {
                imbl::OrdSet::unit(used_variables.consume(parameter_eval))
            } else {
                imbl::OrdSet::default()
            };
            arguments = update_join(arguments, variable_name, parameter_type_expression);
        }

        Ok(ExpressionEval::new(arguments, used_variables))
    }

    pub fn evaluate_expr_bool_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_bool_op: &ast::ExprBoolOp,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let mut values_iter = expr_bool_op.values.iter();

        let mut eval = match values_iter.next() {
            Some(value) => self.evaluate_expr(namespace, value)?,
            None => {
                return Err(ConstraintsBuilderError::InvalidExprBoolOp {
                    expr: expr_bool_op.clone(),
                });
            }
        };

        let operator = match expr_bool_op.op {
            ast::BoolOp::And => BinaryOperator::And,
            ast::BoolOp::Or => BinaryOperator::Or,
        };

        for value in values_iter {
            eval = eval.merge(self.evaluate_expr(namespace, &value)?, |left, right| {
                Expression::Binary(ExpressionBinary {
                    left: Arc::new(left),
                    operator: operator.clone(),
                    right: Arc::new(right),
                })
            })
        }

        Ok(eval)
    }

    pub fn evaluate_expr_bin_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_bin_op: &ast::ExprBinOp,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let left_eval = self.evaluate_expr(namespace, &expr_bin_op.left)?;
        let right_eval = self.evaluate_expr(namespace, &expr_bin_op.right)?;

        let operator = match expr_bin_op.op {
            ast::Operator::Add => BinaryOperator::Add,
            ast::Operator::Sub => BinaryOperator::Sub,
            ast::Operator::Mult => BinaryOperator::Mult,
            ast::Operator::MatMult => BinaryOperator::MatMult,
            ast::Operator::Div => BinaryOperator::Div,
            ast::Operator::Mod => BinaryOperator::Mod,
            ast::Operator::Pow => BinaryOperator::Pow,
            ast::Operator::LShift => BinaryOperator::LShift,
            ast::Operator::RShift => BinaryOperator::RShift,
            ast::Operator::BitOr => BinaryOperator::BitOr,
            ast::Operator::BitXor => BinaryOperator::BitXor,
            ast::Operator::BitAnd => BinaryOperator::BitAnd,
            ast::Operator::FloorDiv => BinaryOperator::FloorDiv,
        };

        Ok(left_eval.merge(right_eval, |left, right| {
            Expression::Binary(ExpressionBinary {
                left: Arc::new(left),
                operator,
                right: Arc::new(right),
            })
        }))
    }

    pub fn evaluate_expr_unary_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_unary_op: &ast::ExprUnaryOp,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let operand_eval = self.evaluate_expr(namespace, &expr_unary_op.operand)?;

        let operator = match expr_unary_op.op {
            ast::UnaryOp::Invert => UnaryOperator::Invert,
            ast::UnaryOp::Not => UnaryOperator::Not,
            ast::UnaryOp::UAdd => UnaryOperator::UAdd,
            ast::UnaryOp::USub => UnaryOperator::USub,
        };

        Ok(operand_eval.map(|operand| {
            Expression::Unary(ExpressionUnary {
                operator,
                operand: Arc::new(operand),
            })
        }))
    }

    pub fn evaluate_expr_compare(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_compare: &ast::ExprCompare,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let mut eval = self.evaluate_expr(namespace, &expr_compare.left)?;

        if expr_compare.ops.is_empty()
            || expr_compare.comparators.is_empty()
            || expr_compare.comparators.len() != expr_compare.ops.len()
        {
            return Err(ConstraintsBuilderError::InvalidExprCompare {
                expr: expr_compare.clone(),
            });
        }

        for (op, comparator) in expr_compare.ops.iter().zip(expr_compare.comparators.iter()) {
            let operator = match op {
                ast::CmpOp::Eq => BinaryOperator::Eq,
                ast::CmpOp::NotEq => BinaryOperator::NotEq,
                ast::CmpOp::Lt => BinaryOperator::Lt,
                ast::CmpOp::LtE => BinaryOperator::LtE,
                ast::CmpOp::Gt => BinaryOperator::Gt,
                ast::CmpOp::GtE => BinaryOperator::GtE,
                ast::CmpOp::Is => BinaryOperator::Is,
                ast::CmpOp::IsNot => BinaryOperator::IsNot,
                ast::CmpOp::In => BinaryOperator::In,
                ast::CmpOp::NotIn => BinaryOperator::NotIn,
            };

            let comparator = self.evaluate_expr(namespace, comparator)?;

            eval = eval.merge(comparator, |left, right| {
                Expression::Binary(ExpressionBinary {
                    left: Arc::new(left),
                    operator,
                    right: Arc::new(right),
                })
            });
        }

        Ok(eval)
    }

    pub fn evaluate_expr_call(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_call: &ast::ExprCall,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let mut func_eval = self.evaluate_expr(namespace, &expr_call.func)?;

        let mut positional_arguments: imbl::Vector<Arc<Expression>> = imbl::Vector::new();
        for positional_argument in &expr_call.arguments.args {
            positional_arguments.push_back(Arc::new(
                func_eval
                    .variables
                    .consume(self.evaluate_expr(namespace, &positional_argument)?),
            ));
        }

        let mut keyword_arguments: imbl::Vector<KeywordArgument> = imbl::Vector::new();
        for keyword_argument in &expr_call.arguments.keywords {
            let keyword_name = match &keyword_argument.arg {
                Some(identifier) => Some(self.gen_variable_name(&identifier)?),
                None => None,
            };
            keyword_arguments.push_back(KeywordArgument {
                name: keyword_name,
                value: Arc::new(
                    func_eval
                        .variables
                        .consume(self.evaluate_expr(namespace, &keyword_argument.value)?),
                ),
            });
        }

        Ok(func_eval.map(|func| {
            Expression::Call(ExpressionCall {
                target: Arc::new(func),
                positional_arguments,
                keyword_arguments,
            })
        }))
    }

    pub fn evaluate_expr_string_literal(
        &self,
        expr_string_literal: &ast::ExprStringLiteral,
    ) -> Expression {
        Expression::LiteralString(LiteralStr {
            value: Arc::new(expr_string_literal.value.to_str().to_owned()),
        })
    }

    pub fn evaluate_expr_bytes_literal(
        &self,
        expr_bytes_literal: &ast::ExprBytesLiteral,
    ) -> Expression {
        Expression::LiteralBytes(LiteralBytes {
            value: Arc::new(
                expr_bytes_literal
                    .value
                    .iter()
                    .flat_map(|part| part.as_slice())
                    .copied()
                    .collect(),
            ),
        })
    }

    pub fn evaluate_expr_number_literal(
        &self,
        expr_number_literal: &ast::ExprNumberLiteral,
    ) -> Expression {
        match &expr_number_literal.value {
            ast::Number::Int(int) => match int.as_i64() {
                Some(value) => Expression::LiteralInteger(LiteralInt::new(Int::SmallInt(value))),
                None => Expression::LiteralInteger(LiteralInt::new(Int::BigInt({
                    let base = int.to_string();

                    if base.starts_with("0x") || base.starts_with("0X") {
                        BigInt::from_str_radix(&base[2..], 16).unwrap()
                    } else if base.starts_with("0o") || base.starts_with("0O") {
                        BigInt::from_str_radix(&base[2..], 8).unwrap()
                    } else if base.starts_with("0b") || base.starts_with("0B") {
                        BigInt::from_str_radix(&base[2..], 2).unwrap()
                    } else {
                        BigInt::from_str_radix(&base, 10).unwrap()
                    }
                }))),
            },
            ast::Number::Float(float) => Expression::LiteralFloat(LiteralFloat { value: *float }),
            ast::Number::Complex { real, imag } => Expression::LiteralComplex(LiteralComplex {
                value: Complex64::new(*real, *imag),
            }),
        }
    }

    pub fn evaluate_expr_boolean_literal(
        &self,
        expr_boolean_literal: &ast::ExprBooleanLiteral,
    ) -> Expression {
        Expression::LiteralBoolean(LiteralBool {
            value: expr_boolean_literal.value,
        })
    }

    pub fn evaluate_expr_none_literal(&self) -> Expression {
        Expression::LiteralNone
    }

    pub fn evaluate_expr_ellipsis_literal(&self) -> Expression {
        Expression::LiteralEllipsis
    }

    pub fn evaluate_expr_attribute(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_attribute: &ast::ExprAttribute,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let value_eval = self.evaluate_expr(namespace, &expr_attribute.value)?;
        let attribute = self.gen_variable_name(&expr_attribute.attr)?;

        Ok(value_eval.map(|value| {
            Expression::Attribute(ExpressionAttribute {
                value: Arc::new(value),
                attribute,
            })
        }))
    }

    pub fn evaluate_expr_subscript(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr_subscript: &ast::ExprSubscript,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let value_eval = self.evaluate_expr(namespace, &expr_subscript.value)?;
        let slice_eval = self.evaluate_expr(namespace, &expr_subscript.slice)?;

        Ok(value_eval.merge(slice_eval, |value, slice| {
            Expression::Subscript(ExpressionSubscript {
                value: Arc::new(value),
                slice: Arc::new(slice),
            })
        }))
    }

    pub fn evaluate_name(
        &self,
        expr_name: &ast::ExprName,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        let location = self.gen_location(expr_name);

        let Ok(identifier) = Identifier::try_from(expr_name.id.as_str()) else {
            return Err(ConstraintsBuilderError::InvalidIdentifier {
                location,
                name: expr_name.id.to_owned(),
            });
        };

        let variable_name = Arc::new(identifier);

        Ok(ExpressionEval::new(
            Expression::Variable(ExpressionVariable::new(NamedQualifiedLocation::new(
                variable_name.clone(),
                location.clone(),
                self.program_entity.namespace.clone(),
            ))),
            UsedVariables::new(imbl::OrdMap::unit(
                variable_name,
                imbl::OrdSet::unit(location),
            )),
        ))
    }

    pub fn evaluate_expr(
        &self,
        namespace: &ProgramEntityAnalysisState,
        expr: &ast::Expr,
    ) -> Result<ExpressionEval<Expression>, ConstraintsBuilderError> {
        match expr {
            ast::Expr::BoolOp(expr_bool_op) => self.evaluate_expr_bool_op(namespace, expr_bool_op),
            ast::Expr::Named(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::BinOp(expr_bin_op) => self.evaluate_expr_bin_op(namespace, expr_bin_op),
            ast::Expr::UnaryOp(expr_unary_op) => {
                self.evaluate_expr_unary_op(namespace, expr_unary_op)
            }
            ast::Expr::Lambda(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::If(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Dict(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Set(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::ListComp(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::SetComp(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::DictComp(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Generator(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Await(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Yield(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::YieldFrom(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Compare(expr_compare) => self.evaluate_expr_compare(namespace, expr_compare),
            ast::Expr::Call(expr_call) => self.evaluate_expr_call(namespace, expr_call),
            ast::Expr::FString(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::StringLiteral(expr_string_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_string_literal(expr_string_literal),
            )),
            ast::Expr::BytesLiteral(expr_bytes_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_bytes_literal(expr_bytes_literal),
            )),
            ast::Expr::NumberLiteral(expr_number_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_number_literal(expr_number_literal),
            )),
            ast::Expr::BooleanLiteral(expr_boolean_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_boolean_literal(expr_boolean_literal),
            )),
            ast::Expr::NoneLiteral(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::EllipsisLiteral(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_ellipsis_literal(),
            )),
            ast::Expr::Attribute(expr_attribute) => {
                self.evaluate_expr_attribute(namespace, expr_attribute)
            }
            ast::Expr::Subscript(expr_subscript) => {
                self.evaluate_expr_subscript(namespace, expr_subscript)
            }
            ast::Expr::Starred(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Name(expr_name) => self.evaluate_name(expr_name),
            ast::Expr::List(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Tuple(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::Slice(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            ast::Expr::IpyEscapeCommand(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
        }
    }

    pub fn evaluate_stmt_function_def(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_function_def: &ast::StmtFunctionDef,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let parameters = self.gen_parameters(namespace, &stmt_function_def.parameters)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            self.gen_location(stmt_function_def.parameters.as_ref()),
            parameters.variables,
        );

        let location = self.gen_location(&stmt_function_def.name);

        let variable_name = self.gen_variable_name(&stmt_function_def.name)?;

        let function_qualified_location = NamedQualifiedLocation::new(
            variable_name.clone(),
            location.clone(),
            self.program_entity.namespace.clone(),
        );

        self.assign_variable(
            &mut target_abstract_environment,
            location,
            variable_name.clone(),
            Arc::new(Expression::Function(ExpressionFunction::new(
                function_qualified_location.clone(),
                stmt_function_def.is_async,
            ))),
        );

        target_abstract_environment.sub_program_entities.insert(
            ProgramEntity::new(
                Arc::new(Namespace::NamedProgramEntity(function_qualified_location)),
                Some(self.gen_location(&stmt_function_def)),
                ProgramEntityKind::Function,
            ),
            SubProgramEntityContext::new(
                ProgramEntitySpecification {
                    arguments: parameters.value,
                    return_type: imbl::OrdSet::default(),
                    exceptions: imbl::OrdSet::default(),
                },
                target_abstract_environment.variable_locations.clone(),
            ),
        );

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_class_def(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_class_def: &ast::StmtClassDef,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let location = self.gen_location(&stmt_class_def.name);

        let variable_name = self.gen_variable_name(&stmt_class_def.name)?;

        let class_qualified_location = NamedQualifiedLocation::new(
            variable_name.clone(),
            location.clone(),
            self.program_entity.namespace.clone(),
        );

        self.assign_variable(
            &mut target_abstract_environment,
            location.clone(),
            variable_name.clone(),
            Arc::new(Expression::Class(ExpressionClass::new(
                class_qualified_location.clone(),
            ))),
        );

        target_abstract_environment.sub_program_entities.insert(
            ProgramEntity::new(
                Arc::new(Namespace::NamedProgramEntity(class_qualified_location)),
                Some(self.gen_location(stmt_class_def)),
                ProgramEntityKind::Class,
            ),
            SubProgramEntityContext::new(
                ProgramEntitySpecification {
                    arguments: imbl::OrdMap::default(),
                    return_type: imbl::OrdSet::default(),
                    exceptions: imbl::OrdSet::default(),
                },
                target_abstract_environment.variable_locations.clone(),
            ),
        );

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_return(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_return: &ast::StmtReturn,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let expression = if let Some(value) = &stmt_return.value {
            let value_eval = self.evaluate_expr(namespace, value.as_ref())?;

            self.create_used_variables_constraints(
                &mut target_abstract_environment,
                self.gen_location(value.as_ref()),
                value_eval.variables,
            );

            value_eval.value
        } else {
            Expression::LiteralNone
        };

        let node = ConstraintNode::Constraint {
            location: Some(self.gen_location(stmt_return)),
            id: None,
        };

        let constraint = Constraint::Return(ReturnConstraint::new(Arc::new(expression), None));

        target_abstract_environment
            .nodes
            .insert(node.clone(), imbl::OrdSet::unit(constraint));

        let current_nodes = drain(
            &mut target_abstract_environment.current_nodes,
            |(_, guards)| {
                guards
                    .iter()
                    .any(|guard| matches!(guard, Guard::Raise { .. }))
            },
        );

        for (from, guards) in target_abstract_environment.current_nodes.as_ref() {
            target_abstract_environment
                .edges
                .insert((from.clone(), node.clone()), guards.clone());
        }

        target_abstract_environment.current_nodes =
            current_nodes.update(node, imbl::OrdSet::default());
        target_abstract_environment.return_status = ReturnStatus::Returning;

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_import(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_import: &ast::StmtImport,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let mut current_nodes = imbl::OrdSet::default();
        for alias in &stmt_import.names {
            let module_name = self.gen_module_name(&alias.name)?;

            if let Some(as_name) = &alias.asname {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_location(as_name),
                    self.gen_variable_name(&as_name)?,
                    Arc::new(Expression::Import(ExpressionImport::new(
                        module_name.clone(),
                    ))),
                );
            } else {
                let identifier = Arc::new(module_name.identifiers.first().clone());
                let mut location = self.gen_location(&alias.name);

                target_abstract_environment
                    .variable_locations
                    .insert(identifier.clone(), imbl::OrdSet::unit(location.clone()));

                let mut expression_option = Some(Arc::new(Expression::Variable(
                    ExpressionVariable::new(NamedQualifiedLocation::new(
                        identifier,
                        location.clone(),
                        self.program_entity.namespace.clone(),
                    )),
                )));

                let mut i = 1;
                while let Some(expression) = expression_option {
                    let (module_identifiers, attribute_identifiers) =
                        module_name.identifiers.split_at(i);
                    let attribute_option = attribute_identifiers.first().cloned();
                    let identifier = Arc::new(module_identifiers[0].clone());

                    self.create_include_constraint(
                        &mut target_abstract_environment,
                        location.clone(),
                        imbl::OrdSet::unit(Constraint::DefinedVariable(ExpressionVariable::new(
                            NamedQualifiedLocation::new(
                                identifier.clone(),
                                location.clone(),
                                self.program_entity.namespace.clone(),
                            ),
                        ))),
                        Arc::new(Expression::Import(ExpressionImport::new(Arc::new(
                            QualifiedName::new(OneOrMany::many(Vec::from(module_identifiers))),
                        )))),
                        expression.clone(),
                    );

                    // TODO: add constraints of exceptions, pureness and mutability
                    if let Some(attribute) = attribute_option {
                        expression_option =
                            Some(Arc::new(Expression::Attribute(ExpressionAttribute {
                                value: expression,
                                attribute: Arc::new(attribute),
                            })));
                    } else {
                        expression_option = None;
                    }

                    current_nodes.extend(drain(
                        &mut target_abstract_environment.current_nodes,
                        |(_, guards)| {
                            guards
                                .iter()
                                .any(|guard| matches!(guard, Guard::Raise { .. }))
                        },
                    ));

                    // Increase the offset to target the right part of the module name
                    location.offset += identifier.len() + 1;

                    i = i + 1;
                }
            };

            current_nodes.extend(drain(
                &mut target_abstract_environment.current_nodes,
                |(_, guards)| {
                    guards
                        .iter()
                        .any(|guard| matches!(guard, Guard::Raise { .. }))
                },
            ));

            target_abstract_environment
                .imports
                .insert(module_name.clone());
        }

        target_abstract_environment
            .current_nodes
            .extend(current_nodes);

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_assign(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_assign: &ast::StmtAssign,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let eval = self.evaluate_expr(namespace, &stmt_assign.value)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            self.gen_location(stmt_assign.value.as_ref()),
            eval.variables,
        );

        let type_expression = Arc::new(eval.value);

        let mut current_nodes = imbl::OrdSet::default();
        for target_expr in &stmt_assign.targets {
            let Ok(target) = AssignmentTarget::try_from(target_expr) else {
                continue; // TODO: fix
            };

            match target {
                AssignmentTarget::Name(target_name) => {
                    self.assign_variable(
                        &mut target_abstract_environment,
                        self.gen_location(target_expr),
                        Arc::new(target_name),
                        type_expression.clone(),
                    );
                }
                AssignmentTarget::Attribute { .. } => {}
                AssignmentTarget::Subscript { .. } => {}
                AssignmentTarget::Starred(_) => {}
                AssignmentTarget::Tuple(_) => {}
                AssignmentTarget::List(_) => {}
            }

            current_nodes.extend(drain(
                &mut target_abstract_environment.current_nodes,
                |(_, guards)| {
                    guards
                        .iter()
                        .any(|guard| matches!(guard, Guard::Raise { .. }))
                },
            ));
        }

        target_abstract_environment
            .current_nodes
            .extend(current_nodes);

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_ann_assign(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_ann_assign: &ast::StmtAnnAssign,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let Ok(target) = AssignmentTarget::try_from(stmt_ann_assign.target.as_ref()) else {
            todo!("add the right error");
        };

        let Some(value) = &stmt_ann_assign.value else {
            return Ok(target_abstract_environment);
        };

        let eval = self.evaluate_expr(namespace, value)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            self.gen_location(value.as_ref()),
            eval.variables,
        );

        let type_expression = Arc::new(eval.value);

        match target {
            AssignmentTarget::Name(target_name) => {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_location(stmt_ann_assign.target.as_ref()),
                    Arc::new(target_name),
                    type_expression.clone(),
                );
            }
            AssignmentTarget::Attribute { .. } => {}
            AssignmentTarget::Subscript { .. } => {}
            AssignmentTarget::Starred(_) => todo!("impossible"),
            AssignmentTarget::Tuple(_) => todo!("impossible"),
            AssignmentTarget::List(_) => todo!("impossible"),
        }

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_while(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_while: &ast::StmtWhile,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let condition_eval = self.evaluate_expr(namespace, &stmt_while.test)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            self.gen_location(stmt_while.test.as_ref()),
            condition_eval.variables,
        );

        let condition_expression = Arc::new(condition_eval.value);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_location(stmt_while),
            imbl::OrdSet::from_iter([
                Guard::IsTrue(condition_expression.clone()),
                Guard::IsFalse(condition_expression.clone()),
                Guard::Raise {
                    expression: condition_expression.clone(),
                    exception: None,
                },
            ]),
        );

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_if(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_if: &ast::StmtIf,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let condition_eval = self.evaluate_expr(namespace, &stmt_if.test)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            self.gen_location(stmt_if.test.as_ref()),
            condition_eval.variables,
        );

        let condition_expression = Arc::new(condition_eval.value);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_location(stmt_if),
            imbl::OrdSet::from_iter([
                Guard::IsTrue(condition_expression.clone()),
                Guard::IsFalse(condition_expression.clone()),
                Guard::Raise {
                    expression: condition_expression.clone(),
                    exception: None,
                },
            ]),
        );

        Ok(target_abstract_environment)
    }

    pub fn evaluate_elif_else_clause(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        elif_else_clause: &ast::ElifElseClause,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let Some(test) = &elif_else_clause.test else {
            todo!("impossible");
        };

        let condition_eval = self.evaluate_expr(namespace, &test)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            self.gen_location(test),
            condition_eval.variables,
        );

        let condition_expression = Arc::new(condition_eval.value);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_location(elif_else_clause),
            imbl::OrdSet::from_iter([
                Guard::IsTrue(condition_expression.clone()),
                Guard::IsFalse(condition_expression.clone()),
                Guard::Raise {
                    expression: condition_expression.clone(),
                    exception: None,
                },
            ]),
        );

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt: &StmtNode,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        match stmt {
            StmtNode::FunctionDef(stmt_function_def) => {
                self.evaluate_stmt_function_def(namespace, program_point, stmt_function_def)
            }
            StmtNode::ClassDef(stmt_class_def) => {
                self.evaluate_stmt_class_def(namespace, program_point, stmt_class_def)
            }
            StmtNode::Return(stmt_return) => {
                self.evaluate_stmt_return(namespace, program_point, stmt_return)
            }
            StmtNode::Delete(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Assign(stmt_assign) => {
                self.evaluate_stmt_assign(namespace, program_point, stmt_assign)
            }
            StmtNode::AugAssign(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::AnnAssign(stmt_ann_assign) => {
                self.evaluate_stmt_ann_assign(namespace, program_point, stmt_ann_assign)
            }
            StmtNode::TypeAlias(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::For(_) => Ok(namespace.clone_abstract_environment_or_default(program_point)),
            StmtNode::While(stmt_while) => {
                self.evaluate_stmt_while(namespace, program_point, stmt_while)
            }
            StmtNode::If(stmt_if) => self.evaluate_stmt_if(namespace, program_point, stmt_if),
            StmtNode::Elif(elif_else_clause) => {
                self.evaluate_elif_else_clause(namespace, program_point, elif_else_clause)
            }
            StmtNode::With(_) => Ok(namespace.clone_abstract_environment_or_default(program_point)),
            StmtNode::Match(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Raise(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Try(_) => Ok(namespace.clone_abstract_environment_or_default(program_point)),
            StmtNode::Assert(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Import(stmt_import) => {
                self.evaluate_stmt_import(namespace, program_point, &stmt_import)
            }
            StmtNode::ImportFrom(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Global(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Nonlocal(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Expr(_) => Ok(namespace.clone_abstract_environment_or_default(program_point)),
            StmtNode::Pass(_) => Ok(namespace.clone_abstract_environment_or_default(program_point)),
            StmtNode::Break(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::Continue(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            StmtNode::IpyEscapeCommand(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
        }
    }
}

impl GraphAnalyser for ConstraintsBuilder<'_> {
    type Node = ProgramPoint;
    type AbstractState = ProgramEntityAbstractEnvironment;
    type AnalysisState = ProgramEntityAnalysisState;
    type Error = ConstraintsBuilderError;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(ProgramPoint::Entry))
    }
    fn next_nodes<'a>(
        &'a self,
        node: &'a Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error> {
        match self.cfg.entries().get(node).map(|entry| &entry.successors) {
            Some(successors) => Ok(successors.iter()),
            None => Err(ConstraintsBuilderError::InvalidProgramPoint {
                program_point: *node,
            }),
        }
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        let mut analysis_state = ProgramEntityAnalysisState::new();

        let mut entry_state = ProgramEntityAbstractEnvironment::default();

        entry_state
            .current_nodes
            .insert(ConstraintNode::Entry, imbl::OrdSet::default());

        if let Some(abstract_parent_state) = self.abstract_parent_state {
            if let Some(context) = abstract_parent_state
                .state
                .sub_program_entities
                .get(self.program_entity)
            {
                for argument in context.specification.arguments.keys() {
                    entry_state.variable_locations.insert(
                        argument.named_qualified_location.name.clone(),
                        imbl::OrdSet::unit(argument.named_qualified_location.location.clone()),
                    );
                }
            }
        }

        analysis_state
            .abstract_states
            .insert(ProgramPoint::Entry, entry_state);

        Ok(analysis_state)
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        if let Some(node_stmt) = self
            .cfg
            .entries()
            .get(node)
            .and_then(|entry| entry.node.as_ref())
        {
            self.evaluate_stmt(analysis_state, *node, &node_stmt)
        } else {
            Ok(analysis_state.clone_abstract_environment_or_default(*node))
        }
    }

    fn update_abstract_state(
        &self,
        _analysis_state: &Self::AnalysisState,
        from: &Self::Node,
        to: &Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        let Some(edge_kinds) = self.cfg.edges().get(&CfgEdge::new(*from, *to)) else {
            return Ok(None);
        };

        let mut target_abstract_environment = abstract_state.clone();

        target_abstract_environment.current_nodes = target_abstract_environment
            .current_nodes
            .iter()
            .filter_map(|(current_node, guard)| {
                if let Some(new_guard) = self.filter_guard(edge_kinds, guard) {
                    Some((current_node.clone(), new_guard))
                } else {
                    None
                }
            })
            .collect();

        if *to == ProgramPoint::Exit {
            let return_node = ConstraintNode::Constraint {
                location: None,
                id: None,
            };
            let are_all_exceptions = edge_kinds
                .iter()
                .all(|edge_kind| matches!(edge_kind, CfgEdgeKind::UnhandledException));

            if are_all_exceptions {
                target_abstract_environment.variable_locations.clear();
                target_abstract_environment.nodes.clear();
                target_abstract_environment.edges.clear();
                target_abstract_environment.imports.clear();
                target_abstract_environment.sub_program_entities.clear();
            }

            for (from, guards) in target_abstract_environment.current_nodes.as_ref() {
                let (can_return, can_raise) = if guards.is_empty() {
                    (!are_all_exceptions, false)
                } else {
                    guards
                        .iter()
                        .map(|guard| match guard {
                            Guard::Raise { .. }
                                if edge_kinds.contains(&CfgEdgeKind::UnhandledException) =>
                            {
                                (false, true)
                            }
                            _ => (!are_all_exceptions, false),
                        })
                        .fold(
                            (false, false),
                            |(acc_can_return, acc_can_raise), (can_return, can_raise)| {
                                (acc_can_return || can_return, acc_can_raise || can_raise)
                            },
                        )
                };

                if can_return {
                    if matches!(
                        target_abstract_environment.return_status,
                        ReturnStatus::Returning
                    ) {
                        target_abstract_environment
                            .edges
                            .insert((from.clone(), ConstraintNode::TypeExit), guards.clone());
                    } else {
                        target_abstract_environment.return_status = ReturnStatus::Returning;
                        target_abstract_environment.nodes.insert(
                            return_node.clone(),
                            imbl::OrdSet::unit(Constraint::Return(ReturnConstraint::new(
                                Arc::new(Expression::LiteralNone),
                                None,
                            ))),
                        );

                        target_abstract_environment
                            .edges
                            .insert((from.clone(), return_node.clone()), guards.clone());
                        target_abstract_environment.edges.insert(
                            (return_node.clone(), ConstraintNode::TypeExit),
                            imbl::OrdSet::default(),
                        );
                    }
                    target_abstract_environment.edges.insert(
                        (ConstraintNode::TypeExit, ConstraintNode::Exit),
                        imbl::OrdSet::default(),
                    );
                }
                if can_raise {
                    target_abstract_environment.edges.insert(
                        (from.clone(), ConstraintNode::ExceptionExit),
                        guards.clone(),
                    );
                    target_abstract_environment.edges.insert(
                        (ConstraintNode::ExceptionExit, ConstraintNode::Exit),
                        imbl::OrdSet::default(),
                    );
                }
            }
        }

        Ok(Some(target_abstract_environment))
    }

    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error> {
        Ok(analysis_state.abstract_states.get(node))
    }

    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: &Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error> {
        analysis_state.abstract_states.insert(*node, abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        _analysis_state: &Self::AnalysisState,
        _node: &Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        Ok(left.join(right))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProgramEntityNode {
    Entry,
    Entity(ProgramEntity),
    Exit,
}

impl Display for ProgramEntityNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramEntityNode::Entry => write!(f, "Entry"),
            ProgramEntityNode::Entity(entity) => write!(f, "{}", entity),
            ProgramEntityNode::Exit => write!(f, "Exit"),
        }
    }
}

pub trait ModuleLoader {
    type Error;

    fn load(&self, module_name: &ModuleName) -> Result<String, Self::Error>;
}

#[derive(Debug, Error)]
pub enum LoadModuleError {
    #[error("failed to load module {0}")]
    FilesystemError(#[from] FilesystemError),
    #[error("module not found")]
    ModuleNotFound,
    #[error("module does not have a source file loader")]
    NonSourceFileLoader,
}

pub struct SpecModuleLoader<F: Filesystem> {
    pub specs: HashMap<Identifier, FinderSpec<Identifier, F>>,
}

impl<F: Filesystem> ModuleLoader for SpecModuleLoader<F> {
    type Error = LoadModuleError;

    fn load(&self, module_name: &ModuleName) -> Result<String, Self::Error> {
        let mut finder_spec = self
            .specs
            .get(module_name.identifiers.first())
            .ok_or(LoadModuleError::ModuleNotFound)?;

        for identifier in module_name.identifiers.iter().skip(1) {
            finder_spec = finder_spec
                .submodules
                .get(identifier)
                .ok_or(LoadModuleError::ModuleNotFound)?;
        }

        match &finder_spec.spec {
            Spec::Module(ModuleSpec {
                kind: ModuleKind::Source,
                file_loader,
                ..
            })
            | Spec::Module(ModuleSpec {
                kind: ModuleKind::Extension,
                stub_spec: Some(StubSpec { file_loader, .. }),
                ..
            })
            | Spec::Stub(StubSpec { file_loader, .. }) => Ok(file_loader.read_file()?),
            _ => Err(LoadModuleError::NonSourceFileLoader),
        }
    }
}

#[derive(Debug, Error)]
pub enum ConstraintsError {
    #[error("failed to build constraints {0}")]
    BuildError(#[from] ConstraintsBuilderError),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct CfgAnalysis {
    pub specification: ProgramEntitySpecification,
    pub environment: ProgramEntityAbstractEnvironment,
}

pub fn analyse_cfg<'a>(
    cfg: &'a Cfg,
    line_index: &'a LineIndex,
    program_entity: ProgramEntity,
    program_entity_analysis_parent_state: Option<&'a ProgramEntityAbstractParentState<'a>>,
) -> BTreeMap<ProgramEntity, CfgAnalysis> {
    let constraint_builder = ConstraintsBuilder::new(
        cfg,
        line_index,
        &program_entity,
        program_entity_analysis_parent_state,
    );

    let mut program_entity_analysis_state =
        analysis(&constraint_builder, &mut DummyAnalysisObserver)
            .expect("constraint builder should work");

    let program_entity_exit_abstract_state = program_entity_analysis_state
        .abstract_states
        .remove(&ProgramPoint::Exit)
        .expect("ProgramPoint::Exit should exist in analysed cfg");

    let sub_program_entity_analysis_parent_state = ProgramEntityAbstractParentState::new(
        &program_entity_exit_abstract_state,
        &program_entity,
        program_entity_analysis_parent_state,
    );
    let mut program_entities = program_entity_exit_abstract_state
        .sub_program_entities
        .keys()
        .par_bridge()
        .flat_map(|sub_program_entity| {
            analyse_cfg(
                cfg.cfgs()
                    .get(&sub_program_entity.cfg_location.unwrap())
                    .unwrap(),
                line_index,
                sub_program_entity.clone(),
                Some(&sub_program_entity_analysis_parent_state),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let cfg_analysis = CfgAnalysis {
        specification: program_entity_analysis_parent_state
            .and_then(|parent_state| parent_state.state.sub_program_entities.get(&program_entity))
            .map(|context| context.specification.clone())
            .unwrap_or_default(),
        environment: program_entity_exit_abstract_state,
    };

    program_entities.insert(program_entity, cfg_analysis);

    program_entities
}

pub fn analyse_module<'a>(
    module_loader: &impl ModuleLoader<Error: Debug>,
    parent_state: Option<&ProgramEntityAbstractParentState>,
    module_name: &ModuleName,
) -> Option<BTreeMap<ProgramEntity, CfgAnalysis>> {
    let source = module_loader.load(&module_name).ok()?;
    let module = parse_module(&source).ok()?;
    let line_index = LineIndex::from_source_text(&source);
    let cfg = build_cfg(&line_index, module.syntax()).ok()?;
    let program_entity = ProgramEntity::new(
        Arc::new(Namespace::Module(module_name.clone())),
        None,
        ProgramEntityKind::Module,
    );
    Some(analyse_cfg(&cfg, &line_index, program_entity, parent_state))
}

pub fn create_constraints(
    program_entity: ProgramEntity,
    cfg_analysis: CfgAnalysis,
) -> (Arc<Namespace>, ProgramEntityConstraints) {
    (
        program_entity.namespace,
        ProgramEntityConstraints {
            specification: cfg_analysis.specification.clone(),
            constraint_graph: ConstraintGraph::new(
                cfg_analysis.environment.nodes.clone(),
                cfg_analysis.environment.edges.into_iter().fold(
                    imbl::OrdMap::default(),
                    |mut acc, ((from, to), guards)| {
                        acc.entry(from).or_default().insert(to, guards);
                        acc
                    },
                ),
            ),
        },
    )
}

pub fn analyse_program<E: Debug, C: ModuleLoader<Error = E> + Sync>(
    module_loader: &C,
    initial_modules: impl Iterator<Item = ModuleName>,
) -> ModuleDependentGraph {
    let builtins_module_name = Arc::new(QualifiedName::parse(BUILTINS_MODULE));

    let builtins_cfg_analyses = analyse_module(module_loader, None, &builtins_module_name)
        .expect("builtins module should be analysable");

    let builtins_module_node = ModuleNode::Module(builtins_module_name.clone());
    let builtins_entity = ProgramEntity::new(
        Arc::new(Namespace::Module(builtins_module_name.clone())),
        None,
        ProgramEntityKind::Module,
    );

    let builtins_module_analysis = &builtins_cfg_analyses[&builtins_entity];
    let builtin_parent_state = &ProgramEntityAbstractParentState::new(
        &builtins_module_analysis.environment,
        &builtins_entity,
        None,
    );

    let imports = builtins_cfg_analyses
        .values()
        .flat_map(|cfg_analysis| cfg_analysis.environment.imports.iter().cloned())
        .collect::<BTreeSet<_>>();

    let mut dependent_graph = ModuleDependentGraph::default();
    dependent_graph.add_dependent(ModuleNode::Entry, builtins_module_node.clone());
    dependent_graph.add_dependent(builtins_module_node.clone(), ModuleNode::Exit);
    for import in &imports {
        dependent_graph.add_dependent(
            ModuleNode::Module(import.clone()),
            builtins_module_node.clone(),
        );
    }

    let mut worklist = initial_modules
        .chain(imports)
        .filter(|import| *import != builtins_module_name)
        .collect::<BTreeSet<_>>();

    while !worklist.is_empty() {
        let analysed_modules = worklist
            .into_par_iter()
            .filter_map(|module_name| {
                let mut imports = BTreeSet::new();
                let constraints =
                    analyse_module(module_loader, Some(builtin_parent_state), &module_name)?
                        .into_iter()
                        .map(|(program_entity, cfg_analysis)| {
                            imports.extend(cfg_analysis.environment.imports.clone());
                            create_constraints(program_entity, cfg_analysis)
                        })
                        .collect();
                Some((ModuleNode::Module(module_name), constraints, imports))
            })
            .collect::<Vec<_>>();

        worklist = BTreeSet::new();
        for (module_node, constraints, imports) in analysed_modules {
            dependent_graph.add_dependent(builtins_module_node.clone(), module_node.clone());
            dependent_graph.remove_dependent(builtins_module_node.clone(), ModuleNode::Exit);
            if !dependent_graph.dependents.contains_key(&module_node) {
                dependent_graph.add_dependent(module_node.clone(), ModuleNode::Exit);
            }

            for import in imports {
                if import == builtins_module_name {
                    continue;
                }
                let import_module_node = ModuleNode::Module(import.clone());

                dependent_graph.add_dependent(import_module_node.clone(), module_node.clone());
                dependent_graph.remove_dependent(import_module_node.clone(), ModuleNode::Exit);

                if !dependent_graph.nodes.contains_key(&import_module_node) {
                    worklist.insert(import.clone());
                }
            }

            dependent_graph.nodes.insert(module_node, constraints);
        }
    }

    dependent_graph.insert(
        builtins_module_node,
        builtins_cfg_analyses
            .into_iter()
            .map(|(program_entity, cfg_analysis)| create_constraints(program_entity, cfg_analysis))
            .collect(),
    );

    dependent_graph
}

#[cfg(test)]
mod tests {
    use super::*;
    use apygen_cfg::graph::dot::ToDot;
    use indoc::indoc;
    use rstest::rstest;
    use std::convert::Infallible;

    pub struct TestModuleLoader {
        pub modules: HashMap<ModuleName, String>,
    }

    impl ModuleLoader for TestModuleLoader {
        type Error = Infallible;
        fn load(&self, module_name: &ModuleName) -> Result<String, Self::Error> {
            Ok(self.modules.get(module_name).cloned().unwrap())
        }
    }

    const TEST_BUILTINS: &str = indoc! {r##"
        class int:
            pass
    "##};

    #[rstest]
    #[case::import(
        "import some_module",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Module(some_module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(builtins)" -> "Module(some_module)";
            "Module(module)" -> "Exit";
            "Module(some_module)" -> "Module(module)";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::import_as(
        "import some_module as mod",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Module(some_module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(builtins)" -> "Module(some_module)";
            "Module(module)" -> "Exit";
            "Module(some_module)" -> "Module(module)";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:22)" [label="#import(some_module) ⊑ mod@{module[1:22]} ∧ #defined(mod@{module[1:22]})"];
            "Entry" -> "Constraint(location=1:22)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:22)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::import_submodule(
        "import some_module.submodule",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Module(some_module.submodule)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(builtins)" -> "Module(some_module.submodule)";
            "Module(module)" -> "Exit";
            "Module(some_module.submodule)" -> "Module(module)";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Constraint(location=1:19)" [label="#import(some_module.submodule) ⊑ (some_module@{module[1:7]}).submodule ∧ #defined(some_module@{module[1:19]})"];
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint(location=1:19)" [label="#succeed(#import(some_module.submodule))"];
            "Constraint(location=1:7)" -> "ExceptionExit" [label="#raise(#import(some_module.submodule))"];
            "Constraint(location=1:19)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::import_module_and_submodule(
        "import some_module, some_module.submodule",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Module(some_module)";
            "Module(some_module.submodule)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(builtins)" -> "Module(some_module)";
            "Module(builtins)" -> "Module(some_module.submodule)";
            "Module(module)" -> "Exit";
            "Module(some_module)" -> "Module(module)";
            "Module(some_module.submodule)" -> "Module(module)";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Constraint(location=1:20)" [label="#import(some_module) ⊑ some_module@{module[1:20]} ∧ #defined(some_module@{module[1:20]})"];
            "Constraint(location=1:32)" [label="#import(some_module.submodule) ⊑ (some_module@{module[1:20]}).submodule ∧ #defined(some_module@{module[1:32]})"];
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint(location=1:20)" [label="#succeed(#import(some_module))"];
            "Constraint(location=1:7)" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint(location=1:20)" -> "Constraint(location=1:32)" [label="#succeed(#import(some_module.submodule))"];
            "Constraint(location=1:20)" -> "ExceptionExit" [label="#raise(#import(some_module.submodule))"];
            "Constraint(location=1:32)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::multiple_import(
        "import some_module, another_module",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(another_module)";
            "Module(builtins)";
            "Module(module)";
            "Module(some_module)";
            "Entry" -> "Module(builtins)";
            "Module(another_module)" -> "Module(module)";
            "Module(builtins)" -> "Module(another_module)";
            "Module(builtins)" -> "Module(module)";
            "Module(builtins)" -> "Module(some_module)";
            "Module(module)" -> "Exit";
            "Module(some_module)" -> "Module(module)";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Constraint(location=1:20)" [label="#import(another_module) ⊑ another_module@{module[1:20]} ∧ #defined(another_module@{module[1:20]})"];
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint(location=1:20)" [label="#succeed(#import(another_module))"];
            "Constraint(location=1:7)" -> "ExceptionExit" [label="#raise(#import(another_module))"];
            "Constraint(location=1:20)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::multiple_import_override(
        "import some_module as mod, another_module as mod",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(another_module)";
            "Module(builtins)";
            "Module(module)";
            "Module(some_module)";
            "Entry" -> "Module(builtins)";
            "Module(another_module)" -> "Module(module)";
            "Module(builtins)" -> "Module(another_module)";
            "Module(builtins)" -> "Module(module)";
            "Module(builtins)" -> "Module(some_module)";
            "Module(module)" -> "Exit";
            "Module(some_module)" -> "Module(module)";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:22)" [label="#import(some_module) ⊑ mod@{module[1:22]} ∧ #defined(mod@{module[1:22]})"];
            "Constraint(location=1:45)" [label="#import(another_module) ⊑ mod@{module[1:45]} ∧ #defined(mod@{module[1:45]})"];
            "Entry" -> "Constraint(location=1:22)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:22)" -> "Constraint(location=1:45)" [label="#succeed(#import(another_module))"];
            "Constraint(location=1:22)" -> "ExceptionExit" [label="#raise(#import(another_module))"];
            "Constraint(location=1:45)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::int_constant_assignment(
        "a = 42",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="42 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
        }
        "##},
    )]
    #[case::bigint_constant_assignment(
        "a = 4200000000000000000000000000",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="4200000000000000000000000000 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
        }
        "##},
    )]
    #[case::add_operation(
        "add = 42 + 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) + (67) ⊑ add@{module[1:0]} ∧ #defined(add@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) + (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) + (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::sub_operation(
        "sub = 42 - 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) - (67) ⊑ sub@{module[1:0]} ∧ #defined(sub@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) - (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) - (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::mult_operation(
        "mult = 42 * 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) * (67) ⊑ mult@{module[1:0]} ∧ #defined(mult@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) * (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) * (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::mat_mult_operation(
        "mat_mult = 42 @ 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) @ (67) ⊑ mat_mult@{module[1:0]} ∧ #defined(mat_mult@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) @ (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) @ (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::div_operation(
        "div = 42 / 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) / (67) ⊑ div@{module[1:0]} ∧ #defined(div@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) / (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) / (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::floor_div_operation(
        "floor_div = 42 // 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) // (67) ⊑ floor_div@{module[1:0]} ∧ #defined(floor_div@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) // (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) // (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::mod_operation(
        "mod = 42 % 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) % (67) ⊑ mod@{module[1:0]} ∧ #defined(mod@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) % (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) % (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::pow_operation(
        "pow = 42 ** 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) ** (67) ⊑ pow@{module[1:0]} ∧ #defined(pow@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) ** (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) ** (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::shl_operation(
        "shl = 42 << 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) << (67) ⊑ shl@{module[1:0]} ∧ #defined(shl@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) << (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) << (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::shr_operation(
        "shr = 42 >> 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) >> (67) ⊑ shr@{module[1:0]} ∧ #defined(shr@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) >> (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) >> (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::bit_or_operation(
        "bit_or = 42 | 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) | (67) ⊑ bit_or@{module[1:0]} ∧ #defined(bit_or@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) | (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) | (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::bit_xor_operation(
        "bit_xor = 42 ^ 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) ^ (67) ⊑ bit_xor@{module[1:0]} ∧ #defined(bit_xor@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) ^ (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) ^ (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::bit_and_operation(
        "bit_and = 42 & 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) & (67) ⊑ bit_and@{module[1:0]} ∧ #defined(bit_and@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) & (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) & (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::and_operation(
        "and_ = 42 and 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) and (67) ⊑ and_@{module[1:0]} ∧ #defined(and_@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) and (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) and (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::or_operation(
        "or_ = 42 or 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) or (67) ⊑ or_@{module[1:0]} ∧ #defined(or_@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) or (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) or (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::eq_operation(
        "eq = 42 == 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) == (67) ⊑ eq@{module[1:0]} ∧ #defined(eq@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) == (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) == (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::not_eq_operation(
        "not_eq = 42 != 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) != (67) ⊑ not_eq@{module[1:0]} ∧ #defined(not_eq@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) != (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) != (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::lt_operation(
        "lt = 42 < 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) < (67) ⊑ lt@{module[1:0]} ∧ #defined(lt@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) < (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) < (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::gt_operation(
        "gt = 42 > 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) > (67) ⊑ gt@{module[1:0]} ∧ #defined(gt@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) > (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) > (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::lte_operation(
        "lte = 42 <= 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) <= (67) ⊑ lte@{module[1:0]} ∧ #defined(lte@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) <= (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) <= (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::gte_operation(
        "gte = 42 >= 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) >= (67) ⊑ gte@{module[1:0]} ∧ #defined(gte@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) >= (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) >= (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::is_operation(
        "is_ = 42 is 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) is (67) ⊑ is_@{module[1:0]} ∧ #defined(is_@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) is (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) is (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::is_not_operation(
        "is_not = 42 is not 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) is not (67) ⊑ is_not@{module[1:0]} ∧ #defined(is_not@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) is not (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) is not (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::in_operation(
        "in_ = 42 in 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) in (67) ⊑ in_@{module[1:0]} ∧ #defined(in_@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) in (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) in (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::not_in_operation(
        "not_in = 42 not in 67",
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) not in (67) ⊑ not_in@{module[1:0]} ∧ #defined(not_in@{module[1:0]})"];
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) not in (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) not in (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::add_same_variable(
        indoc! {r##"
        a = 4

        b = a + a
        "##},
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="4 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "Constraint(location=3:0)" [label="(a@{module[3:4]}) + (a@{module[3:8]}) ⊑ b@{module[3:0]} ∧ #defined(b@{module[3:0]})"];
            "Constraint(location=3:4)" [label="a@{module[1:0]} ⊑ a@{module[3:4]} ∧ a@{module[1:0]} ⊑ a@{module[3:8]}"];
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint(location=3:4)" [label="#succeed(a@{module[1:0]})"];
            "Constraint(location=1:0)" -> "ExceptionExit" [label="#raise(a@{module[1:0]})"];
            "Constraint(location=3:0)" -> "Constraint()";
            "Constraint(location=3:4)" -> "Constraint(location=3:0)" [label="#succeed((a@{module[3:4]}) + (a@{module[3:8]}))"];
            "Constraint(location=3:4)" -> "ExceptionExit" [label="#raise((a@{module[3:4]}) + (a@{module[3:8]}))"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::simple_if_statement(
        indoc! {r##"
        x = True

        if x:
            a = 42
        else:
            a = 67

        b = a
        "##},
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="True ⊑ x@{module[1:0]} ∧ #defined(x@{module[1:0]})"];
            "Constraint(location=3:3)" [label="x@{module[1:0]} ⊑ x@{module[3:3]}"];
            "Constraint(location=4:4)" [label="42 ⊑ a@{module[4:4]} ∧ #defined(a@{module[4:4]})"];
            "Constraint(location=6:4)" [label="67 ⊑ a@{module[6:4]} ∧ #defined(a@{module[6:4]})"];
            "Constraint(location=8:0)" [label="a@{module[8:4]} ⊑ b@{module[8:0]} ∧ #defined(b@{module[8:0]})"];
            "Constraint(location=8:4)" [label="a@{module[4:4]} ⊑ a@{module[8:4]} ∧ a@{module[6:4]} ⊑ a@{module[8:4]}"];
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint(location=3:3)" [label="#succeed(x@{module[1:0]})"];
            "Constraint(location=1:0)" -> "ExceptionExit" [label="#raise(x@{module[1:0]})"];
            "Constraint(location=3:3)" -> "Constraint(location=4:4)" [label="#is_true(x@{module[3:3]})"];
            "Constraint(location=3:3)" -> "Constraint(location=6:4)" [label="#is_false(x@{module[3:3]})"];
            "Constraint(location=3:3)" -> "ExceptionExit" [label="#raise(x@{module[3:3]})"];
            "Constraint(location=4:4)" -> "Constraint(location=8:4)" [label="#succeed(a@{module[4:4]})"];
            "Constraint(location=4:4)" -> "Constraint(location=8:4)" [label="#succeed(a@{module[6:4]})"];
            "Constraint(location=4:4)" -> "ExceptionExit" [label="#raise(a@{module[4:4]})"];
            "Constraint(location=4:4)" -> "ExceptionExit" [label="#raise(a@{module[6:4]})"];
            "Constraint(location=6:4)" -> "Constraint(location=8:4)" [label="#succeed(a@{module[4:4]})"];
            "Constraint(location=6:4)" -> "Constraint(location=8:4)" [label="#succeed(a@{module[6:4]})"];
            "Constraint(location=6:4)" -> "ExceptionExit" [label="#raise(a@{module[4:4]})"];
            "Constraint(location=6:4)" -> "ExceptionExit" [label="#raise(a@{module[6:4]})"];
            "Constraint(location=8:0)" -> "Constraint()";
            "Constraint(location=8:4)" -> "Constraint(location=8:0)" [label="#succeed(a@{module[8:4]})"];
            "Constraint(location=8:4)" -> "ExceptionExit" [label="#raise(a@{module[8:4]})"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::simple_while_statement(
        indoc! {r##"
        a = 0

        while a < 5:
            a = a + 1

        b = a
        "##},
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="0 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "Constraint(location=3:6)" [label="a@{module[1:0]} ⊑ a@{module[3:6]} ∧ a@{module[4:4]} ⊑ a@{module[3:6]}"];
            "Constraint(location=4:4)" [label="(a@{module[4:8]}) + (1) ⊑ a@{module[4:4]} ∧ #defined(a@{module[4:4]})"];
            "Constraint(location=4:8)" [label="a@{module[1:0]} ⊑ a@{module[4:8]} ∧ a@{module[4:4]} ⊑ a@{module[4:8]}"];
            "Constraint(location=6:0)" [label="a@{module[6:4]} ⊑ b@{module[6:0]} ∧ #defined(b@{module[6:0]})"];
            "Constraint(location=6:4)" [label="a@{module[1:0]} ⊑ a@{module[6:4]} ∧ a@{module[4:4]} ⊑ a@{module[6:4]}"];
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint(location=3:6)" [label="#succeed(a@{module[1:0]})"];
            "Constraint(location=1:0)" -> "Constraint(location=3:6)" [label="#succeed(a@{module[4:4]})"];
            "Constraint(location=1:0)" -> "ExceptionExit" [label="#raise(a@{module[1:0]})"];
            "Constraint(location=1:0)" -> "ExceptionExit" [label="#raise(a@{module[4:4]})"];
            "Constraint(location=3:6)" -> "Constraint(location=4:8, id=#empty)" [label="#is_true((a@{module[3:6]}) < (5))"];
            "Constraint(location=3:6)" -> "Constraint(location=6:4, id=#empty)" [label="#is_false((a@{module[3:6]}) < (5))"];
            "Constraint(location=3:6)" -> "ExceptionExit" [label="#raise((a@{module[3:6]}) < (5))"];
            "Constraint(location=4:4)" -> "Constraint(location=3:6)" [label="#succeed(a@{module[1:0]})"];
            "Constraint(location=4:4)" -> "Constraint(location=3:6)" [label="#succeed(a@{module[4:4]})"];
            "Constraint(location=4:4)" -> "ExceptionExit" [label="#raise(a@{module[1:0]})"];
            "Constraint(location=4:4)" -> "ExceptionExit" [label="#raise(a@{module[4:4]})"];
            "Constraint(location=4:8)" -> "Constraint(location=4:4)" [label="#succeed((a@{module[4:8]}) + (1))"];
            "Constraint(location=4:8)" -> "ExceptionExit" [label="#raise((a@{module[4:8]}) + (1))"];
            "Constraint(location=4:8, id=#empty)" -> "Constraint(location=4:8)" [label="#succeed(a@{module[1:0]})"];
            "Constraint(location=4:8, id=#empty)" -> "Constraint(location=4:8)" [label="#succeed(a@{module[4:4]})"];
            "Constraint(location=4:8, id=#empty)" -> "ExceptionExit" [label="#raise(a@{module[1:0]})"];
            "Constraint(location=4:8, id=#empty)" -> "ExceptionExit" [label="#raise(a@{module[4:4]})"];
            "Constraint(location=6:0)" -> "Constraint()";
            "Constraint(location=6:4)" -> "Constraint(location=6:0)" [label="#succeed(a@{module[6:4]})"];
            "Constraint(location=6:4)" -> "ExceptionExit" [label="#raise(a@{module[6:4]})"];
            "Constraint(location=6:4, id=#empty)" -> "Constraint(location=6:4)" [label="#succeed(a@{module[1:0]})"];
            "Constraint(location=6:4, id=#empty)" -> "Constraint(location=6:4)" [label="#succeed(a@{module[4:4]})"];
            "Constraint(location=6:4, id=#empty)" -> "ExceptionExit" [label="#raise(a@{module[1:0]})"];
            "Constraint(location=6:4, id=#empty)" -> "ExceptionExit" [label="#raise(a@{module[4:4]})"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b: int):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:4)" [label="#function(identifier=module[add_two@{1:4}], async=false) ⊑ add_two@{module[1:4]} ∧ #defined(add_two@{module[1:4]})"];
            "Constraint(location=1:11)" [label="int@{builtins[1:6]} ⊑ int@{module[1:15]} ∧ int@{builtins[1:6]} ⊑ int@{module[1:23]}"];
            "Constraint(location=4:0)" [label="(add_two@{module[4:9]})(42, 67) ⊑ result@{module[4:0]} ∧ #defined(result@{module[4:0]})"];
            "Constraint(location=4:9)" [label="add_two@{module[1:4]} ⊑ add_two@{module[4:9]}"];
            "Entry" -> "Constraint(location=1:11)" [label="#succeed(int@{builtins[1:6]})"];
            "Entry" -> "ExceptionExit" [label="#raise(int@{builtins[1:6]})"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:4)" -> "Constraint(location=4:9)" [label="#succeed(add_two@{module[1:4]})"];
            "Constraint(location=1:4)" -> "ExceptionExit" [label="#raise(add_two@{module[1:4]})"];
            "Constraint(location=1:11)" -> "Constraint(location=1:4)" [label="#succeed(#function(identifier=module[add_two@{1:4}], async=false))"];
            "Constraint(location=1:11)" -> "ExceptionExit" [label="#raise(#function(identifier=module[add_two@{1:4}], async=false))"];
            "Constraint(location=4:0)" -> "Constraint()";
            "Constraint(location=4:9)" -> "Constraint(location=4:0)" [label="#succeed((add_two@{module[4:9]})(42, 67))"];
            "Constraint(location=4:9)" -> "ExceptionExit" [label="#raise((add_two@{module[4:9]})(42, 67))"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        specification "module[add_two@{1:4}]":
            {arguments: {a@{module[1:12]}: #annotated(int@{module[1:15]}), b@{module[1:20]}: #annotated(int@{module[1:23]})}, return_type: {}, exceptions: {}}
        digraph "module[add_two@{1:4}]" {
            "Constraint(location=2:4)" [label="#return((a@{module[add_two@{1:4}][2:11]}) + (b@{module[add_two@{1:4}][2:15]}))"];
            "Constraint(location=2:11)" [label="a@{module[add_two@{1:4}][1:12]} ⊑ a@{module[add_two@{1:4}][2:11]} ∧ b@{module[add_two@{1:4}][1:20]} ⊑ b@{module[add_two@{1:4}][2:15]}"];
            "Entry" -> "Constraint(location=2:11)" [label="#succeed(a@{module[add_two@{1:4}][1:12]})"];
            "Entry" -> "Constraint(location=2:11)" [label="#succeed(b@{module[add_two@{1:4}][1:20]})"];
            "Entry" -> "ExceptionExit" [label="#raise(a@{module[add_two@{1:4}][1:12]})"];
            "Entry" -> "ExceptionExit" [label="#raise(b@{module[add_two@{1:4}][1:20]})"];
            "Constraint(location=2:4)" -> "TypeExit";
            "Constraint(location=2:11)" -> "Constraint(location=2:4)";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[rstest]
    #[case::forward_reference(
        indoc! {r##"
        def foo():
            return CONST

        CONST = 5

        result = foo()
        "##},
        indoc! {r##"
        digraph "DependentGraph" {
            "Module(builtins)";
            "Module(module)";
            "Entry" -> "Module(builtins)";
            "Module(builtins)" -> "Module(module)";
            "Module(module)" -> "Exit";
        }
        specification "module":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module" {
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:4)" [label="#function(identifier=module[foo@{1:4}], async=false) ⊑ foo@{module[1:4]} ∧ #defined(foo@{module[1:4]})"];
            "Constraint(location=4:0)" [label="5 ⊑ CONST@{module[4:0]} ∧ #defined(CONST@{module[4:0]})"];
            "Constraint(location=6:0)" [label="(foo@{module[6:9]})() ⊑ result@{module[6:0]} ∧ #defined(result@{module[6:0]})"];
            "Constraint(location=6:9)" [label="foo@{module[1:4]} ⊑ foo@{module[6:9]}"];
            "Entry" -> "Constraint(location=1:4)" [label="#succeed(#function(identifier=module[foo@{1:4}], async=false))"];
            "Entry" -> "ExceptionExit" [label="#raise(#function(identifier=module[foo@{1:4}], async=false))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:4)" -> "Constraint(location=4:0)";
            "Constraint(location=4:0)" -> "Constraint(location=6:9)" [label="#succeed(foo@{module[1:4]})"];
            "Constraint(location=4:0)" -> "ExceptionExit" [label="#raise(foo@{module[1:4]})"];
            "Constraint(location=6:0)" -> "Constraint()";
            "Constraint(location=6:9)" -> "Constraint(location=6:0)" [label="#succeed((foo@{module[6:9]})())"];
            "Constraint(location=6:9)" -> "ExceptionExit" [label="#raise((foo@{module[6:9]})())"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        specification "module[foo@{1:4}]":
            {arguments: {}, return_type: {}, exceptions: {}}
        digraph "module[foo@{1:4}]" {
            "Constraint(location=2:4)" [label="#return(CONST@{module[foo@{1:4}][2:11]})"];
            "Constraint(location=2:11)" [label="CONST@{module[4:0]} ⊑ CONST@{module[foo@{1:4}][2:11]}"];
            "Entry" -> "Constraint(location=2:11)" [label="#succeed(CONST@{module[4:0]})"];
            "Entry" -> "ExceptionExit" [label="#raise(CONST@{module[4:0]})"];
            "Constraint(location=2:4)" -> "TypeExit";
            "Constraint(location=2:11)" -> "Constraint(location=2:4)";
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    fn test_program_analysis(#[case] source: &str, #[case] expected_constraints: &str) {
        let module_name = Arc::new(QualifiedName::parse("module"));

        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([
                (module_name.clone(), source.to_string()),
                (Arc::new(QualifiedName::parse("some_module")), String::new()),
                (
                    Arc::new(QualifiedName::parse("some_module.submodule")),
                    String::new(),
                ),
                (
                    Arc::new(QualifiedName::parse("another_module")),
                    String::new(),
                ),
                (
                    Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                    TEST_BUILTINS.to_owned(),
                ),
            ]),
        };
        let dependent_graph = analyse_program(&module_loader, std::iter::once(module_name.clone()));

        let mut actual_constraints = dependent_graph.dot("DependentGraph");

        for program_entities in dependent_graph.nodes.values() {
            for (namespace, constraints) in program_entities {
                if *namespace.module_name() != module_name {
                    continue;
                }
                actual_constraints.push_str(&format!(
                    "specification \"{}\":\n    {}\n",
                    namespace, constraints.specification
                ));
                actual_constraints
                    .push_str(&constraints.constraint_graph.dot(&namespace.to_string()));
            }
        }

        assert_eq!(
            expected_constraints, actual_constraints,
            "{actual_constraints}"
        );
    }
}
