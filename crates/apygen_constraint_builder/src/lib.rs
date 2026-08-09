#![recursion_limit = "256"]

use crate::analysis::lattice::{Join, OrdJoin};
use crate::analysis::{DummyAnalysisObserver, GraphAnalyser, analysis};
use crate::cfg::ast;
use crate::cfg::build_cfg;
use crate::cfg::convert_text_size_to_location;
use crate::cfg::graph::{Graph, OrdGraph};
use crate::cfg::parser::parse_module;
use crate::cfg::source_file::LineIndex;
use crate::cfg::text_size::Ranged;
use crate::cfg::{Cfg, CfgEdgeKind, CfgNode as StmtNode, ProgramPoint};
use crate::constraint_graph::expressions::{
    BinaryOperator, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionFunction, ExpressionImport, ExpressionOverride,
    ExpressionSubscript, ExpressionUnary, ExpressionVariableDefinition,
    ExpressionVariableReference, KeywordArgument, Parameter, ParameterKind, UnaryOperator,
};
use crate::constraint_graph::identifiers::smol_str::SmolStrBuilder;
use crate::constraint_graph::identifiers::{Location, NamedQualifiedLocation, Namespace, SmolStr};
use crate::constraint_graph::primitives::literals::{
    LiteralBool, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInt, LiteralStr,
};
use crate::constraint_graph::primitives::{BigInt, Complex64, Int, Num};
use crate::constraint_graph::{
    Constraint, ConstraintGraph, ConstraintNode, Guard, ImportGraph, IncludeConstraint,
    ReturnConstraint,
};
use crate::finder::filesystem::{Error as FilesystemError, Filesystem};
use crate::finder::pathfinder::{FinderSpec, ModuleKind, ModuleSpec, Spec, StubSpec};
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use std::collections::{BTreeSet, HashMap};
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;
use thiserror::Error;

pub use apygen_analysis as analysis;
pub use apygen_cfg as cfg;
pub use apygen_constraint_graph as constraint_graph;
pub use apygen_finder as finder;

pub const BUILTINS_MODULE: SmolStr = SmolStr::new_static("builtins");

#[derive(Debug, Error)]
pub enum FromAssignmentTargetError {
    #[error("the expression is not a valid assignment target")]
    InvalidTarget,
}

pub enum AssignmentTarget<'e> {
    Name(SmolStr),
    Attribute {
        target: Box<AssignmentTarget<'e>>,
        attr: SmolStr,
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
        Ok(AssignmentTarget::Name(SmolStr::new(value.id.as_str())))
    }
}

impl<'e> TryFrom<&'e ast::ExprAttribute> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ast::ExprAttribute) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Attribute {
            attr: SmolStr::new(value.attr.id.as_str()),
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
    pub kind: ProgramEntityKind,
}

impl ProgramEntity {
    pub fn new(namespace: Arc<Namespace>, kind: ProgramEntityKind) -> Self {
        Self { namespace, kind }
    }
}

impl Display for ProgramEntity {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}Entity({})", self.kind, self.namespace)
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReturnStatus {
    #[default]
    NotReturning,
    Returning,
}

impl OrdJoin for ReturnStatus {}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityAbstractEnvironment {
    pub return_status: ReturnStatus,
    pub current_nodes: imbl::OrdMap<ConstraintNode, imbl::OrdSet<Guard>>,
    pub nodes: imbl::OrdMap<ConstraintNode, imbl::OrdSet<Constraint>>,
    pub edges: imbl::OrdMap<(ConstraintNode, ConstraintNode), imbl::OrdSet<Guard>>,
    pub imports: imbl::OrdSet<SmolStr>,
    pub sub_program_entities: imbl::OrdMap<ProgramEntity, ProgramEntityAbstractEnvironment>,
}

impl Join for ProgramEntityAbstractEnvironment {
    fn join(&self, other: &Self) -> Self {
        Self {
            return_status: self.return_status.join(&other.return_status),
            current_nodes: self.current_nodes.join(&other.current_nodes),
            nodes: self.nodes.join(&other.nodes),
            edges: self.edges.join(&other.edges),
            imports: self.imports.join(&other.imports),
            sub_program_entities: self.sub_program_entities.join(&other.sub_program_entities),
        }
    }
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionEval<T> {
    pub value: T,
    pub variables: imbl::OrdSet<SmolStr>,
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
}

impl<'a> ConstraintsBuilder<'a> {
    pub fn new(
        cfg: &'a Cfg<'a>,
        line_index: &'a LineIndex,
        program_entity: &'a ProgramEntity,
    ) -> ConstraintsBuilder<'a> {
        ConstraintsBuilder {
            cfg,
            line_index,
            program_entity,
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
                Guard::ForwardReference => true,
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

    pub fn create_include_constraint(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        additional_constraints: imbl::OrdSet<Constraint>,
        left: Arc<Expression>,
        right: Arc<Expression>,
    ) -> ConstraintNode {
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
            return node;
        }

        let current_empty_constraint = ConstraintNode::Constraint {
            location: Some(location.clone()),
            id: Some(SmolStr::new_static("#empty")),
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

        node
    }

    pub fn assign_variable(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        variable_name: SmolStr,
        type_expression: Arc<Expression>,
        initialised: bool,
    ) {
        let expression_variable = ExpressionVariableDefinition::new(NamedQualifiedLocation::new(
            variable_name.clone(),
            location.clone(),
            self.program_entity.namespace.clone(),
        ));

        self.create_include_constraint(
            abstract_environment,
            location.clone(),
            if initialised {
                imbl::OrdSet::unit(Constraint::DefinedVariable(expression_variable.clone()))
            } else {
                imbl::OrdSet::default()
            },
            type_expression,
            Arc::new(Expression::VariableDefinition(expression_variable)),
        );
    }

    pub fn assign_empty_constraint(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: Location,
        new_guards: imbl::OrdSet<Guard>,
        allow_simplify: bool,
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
                    abstract_environment.current_nodes.len() == 1
                        && guards.is_empty()
                        && allow_simplify
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

    pub fn gen_location(&self, ranged: &impl Ranged) -> Location {
        let program_point_location =
            convert_text_size_to_location(self.line_index, ranged.start()).unwrap();
        Location::new(program_point_location.line, program_point_location.offset)
    }

    pub fn evaluate_parameter(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        function_namespace: &Arc<Namespace>,
        parameter: &ast::Parameter,
    ) -> Result<(ExpressionVariableDefinition, Option<Expression>), ConstraintsBuilderError> {
        let parameter_name = SmolStr::new(&parameter.name);

        let annotation = if let Some(annotation) = &parameter.annotation {
            Some(Expression::Annotated(ExpressionAnnotated::new(Arc::new(
                self.evaluate_expr(&namespace, abstract_environment, &annotation)?,
            ))))
        } else {
            None
        };

        Ok((
            ExpressionVariableDefinition::new(NamedQualifiedLocation::new(
                parameter_name,
                self.gen_location(parameter),
                function_namespace.clone(),
            )),
            annotation,
        ))
    }

    pub fn evaluate_parameter_with_default(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        function_namespace: &Arc<Namespace>,
        parameter_with_default: &ast::ParameterWithDefault,
    ) -> Result<(ExpressionVariableDefinition, Option<Expression>), ConstraintsBuilderError> {
        let (parameter_name, annotation_eval_option) = self.evaluate_parameter(
            namespace,
            abstract_environment,
            function_namespace,
            &parameter_with_default.parameter,
        )?;

        let parameter_eval_option = if let Some(default) = &parameter_with_default.default {
            let default = self.evaluate_expr(&namespace, abstract_environment, &default)?;

            if let Some(annotation) = annotation_eval_option {
                Some(Expression::Override(ExpressionOverride::new(
                    Arc::new(annotation),
                    Arc::new(default),
                )))
            } else {
                Some(default)
            }
        } else {
            annotation_eval_option
        };

        Ok((parameter_name, parameter_eval_option))
    }

    pub fn gen_parameters(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        function_namespace: &Arc<Namespace>,
        parameters: &ast::Parameters,
    ) -> Result<imbl::Vector<(Parameter, Option<Arc<Expression>>)>, ConstraintsBuilderError> {
        let positional_only_parameters = parameters.posonlyargs.iter().map(|parameter| {
            Ok((
                self.evaluate_parameter_with_default(
                    namespace,
                    abstract_environment,
                    function_namespace,
                    &parameter,
                )?,
                ParameterKind::PositionalOnly,
            ))
        });
        let positional_or_keyword_parameters = parameters.args.iter().map(|parameter| {
            Ok((
                self.evaluate_parameter(
                    namespace,
                    abstract_environment,
                    function_namespace,
                    &parameter.parameter,
                )?,
                ParameterKind::PositionalOrKeyword,
            ))
        });
        let var_positional_parameters = parameters.vararg.iter().map(|parameter| {
            Ok((
                self.evaluate_parameter(
                    namespace,
                    abstract_environment,
                    function_namespace,
                    &parameter,
                )?,
                ParameterKind::VarPositional,
            ))
        });
        let keyword_only_parameters = parameters.kwonlyargs.iter().map(|parameter| {
            Ok((
                self.evaluate_parameter_with_default(
                    namespace,
                    abstract_environment,
                    function_namespace,
                    &parameter,
                )?,
                ParameterKind::KeywordOnly,
            ))
        });
        let var_keyword_parameters = parameters.kwarg.iter().map(|parameter| {
            Ok((
                self.evaluate_parameter(
                    namespace,
                    abstract_environment,
                    function_namespace,
                    &parameter,
                )?,
                ParameterKind::VarKeyword,
            ))
        });

        let parameter_evals = positional_only_parameters
            .chain(positional_or_keyword_parameters)
            .chain(var_positional_parameters)
            .chain(keyword_only_parameters)
            .chain(var_keyword_parameters)
            .collect::<Result<
                Vec<(
                    (ExpressionVariableDefinition, Option<Expression>),
                    ParameterKind,
                )>,
                _,
            >>()?;

        Ok(parameter_evals
            .into_iter()
            .map(|((variable_name, expression), kind)| {
                (
                    Parameter::new(variable_name, kind, false),
                    expression.map(|expression| Arc::new(expression)),
                )
            })
            .collect())
    }

    pub fn evaluate_expr_bool_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_bool_op: &ast::ExprBoolOp,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let mut values_iter = expr_bool_op.values.iter();

        let mut expression = match values_iter.next() {
            Some(value) => self.evaluate_expr(namespace, abstract_environment, value)?,
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
            expression = Expression::Binary(ExpressionBinary {
                left: Arc::new(expression),
                operator: operator.clone(),
                right: Arc::new(self.evaluate_expr(namespace, abstract_environment, &value)?),
            });
        }

        Ok(expression)
    }

    pub fn evaluate_expr_bin_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_bin_op: &ast::ExprBinOp,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let left = self.evaluate_expr(namespace, abstract_environment, &expr_bin_op.left)?;
        let right = self.evaluate_expr(namespace, abstract_environment, &expr_bin_op.right)?;

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

        Ok(Expression::Binary(ExpressionBinary {
            left: Arc::new(left),
            operator,
            right: Arc::new(right),
        }))
    }

    pub fn evaluate_expr_unary_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_unary_op: &ast::ExprUnaryOp,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let operand =
            self.evaluate_expr(namespace, abstract_environment, &expr_unary_op.operand)?;

        let operator = match expr_unary_op.op {
            ast::UnaryOp::Invert => UnaryOperator::Invert,
            ast::UnaryOp::Not => UnaryOperator::Not,
            ast::UnaryOp::UAdd => UnaryOperator::UAdd,
            ast::UnaryOp::USub => UnaryOperator::USub,
        };

        Ok(Expression::Unary(ExpressionUnary {
            operator,
            operand: Arc::new(operand),
        }))
    }

    pub fn evaluate_expr_compare(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_compare: &ast::ExprCompare,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let mut expression =
            self.evaluate_expr(namespace, abstract_environment, &expr_compare.left)?;

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

            let comparator = self.evaluate_expr(namespace, abstract_environment, comparator)?;

            expression = Expression::Binary(ExpressionBinary {
                left: Arc::new(expression),
                operator,
                right: Arc::new(comparator),
            });
        }

        Ok(expression)
    }

    pub fn evaluate_expr_call(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_call: &ast::ExprCall,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let func = self.evaluate_expr(namespace, abstract_environment, &expr_call.func)?;

        let mut positional_arguments: imbl::Vector<Arc<Expression>> = imbl::Vector::new();
        for positional_argument in &expr_call.arguments.args {
            positional_arguments.push_back(Arc::new(self.evaluate_expr(
                namespace,
                abstract_environment,
                &positional_argument,
            )?));
        }

        let mut keyword_arguments: imbl::Vector<KeywordArgument> = imbl::Vector::new();
        for keyword_argument in &expr_call.arguments.keywords {
            let keyword_name = match &keyword_argument.arg {
                Some(identifier) => Some(SmolStr::new(&identifier)),
                None => None,
            };
            keyword_arguments.push_back(KeywordArgument {
                name: keyword_name,
                value: Arc::new(self.evaluate_expr(
                    namespace,
                    abstract_environment,
                    &keyword_argument.value,
                )?),
            });
        }

        Ok(Expression::Call(ExpressionCall {
            target: Arc::new(func),
            positional_arguments,
            keyword_arguments,
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
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_attribute: &ast::ExprAttribute,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let value = self.evaluate_expr(namespace, abstract_environment, &expr_attribute.value)?;
        let attribute = SmolStr::new(&expr_attribute.attr);

        Ok(Expression::Attribute(ExpressionAttribute {
            value: Arc::new(value),
            attribute,
        }))
    }

    pub fn evaluate_expr_subscript(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr_subscript: &ast::ExprSubscript,
    ) -> Result<Expression, ConstraintsBuilderError> {
        let value = self.evaluate_expr(namespace, abstract_environment, &expr_subscript.value)?;
        let slice = self.evaluate_expr(namespace, abstract_environment, &expr_subscript.slice)?;

        Ok(Expression::Subscript(ExpressionSubscript {
            value: Arc::new(value),
            slice: Arc::new(slice),
        }))
    }

    pub fn evaluate_name(
        &self,
        expr_name: &ast::ExprName,
    ) -> Result<Expression, ConstraintsBuilderError> {
        Ok(Expression::VariableReference(
            ExpressionVariableReference::new(SmolStr::new(&expr_name.id)),
        ))
    }

    pub fn evaluate_expr(
        &self,
        namespace: &ProgramEntityAnalysisState,
        abstract_environment: &ProgramEntityAbstractEnvironment,
        expr: &ast::Expr,
    ) -> Result<Expression, ConstraintsBuilderError> {
        match expr {
            ast::Expr::BoolOp(expr_bool_op) => {
                self.evaluate_expr_bool_op(namespace, abstract_environment, expr_bool_op)
            }
            ast::Expr::Named(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::BinOp(expr_bin_op) => {
                self.evaluate_expr_bin_op(namespace, abstract_environment, expr_bin_op)
            }
            ast::Expr::UnaryOp(expr_unary_op) => {
                self.evaluate_expr_unary_op(namespace, abstract_environment, expr_unary_op)
            }
            ast::Expr::Lambda(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::If(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Dict(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Set(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::ListComp(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::SetComp(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::DictComp(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Generator(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Await(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Yield(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::YieldFrom(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Compare(expr_compare) => {
                self.evaluate_expr_compare(namespace, abstract_environment, expr_compare)
            }
            ast::Expr::Call(expr_call) => {
                self.evaluate_expr_call(namespace, abstract_environment, expr_call)
            }
            ast::Expr::FString(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::StringLiteral(expr_string_literal) => {
                Ok(self.evaluate_expr_string_literal(expr_string_literal))
            }
            ast::Expr::BytesLiteral(expr_bytes_literal) => {
                Ok(self.evaluate_expr_bytes_literal(expr_bytes_literal))
            }
            ast::Expr::NumberLiteral(expr_number_literal) => {
                Ok(self.evaluate_expr_number_literal(expr_number_literal))
            }
            ast::Expr::BooleanLiteral(expr_boolean_literal) => {
                Ok(self.evaluate_expr_boolean_literal(expr_boolean_literal))
            }
            ast::Expr::NoneLiteral(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::EllipsisLiteral(_) => Ok(self.evaluate_expr_ellipsis_literal()),
            ast::Expr::Attribute(expr_attribute) => {
                self.evaluate_expr_attribute(namespace, abstract_environment, expr_attribute)
            }
            ast::Expr::Subscript(expr_subscript) => {
                self.evaluate_expr_subscript(namespace, abstract_environment, expr_subscript)
            }
            ast::Expr::Starred(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Name(expr_name) => self.evaluate_name(expr_name),
            ast::Expr::List(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Tuple(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::Slice(_) => Ok(self.evaluate_expr_none_literal()),
            ast::Expr::IpyEscapeCommand(_) => Ok(self.evaluate_expr_none_literal()),
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

        let location = self.gen_location(&stmt_function_def.name);

        let variable_name = SmolStr::new(&stmt_function_def.name);

        let function_qualified_location = NamedQualifiedLocation::new(
            variable_name.clone(),
            location.clone(),
            self.program_entity.namespace.clone(),
        );

        let function_namespace = Arc::new(Namespace::NamedProgramEntity(
            function_qualified_location.clone(),
        ));

        let parameters = self.gen_parameters(
            namespace,
            &target_abstract_environment,
            &function_namespace,
            &stmt_function_def.parameters,
        )?;
        let return_type = if let Some(returns) = &stmt_function_def.returns {
            Some(Arc::new(Expression::Annotated(ExpressionAnnotated::new(
                Arc::new(self.evaluate_expr(namespace, &target_abstract_environment, &returns)?),
            ))))
        } else {
            None
        };

        let function_program_entity =
            ProgramEntity::new(function_namespace, ProgramEntityKind::Function);

        let sub_cfg_analysis = analyse_cfg(
            self.cfg
                .cfgs
                .get(&self.gen_location(&stmt_function_def))
                .unwrap(),
            self.line_index,
            &function_program_entity,
        );

        self.assign_variable(
            &mut target_abstract_environment,
            location,
            variable_name.clone(),
            Arc::new(Expression::Function(ExpressionFunction::new(
                function_qualified_location,
                parameters,
                imbl::OrdSet::default(),
                return_type,
                stmt_function_def.is_async,
            ))),
            true,
        );

        target_abstract_environment
            .sub_program_entities
            .insert(function_program_entity, sub_cfg_analysis);

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

        let variable_name = SmolStr::new(&stmt_class_def.name);

        let class_qualified_location = NamedQualifiedLocation::new(
            variable_name.clone(),
            location.clone(),
            self.program_entity.namespace.clone(),
        );

        let class_namespace = Arc::new(Namespace::NamedProgramEntity(
            class_qualified_location.clone(),
        ));

        let class_program_entity = ProgramEntity::new(class_namespace, ProgramEntityKind::Class);

        let sub_cfg_analysis = analyse_cfg(
            self.cfg
                .cfgs
                .get(&self.gen_location(&stmt_class_def))
                .unwrap(),
            self.line_index,
            &class_program_entity,
        );

        self.assign_variable(
            &mut target_abstract_environment,
            location.clone(),
            variable_name.clone(),
            Arc::new(Expression::Class(ExpressionClass::new(
                class_qualified_location.clone(),
            ))),
            true,
        );

        target_abstract_environment
            .sub_program_entities
            .insert(class_program_entity, sub_cfg_analysis);

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
            Arc::new(self.evaluate_expr(namespace, &target_abstract_environment, value.as_ref())?)
        } else {
            Arc::new(Expression::LiteralNone)
        };

        let node = ConstraintNode::Constraint {
            location: Some(self.gen_location(stmt_return)),
            id: None,
        };

        let constraint = Constraint::Return(ReturnConstraint::new(expression.clone(), None));

        target_abstract_environment
            .nodes
            .insert(node.clone(), imbl::OrdSet::unit(constraint));

        let mut current_nodes = drain(
            &mut target_abstract_environment.current_nodes,
            |(_, guards)| {
                guards
                    .iter()
                    .any(|guard| matches!(guard, Guard::Raise { .. }))
            },
        );

        let current_empty_constraint = ConstraintNode::Constraint {
            location: Some(self.gen_location(stmt_return)),
            id: Some(SmolStr::new_static("#empty")),
        };

        for (from, guards) in target_abstract_environment.current_nodes.as_ref() {
            let from = if guards.is_empty() {
                &from
            } else {
                target_abstract_environment.edges.insert(
                    (from.clone(), current_empty_constraint.clone()),
                    guards.clone(),
                );
                &current_empty_constraint
            };

            target_abstract_environment.edges.insert(
                (from.clone(), node.clone()),
                imbl::OrdSet::unit(Guard::Succeed(expression.clone())),
            );
            current_nodes.insert(
                from.clone(),
                imbl::OrdSet::unit(Guard::Raise {
                    expression: expression.clone(),
                    exception: None,
                }),
            );
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
            if let Some(as_name) = &alias.asname {
                let module_name = SmolStr::new(&alias.name);
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_location(as_name),
                    SmolStr::new(&as_name),
                    Arc::new(Expression::Import(ExpressionImport::new(
                        module_name.clone(),
                    ))),
                    true,
                );
                target_abstract_environment.imports.insert(module_name);
            } else {
                let identifiers = alias.name.split('.').collect::<Vec<_>>();

                let identifier = SmolStr::new(
                    identifiers
                        .first()
                        .cloned()
                        .expect("Module name should not be empty"),
                );

                let mut location = self.gen_location(&alias.name);

                let mut expression_option = Some(Arc::new(Expression::VariableDefinition(
                    ExpressionVariableDefinition::new(NamedQualifiedLocation::new(
                        identifier.clone(),
                        location.clone(),
                        self.program_entity.namespace.clone(),
                    )),
                )));

                let mut i = 1;
                while let Some(expression) = expression_option {
                    let (module_identifiers, attribute_identifiers) = identifiers.split_at(i);
                    let attribute_option = attribute_identifiers.first().cloned();
                    let identifier = SmolStr::new(module_identifiers[0]);
                    let mut module_name_builder = SmolStrBuilder::new();
                    for (i, module_identifier) in module_identifiers.iter().enumerate() {
                        if i > 0 {
                            module_name_builder.push('.');
                        }
                        module_name_builder.push_str(module_identifier);
                    }
                    let module_name = module_name_builder.finish();
                    target_abstract_environment
                        .imports
                        .insert(module_name.clone());

                    self.create_include_constraint(
                        &mut target_abstract_environment,
                        location.clone(),
                        imbl::OrdSet::unit(Constraint::DefinedVariable(
                            ExpressionVariableDefinition::new(NamedQualifiedLocation::new(
                                identifier.clone(),
                                location.clone(),
                                self.program_entity.namespace.clone(),
                            )),
                        )),
                        Arc::new(Expression::Import(ExpressionImport::new(module_name))),
                        expression.clone(),
                    );

                    // TODO: add constraints of exceptions, pureness and mutability
                    if let Some(attribute) = attribute_option {
                        expression_option =
                            Some(Arc::new(Expression::Attribute(ExpressionAttribute {
                                value: expression,
                                attribute: SmolStr::new(attribute),
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

        let type_expression = Arc::new(self.evaluate_expr(
            namespace,
            &target_abstract_environment,
            &stmt_assign.value,
        )?);

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
                        target_name,
                        type_expression.clone(),
                        true,
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

        let annotation_expression =
            Expression::Annotated(ExpressionAnnotated::new(Arc::new(self.evaluate_expr(
                namespace,
                &target_abstract_environment,
                &stmt_ann_assign.annotation,
            )?)));

        let type_expression = if let Some(value) = &stmt_ann_assign.value {
            Expression::Override(ExpressionOverride::new(
                Arc::new(annotation_expression),
                Arc::new(self.evaluate_expr(namespace, &target_abstract_environment, value)?),
            ))
        } else {
            annotation_expression
        };

        match target {
            AssignmentTarget::Name(target_name) => {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_location(stmt_ann_assign.target.as_ref()),
                    target_name,
                    Arc::new(type_expression),
                    stmt_ann_assign.value.is_some(),
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

        let condition_expression = Arc::new(self.evaluate_expr(
            namespace,
            &target_abstract_environment,
            &stmt_while.test,
        )?);

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
            false,
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

        let condition_expression =
            Arc::new(self.evaluate_expr(namespace, &target_abstract_environment, &stmt_if.test)?);

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
            true,
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

        let condition_expression =
            Arc::new(self.evaluate_expr(namespace, &target_abstract_environment, &test)?);

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
            true,
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
    fn next_nodes(
        &self,
        node: &Self::Node,
    ) -> Result<impl Iterator<Item = &Self::Node>, Self::Error> {
        Ok(self.cfg.graph.successors(node))
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        let mut analysis_state = ProgramEntityAnalysisState::new();

        let mut entry_state = ProgramEntityAbstractEnvironment::default();

        entry_state
            .current_nodes
            .insert(ConstraintNode::Entry, imbl::OrdSet::default());

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
            .graph
            .get_node_data(node)
            .and_then(|cfg_node| cfg_node.as_ref())
        {
            self.evaluate_stmt(analysis_state, *node, node_stmt)
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
        let Some(edge_kinds) = self.cfg.graph.get_edge_data(&(*from, *to)) else {
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
                        (ConstraintNode::TypeExit, ConstraintNode::Entry),
                        imbl::OrdSet::unit(Guard::ForwardReference),
                    );
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

    fn load(&self, module_name: &SmolStr) -> Result<String, Self::Error>;
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
    pub specs: HashMap<SmolStr, FinderSpec<SmolStr, F>>,
}

impl<F: Filesystem> ModuleLoader for SpecModuleLoader<F> {
    type Error = LoadModuleError;

    fn load(&self, module_name: &SmolStr) -> Result<String, Self::Error> {
        let mut identifiers = module_name.split('.');

        let Some(identifier) = identifiers.next() else {
            return Err(LoadModuleError::ModuleNotFound);
        };

        let mut finder_spec = self
            .specs
            .get(identifier)
            .ok_or(LoadModuleError::ModuleNotFound)?;

        for identifier in identifiers {
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

pub fn analyse_cfg<'a>(
    cfg: &'a Cfg,
    line_index: &'a LineIndex,
    program_entity: &ProgramEntity,
) -> ProgramEntityAbstractEnvironment {
    let constraint_builder = ConstraintsBuilder::new(cfg, line_index, program_entity);

    let mut program_entity_analysis_state =
        analysis(&constraint_builder, &mut DummyAnalysisObserver)
            .expect("constraint builder should work");

    program_entity_analysis_state
        .abstract_states
        .remove(&ProgramPoint::Exit)
        .expect("ProgramPoint::Exit should exist in analysed cfg")
}

pub fn create_constraint_graph(
    environment: ProgramEntityAbstractEnvironment,
) -> (ConstraintGraph, imbl::OrdSet<SmolStr>) {
    let mut imports = environment.imports;
    let mut graph = OrdGraph::new();

    for (node, constraints) in environment.nodes {
        graph.insert_node(node, constraints);
    }
    for ((from, to), guards) in environment.edges {
        graph.get_or_insert_default_node(from.clone());
        graph.get_or_insert_default_node(to.clone());
        graph.edge_entry((from, to)).or_insert(guards);
    }

    let constraint_graph = ConstraintGraph::new(
        graph,
        environment
            .sub_program_entities
            .into_iter()
            .map(|(sub_program_entity, sub_cfg_analysis)| {
                let (sub_constraint_graph, sub_imports) = create_constraint_graph(sub_cfg_analysis);
                imports.extend(sub_imports);
                (sub_program_entity.namespace, sub_constraint_graph)
            })
            .collect(),
    );

    (constraint_graph, imports)
}

pub fn analyse_module<'a>(
    module_loader: &impl ModuleLoader<Error: Debug>,
    module_name: &SmolStr,
) -> Option<(ConstraintGraph, imbl::OrdSet<SmolStr>)> {
    let source = module_loader.load(&module_name).ok()?;
    let module = parse_module(&source).ok()?;
    let line_index = LineIndex::from_source_text(&source);
    let cfg = build_cfg(&line_index, module.syntax()).ok()?;
    let program_entity = ProgramEntity::new(
        Arc::new(Namespace::Module(module_name.clone())),
        ProgramEntityKind::Module,
    );
    Some(create_constraint_graph(analyse_cfg(
        &cfg,
        &line_index,
        &program_entity,
    )))
}

pub fn analyse_program<E: Debug, C: ModuleLoader<Error = E> + Sync>(
    module_loader: &C,
    initial_modules: impl Iterator<Item = SmolStr>,
) -> ImportGraph {
    let mut import_graph = ImportGraph::default();
    let mut worklist = initial_modules
        .chain(std::iter::once(BUILTINS_MODULE))
        .collect::<BTreeSet<_>>();

    while !worklist.is_empty() {
        let analysed_modules = worklist
            .into_par_iter()
            .filter_map(|module_name| {
                let (constraint_graph, imports) = analyse_module(module_loader, &module_name)?;
                Some((module_name, constraint_graph, imports))
            })
            .collect::<Vec<_>>();

        worklist = BTreeSet::new();
        for (module_name, constraint_graph, imports) in analysed_modules {
            if module_name != BUILTINS_MODULE {
                import_graph.add_import(module_name.clone(), BUILTINS_MODULE);
            }

            for import in imports {
                if import == BUILTINS_MODULE {
                    continue;
                }

                import_graph.add_import(module_name.clone(), import.clone());

                if !import_graph.modules.contains_key(&import) {
                    worklist.insert(import);
                }
            }

            import_graph.modules.insert(module_name, constraint_graph);
        }
    }

    import_graph
}

#[cfg(test)]
mod tests {
    use super::*;
    use apygen_cfg::graph::dot::ToDot;
    use indoc::indoc;
    use rstest::rstest;
    use std::convert::Infallible;

    pub struct TestModuleLoader {
        pub modules: HashMap<SmolStr, String>,
    }

    impl ModuleLoader for TestModuleLoader {
        type Error = Infallible;
        fn load(&self, module_name: &SmolStr) -> Result<String, Self::Error> {
            Ok(self
                .modules
                .get(module_name)
                .cloned()
                .expect(&format!("{module_name} should exists")))
        }
    }

    const TEST_BUILTINS: &str = indoc! {r##"
        class int:
            def __add__(self, value: int, /) -> int: ...
    "##};

    fn push_constraint_graph(
        target: &mut String,
        namespace: &Namespace,
        constraint_graph: ConstraintGraph,
    ) {
        target.push_str(&constraint_graph.dot(&namespace.to_string()));
        for (namespace, constraint_graph) in constraint_graph.subgraphs {
            push_constraint_graph(target, &namespace, constraint_graph);
        }
    }

    #[rstest]
    fn test_build_builtins_constraints() {
        let expected_constraints = indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
        }
        digraph "builtins" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:6)" [label="#class(identifier=builtins[int@{1:6}]) ⊑ int@{builtins[1:6]} ∧ #defined(int@{builtins[1:6]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:6)" [label="#succeed(#class(identifier=builtins[int@{1:6}]))"];
            "Entry" -> "ExceptionExit" [label="#raise(#class(identifier=builtins[int@{1:6}]))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:6)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        digraph "builtins[int@{1:6}]" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=2:8)" [label="#function(builtins[int@{1:6}][__add__@{2:8}](self@{builtins[int@{1:6}][__add__@{2:8}][2:16]}, value@{builtins[int@{1:6}][__add__@{2:8}][2:22]}: #annotated(int)) -> #annotated(int)) ⊑ __add__@{builtins[int@{1:6}][2:8]} ∧ #defined(__add__@{builtins[int@{1:6}][2:8]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=2:8)" [label="#succeed(#function(builtins[int@{1:6}][__add__@{2:8}](self@{builtins[int@{1:6}][__add__@{2:8}][2:16]}, value@{builtins[int@{1:6}][__add__@{2:8}][2:22]}: #annotated(int)) -> #annotated(int)))"];
            "Entry" -> "ExceptionExit" [label="#raise(#function(builtins[int@{1:6}][__add__@{2:8}](self@{builtins[int@{1:6}][__add__@{2:8}][2:16]}, value@{builtins[int@{1:6}][__add__@{2:8}][2:22]}: #annotated(int)) -> #annotated(int)))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=2:8)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        digraph "builtins[int@{1:6}][__add__@{2:8}]" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "TypeExit";
            "Exit";
            "Entry" -> "Constraint()";
            "Constraint()" -> "TypeExit";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
        }
        "##};

        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([(BUILTINS_MODULE, TEST_BUILTINS.to_owned())]),
        };
        let import_graph = analyse_program(&module_loader, [].into_iter());

        let mut actual_constraints = import_graph.dot("ImportGraph");

        for (module_name, constraint_graph) in import_graph.modules {
            push_constraint_graph(
                &mut actual_constraints,
                &Namespace::Module(module_name),
                constraint_graph,
            );
        }

        assert_eq!(
            expected_constraints, actual_constraints,
            "{actual_constraints}"
        );
    }

    #[rstest]
    #[case::import(
        "import some_module",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "some_module";
            "module" -> "builtins";
            "module" -> "some_module";
            "some_module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::import_as(
        "import some_module as mod",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "some_module";
            "module" -> "builtins";
            "module" -> "some_module";
            "some_module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:22)" [label="#import(some_module) ⊑ mod@{module[1:22]} ∧ #defined(mod@{module[1:22]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:22)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:22)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::import_submodule(
        "import some_module.submodule",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "some_module";
            "some_module.submodule";
            "module" -> "builtins";
            "module" -> "some_module";
            "module" -> "some_module.submodule";
            "some_module" -> "builtins";
            "some_module.submodule" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Constraint(location=1:19)" [label="#import(some_module.submodule) ⊑ (some_module@{module[1:7]}).submodule ∧ #defined(some_module@{module[1:19]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint(location=1:19)" [label="#succeed(#import(some_module.submodule))"];
            "Constraint(location=1:7)" -> "ExceptionExit" [label="#raise(#import(some_module.submodule))"];
            "Constraint(location=1:19)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::import_module_and_submodule(
        "import some_module, some_module.submodule",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "some_module";
            "some_module.submodule";
            "module" -> "builtins";
            "module" -> "some_module";
            "module" -> "some_module.submodule";
            "some_module" -> "builtins";
            "some_module.submodule" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Constraint(location=1:20)" [label="#import(some_module) ⊑ some_module@{module[1:20]} ∧ #defined(some_module@{module[1:20]})"];
            "Constraint(location=1:32)" [label="#import(some_module.submodule) ⊑ (some_module@{module[1:20]}).submodule ∧ #defined(some_module@{module[1:32]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint(location=1:20)" [label="#succeed(#import(some_module))"];
            "Constraint(location=1:7)" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint(location=1:20)" -> "Constraint(location=1:32)" [label="#succeed(#import(some_module.submodule))"];
            "Constraint(location=1:20)" -> "ExceptionExit" [label="#raise(#import(some_module.submodule))"];
            "Constraint(location=1:32)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::multiple_import(
        "import some_module, another_module",
        indoc! {r##"
        digraph "ImportGraph" {
            "another_module";
            "builtins";
            "module";
            "some_module";
            "another_module" -> "builtins";
            "module" -> "another_module";
            "module" -> "builtins";
            "module" -> "some_module";
            "some_module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:7)" [label="#import(some_module) ⊑ some_module@{module[1:7]} ∧ #defined(some_module@{module[1:7]})"];
            "Constraint(location=1:20)" [label="#import(another_module) ⊑ another_module@{module[1:20]} ∧ #defined(another_module@{module[1:20]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:7)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:7)" -> "Constraint(location=1:20)" [label="#succeed(#import(another_module))"];
            "Constraint(location=1:7)" -> "ExceptionExit" [label="#raise(#import(another_module))"];
            "Constraint(location=1:20)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::multiple_import_override(
        "import some_module as mod, another_module as mod",
        indoc! {r##"
        digraph "ImportGraph" {
            "another_module";
            "builtins";
            "module";
            "some_module";
            "another_module" -> "builtins";
            "module" -> "another_module";
            "module" -> "builtins";
            "module" -> "some_module";
            "some_module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:22)" [label="#import(some_module) ⊑ mod@{module[1:22]} ∧ #defined(mod@{module[1:22]})"];
            "Constraint(location=1:45)" [label="#import(another_module) ⊑ mod@{module[1:45]} ∧ #defined(mod@{module[1:45]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:22)" [label="#succeed(#import(some_module))"];
            "Entry" -> "ExceptionExit" [label="#raise(#import(some_module))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:22)" -> "Constraint(location=1:45)" [label="#succeed(#import(another_module))"];
            "Constraint(location=1:22)" -> "ExceptionExit" [label="#raise(#import(another_module))"];
            "Constraint(location=1:45)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::int_constant_assignment(
        "a = 42",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="42 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "TypeExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
        }
        "##},
    )]
    #[case::bigint_constant_assignment(
        "a = 4200000000000000000000000000",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="4200000000000000000000000000 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "TypeExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
        }
        "##},
    )]
    #[case::add_operation(
        "add = 42 + 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) + (67) ⊑ add@{module[1:0]} ∧ #defined(add@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) + (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) + (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::sub_operation(
        "sub = 42 - 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) - (67) ⊑ sub@{module[1:0]} ∧ #defined(sub@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) - (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) - (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::mult_operation(
        "mult = 42 * 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) * (67) ⊑ mult@{module[1:0]} ∧ #defined(mult@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) * (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) * (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::mat_mult_operation(
        "mat_mult = 42 @ 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) @ (67) ⊑ mat_mult@{module[1:0]} ∧ #defined(mat_mult@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) @ (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) @ (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::div_operation(
        "div = 42 / 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) / (67) ⊑ div@{module[1:0]} ∧ #defined(div@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) / (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) / (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::floor_div_operation(
        "floor_div = 42 // 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) // (67) ⊑ floor_div@{module[1:0]} ∧ #defined(floor_div@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) // (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) // (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::mod_operation(
        "mod = 42 % 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) % (67) ⊑ mod@{module[1:0]} ∧ #defined(mod@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) % (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) % (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::pow_operation(
        "pow = 42 ** 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) ** (67) ⊑ pow@{module[1:0]} ∧ #defined(pow@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) ** (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) ** (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::shl_operation(
        "shl = 42 << 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) << (67) ⊑ shl@{module[1:0]} ∧ #defined(shl@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) << (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) << (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::shr_operation(
        "shr = 42 >> 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) >> (67) ⊑ shr@{module[1:0]} ∧ #defined(shr@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) >> (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) >> (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::bit_or_operation(
        "bit_or = 42 | 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) | (67) ⊑ bit_or@{module[1:0]} ∧ #defined(bit_or@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) | (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) | (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::bit_xor_operation(
        "bit_xor = 42 ^ 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) ^ (67) ⊑ bit_xor@{module[1:0]} ∧ #defined(bit_xor@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) ^ (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) ^ (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::bit_and_operation(
        "bit_and = 42 & 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) & (67) ⊑ bit_and@{module[1:0]} ∧ #defined(bit_and@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) & (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) & (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::and_operation(
        "and_ = 42 and 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) and (67) ⊑ and_@{module[1:0]} ∧ #defined(and_@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) and (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) and (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::or_operation(
        "or_ = 42 or 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) or (67) ⊑ or_@{module[1:0]} ∧ #defined(or_@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) or (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) or (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::eq_operation(
        "eq = 42 == 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) == (67) ⊑ eq@{module[1:0]} ∧ #defined(eq@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) == (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) == (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::not_eq_operation(
        "not_eq = 42 != 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) != (67) ⊑ not_eq@{module[1:0]} ∧ #defined(not_eq@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) != (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) != (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::lt_operation(
        "lt = 42 < 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) < (67) ⊑ lt@{module[1:0]} ∧ #defined(lt@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) < (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) < (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::gt_operation(
        "gt = 42 > 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) > (67) ⊑ gt@{module[1:0]} ∧ #defined(gt@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) > (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) > (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::lte_operation(
        "lte = 42 <= 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) <= (67) ⊑ lte@{module[1:0]} ∧ #defined(lte@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) <= (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) <= (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::gte_operation(
        "gte = 42 >= 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) >= (67) ⊑ gte@{module[1:0]} ∧ #defined(gte@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) >= (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) >= (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::is_operation(
        "is_ = 42 is 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) is (67) ⊑ is_@{module[1:0]} ∧ #defined(is_@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) is (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) is (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::is_not_operation(
        "is_not = 42 is not 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) is not (67) ⊑ is_not@{module[1:0]} ∧ #defined(is_not@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) is not (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) is not (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::in_operation(
        "in_ = 42 in 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) in (67) ⊑ in_@{module[1:0]} ∧ #defined(in_@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) in (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) in (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::not_in_operation(
        "not_in = 42 not in 67",
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="(42) not in (67) ⊑ not_in@{module[1:0]} ∧ #defined(not_in@{module[1:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)" [label="#succeed((42) not in (67))"];
            "Entry" -> "ExceptionExit" [label="#raise((42) not in (67))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
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
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="4 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "Constraint(location=3:0)" [label="(a) + (a) ⊑ b@{module[3:0]} ∧ #defined(b@{module[3:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint(location=3:0)" [label="#succeed((a) + (a))"];
            "Constraint(location=1:0)" -> "ExceptionExit" [label="#raise((a) + (a))"];
            "Constraint(location=3:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
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
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="True ⊑ x@{module[1:0]} ∧ #defined(x@{module[1:0]})"];
            "Constraint(location=4:4)" [label="42 ⊑ a@{module[4:4]} ∧ #defined(a@{module[4:4]})"];
            "Constraint(location=6:4)" [label="67 ⊑ a@{module[6:4]} ∧ #defined(a@{module[6:4]})"];
            "Constraint(location=8:0)" [label="a ⊑ b@{module[8:0]} ∧ #defined(b@{module[8:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint(location=4:4)" [label="#is_true(x)"];
            "Constraint(location=1:0)" -> "Constraint(location=6:4)" [label="#is_false(x)"];
            "Constraint(location=1:0)" -> "ExceptionExit" [label="#raise(x)"];
            "Constraint(location=4:4)" -> "Constraint(location=8:0)" [label="#succeed(a)"];
            "Constraint(location=4:4)" -> "ExceptionExit" [label="#raise(a)"];
            "Constraint(location=6:4)" -> "Constraint(location=8:0)" [label="#succeed(a)"];
            "Constraint(location=6:4)" -> "ExceptionExit" [label="#raise(a)"];
            "Constraint(location=8:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
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
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:0)" [label="0 ⊑ a@{module[1:0]} ∧ #defined(a@{module[1:0]})"];
            "Constraint(location=3:0)";
            "Constraint(location=4:4)" [label="(a) + (1) ⊑ a@{module[4:4]} ∧ #defined(a@{module[4:4]})"];
            "Constraint(location=4:4, id=#empty)";
            "Constraint(location=6:0)" [label="a ⊑ b@{module[6:0]} ∧ #defined(b@{module[6:0]})"];
            "Constraint(location=6:0, id=#empty)";
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:0)";
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:0)" -> "Constraint(location=3:0)";
            "Constraint(location=3:0)" -> "Constraint(location=4:4, id=#empty)" [label="#is_true((a) < (5))"];
            "Constraint(location=3:0)" -> "Constraint(location=6:0, id=#empty)" [label="#is_false((a) < (5))"];
            "Constraint(location=3:0)" -> "ExceptionExit" [label="#raise((a) < (5))"];
            "Constraint(location=4:4)" -> "Constraint(location=3:0)";
            "Constraint(location=4:4, id=#empty)" -> "Constraint(location=4:4)" [label="#succeed((a) + (1))"];
            "Constraint(location=4:4, id=#empty)" -> "ExceptionExit" [label="#raise((a) + (1))"];
            "Constraint(location=6:0)" -> "Constraint()";
            "Constraint(location=6:0, id=#empty)" -> "Constraint(location=6:0)" [label="#succeed(a)"];
            "Constraint(location=6:0, id=#empty)" -> "ExceptionExit" [label="#raise(a)"];
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b: int) -> int:
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:4)" [label="#function(module[add_two@{1:4}](a@{module[add_two@{1:4}][1:12]}: #annotated(int), b@{module[add_two@{1:4}][1:20]}: #annotated(int)) -> #annotated(int)) ⊑ add_two@{module[1:4]} ∧ #defined(add_two@{module[1:4]})"];
            "Constraint(location=4:0)" [label="(add_two)(42, 67) ⊑ result@{module[4:0]} ∧ #defined(result@{module[4:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:4)" [label="#succeed(#function(module[add_two@{1:4}](a@{module[add_two@{1:4}][1:12]}: #annotated(int), b@{module[add_two@{1:4}][1:20]}: #annotated(int)) -> #annotated(int)))"];
            "Entry" -> "ExceptionExit" [label="#raise(#function(module[add_two@{1:4}](a@{module[add_two@{1:4}][1:12]}: #annotated(int), b@{module[add_two@{1:4}][1:20]}: #annotated(int)) -> #annotated(int)))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:4)" -> "Constraint(location=4:0)" [label="#succeed((add_two)(42, 67))"];
            "Constraint(location=1:4)" -> "ExceptionExit" [label="#raise((add_two)(42, 67))"];
            "Constraint(location=4:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        digraph "module[add_two@{1:4}]" {
            "Entry";
            "Constraint(location=2:4)" [label="#return((a) + (b))"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=2:4)" [label="#succeed((a) + (b))"];
            "Entry" -> "ExceptionExit" [label="#raise((a) + (b))"];
            "Constraint(location=2:4)" -> "TypeExit";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::hard_function_call(
        indoc! {r##"
        def foo():
            return CONST

        result = foo()

        CONST = 5
        "##},
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:4)" [label="#function(module[foo@{1:4}]()) ⊑ foo@{module[1:4]} ∧ #defined(foo@{module[1:4]})"];
            "Constraint(location=4:0)" [label="(foo)() ⊑ result@{module[4:0]} ∧ #defined(result@{module[4:0]})"];
            "Constraint(location=6:0)" [label="5 ⊑ CONST@{module[6:0]} ∧ #defined(CONST@{module[6:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:4)" [label="#succeed(#function(module[foo@{1:4}]()))"];
            "Entry" -> "ExceptionExit" [label="#raise(#function(module[foo@{1:4}]()))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:4)" -> "Constraint(location=4:0)" [label="#succeed((foo)())"];
            "Constraint(location=1:4)" -> "ExceptionExit" [label="#raise((foo)())"];
            "Constraint(location=4:0)" -> "Constraint(location=6:0)";
            "Constraint(location=6:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        digraph "module[foo@{1:4}]" {
            "Entry";
            "Constraint(location=2:4)" [label="#return(CONST)"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=2:4)" [label="#succeed(CONST)"];
            "Entry" -> "ExceptionExit" [label="#raise(CONST)"];
            "Constraint(location=2:4)" -> "TypeExit";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    #[case::forward_reference_function_call(
        indoc! {r##"
        def foo():
            return CONST

        CONST = 5

        result = foo()
        "##},
        indoc! {r##"
        digraph "ImportGraph" {
            "builtins";
            "module";
            "module" -> "builtins";
        }
        digraph "module" {
            "Entry";
            "Constraint()" [label="#return(None)"];
            "Constraint(location=1:4)" [label="#function(module[foo@{1:4}]()) ⊑ foo@{module[1:4]} ∧ #defined(foo@{module[1:4]})"];
            "Constraint(location=4:0)" [label="5 ⊑ CONST@{module[4:0]} ∧ #defined(CONST@{module[4:0]})"];
            "Constraint(location=6:0)" [label="(foo)() ⊑ result@{module[6:0]} ∧ #defined(result@{module[6:0]})"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=1:4)" [label="#succeed(#function(module[foo@{1:4}]()))"];
            "Entry" -> "ExceptionExit" [label="#raise(#function(module[foo@{1:4}]()))"];
            "Constraint()" -> "TypeExit";
            "Constraint(location=1:4)" -> "Constraint(location=4:0)";
            "Constraint(location=4:0)" -> "Constraint(location=6:0)" [label="#succeed((foo)())"];
            "Constraint(location=4:0)" -> "ExceptionExit" [label="#raise((foo)())"];
            "Constraint(location=6:0)" -> "Constraint()";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        digraph "module[foo@{1:4}]" {
            "Entry";
            "Constraint(location=2:4)" [label="#return(CONST)"];
            "TypeExit";
            "ExceptionExit";
            "Exit";
            "Entry" -> "Constraint(location=2:4)" [label="#succeed(CONST)"];
            "Entry" -> "ExceptionExit" [label="#raise(CONST)"];
            "Constraint(location=2:4)" -> "TypeExit";
            "TypeExit" -> "Entry" [label="#forward_reference"];
            "TypeExit" -> "Exit";
            "ExceptionExit" -> "Exit";
        }
        "##},
    )]
    fn test_program_analysis(#[case] source: &str, #[case] expected_constraints: &str) {
        let target_module_name = SmolStr::new_static("module");

        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([
                (target_module_name.clone(), source.to_string()),
                (SmolStr::new_static("some_module"), String::new()),
                (SmolStr::new_static("some_module.submodule"), String::new()),
                (SmolStr::new_static("another_module"), String::new()),
                (BUILTINS_MODULE, TEST_BUILTINS.to_owned()),
            ]),
        };
        let import_graph =
            analyse_program(&module_loader, std::iter::once(target_module_name.clone()));

        let mut actual_constraints = import_graph.dot("ImportGraph");

        for (module_name, constraint_graph) in import_graph.modules {
            if module_name != target_module_name {
                continue;
            }
            push_constraint_graph(
                &mut actual_constraints,
                &Namespace::Module(module_name),
                constraint_graph,
            );
        }

        assert_eq!(
            expected_constraints, actual_constraints,
            "{actual_constraints}"
        );
    }
}
