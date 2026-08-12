#![recursion_limit = "256"]

use crate::analysis::abstract_state::{AbstractState, AbstractStateProxy};
use crate::analysis::lattice::Join;
use crate::analysis::{DependencyGraphAnalyser, DummyAnalysisObserver, GraphAnalyser, analysis};
use crate::constraint_graph::expressions::{Expression, Namespace, Parameter, SmolStr};
use crate::constraint_graph::graph::{Graph, GraphMut};
use crate::constraint_graph::{Constraint, ConstraintGraph, ConstraintNode, Guard, ImportGraph};
use crate::dependent_graph::{DependentGraph, DependentGraphProxy, ImmutableHashDependentGraph};
use crate::evaluation::{
    Call, Definition, EdgeCall, EdgeKind, EvaluationError, EvaluationState, EvaluatorMode,
    ExpressionEvaluator, PyTypeEval, gen_bool_value,
};
use crate::identifiers::QualifiedLocation;
use crate::inference::{
    BUILTINS_MODULE, DEPTH_LIMIT, Deferred, ProgramEvaluation, Source, Sourced, StructuralDepth,
    StructuralWidth, Type, WIDTH_LIMIT,
};
use imbl::ordmap;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::convert::Infallible;
use std::fmt::Debug;
use std::sync::Arc;

pub use apygen_analysis as analysis;
pub use apygen_constraint_graph as constraint_graph;
pub use apygen_identifiers as identifiers;
pub use apygen_inference as inference;
pub use apygen_primitives as primitives;
pub use imbl;
pub mod dependent_graph;
pub mod evaluation;

#[derive(Debug, Clone, PartialEq, Eq, Join)]
pub struct SolverState<N: Ord, S> {
    pub abstract_states: imbl::OrdMap<N, S>,
}

impl<N: Ord, S> SolverState<N, S> {
    pub fn new(abstract_states: imbl::OrdMap<N, S>) -> Self {
        Self { abstract_states }
    }
}

impl<N: Ord, S> Default for SolverState<N, S> {
    fn default() -> Self {
        Self {
            abstract_states: imbl::OrdMap::default(),
        }
    }
}

impl<N: Clone + Ord + Send + Sync, S: Clone + Send + Sync> AbstractState for SolverState<N, S> {
    type Key = N;
    type AbstractValue = S;

    fn get(&self, key: &Self::Key) -> Option<&Self::AbstractValue> {
        self.abstract_states.get(key)
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::AbstractValue> {
        self.abstract_states.get_mut(key)
    }

    fn get_or_insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        self.abstract_states.entry(key).or_insert(abstract_value)
    }

    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        match self.abstract_states.entry(key) {
            ordmap::Entry::Occupied(entry) => {
                let previous_abstract_value = entry.into_mut();
                *previous_abstract_value = abstract_value;
                previous_abstract_value
            }
            ordmap::Entry::Vacant(entry) => entry.insert(abstract_value),
        }
    }
}

pub struct ConstraintSolver<'s> {
    pub namespace: &'s Namespace,
    pub definition: &'s Definition,
    pub constraint_graph: &'s ConstraintGraph,
    pub program_evaluation: &'s dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
    pub namespace_dependent_graph: &'s dyn DependentGraph<
        Node = Namespace,
        NodeData = Definition,
        EdgeData = imbl::OrdSet<EdgeKind>,
    >,
}

impl<'s> ConstraintSolver<'s> {
    pub fn new(
        namespace: &'s Namespace,
        definition: &'s Definition,
        constraint_graph: &'s ConstraintGraph,
        program_evaluation: &'s dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        namespace_dependent_graph: &'s dyn DependentGraph<
            Node = Namespace,
            NodeData = Definition,
            EdgeData = imbl::OrdSet<EdgeKind>,
        >,
    ) -> Self {
        Self {
            namespace,
            definition,
            constraint_graph,
            program_evaluation,
            namespace_dependent_graph,
        }
    }

    pub fn evaluator<
        'a,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &'a self,
        abstract_state: &'a S,
    ) -> ExpressionEvaluator<'a, S> {
        ExpressionEvaluator::new(
            EvaluatorMode::Normal,
            self.namespace,
            abstract_state,
            self.namespace_dependent_graph,
            None,
        )
    }

    pub fn evaluate_expression<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression: &Expression,
    ) -> Deferred<PyTypeEval<S>, Expression> {
        let mut expression_evaluator = self.evaluator(abstract_state);

        let mut known_evaluations = BTreeMap::new();

        match expression_evaluator.evaluate_expression(&mut known_evaluations, expression) {
            Ok(eval) => Deferred::known(eval),
            Err(_) => Deferred::unknown(imbl::OrdSet::unit(Arc::new(expression.clone()))),
        }
    }

    pub fn evaluate_deferred_type<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        deferred_ty: &Deferred<Sourced<Type>, Expression>,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut expression_evaluator = self.evaluator(abstract_state);

        let mut known_evaluations = BTreeMap::new();

        expression_evaluator.evaluate_deferred_type(&mut known_evaluations, deferred_ty)
    }
}

impl<'s> GraphAnalyser for ConstraintSolver<'s> {
    type Node = ConstraintNode;
    type AbstractState = (
        AbstractStateProxy<'s, Namespace, EvaluationState, ProgramEvaluation<EvaluationState>>,
        imbl::OrdSet<(
            QualifiedLocation,
            Call<
                AbstractStateProxy<
                    's,
                    Namespace,
                    EvaluationState,
                    ProgramEvaluation<EvaluationState>,
                >,
            >,
        )>,
        imbl::OrdSet<(Namespace, Definition)>,
    );
    type AnalysisState = SolverState<Self::Node, Self::AbstractState>;
    type Error = Infallible;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(ConstraintNode::Entry))
    }

    fn next_nodes<'a: 'n, 'n>(
        &'a self,
        node: &'n Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error> {
        Ok(self.constraint_graph.graph.successors(node))
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        Ok(SolverState::default())
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        let (mut program_evaluation, mut calls, mut definitions) =
            analysis_state.get_clone(node).unwrap_or_else(|| {
                (
                    AbstractStateProxy::new(
                        self.program_evaluation,
                        ProgramEvaluation::new(imbl::OrdMap::unit(
                            self.namespace.clone(),
                            EvaluationState::default(),
                        )),
                    ),
                    imbl::OrdSet::default(),
                    imbl::OrdSet::default(),
                )
            });

        match &node {
            ConstraintNode::Entry => {
                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.namespace.clone());

                let (arguments, _) = inputs(self.namespace_dependent_graph, self.namespace);
                for (parameter, deferred_ty) in arguments {
                    evaluation_state.defined_variables.names.insert(
                        parameter.name.named_qualified_location.name.clone(),
                        imbl::OrdSet::unit((
                            parameter.name.named_qualified_location.namespace.clone(),
                            parameter.name.named_qualified_location.location.clone(),
                        )),
                    );
                    evaluation_state.type_variables.insert(
                        parameter.name.named_qualified_location.name.clone(),
                        imbl::OrdSet::unit((
                            parameter.name.named_qualified_location.namespace.clone(),
                            parameter.name.named_qualified_location.location.clone(),
                        )),
                    );
                    evaluation_state.types.insert(
                        Arc::new(Expression::VariableDefinition(parameter.name.clone())),
                        if let Some(deferred_ty) = &deferred_ty {
                            deferred_ty.clone()
                        } else {
                            Deferred::known(Sourced::inferred(Type::Any))
                        },
                    );
                }

                evaluation_state.raised_exceptions = self.definition.exceptions.clone();
                evaluation_state.return_value = self.definition.return_value.clone();
            }
            ConstraintNode::Constraint { location, .. } => {
                if let Some(constraints) = self.constraint_graph.graph.get_node_data(node) {
                    for constraint in constraints {
                        match constraint {
                            Constraint::Type(type_constraint) => {
                                let deferred = self.evaluate_expression(
                                    &program_evaluation,
                                    &type_constraint.left,
                                );
                                let deferred_ty = deferred.clone().map(|eval| eval.value);
                                let deferred_raised_exceptions =
                                    deferred.clone().map(|eval| eval.effects.exceptions);
                                let mut previous_deferred_ty = Deferred::known(Sourced::specified(Type::Never));
                                if let Some(evaluation_state) =
                                    program_evaluation.get(self.namespace)
                                {
                                    if let Some(deferred_ty) =
                                        evaluation_state.types.get(&type_constraint.right)
                                    {
                                        if !deferred_ty.expressions.is_empty() {
                                            if let Ok(eval) = self.evaluate_deferred_type(
                                                &program_evaluation,
                                                &deferred_ty,
                                            ) {
                                                previous_deferred_ty.value = eval.value;
                                            }
                                        }
                                    }
                                }

                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                evaluation_state.types.insert(
                                    type_constraint.right.clone(),
                                    previous_deferred_ty.join(&deferred_ty),
                                );

                                evaluation_state.raised_exceptions = evaluation_state
                                    .raised_exceptions
                                    .join(&deferred_raised_exceptions);
                                if let Some(location) = location {
                                    for call in deferred.value.effects.calls {
                                        calls.insert((
                                            QualifiedLocation::new(
                                                location.clone(),
                                                Arc::new(self.namespace.clone()),
                                            ),
                                            call.clone(),
                                        ));
                                    }
                                }
                                definitions.extend(deferred.value.effects.definitions);
                            }
                            Constraint::Return(return_constraint) => {
                                let deferred = self.evaluate_expression(
                                    &program_evaluation,
                                    &return_constraint.expression,
                                );
                                let deferred_ty = deferred.clone().map(|eval| eval.value);
                                let deferred_raised_exceptions =
                                    deferred.map(|eval| eval.effects.exceptions);

                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                if let Some(return_value) = &evaluation_state.return_value {
                                    if !matches!(
                                        // TODO: fix
                                        return_value.value.source,
                                        Source::Specified
                                    ) {
                                        evaluation_state.return_value =
                                            Some(Deferred::known(deferred_ty.value));
                                    }
                                } else {
                                    evaluation_state.return_value =
                                        Some(Deferred::known(deferred_ty.value));
                                }
                                evaluation_state.raised_exceptions = evaluation_state
                                    .raised_exceptions
                                    .join(&deferred_raised_exceptions);
                            }
                            Constraint::DefinedVariable(expression) => {
                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                evaluation_state.defined_variables.names.insert(
                                    expression.named_qualified_location.name.clone(),
                                    imbl::OrdSet::unit((
                                        expression.named_qualified_location.namespace.clone(),
                                        expression.named_qualified_location.location.clone(),
                                    )),
                                );
                                evaluation_state.type_variables.insert(
                                    expression.named_qualified_location.name.clone(),
                                    imbl::OrdSet::unit((
                                        expression.named_qualified_location.namespace.clone(),
                                        expression.named_qualified_location.location.clone(),
                                    )),
                                );
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        Ok((program_evaluation, calls, definitions))
    }

    fn update_abstract_state(
        &self,
        _analysis_state: &Self::AnalysisState,
        from: &Self::Node,
        to: &Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        let (mut new_abstract_state, calls, definitions) = abstract_state.clone();

        let guards = self
            .constraint_graph
            .graph
            .get_edge_data(&(from.clone(), to.clone()))
            .unwrap();

        let mut should_ignore = !guards.is_empty();

        for guard in guards {
            match guard {
                Guard::ForwardReference => {
                    let evaluation_state =
                        new_abstract_state.get_or_insert_default(self.namespace.clone());

                    if evaluation_state
                        .types
                        .values()
                        .all(|ty| ty.expressions.is_empty())
                        && evaluation_state.raised_exceptions.expressions.is_empty()
                        && evaluation_state
                            .return_value
                            .as_ref()
                            .map(|deferred_ty| deferred_ty.expressions.is_empty())
                            .unwrap_or(true)
                        && definitions.iter().all(|(_, definition)| {
                            definition.parameters.iter().all(|(_, deferred_ty_option)| {
                                deferred_ty_option
                                    .as_ref()
                                    .map(|deferred_ty| deferred_ty.expressions.is_empty())
                                    .unwrap_or(true)
                            }) && definition.exceptions.expressions.is_empty()
                                && definition
                                    .return_value
                                    .as_ref()
                                    .map(|deferred_ty| deferred_ty.expressions.is_empty())
                                    .unwrap_or(true)
                        })
                    {
                        continue;
                    }

                    evaluation_state.type_variables = evaluation_state
                        .type_variables
                        .clone()
                        .union(evaluation_state.defined_variables.names.clone());
                    evaluation_state.defined_variables.names.clear();
                    should_ignore = false;
                }
                Guard::IsTrue(expression) => {
                    let deferred = self.evaluate_expression(&new_abstract_state, &expression);

                    if let Some(eval) = deferred.to_value() {
                        if let Some(bool_value) = gen_bool_value(&eval.value.data) {
                            if !bool_value {
                                continue;
                            }
                        }
                    }

                    should_ignore = false;
                }
                Guard::IsFalse(expression) => {
                    let deferred = self.evaluate_expression(&new_abstract_state, &expression);

                    if let Some(eval) = deferred.to_value() {
                        if let Some(bool_value) = gen_bool_value(&eval.value.data) {
                            if bool_value {
                                continue;
                            }
                        }
                    }

                    should_ignore = false;
                }
                Guard::Succeed(expression) => {
                    let deferred = self.evaluate_expression(&new_abstract_state, &expression);

                    if let Some(eval) = deferred.to_value() {
                        if is_sourced_type_unreachable!(eval.value) {
                            continue;
                        }
                    }

                    should_ignore = false;
                }
                Guard::Raise { expression, .. } => {
                    let deferred = self.evaluate_expression(&new_abstract_state, &expression);

                    if let Some(eval) = deferred.as_value() {
                        if eval.effects.exceptions.exceptions.is_empty() {
                            continue;
                        }
                    }

                    let evaluation_state =
                        new_abstract_state.get_or_insert_default(self.namespace.clone());

                    evaluation_state.raised_exceptions = evaluation_state
                        .raised_exceptions
                        .join(&deferred.map(|eval| eval.effects.exceptions));

                    should_ignore = false;
                }
            }
        }

        if should_ignore {
            Ok(None)
        } else {
            Ok(Some((new_abstract_state, calls, definitions)))
        }
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
        analysis_state
            .abstract_states
            .insert(node.clone(), abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        _analysis_state: &Self::AnalysisState,
        _node: &Self::Node,
        (left_abstract_state, left_calls, left_definitions): &Self::AbstractState,
        (right_abstract_state, right_calls, right_definitions): &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        assert!(std::ptr::addr_eq(
            left_abstract_state.abstract_state,
            self.program_evaluation
        ));
        assert!(std::ptr::addr_eq(
            right_abstract_state.abstract_state,
            self.program_evaluation
        ));

        let mut new_abstract_state = AbstractStateProxy::new(
            self.program_evaluation,
            left_abstract_state.proxy.join(&right_abstract_state.proxy),
        );

        if let Some(evaluation_state) = new_abstract_state.get(&self.namespace) {
            let new_types = evaluation_state
                .types
                .clone()
                .into_iter()
                .map(|(expression, mut deferred)| {
                    if !deferred.expressions.is_empty() {
                        if let Ok(eval) =
                            self.evaluate_deferred_type(&new_abstract_state, &deferred)
                        {
                            deferred.value = eval.value;
                        }
                    }
                    while deferred.value.data.width() > WIDTH_LIMIT {
                        deferred.value = match deferred.value.data {
                            Type::Union(type_union) => {
                                let mut new_ty = Type::Never;
                                for ty in type_union.into_types() {
                                    new_ty =
                                        new_ty.join(&if let Type::Literal(type_literal) = &ty {
                                            type_literal
                                                .as_type_instance(&new_abstract_state)
                                                .map(|type_instance| Type::Instance(type_instance))
                                                .unwrap_or(Type::Any)
                                        } else {
                                            ty
                                        });
                                }
                                Sourced::inferred(new_ty)
                            }
                            _ => Sourced::inferred(Type::Any),
                        };
                    }

                    if deferred.value.data.depth() > DEPTH_LIMIT {
                        deferred.value = Sourced::inferred(Type::Any);
                    }

                    (expression, deferred)
                })
                .collect();

            new_abstract_state
                .get_mut(&self.namespace)
                .expect("evaluation_state should exists")
                .types = new_types;
        }

        Ok((
            new_abstract_state,
            left_calls.join(&right_calls),
            left_definitions.join(&right_definitions),
        ))
    }

    fn optimise(
        &self,
        analysis_state: &mut Self::AnalysisState,
        worklist: &mut BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        let mut marked = BTreeSet::new();

        for worklist_node in worklist.iter() {
            if marked.contains(worklist_node) {
                continue;
            }

            let mut to_remove = BTreeSet::from_iter([worklist_node]);
            while let Some(node) = to_remove.pop_first() {
                for next_node in self.constraint_graph.graph.successors(node) {
                    if next_node != worklist_node
                        && *next_node != ConstraintNode::Entry
                        && !marked.contains(next_node)
                        && analysis_state.abstract_states.contains_key(next_node)
                        && self
                            .constraint_graph
                            .graph
                            .predecessors(next_node)
                            .all(|predecessor| predecessor == node || marked.contains(predecessor))
                    {
                        marked.insert(next_node);
                        to_remove.insert(next_node);
                    }
                }
            }
        }

        *worklist = worklist
            .extract_if(.., |node| !marked.contains(node))
            .collect();

        for node in marked {
            analysis_state.abstract_states.remove(node);
        }

        Ok(())
    }
}

pub fn inputs(
    dependent_graph: &dyn DependentGraph<Node = Namespace, NodeData = Definition, EdgeData = imbl::OrdSet<EdgeKind>>,
    namespace: &Namespace,
) -> (
    imbl::OrdMap<Parameter, Option<Deferred<Sourced<Type>, Expression>>>,
    imbl::OrdMap<Option<QualifiedLocation>, ProgramEvaluation<EvaluationState>>,
) {
    let mut call_sites = imbl::OrdMap::default();
    let mut arguments = imbl::OrdMap::default();

    if let Some(definition) = dependent_graph.get_node_data(namespace) {
        arguments.extend(definition.parameters.iter().cloned());
    }

    let callers = dependent_graph
        .dependents(namespace)
        .flat_map(move |dependent| {
            dependent_graph
                .get_edge_data(namespace, dependent)
                .into_iter()
                .flat_map(move |edge_kinds| {
                    edge_kinds
                        .iter()
                        .filter_map(move |edge_kind| match edge_kind {
                            EdgeKind::Definition => None,
                            EdgeKind::Call(call) => Some((dependent.clone(), call.clone())),
                        })
                })
        });

    for (caller_namespace, edge_call) in callers {
        call_sites.insert(
            if namespace.module_name() == caller_namespace.module_name() {
                Some(QualifiedLocation::new(
                    edge_call.location.clone(),
                    Arc::new(caller_namespace.clone()),
                ))
            } else {
                None
            },
            edge_call.context,
        );
        for (parameter, ty) in edge_call.arguments.variables {
            match arguments.entry(parameter.clone()) {
                ordmap::Entry::Occupied(entry) => {
                    let current_deferred_ty: &mut Option<Deferred<Sourced<Type>, Expression>> =
                        entry.into_mut();

                    *current_deferred_ty = if let Some(current_deferred_ty) = current_deferred_ty {
                        if current_deferred_ty.value.source > ty.source {
                            Some(current_deferred_ty.clone())
                        } else {
                            Some(current_deferred_ty.join(&Deferred::known(ty)))
                        }
                    } else {
                        Some(Deferred::known(ty))
                    };
                }
                ordmap::Entry::Vacant(entry) => {
                    entry.insert(Some(Deferred::known(ty)));
                }
            }
        }
    }

    (arguments, call_sites)
}

pub fn solve_namespace(
    namespace: &Namespace,
    definition: &Definition,
    constraint_graph: &ConstraintGraph,
    abstract_state: &dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
    namespace_dependent_graph: &dyn DependentGraph<Node = Namespace, NodeData = Definition, EdgeData = imbl::OrdSet<EdgeKind>>,
) -> Result<
    (
        ProgramEvaluation<EvaluationState>,
        HashMap<Namespace, Definition>,
        HashMap<Namespace, HashMap<Namespace, Option<imbl::OrdSet<EdgeKind>>>>,
    ),
    Infallible,
> {
    let mut abstract_state_proxy = AbstractStateProxy::with_default_proxy(abstract_state);
    let mut namespace_dependent_graph_proxy =
        DependentGraphProxy::with_default_proxy(namespace_dependent_graph);

    let mut previous_evaluation_state: Option<EvaluationState> = None;
    let mut previous_calls = BTreeSet::default();
    loop {
        abstract_state_proxy.insert(namespace.clone(), EvaluationState::default());
        namespace_dependent_graph_proxy.insert_node(namespace.clone(), definition.clone());

        let mut solver_state = analysis(
            &ConstraintSolver::new(
                &namespace,
                definition,
                constraint_graph,
                &abstract_state_proxy,
                &namespace_dependent_graph_proxy,
            ),
            &mut DummyAnalysisObserver::default(),
        )?;

        let evaluation_state =
            if let Some((program_evaluation, _, _)) = solver_state.get(&ConstraintNode::TypeExit) {
                let mut evaluation_state = program_evaluation.get_clone_or_default(namespace);

                if let Some(exception_evaluation_state) = solver_state
                    .get(&ConstraintNode::ExceptionExit)
                    .and_then(|(program_evaluation, _, _)| program_evaluation.get(namespace))
                {
                    evaluation_state.types = evaluation_state
                        .types
                        .join(&exception_evaluation_state.types);
                    evaluation_state.raised_exceptions = evaluation_state
                        .raised_exceptions
                        .join(&exception_evaluation_state.raised_exceptions);
                }

                evaluation_state
            } else {
                solver_state
                    .get(&ConstraintNode::ExceptionExit)
                    .and_then(|(program_evaluation, _, _)| program_evaluation.get(namespace))
                    .cloned()
                    .unwrap_or_default()
            };

        let (new_calls, new_definitions) = solver_state
            .abstract_states
            .remove(&ConstraintNode::Exit)
            .map(|(program_evaluation, calls, definitions)| {
                assert_eq!(program_evaluation.proxy.states.len(), 1);
                (
                    calls
                        .into_iter()
                        .map(|(qualified_location, call)| {
                            (
                                (call.target.as_ref().clone(), namespace.clone()),
                                EdgeCall::new(
                                    qualified_location.location,
                                    call.context.proxy,
                                    call.arguments,
                                ),
                            )
                        })
                        .collect(),
                    definitions.into_iter().collect(),
                )
            })
            .unwrap_or_else(|| (BTreeSet::default(), BTreeMap::default()));

        drop(solver_state);

        let new_evaluation_state = abstract_state_proxy
            .insert(namespace.clone(), evaluation_state)
            .clone();

        for (sub_namespace, definition) in &new_definitions {
            namespace_dependent_graph_proxy.insert_node(sub_namespace.clone(), definition.clone());
            namespace_dependent_graph_proxy
                .get_or_insert_edge(namespace.clone(), sub_namespace.clone(), &|| {
                    imbl::OrdSet::default()
                })
                .expect("failed to insert edge")
                .insert(EdgeKind::Definition);
        }
        for ((target, caller_namespace), call) in &new_calls {
            namespace_dependent_graph_proxy
                .get_or_insert_edge(target.clone(), caller_namespace.clone(), &|| {
                    imbl::OrdSet::default()
                })
                .expect("failed to insert edge")
                .insert(EdgeKind::Call(call.clone()));
        }

        if Some(&new_evaluation_state) == previous_evaluation_state.as_ref()
            && new_calls == previous_calls
        {
            return Ok((
                abstract_state_proxy.proxy,
                namespace_dependent_graph_proxy.nodes,
                namespace_dependent_graph_proxy.dependents,
            ));
        }

        let (sub_program_evaluation, sub_nodes, sub_dependents) = new_definitions
            .par_iter()
            .map(|(sub_namespace, definition)| {
                solve_namespace(
                    sub_namespace,
                    definition,
                    constraint_graph.subgraphs.get(sub_namespace).unwrap(),
                    &abstract_state_proxy,
                    &namespace_dependent_graph_proxy,
                )
            })
            .try_reduce(
                || {
                    (
                        ProgramEvaluation::default(),
                        HashMap::default(),
                        HashMap::default(),
                    )
                },
                |(mut program_evaluation_acc, mut calls_acc, mut definitions_acc),
                 (new_program_evaluation, new_calls, new_definitions)| {
                    program_evaluation_acc
                        .states
                        .extend(new_program_evaluation.states);
                    calls_acc.extend(new_calls);
                    definitions_acc.extend(new_definitions);
                    Ok((program_evaluation_acc, calls_acc, definitions_acc))
                },
            )?;

        abstract_state_proxy.proxy.states = sub_program_evaluation.states;
        namespace_dependent_graph_proxy.nodes.extend(sub_nodes);
        namespace_dependent_graph_proxy.dependents = namespace_dependent_graph_proxy
            .dependents
            .join(&sub_dependents);

        previous_evaluation_state = Some(new_evaluation_state);
        previous_calls = new_calls;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Join)]
pub struct ModuleConstraintSolverAbstractState {
    pub program_evaluation: ProgramEvaluation<EvaluationState>,
    pub nodes: BTreeSet<(Namespace, Definition)>,
    pub dependents: HashMap<Namespace, HashMap<Namespace, Option<imbl::OrdSet<EdgeKind>>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModuleConstraintSolverAnalysisState {
    pub program_evaluation: ProgramEvaluation<EvaluationState>,
    pub namespace_dependency_graph:
        ImmutableHashDependentGraph<Namespace, Definition, imbl::OrdSet<EdgeKind>>,
}

pub struct ModuleConstraintSolver<'a> {
    pub module_namespaces: HashMap<SmolStr, HashMap<Namespace, &'a ConstraintGraph>>,
    pub module_imports: &'a imbl::OrdMap<SmolStr, imbl::OrdSet<SmolStr>>,
}

impl<'a> ModuleConstraintSolver<'a> {
    pub fn new(import_graph: &'a ImportGraph) -> Self {
        fn create_namespaces(
            import_graph: &ImportGraph,
            namespace: Namespace,
        ) -> Option<HashMap<Namespace, &ConstraintGraph>> {
            import_graph
                .get_constraint_graph(&namespace)
                .map(|constraint_graph| {
                    constraint_graph
                        .subgraphs
                        .keys()
                        .filter_map(|sub_namespace| {
                            create_namespaces(import_graph, sub_namespace.as_ref().clone())
                        })
                        .flatten()
                        .chain(std::iter::once((namespace, constraint_graph)))
                        .collect()
                })
        }

        Self {
            module_namespaces: import_graph
                .modules
                .keys()
                .map(|module_name| {
                    (
                        module_name.clone(),
                        create_namespaces(import_graph, Namespace::Module(module_name.clone()))
                            .unwrap_or_default(),
                    )
                })
                .collect(),
            module_imports: &import_graph.imports,
        }
    }
}

impl DependencyGraphAnalyser for ModuleConstraintSolver<'_> {
    type Node = SmolStr;
    type InputState = BTreeMap<
        Namespace,
        (
            imbl::OrdMap<Parameter, Option<Deferred<Sourced<Type>, Expression>>>,
            imbl::OrdSet<Option<QualifiedLocation>>,
        ),
    >;
    type OutputState = BTreeMap<Namespace, EvaluationState>;
    type AbstractState = ModuleConstraintSolverAbstractState;
    type AnalysisState = ModuleConstraintSolverAnalysisState;
    type Error = Infallible;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(BUILTINS_MODULE))
    }
    fn dependency_nodes<'a: 'n, 'n>(
        &'a self,
        analysis_state: &'a Self::AnalysisState,
        node: &'n Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error> {
        Ok(self
            .module_namespaces
            .get(node)
            .unwrap()
            .keys()
            .flat_map(|namespace| {
                analysis_state
                    .namespace_dependency_graph
                    .graph
                    .predecessors(namespace)
            })
            .filter_map(move |dependency_namespace| {
                let dependency_module_name = dependency_namespace.module_name();
                if node != dependency_module_name {
                    Some(dependency_module_name)
                } else {
                    None
                }
            }))
    }
    fn dependent_nodes<'a: 'n, 'n>(
        &'a self,
        analysis_state: &'a Self::AnalysisState,
        node: &'n Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error> {
        Ok(self
            .module_namespaces
            .get(node)
            .unwrap()
            .keys()
            .flat_map(|namespace| {
                analysis_state
                    .namespace_dependency_graph
                    .graph
                    .successors(namespace)
            })
            .filter_map(move |dependent_namespace| {
                let dependent_module_name = dependent_namespace.module_name();
                if node != dependent_module_name {
                    Some(dependent_module_name)
                } else {
                    None
                }
            }))
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        let mut analysis_state = ModuleConstraintSolverAnalysisState::default();
        for (module_name, import_names) in self.module_imports {
            analysis_state
                .namespace_dependency_graph
                .graph
                .get_or_insert_default_node(Namespace::Module(module_name.clone()));
            for import_name in import_names {
                analysis_state
                    .namespace_dependency_graph
                    .graph
                    .get_or_insert_default_node(Namespace::Module(import_name.clone()));
                analysis_state
                    .namespace_dependency_graph
                    .graph
                    .edge_entry((
                        Namespace::Module(import_name.clone()),
                        Namespace::Module(module_name.clone()),
                    ))
                    .or_default()
                    .insert(EdgeKind::Definition);
            }
        }
        Ok(analysis_state)
    }
    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        let namespace = Namespace::Module(node.clone());

        let constraint_graph = self
            .module_namespaces
            .get(node)
            .unwrap()
            .get(&namespace)
            .unwrap();

        let (program_evaluation, nodes, dependents) = solve_namespace(
            &namespace,
            &Definition::default(),
            constraint_graph,
            &analysis_state.program_evaluation,
            &analysis_state.namespace_dependency_graph,
        )?;

        Ok(ModuleConstraintSolverAbstractState {
            program_evaluation,
            nodes: nodes
                .into_iter()
                .map(|(namespace, definition)| (namespace, definition))
                .collect(),
            dependents,
        })
    }
    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        abstract_state: Self::AbstractState,
    ) -> Result<Self::AnalysisState, Self::Error> {
        let mut new_analysis_state = analysis_state.clone();

        rayon::scope(|scope| {
            scope.spawn(|_| {
                for (node, definition) in abstract_state.nodes {
                    new_analysis_state
                        .namespace_dependency_graph
                        .graph
                        .insert_node(node, definition);
                }
                for (from, tos) in abstract_state.dependents {
                    for (to, edge_data) in tos {
                        if let Some(edge_data) = edge_data {
                            new_analysis_state
                                .namespace_dependency_graph
                                .graph
                                .edge_entry((from.clone(), to.clone()))
                                .or_default()
                                .extend(edge_data);
                        }
                    }
                }
            });
            scope.spawn(|_| {
                new_analysis_state
                    .program_evaluation
                    .states
                    .extend(abstract_state.program_evaluation.states);
            });
        });

        Ok(new_analysis_state)
    }
    fn get_input_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::InputState, Self::Error> {
        Ok(self
            .module_namespaces
            .get(node)
            .par_iter()
            .flat_map_iter(|namespaces| namespaces.keys())
            .map(|namespace| {
                let (arguments, call_sites) =
                    inputs(&analysis_state.namespace_dependency_graph, &namespace);

                (
                    namespace.clone(),
                    (arguments, call_sites.keys().cloned().collect()),
                )
            })
            .collect())
    }
    fn get_output_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::OutputState, Self::Error> {
        Ok(self
            .module_namespaces
            .get(node)
            .par_iter()
            .flat_map_iter(|namespaces| namespaces.keys())
            .map(|namespace| {
                (
                    namespace.clone(),
                    analysis_state
                        .program_evaluation
                        .get_clone_or_default(namespace),
                )
            })
            .collect())
    }
    fn optimise(
        &self,
        analysis_state: &mut Self::AnalysisState,
        worklist: &mut BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        let mut marked = BTreeSet::new();

        for worklist_node in worklist.iter() {
            if marked.contains(worklist_node) {
                continue;
            }

            let mut to_remove = BTreeSet::from_iter([worklist_node]);
            while let Some(node) = to_remove.pop_first() {
                let namespace = Namespace::Module(node.clone());

                for next_namespace in analysis_state
                    .namespace_dependency_graph
                    .graph
                    .successors(&namespace)
                {
                    let Namespace::Module(next_node) = next_namespace else {
                        continue;
                    };
                    if next_node != worklist_node
                        && !marked.contains(next_node)
                        && analysis_state
                            .namespace_dependency_graph
                            .graph
                            .predecessors(next_namespace)
                            .filter_map(|predecessor_namespace| {
                                if let Namespace::Module(predecessor_node) = predecessor_namespace {
                                    Some(predecessor_node)
                                } else {
                                    None
                                }
                            })
                            .all(|predecessor_node| {
                                predecessor_node == node || marked.contains(predecessor_node)
                            })
                    {
                        marked.insert(next_node);
                        to_remove.insert(next_node);
                    }
                }
            }
        }

        *worklist = worklist
            .extract_if(.., |node| !marked.contains(node))
            .collect();

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inference::BUILTINS_MODULE;
    use apygen_analysis::log::LogAnalysisObserver;
    use apygen_analysis::rayon::par_dependencies_analysis;
    use apygen_constraint_builder::{ModuleLoader, analyse_program};
    use indoc::indoc;
    use rstest::rstest;
    use std::collections::HashMap;

    fn init_logger() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    pub struct TestModuleLoader {
        pub modules: HashMap<SmolStr, String>,
    }

    impl ModuleLoader for TestModuleLoader {
        type Error = Infallible;
        fn load(&self, module_name: &SmolStr) -> Result<String, Self::Error> {
            Ok(self.modules.get(module_name).cloned().unwrap())
        }
    }

    const TEST_BUILTINS: &str = indoc! {r##"
        class int:
            def __add__(self, value: int, /) -> int: ...

        class NameError:
            pass
    "##};

    #[rstest]
    fn test_builtins_constraints_solving() {
        init_logger();

        let expected_expressions = indoc! {r##"
        builtins:
            NameError@{builtins[4:6]} = Inferred(class(builtins[NameError@{4:6}]))
            int@{builtins[1:6]} = Inferred(class(builtins[int@{1:6}]))
            #variables = {NameError: {builtins[4:6]}, int: {builtins[1:6]}}
            #raise = {}
            #return = Inferred(None)
        builtins[NameError@{4:6}]:
            #variables = {}
            #raise = {}
            #return = Inferred(None)
        builtins[int@{1:6}][__add__@{2:8}]:
            self@{builtins[int@{1:6}][__add__@{2:8}][2:16]} = Inferred(Any)
            value@{builtins[int@{1:6}][__add__@{2:8}][2:22]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {self: {builtins[int@{1:6}][__add__@{2:8}][2:16]}, value: {builtins[int@{1:6}][__add__@{2:8}][2:22]}}
            #raise = {}
            #return = Specified(@class(builtins[int@{1:6}]))
        builtins[int@{1:6}]:
            __add__@{builtins[int@{1:6}][2:8]} = Inferred(function(builtins[int@{1:6}][__add__@{2:8}]))
            #variables = {__add__: {builtins[int@{1:6}][2:8]}}
            #raise = {}
            #return = Inferred(None)
        "##};

        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([(BUILTINS_MODULE, TEST_BUILTINS.to_owned())]),
        };
        let import_graph = analyse_program(&module_loader, std::iter::empty());

        let solver = ModuleConstraintSolver::new(&import_graph);

        let analysis_state =
            par_dependencies_analysis(&solver, &mut LogAnalysisObserver::default())
                .expect("analysis should work");

        let actual_expressions = format!("{:#}", analysis_state.program_evaluation);

        assert_eq!(
            expected_expressions, actual_expressions,
            "{actual_expressions}"
        );
    }

    #[rstest]
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
        module:
            a@{module[4:4]} = Inferred(42)
            b@{module[8:0]} = Inferred(42)
            x@{module[1:0]} = Inferred(True)
            #variables = {a: {module[4:4]}, b: {module[8:0]}, x: {module[1:0]}}
            #raise = {}
            #return = Inferred(None)
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
        module:
            a@{module[1:0]} = Inferred(0)
            a@{module[4:4]} = Inferred(@class(builtins[int@{1:6}]))
            b@{module[6:0]} = Inferred(@class(builtins[int@{1:6}]))
            #variables = {a: {module[1:0], module[4:4]}, b: {module[6:0]}}
            #raise = {Exception(type=Inferred(Any), origin=Unknown)}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b: int) -> int:
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        module:
            add_two@{module[1:4]} = Inferred(function(module[add_two@{1:4}]))
            result@{module[4:0]} = Inferred(@class(builtins[int@{1:6}]))
            #variables = {add_two: {module[1:4]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[add_two@{1:4}]:
            a@{module[add_two@{1:4}][1:12]} = Specified(@class(builtins[int@{1:6}]))
            b@{module[add_two@{1:4}][1:20]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {a: {module[add_two@{1:4}][1:12]}, b: {module[add_two@{1:4}][1:20]}}
            #raise = {}
            #return = Specified(@class(builtins[int@{1:6}]))
        "##},
    )]
    #[case::simple_class_attribute_access(
        indoc! {r##"
        class A:
            b = 5

        result = A.b
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            result@{module[4:0]} = Inferred(5)
            #variables = {A: {module[1:6]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
            #variables = {b: {module[A@{1:6}][2:4]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_attribute_access(
        indoc! {r##"
        class A:
            b = 5

        a = A()
        result = a.b
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            a@{module[4:0]} = Inferred(@class(module[A@{1:6}]))
            result@{module[5:0]} = Inferred(5)
            #variables = {A: {module[1:6]}, a: {module[4:0]}, result: {module[5:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
            #variables = {b: {module[A@{1:6}][2:4]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_class_function_access(
        indoc! {r##"
        class A:
            def foo():
                return 5

        result = A.foo
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            result@{module[5:0]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {A: {module[1:6]}, result: {module[5:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {foo: {module[A@{1:6}][2:8]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    #[case::simple_method_access(
        indoc! {r##"
        class A:
            def foo():
                return 5

        a = A()
        result = a.foo
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            a@{module[5:0]} = Inferred(@class(module[A@{1:6}]))
            result@{module[6:0]} = Inferred(method(class(module[A@{1:6}])[], function(module[A@{1:6}][foo@{2:8}])))
            #variables = {A: {module[1:6]}, a: {module[5:0]}, result: {module[6:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {foo: {module[A@{1:6}][2:8]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
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
        module:
            CONST@{module[6:0]} = Inferred(5)
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            result@{module[4:0]} = Inferred(5)
            #variables = {CONST: {module[6:0]}, foo: {module[1:4]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},  // TODO: fix when possible
    )]
    #[case::forward_reference_function_call(
        indoc! {r##"
        def foo():
            return CONST

        CONST = 5

        result = foo()
        "##},
        indoc! {r##"
        module:
            CONST@{module[4:0]} = Inferred(5)
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            result@{module[6:0]} = Inferred(5)
            #variables = {CONST: {module[4:0]}, foo: {module[1:4]}, result: {module[6:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    #[case::forward_annotation(
        indoc! {r##"
        a: A

        class A:
            b = 5
        "##},
        indoc! {r##"
        module:
            A@{module[3:6]} = Inferred(class(module[A@{3:6}]))
            a@{module[1:0]} = Inferred(@class(module[A@{3:6}]))
            #variables = {A: {module[3:6]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{3:6}]:
            b@{module[A@{3:6}][4:4]} = Inferred(5)
            #variables = {b: {module[A@{3:6}][4:4]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::argument_inference(
        indoc! {r##"
        def foo(x):
            return x

        result = foo(5)
        "##},
        indoc! {r##"
        module:
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            result@{module[4:0]} = Inferred(5)
            #variables = {foo: {module[1:4]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            x@{module[foo@{1:4}][1:8]} = Inferred(5)
            #variables = {x: {module[foo@{1:4}][1:8]}}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    #[case::argument_inference_different_calls(
        indoc! {r##"
        def foo(x):
            return x

        one = foo(1)
        two = foo(2)
        "##},
        indoc! {r##"
        module:
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            one@{module[4:0]} = Inferred(1 ⊔ 2)
            two@{module[5:0]} = Inferred(1 ⊔ 2)
            #variables = {foo: {module[1:4]}, one: {module[4:0]}, two: {module[5:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            x@{module[foo@{1:4}][1:8]} = Inferred(1 ⊔ 2)
            #variables = {x: {module[foo@{1:4}][1:8]}}
            #raise = {}
            #return = Inferred(1 ⊔ 2)
        "##},
    )]
    #[case::inferred_variable_reassign(
        indoc! {r##"
        x = 1
        x = 2
        "##},
        indoc! {r##"
        module:
            x@{module[1:0]} = Inferred(1)
            x@{module[2:0]} = Inferred(2)
            #variables = {x: {module[2:0]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::specified_variable_reassign(
        indoc! {r##"
        x: int = 1
        x = "test"
        "##},
        indoc! {r##"
        module:
            x@{module[1:0]} = Specified(@class(builtins[int@{1:6}]))
            x@{module[2:0]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {x: {module[2:0]}}
            #raise = {}
            #return = Inferred(None)
        "##},  // TODO: fix when warnings are implemented
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_expressions: &str) {
        init_logger();

        let module_name = SmolStr::new_static("module");
        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([
                (module_name.clone(), source.to_string()),
                (BUILTINS_MODULE, TEST_BUILTINS.to_owned()),
            ]),
        };

        let import_graph = analyse_program(&module_loader, std::iter::once(module_name.clone()));

        let solver = ModuleConstraintSolver::new(&import_graph);

        let mut analysis_state =
            par_dependencies_analysis(&solver, &mut LogAnalysisObserver::default())
                .expect("analysis should work");

        analysis_state.program_evaluation.states = analysis_state
            .program_evaluation
            .states
            .into_iter()
            .filter(|(namespace, _)| *namespace.module_name() == module_name)
            .collect();

        let actual_expressions = format!("{:#}", analysis_state.program_evaluation);

        assert_eq!(
            expected_expressions, actual_expressions,
            "{actual_expressions}"
        );
    }
}
