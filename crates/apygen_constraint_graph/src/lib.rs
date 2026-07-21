pub mod expressions;

use crate::analysis::fmt::fmt_iterator;
use crate::analysis::lattice::Join;
use crate::expressions::{Expression, ExpressionVariable};
use crate::graph::Graph;
use crate::graph::dot::{DiGraphDot, escape_dot};
use crate::identifiers::{Location, ModuleName, Namespace};
pub use apygen_analysis as analysis;
pub use apygen_graph as graph;
pub use apygen_identifiers as identifiers;
pub use apygen_primitives as primitives;
use imbl::ordmap::Entry;
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Guard {
    IsTrue(Arc<Expression>),
    IsFalse(Arc<Expression>),
    Succeed(Arc<Expression>),
    Raise {
        expression: Arc<Expression>,
        exception: Option<Arc<Expression>>,
    },
}

impl Display for Guard {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Guard::IsTrue(expression) => write!(f, "#is_true({})", expression),
            Guard::IsFalse(expression) => write!(f, "#is_false({})", expression),
            Guard::Succeed(expression) => write!(f, "#succeed({})", expression),
            Guard::Raise {
                expression,
                exception,
            } => match exception {
                Some(exception) => write!(f, "#raise({}, {})", expression, exception),
                None => write!(f, "#raise({})", expression),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IncludeConstraint<T> {
    pub left: T,
    pub right: T,
}

impl<T> IncludeConstraint<T> {
    pub fn new(left: T, right: T) -> Self {
        Self { left, right }
    }
}

impl<T: Display> Display for IncludeConstraint<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ⊑ {}", self.left, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReturnConstraint {
    pub expression: Arc<Expression>,
    pub origin: Option<Namespace>,
}

impl ReturnConstraint {
    pub fn new(expression: Arc<Expression>, origin: Option<Namespace>) -> Self {
        Self { expression, origin }
    }
}

impl Display for ReturnConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#return({}", self.expression)?;
        if let Some(origin) = &self.origin {
            write!(f, ", origin={}", origin)?;
        }
        f.write_str(")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constraint {
    Type(IncludeConstraint<Arc<Expression>>),
    Return(ReturnConstraint),
    DefinedVariable(ExpressionVariable),
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Type(constraint) => write!(f, "{}", constraint),
            Constraint::Return(constraint) => write!(f, "{}", constraint),
            Constraint::DefinedVariable(defined_variable) => {
                write!(f, "#defined({})", defined_variable)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstraintNode {
    Entry,
    Constraint {
        location: Option<Location>,
        id: Option<Arc<String>>,
    },
    TypeExit,
    ExceptionExit,
    Exit,
}

impl Display for ConstraintNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintNode::Entry => f.write_str("Entry"),
            ConstraintNode::Constraint { location, id } => {
                f.write_str("Constraint(")?;
                match (location, id) {
                    (Some(location), Some(id)) => write!(f, "location={}, id={}", location, id)?,
                    (Some(location), None) => write!(f, "location={}", location)?,
                    (None, Some(id)) => write!(f, "id={}", id)?,
                    (None, None) => {}
                }
                f.write_str(")")
            }
            ConstraintNode::TypeExit => f.write_str("TypeExit"),
            ConstraintNode::ExceptionExit => f.write_str("ExceptionExit"),
            ConstraintNode::Exit => f.write_str("Exit"),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct ConstraintGraph {
    pub nodes: imbl::OrdMap<ConstraintNode, imbl::OrdSet<Constraint>>,
    pub edges: imbl::OrdMap<ConstraintNode, imbl::OrdMap<ConstraintNode, imbl::OrdSet<Guard>>>,
}

impl ConstraintGraph {
    pub fn new(
        nodes: imbl::OrdMap<ConstraintNode, imbl::OrdSet<Constraint>>,
        edges: imbl::OrdMap<ConstraintNode, imbl::OrdMap<ConstraintNode, imbl::OrdSet<Guard>>>,
    ) -> Self {
        Self { nodes, edges }
    }

    pub fn add_edge(
        &mut self,
        from: ConstraintNode,
        to: ConstraintNode,
        guards: imbl::OrdSet<Guard>,
    ) {
        match self.edges.entry(from.clone()).or_default().entry(to) {
            Entry::Occupied(entry) => {
                entry.into_mut().extend(guards);
            }
            Entry::Vacant(entry) => {
                entry.insert(guards);
            }
        }
    }

    pub fn exists(&self, from: &ConstraintNode, to: &ConstraintNode) -> bool {
        self.edges.get(from).and_then(|tos| tos.get(to)).is_some()
    }
}

impl Graph for ConstraintGraph {
    type Node = ConstraintNode;
    type NodeData = imbl::OrdSet<Constraint>;
    type EdgeData = imbl::OrdSet<Guard>;

    fn node_data_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)> {
        self.nodes.iter()
    }

    fn edge_data_iter(
        &self,
    ) -> impl Iterator<Item = ((&Self::Node, &Self::Node), &Self::EdgeData)> {
        self.edges
            .iter()
            .flat_map(|(from, tos)| tos.iter().map(move |(to, guards)| ((from, to), guards)))
    }

    fn node_iter(&self) -> impl Iterator<Item = &Self::Node> {
        self.nodes.keys()
    }

    fn edge_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::Node)> {
        self.edges
            .iter()
            .flat_map(|(from, tos)| tos.keys().map(move |to| (from, to)))
    }

    fn get_node_data(&self, node: &Self::Node) -> Option<&Self::NodeData> {
        self.nodes.get(node)
    }

    fn get_edge_data(&self, (from, to): (&Self::Node, &Self::Node)) -> Option<&Self::EdgeData> {
        self.edges.get(from).and_then(|tos| tos.get(to))
    }

    fn successor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edges.get(node).into_iter().flat_map(|tos| tos.keys())
    }
}

impl DiGraphDot for ConstraintGraph {
    fn fmt_node(
        &self,
        f: &mut Formatter<'_>,
        node: &Self::Node,
        node_data: &Self::NodeData,
    ) -> std::fmt::Result {
        write!(f, "    \"{}\" [label=\"", escape_dot(&node.to_string()))?;
        fmt_iterator(f, node_data.iter(), " ∧ ", |f, constraint| {
            write!(f, "{}", escape_dot(&constraint.to_string()))
        })?;
        f.write_str("\"];\n")
    }

    fn fmt_edge(
        &self,
        f: &mut Formatter<'_>,
        (from, to): (&Self::Node, &Self::Node),
        edge_data: &Self::EdgeData,
    ) -> std::fmt::Result {
        if edge_data.is_empty() {
            write!(
                f,
                "    \"{}\" -> \"{}\";\n",
                escape_dot(&from.to_string()),
                escape_dot(&to.to_string()),
            )?;
        } else {
            for guard in edge_data {
                write!(
                    f,
                    "    \"{}\" -> \"{}\" [label=\"{}\"];\n",
                    escape_dot(&from.to_string()),
                    escape_dot(&to.to_string()),
                    escape_dot(&guard.to_string())
                )?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ModuleNode {
    Entry,
    Module(ModuleName),
    Exit,
}

impl Display for ModuleNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ModuleNode::Entry => write!(f, "Entry"),
            ModuleNode::Module(module_name) => write!(f, "Module({})", module_name),
            ModuleNode::Exit => write!(f, "Exit"),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct ProgramEntitySpecification {
    pub arguments: imbl::OrdMap<ExpressionVariable, imbl::OrdSet<Expression>>,
    pub return_type: imbl::OrdSet<Expression>,
    pub exceptions: imbl::OrdSet<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct ProgramEntityConstraints {
    pub specification: ProgramEntitySpecification,
    pub constraint_graph: ConstraintGraph,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct ModuleDependentGraph {
    pub nodes: imbl::OrdMap<ModuleNode, imbl::OrdMap<Arc<Namespace>, ProgramEntityConstraints>>,
    pub dependents: imbl::OrdMap<ModuleNode, imbl::OrdSet<ModuleNode>>,
}

impl ModuleDependentGraph {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Default for ModuleDependentGraph {
    fn default() -> Self {
        Self {
            nodes: imbl::OrdMap::default(),
            dependents: imbl::OrdMap::default(),
        }
    }
}

impl ModuleDependentGraph {
    pub fn insert(
        &mut self,
        node: ModuleNode,
        state: imbl::OrdMap<Arc<Namespace>, ProgramEntityConstraints>,
    ) {
        self.nodes.insert(node.clone(), state);
    }

    pub fn add_dependent(&mut self, from: ModuleNode, to: ModuleNode) {
        self.dependents.entry(from).or_default().insert(to);
    }

    pub fn remove_dependent(&mut self, from: ModuleNode, to: ModuleNode) {
        if let Entry::Occupied(mut tos) = self.dependents.entry(from) {
            tos.get_mut().remove(&to);
        }
    }
}

impl Display for ModuleDependentGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ nodes: {:?}, dependents: {:?} }}",
            self.nodes, self.dependents
        )
    }
}

impl Graph for ModuleDependentGraph {
    type Node = ModuleNode;
    type NodeData = imbl::OrdMap<Arc<Namespace>, ProgramEntityConstraints>;
    type EdgeData = ();

    fn node_data_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)> {
        self.nodes.iter()
    }

    fn edge_data_iter(
        &self,
    ) -> impl Iterator<Item = ((&Self::Node, &Self::Node), &Self::EdgeData)> {
        self.dependents
            .iter()
            .flat_map(|(from, tos)| tos.iter().map(move |to| ((from, to), &())))
    }

    fn node_iter(&self) -> impl Iterator<Item = &Self::Node> {
        self.nodes.keys()
    }

    fn edge_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::Node)> {
        self.dependents
            .iter()
            .flat_map(|(from, tos)| tos.iter().map(move |to| (from, to)))
    }

    fn get_node_data(&self, node: &Self::Node) -> Option<&Self::NodeData> {
        self.nodes.get(node)
    }
}

impl DiGraphDot for ModuleDependentGraph {
    fn fmt_node(
        &self,
        f: &mut Formatter<'_>,
        node: &Self::Node,
        _node_data: &Self::NodeData,
    ) -> std::fmt::Result {
        write!(f, "    \"{}\";\n", escape_dot(&node.to_string()))
    }

    fn fmt_edge(
        &self,
        f: &mut Formatter<'_>,
        (from, to): (&Self::Node, &Self::Node),
        _edge_data: &Self::EdgeData,
    ) -> std::fmt::Result {
        write!(
            f,
            "    \"{}\" -> \"{}\";\n",
            escape_dot(&from.to_string()),
            escape_dot(&to.to_string())
        )
    }
}
