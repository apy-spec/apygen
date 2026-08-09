use crate::analysis::fmt::fmt_iterator;
use crate::expressions::{Expression, ExpressionVariableDefinition};
use crate::graph::dot::{
    Dot, escape_dot, fmt_digraph, fmt_display_edge, fmt_display_labelled_edge, fmt_display_node,
    fmt_labelled_node,
};
use crate::graph::{Graph, OrdGraph};
use crate::identifiers::{Location, Namespace, SmolStr};
use imbl::ordmap::Entry;
use std::fmt::{self, Debug, Display, Formatter};
use std::sync::Arc;

pub use apygen_analysis as analysis;
pub use apygen_graph as graph;
pub use apygen_identifiers as identifiers;
pub use apygen_primitives as primitives;
pub mod expressions;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Guard {
    ForwardReference,
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
            Guard::ForwardReference => write!(f, "#forward_reference"),
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
    DefinedVariable(ExpressionVariableDefinition),
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
        id: Option<SmolStr>,
    },
    TypeExit,
    ExceptionExit,
    Exit,
}

impl Display for ConstraintNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintGraph {
    pub graph: OrdGraph<ConstraintNode, imbl::OrdSet<Constraint>, imbl::OrdSet<Guard>>,
    pub subgraphs: imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
}

impl ConstraintGraph {
    pub fn new(
        graph: OrdGraph<ConstraintNode, imbl::OrdSet<Constraint>, imbl::OrdSet<Guard>>,
        subgraphs: imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
    ) -> Self {
        Self { graph, subgraphs }
    }
}

impl Dot for ConstraintGraph {
    fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> fmt::Result {
        fmt_digraph(f, &name, |f| {
            for (node, constraints) in self.graph.nodes() {
                if !constraints.is_empty() {
                    fmt_labelled_node(
                        f,
                        |f| write!(f, "{}", &escape_dot(&node.to_string())),
                        |f| {
                            fmt_iterator(f, constraints.iter(), " ∧ ", |f, constraint| {
                                write!(f, "{}", escape_dot(&constraint.to_string()))
                            })
                        },
                    )?;
                } else {
                    fmt_display_node(f, node)?;
                }
            }
            for (edge, guards) in self.graph.edges() {
                if guards.is_empty() {
                    fmt_display_edge(f, edge)?;
                } else {
                    for guard in guards {
                        fmt_display_labelled_edge(f, edge, guard)?;
                    }
                }
            }
            Ok(())
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleDependentGraph {
    pub nodes: imbl::OrdMap<SmolStr, ConstraintGraph>,
    pub dependents: imbl::OrdMap<SmolStr, imbl::OrdSet<SmolStr>>,
}

impl ModuleDependentGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_constraint_graph(&self, namespace: &Namespace) -> Option<&ConstraintGraph> {
        match namespace {
            Namespace::Module(module_name) => self.nodes.get(module_name),
            Namespace::ProgramEntity(qualified_location) => self
                .get_constraint_graph(qualified_location.namespace.as_ref())?
                .subgraphs
                .get(namespace),
            Namespace::NamedProgramEntity(named_qualified_location) => self
                .get_constraint_graph(&named_qualified_location.namespace.as_ref())?
                .subgraphs
                .get(namespace),
        }
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
    pub fn insert(&mut self, node: SmolStr, state: ConstraintGraph) {
        self.nodes.insert(node.clone(), state);
    }

    pub fn add_dependent(&mut self, from: SmolStr, to: SmolStr) {
        self.dependents.entry(from).or_default().insert(to);
    }

    pub fn remove_dependent(&mut self, from: SmolStr, to: SmolStr) {
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

impl Dot for ModuleDependentGraph {
    fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> fmt::Result {
        fmt_digraph(f, &name, |f| {
            for (node, _) in &self.nodes {
                fmt_display_node(f, node)?;
            }
            for (from, tos) in &self.dependents {
                for to in tos {
                    fmt_display_edge(f, &(from.clone(), to.clone()))?;
                }
            }
            Ok(())
        })
    }
}
