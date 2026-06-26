use crate::abstract_environment::{
    LiteralBoolean, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInteger, LiteralString,
};
use crate::genkill::assignment::AssignmentTarget;
use apy::OneOrMany;
use apy::v1::{GenericKind, Identifier, ParameterKind, QualifiedName};
use apygen_analysis::GraphAnalyser;
use apygen_analysis::cfg::nodes::Number;
use apygen_analysis::cfg::{Cfg, EdgeData, NodeData, ProgramPoint, Ranged, TextRange, nodes};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::Namespace;
use num_bigint::BigInt;
use num_complex::Complex64;
use num_traits::Num;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;
use std::sync::Arc;
use std::sync::mpsc::{SendError, Sender};
use thiserror::Error;

pub type ModuleName = Arc<QualifiedName>;
pub type VariableName = Arc<Identifier>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatticeSet<T: Ord> {
    pub values: imbl::OrdSet<T>,
}

impl<T: Ord> LatticeSet<T> {
    pub fn unit(value: T) -> Self {
        Self::new(imbl::OrdSet::unit(value))
    }

    pub fn new(values: imbl::OrdSet<T>) -> Self {
        Self { values }
    }

    pub fn contains(&self, value: &T) -> bool {
        self.values.contains(value)
    }
}

impl<T: Clone + Ord> LatticeSet<T> {
    pub fn insert(&mut self, value: T) -> Option<T> {
        self.values.insert(value)
    }

    pub fn remove(&mut self, value: &T) -> Option<T> {
        self.values.remove(value)
    }

    pub fn drain(&mut self, f: impl Fn(&T) -> bool) -> Self {
        let mut drained = Self::default();

        self.values = self
            .values
            .iter()
            .filter(|value| {
                if f(*value) {
                    drained.insert((*value).clone());
                    false
                } else {
                    true
                }
            })
            .cloned()
            .collect();

        drained
    }

    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.values.extend(iter);
    }

    pub fn update(&self, value: T) -> Self {
        Self::new(self.values.update(value))
    }

    pub fn union(self, other: Self) -> Self {
        Self::new(self.values.union(other.values))
    }
}

impl<T: Clone + Ord> Lattice for LatticeSet<T> {
    fn includes(&self, other: &Self) -> bool {
        other.values.is_subset(&self.values)
    }

    fn join(&self, other: &Self) -> Self {
        if self.values.is_empty() {
            other.clone()
        } else if other.values.is_empty() {
            self.clone()
        } else {
            Self::new(self.values.clone().union(other.values.clone()))
        }
    }
}

impl<T: Ord> Default for LatticeSet<T> {
    fn default() -> Self {
        Self::new(imbl::OrdSet::default())
    }
}

impl<T: Ord> Deref for LatticeSet<T> {
    type Target = imbl::OrdSet<T>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<T: Ord> AsRef<imbl::OrdSet<T>> for LatticeSet<T> {
    fn as_ref(&self) -> &imbl::OrdSet<T> {
        &self.values
    }
}

impl<T: Clone + Ord> FromIterator<T> for LatticeSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::new(imbl::OrdSet::from_iter(iter))
    }
}

impl<T: Ord + Display> Display for LatticeSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, value) in self.values.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", value)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatticeMap<K: Ord, V> {
    pub values: imbl::OrdMap<K, V>,
}

impl<K: Ord, V> LatticeMap<K, V> {
    pub fn new(values: imbl::OrdMap<K, V>) -> Self {
        Self { values }
    }
}

impl<K: Clone + Ord, V: Clone + Lattice> Lattice for LatticeMap<K, V> {
    fn includes(&self, other: &Self) -> bool {
        other
            .values
            .is_submap_by(&self.values, |self_value, other_value| {
                self_value.includes(other_value)
            })
    }

    fn join(&self, other: &Self) -> Self {
        if self.values.is_empty() {
            other.clone()
        } else if other.values.is_empty() {
            self.clone()
        } else {
            Self::new(
                self.values
                    .clone()
                    .union_with(other.values.clone(), |self_value, other_value| {
                        self_value.join(&other_value)
                    }),
            )
        }
    }
}

impl<K: Ord, V> Default for LatticeMap<K, V> {
    fn default() -> Self {
        Self::new(imbl::OrdMap::default())
    }
}

impl<K: Clone + Ord, V: Clone> FromIterator<(K, V)> for LatticeMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self::new(imbl::OrdMap::from_iter(iter))
    }
}

impl<K: Ord + Display, V: Display> Display for LatticeMap<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, (key, value)) in self.values.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", key, value)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariableLocation {
    pub line: usize,
    pub offset: usize,
}

impl VariableLocation {
    pub fn new(line: usize, offset: usize) -> Self {
        Self { line, offset }
    }
}

impl Display for VariableLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.offset)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VariableDefinition {
    At(VariableLocation),
    Before(VariableLocation),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionVariable {
    pub name: VariableName,
    pub definition: VariableDefinition,
}

impl ExpressionVariable {
    pub fn new(name: VariableName, definition: VariableDefinition) -> Self {
        Self { name, definition }
    }
}

impl Display for ExpressionVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.definition {
            VariableDefinition::At(program_point) => write!(f, "{}@({})", self.name, program_point),
            VariableDefinition::Before(program_point) => {
                write!(f, "{}~({})", self.name, program_point)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionImport {
    pub module: ModuleName,
}

impl ExpressionImport {
    pub fn new(module: ModuleName) -> Self {
        Self { module }
    }
}

impl Display for ExpressionImport {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#import({})", self.module)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeywordArgument {
    pub name: Option<VariableName>,
    pub value: Arc<TypeExpression>,
}

impl Display for KeywordArgument {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{}={}", name, self.value)
        } else {
            write!(f, "**({})", self.value)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionCall {
    pub target: Arc<TypeExpression>,
    pub positional_arguments: imbl::Vector<Arc<TypeExpression>>,
    pub keyword_arguments: imbl::Vector<KeywordArgument>,
}

impl Display for ExpressionCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})(", self.target)?;

        for (i, arg) in self.positional_arguments.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }

        for (i, keyword_argument) in self.keyword_arguments.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", keyword_argument)?;
        }

        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionAttribute {
    pub value: Arc<TypeExpression>,
    pub attribute: VariableName,
}

impl Display for ExpressionAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}).{}", self.value, self.attribute)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionSubscript {
    pub value: Arc<TypeExpression>,
    pub slice: Arc<TypeExpression>,
}

impl Display for ExpressionSubscript {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})[{}]", self.value, self.slice)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionGeneric {
    pub kind: GenericKind,

    pub bound: Arc<TypeExpression>,

    pub constraints: imbl::Vector<Arc<TypeExpression>>,

    pub default: Option<Arc<TypeExpression>>,

    pub is_covariant: bool,

    pub is_contravariant: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Parameter {
    pub name: VariableName,

    pub kind: ParameterKind,

    pub is_optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionFunction {
    pub program_point: ProgramPoint,

    pub parameters: Arc<Vec<Parameter>>,

    pub is_async: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionImportFrom {
    pub module: ModuleName,
    pub attribute: VariableName,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mult,
    MatMult,
    Div,
    FloorDiv,
    Mod,
    Pow,
    LShift,
    RShift,
    BitOr,
    BitXor,
    BitAnd,

    And,
    Or,

    Eq,
    NotEq,
    Lt,
    LtE,
    Gt,
    GtE,
    Is,
    IsNot,
    In,
    NotIn,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            BinaryOperator::Add => "+",
            BinaryOperator::Sub => "-",
            BinaryOperator::Mult => "*",
            BinaryOperator::MatMult => "@",
            BinaryOperator::Div => "/",
            BinaryOperator::FloorDiv => "//",
            BinaryOperator::Mod => "%",
            BinaryOperator::Pow => "**",
            BinaryOperator::LShift => "<<",
            BinaryOperator::RShift => ">>",
            BinaryOperator::BitOr => "|",
            BinaryOperator::BitXor => "^",
            BinaryOperator::BitAnd => "&",
            BinaryOperator::And => "and",
            BinaryOperator::Or => "or",
            BinaryOperator::Eq => "==",
            BinaryOperator::NotEq => "!=",
            BinaryOperator::Lt => "<",
            BinaryOperator::LtE => "<=",
            BinaryOperator::Gt => ">",
            BinaryOperator::GtE => ">=",
            BinaryOperator::Is => "is",
            BinaryOperator::IsNot => "is not",
            BinaryOperator::In => "in",
            BinaryOperator::NotIn => "not in",
        };

        write!(f, "{}", symbol)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionBinary {
    pub left: Arc<TypeExpression>,
    pub operator: BinaryOperator,
    pub right: Arc<TypeExpression>,
}

impl Display for ExpressionBinary {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}) {} ({})", self.left, self.operator, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryOperator {
    Invert,
    Not,
    UAdd,
    USub,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            UnaryOperator::Invert => "~",
            UnaryOperator::Not => "not",
            UnaryOperator::UAdd => "+",
            UnaryOperator::USub => "-",
        };

        write!(f, "{}", symbol)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionUnary {
    pub operator: UnaryOperator,
    pub operand: Arc<TypeExpression>,
}

impl Display for ExpressionUnary {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.operator {
            UnaryOperator::Not => write!(f, "{} ({})", self.operator, self.operand),
            _ => write!(f, "{}({})", self.operator, self.operand),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeExpression {
    Variable(ExpressionVariable),
    Import(ExpressionImport),
    Attribute(ExpressionAttribute),
    Subscript(ExpressionSubscript),
    Call(ExpressionCall),
    Unary(ExpressionUnary),
    Binary(ExpressionBinary),
    LiteralInteger(LiteralInteger),
    LiteralFloat(LiteralFloat),
    LiteralComplex(LiteralComplex),
    LiteralString(LiteralString),
    LiteralBytes(LiteralBytes),
    LiteralBoolean(LiteralBoolean),
    LiteralNone,
    LiteralEllipsis,
}

impl Display for TypeExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpression::Variable(expression_variable) => write!(f, "{}", expression_variable),
            TypeExpression::Import(expression_import) => write!(f, "{}", expression_import),
            TypeExpression::Attribute(expression_attribute) => {
                write!(f, "{}", expression_attribute)
            }
            TypeExpression::Subscript(expression_subscript) => {
                write!(f, "{}", expression_subscript)
            }
            TypeExpression::Call(expression_call) => write!(f, "{}", expression_call),
            TypeExpression::Unary(expression_unary) => write!(f, "{}", expression_unary),
            TypeExpression::Binary(expression_binary) => write!(f, "{}", expression_binary),
            TypeExpression::LiteralInteger(literal_integer) => write!(f, "{}", literal_integer),
            TypeExpression::LiteralFloat(literal_float) => write!(f, "{}", literal_float),
            TypeExpression::LiteralComplex(literal_complex) => write!(f, "{}", literal_complex),
            TypeExpression::LiteralString(literal_string) => write!(f, "{}", literal_string),
            TypeExpression::LiteralBytes(literal_bytes) => write!(f, "{}", literal_bytes),
            TypeExpression::LiteralBoolean(literal_boolean) => write!(f, "{}", literal_boolean),
            TypeExpression::LiteralNone => write!(f, "None"),
            TypeExpression::LiteralEllipsis => write!(f, "..."),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RaisedException {
    pub program_points: imbl::Vector<ProgramPoint>,
}

impl Display for RaisedException {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#raised_exceptions(")?;
        for (i, program_point) in self.program_points.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", program_point)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExceptionExpression {
    Raised(RaisedException),
    Type(Arc<TypeExpression>),
}

impl Display for ExceptionExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ExceptionExpression::Raised(raised_exception) => write!(f, "{}", raised_exception),
            ExceptionExpression::Type(type_expression) => {
                write!(f, "#exceptions({})", type_expression)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Guard {
    IsTrue(Arc<TypeExpression>),
    IsFalse(Arc<TypeExpression>),
    Succeed(Arc<TypeExpression>),
    Raise {
        expression: Arc<TypeExpression>,
        exception: Option<Arc<TypeExpression>>,
    },
    Multiple(LatticeSet<Guard>),
}

impl Guard {
    pub fn is_empty(&self) -> bool {
        match self {
            Guard::Multiple(guards) => guards.is_empty(),
            _ => false,
        }
    }
}

impl Default for Guard {
    fn default() -> Self {
        Guard::Multiple(LatticeSet::default())
    }
}

impl Lattice for Guard {
    fn includes(&self, other: &Self) -> bool {
        match (self, other) {
            (Guard::Multiple(self_guards), Guard::Multiple(other_guards)) => {
                self_guards.includes(other_guards)
            }
            (Guard::Multiple(self_guards), _) => self_guards.contains(other),
            (_, Guard::Multiple(other_guards)) => {
                LatticeSet::unit(self.clone()).includes(other_guards)
            }
            _ => self == other,
        }
    }

    fn join(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }

        match (self, other) {
            (Guard::Multiple(self_guards), Guard::Multiple(other_guards)) => {
                Guard::Multiple(self_guards.join(other_guards))
            }
            (Guard::Multiple(self_guards), _) => Guard::Multiple(self_guards.update(other.clone())),
            (_, Guard::Multiple(other_guards)) => {
                Guard::Multiple(other_guards.update(self.clone()))
            }
            _ => Guard::Multiple(LatticeSet::from_iter([self.clone(), other.clone()])),
        }
    }
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
            Guard::Multiple(guards) => {
                write!(f, "{}", guards)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstraintKind {
    Include,
    Equal,
}

impl Display for ConstraintKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            ConstraintKind::Include => "⊑",
            ConstraintKind::Equal => "=",
        };

        write!(f, "{}", symbol)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintDefinition<T> {
    pub left: Arc<T>,
    pub kind: ConstraintKind,
    pub right: Arc<T>,
}

impl<T: Clone> ConstraintDefinition<T> {
    pub fn new(left: Arc<T>, kind: ConstraintKind, right: Arc<T>) -> Self {
        Self { left, kind, right }
    }

    pub fn equal(left: T, right: T) -> Self {
        Self::new(Arc::new(left), ConstraintKind::Equal, Arc::new(right))
    }

    pub fn include(left: T, right: T) -> Self {
        Self::new(Arc::new(left), ConstraintKind::Include, Arc::new(right))
    }
}

impl<T: Display> Display for ConstraintDefinition<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.left, self.kind, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constraint {
    Type(ConstraintDefinition<TypeExpression>),
    Exception(ConstraintDefinition<ExceptionExpression>),
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Type(constraint_type) => write!(f, "{}", constraint_type),
            Constraint::Exception(constraint_exception) => write!(f, "{}", constraint_exception),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstraintNode {
    Entry,
    Constraint(Arc<Constraint>),
    Empty(VariableLocation),
    Exit,
}

impl Display for ConstraintNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintNode::Entry => write!(f, "#entry"),
            ConstraintNode::Constraint(constraint) => write!(f, "{}", constraint),
            ConstraintNode::Empty(location) => write!(f, "#empty({})", location),
            ConstraintNode::Exit => write!(f, "#exit"),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintGraph {
    pub edges: LatticeMap<ConstraintNode, LatticeMap<ConstraintNode, Guard>>,
}

impl ConstraintGraph {
    pub fn new(edges: LatticeMap<ConstraintNode, LatticeMap<ConstraintNode, Guard>>) -> Self {
        Self { edges }
    }

    pub fn add_edge(&mut self, from: ConstraintNode, to: ConstraintNode, guard: Guard) {
        self.edges
            .values
            .entry(from.clone())
            .or_default()
            .values
            .entry(to)
            .or_insert(guard);
    }

    pub fn dot(&self) -> String {
        let mut nodes: imbl::OrdSet<ConstraintNode> = imbl::OrdSet::new();
        let mut edges: imbl::OrdMap<(ConstraintNode, ConstraintNode), Guard> = imbl::OrdMap::new();
        for (from, tos) in &self.edges.values {
            for (to, guard) in &tos.values {
                nodes.insert(from.clone());
                nodes.insert(to.clone());
                edges.insert((from.clone(), to.clone()), guard.clone());
            }
        }

        let mut dot_representation = String::from("digraph \"Constraints\" {\n");
        for node in &nodes {
            dot_representation.push_str("    \"");
            dot_representation.push_str(&node.to_string());
            dot_representation.push_str("\";\n");
        }
        for ((from, to), guard) in &edges {
            dot_representation.push_str("    \"");
            dot_representation.push_str(&from.to_string());
            dot_representation.push_str("\" -> \"");
            dot_representation.push_str(&to.to_string());
            dot_representation.push_str("\" [label=\"");
            dot_representation.push_str(&guard.to_string());
            dot_representation.push_str("\"];\n");
        }
        dot_representation.push_str("}\n");

        dot_representation
    }
}

impl Lattice for ConstraintGraph {
    fn includes(&self, other: &Self) -> bool {
        self.edges.includes(&other.edges)
    }

    fn join(&self, other: &Self) -> Self {
        Self::new(self.edges.join(&other.edges))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbstractEnvironment {
    pub current_nodes: LatticeSet<(ConstraintNode, Guard)>,
    pub variable_locations: LatticeMap<VariableName, LatticeSet<VariableLocation>>,
    pub constraint_graph: ConstraintGraph,
}

impl Default for AbstractEnvironment {
    fn default() -> Self {
        Self {
            current_nodes: LatticeSet::unit((
                ConstraintNode::Entry,
                Guard::Multiple(LatticeSet::default()),
            )),
            variable_locations: LatticeMap::default(),
            constraint_graph: ConstraintGraph::default(),
        }
    }
}
impl Lattice for AbstractEnvironment {
    fn includes(&self, other: &Self) -> bool {
        self.current_nodes.includes(&other.current_nodes)
            && self.variable_locations.includes(&other.variable_locations)
            && self.constraint_graph.includes(&other.constraint_graph)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            current_nodes: self.current_nodes.join(&other.current_nodes),
            variable_locations: self.variable_locations.join(&other.variable_locations),
            constraint_graph: self.constraint_graph.join(&other.constraint_graph),
        }
    }
}

#[derive(Debug, Error)]
pub enum ConstraintsBuilderError {
    #[error("`{name}` at program point `{program_point}` is an invalid Python module")]
    InvalidModule {
        program_point: ProgramPoint,
        name: String,
    },
    #[error("`{name}` at program point `{program_point}` is an invalid Python identifier")]
    InvalidIdentifier {
        program_point: ProgramPoint,
        name: String,
    },
    #[error("failed to send import `{0}`")]
    SendImportError(#[from] SendError<ModuleName>),
    #[error("program point `{program_point}` is invalid")]
    InvalidProgramPoint { program_point: ProgramPoint },
    #[error("invalid bool expression `{expr:?}`")]
    InvalidExprBoolOp { expr: nodes::ExprBoolOp },
    #[error("invalid compare expression `{expr:?}`")]
    InvalidExprCompare { expr: nodes::ExprCompare },
}

#[derive(Debug, Clone)]
pub struct ConstraintsBuilder<'a> {
    pub cfg: &'a Cfg,
    pub import_tx: &'a Sender<ModuleName>,
}

impl<'a> ConstraintsBuilder<'a> {
    pub fn new(cfg: &'a Cfg, import_tx: &'a Sender<ModuleName>) -> ConstraintsBuilder<'a> {
        ConstraintsBuilder { cfg, import_tx }
    }

    pub fn import_module(&self, module: ModuleName) -> Result<(), ConstraintsBuilderError> {
        Ok(self.import_tx.send(module)?)
    }

    pub fn create_include_constraint(
        &self,
        abstract_environment: &mut AbstractEnvironment,
        location: VariableLocation,
        left: Arc<TypeExpression>,
        right: Arc<TypeExpression>,
    ) {
        let node = ConstraintNode::Constraint(Arc::new(Constraint::Type(
            ConstraintDefinition::new(left.clone(), ConstraintKind::Include, right.clone()),
        )));

        let mut current_nodes = LatticeSet::unit((node.clone(), Guard::default()));

        let current_empty_constraint = ConstraintNode::Empty(location);

        for (from, guard) in abstract_environment.current_nodes.as_ref() {
            let from = if guard.is_empty() {
                from
            } else {
                abstract_environment.constraint_graph.add_edge(
                    from.clone(),
                    current_empty_constraint.clone(),
                    guard.clone(),
                );
                &current_empty_constraint
            };

            abstract_environment.constraint_graph.add_edge(
                from.clone(),
                node.clone(),
                Guard::Succeed(left.clone()),
            );
            current_nodes.insert((
                from.clone(),
                Guard::Raise {
                    expression: left.clone(),
                    exception: None,
                },
            ));
        }

        abstract_environment.current_nodes = current_nodes;
    }

    pub fn assign_variable(
        &self,
        abstract_environment: &mut AbstractEnvironment,
        location: VariableLocation,
        variable: VariableName,
        type_expression: Arc<TypeExpression>,
    ) {
        self.create_include_constraint(
            abstract_environment,
            location.clone(),
            type_expression,
            Arc::new(TypeExpression::Variable(ExpressionVariable::new(
                variable.clone(),
                VariableDefinition::At(location.clone()),
            ))),
        );

        abstract_environment
            .variable_locations
            .values
            .insert(variable, LatticeSet::from_iter([location]));
    }

    pub fn assign_empty_constraint(
        &self,
        abstract_environment: &mut AbstractEnvironment,
        location: VariableLocation,
        guards: &[Guard],
    ) {
        let node = ConstraintNode::Empty(location);

        for (from, guard) in abstract_environment.current_nodes.as_ref() {
            abstract_environment.constraint_graph.add_edge(
                from.clone(),
                node.clone(),
                guard.clone(),
            );
        }

        abstract_environment.current_nodes =
            LatticeSet::from_iter(guards.iter().map(|guard| (node.clone(), guard.clone())));
    }

    pub fn gen_module_name(
        &self,
        program_point: ProgramPoint,
        name: &str,
    ) -> Result<ModuleName, ConstraintsBuilderError> {
        match QualifiedName::try_from(name) {
            Ok(module_name) => Ok(Arc::new(module_name)),
            Err(_) => Err(ConstraintsBuilderError::InvalidModule {
                program_point,
                name: name.to_owned(),
            }),
        }
    }

    pub fn gen_variable_name(
        &self,
        program_point: ProgramPoint,
        name: &str,
    ) -> Result<VariableName, ConstraintsBuilderError> {
        match Identifier::try_from(name) {
            Ok(module_name) => Ok(Arc::new(module_name)),
            Err(_) => Err(ConstraintsBuilderError::InvalidIdentifier {
                program_point,
                name: name.to_owned(),
            }),
        }
    }

    pub fn gen_variable_location(&self, range: TextRange) -> VariableLocation {
        let line = self.cfg.line_index.line_index(range.start()).get();
        VariableLocation::new(line, range.start().to_usize())
    }

    pub fn gen_parameter(
        &self,
        program_point: ProgramPoint,
        parameter: &nodes::Parameter,
    ) -> Result<(VariableName, ConstraintGraph), ConstraintsBuilderError> {
        let parameter_name = self.gen_variable_name(program_point, &parameter.name)?;

        let constraint_graph = ConstraintGraph::default();

        if let Some(annotation) = &parameter.annotation {
            // TODO: add support for annotations
        }

        Ok((parameter_name, constraint_graph))
    }

    pub fn gen_parameter_with_default(
        &self,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        parameter_with_default: &nodes::ParameterWithDefault,
    ) -> Result<(VariableName, ConstraintGraph), ConstraintsBuilderError> {
        let (parameter_name, mut constraint_graph) =
            self.gen_parameter(program_point, &parameter_with_default.parameter)?;

        if let Some(default) = &parameter_with_default.default {
            let type_expression = self.gen_expr(
                &Namespace::default(),
                program_point,
                target_abstract_environment,
                &default,
            )?;
            constraint_graph.add_edge(
                ConstraintNode::Entry,
                ConstraintNode::Constraint(Arc::new(Constraint::Type(
                    ConstraintDefinition::equal(
                        TypeExpression::Variable(ExpressionVariable::new(
                            parameter_name.clone(),
                            VariableDefinition::At(
                                self.gen_variable_location(parameter_with_default.range),
                            ),
                        )),
                        type_expression,
                    ),
                ))),
                Guard::default(),
            );
        }

        Ok((parameter_name, constraint_graph))
    }

    pub fn gen_parameters(
        &self,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        parameters: &nodes::Parameters,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut abstract_environment = AbstractEnvironment::default();

        for parameter in &parameters.posonlyargs {
            let (parameter_name, constraints) = self.gen_parameter_with_default(
                program_point,
                target_abstract_environment,
                &parameter,
            )?;
        }

        for parameter in &parameters.args {
            let (parameter_name, constraints) =
                self.gen_parameter(program_point, &parameter.parameter)?;
        }

        if let Some(parameter) = &parameters.vararg {
            let (parameter_name, constraints) = self.gen_parameter(program_point, &parameter)?;
        }

        for parameter in &parameters.kwonlyargs {
            let (parameter_name, constraints) = self.gen_parameter_with_default(
                program_point,
                target_abstract_environment,
                &parameter,
            )?;
        }

        if let Some(parameter) = &parameters.kwarg {
            let (parameter_name, constraints) = self.gen_parameter(program_point, &parameter)?;
        }

        Ok(abstract_environment)
    }

    pub fn gen_expr_bool_op(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_bool_op: &nodes::ExprBoolOp,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let mut values_iter = expr_bool_op.values.iter();

        let mut type_expression = match values_iter.next() {
            Some(value) => {
                self.gen_expr(namespace, program_point, target_abstract_environment, value)?
            }
            None => {
                return Err(ConstraintsBuilderError::InvalidExprBoolOp {
                    expr: expr_bool_op.clone(),
                });
            }
        };

        let operator = match expr_bool_op.op {
            nodes::BoolOp::And => BinaryOperator::And,
            nodes::BoolOp::Or => BinaryOperator::Or,
        };

        for value in values_iter {
            type_expression = TypeExpression::Binary(ExpressionBinary {
                left: Arc::new(type_expression),
                operator: operator.clone(),
                right: Arc::new(self.gen_expr(
                    namespace,
                    program_point,
                    target_abstract_environment,
                    &value,
                )?),
            });
        }

        Ok(type_expression)
    }

    pub fn gen_expr_bin_op(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_bin_op: &nodes::ExprBinOp,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let left = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_bin_op.left,
        )?;
        let right = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_bin_op.right,
        )?;

        let operator = match expr_bin_op.op {
            nodes::Operator::Add => BinaryOperator::Add,
            nodes::Operator::Sub => BinaryOperator::Sub,
            nodes::Operator::Mult => BinaryOperator::Mult,
            nodes::Operator::MatMult => BinaryOperator::MatMult,
            nodes::Operator::Div => BinaryOperator::Div,
            nodes::Operator::Mod => BinaryOperator::Mod,
            nodes::Operator::Pow => BinaryOperator::Pow,
            nodes::Operator::LShift => BinaryOperator::LShift,
            nodes::Operator::RShift => BinaryOperator::RShift,
            nodes::Operator::BitOr => BinaryOperator::BitOr,
            nodes::Operator::BitXor => BinaryOperator::BitXor,
            nodes::Operator::BitAnd => BinaryOperator::BitAnd,
            nodes::Operator::FloorDiv => BinaryOperator::FloorDiv,
        };

        Ok(TypeExpression::Binary(ExpressionBinary {
            left: Arc::new(left),
            operator,
            right: Arc::new(right),
        }))
    }

    pub fn gen_expr_unary_op(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_unary_op: &nodes::ExprUnaryOp,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let operand = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_unary_op.operand,
        )?;

        let operator = match expr_unary_op.op {
            nodes::UnaryOp::Invert => UnaryOperator::Invert,
            nodes::UnaryOp::Not => UnaryOperator::Not,
            nodes::UnaryOp::UAdd => UnaryOperator::UAdd,
            nodes::UnaryOp::USub => UnaryOperator::USub,
        };

        Ok(TypeExpression::Unary(ExpressionUnary {
            operator,
            operand: Arc::new(operand),
        }))
    }

    pub fn gen_expr_compare(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_compare: &nodes::ExprCompare,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let mut type_expression = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_compare.left,
        )?;

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
                nodes::CmpOp::Eq => BinaryOperator::Eq,
                nodes::CmpOp::NotEq => BinaryOperator::NotEq,
                nodes::CmpOp::Lt => BinaryOperator::Lt,
                nodes::CmpOp::LtE => BinaryOperator::LtE,
                nodes::CmpOp::Gt => BinaryOperator::Gt,
                nodes::CmpOp::GtE => BinaryOperator::GtE,
                nodes::CmpOp::Is => BinaryOperator::Is,
                nodes::CmpOp::IsNot => BinaryOperator::IsNot,
                nodes::CmpOp::In => BinaryOperator::In,
                nodes::CmpOp::NotIn => BinaryOperator::NotIn,
            };

            let comparator = self.gen_expr(
                namespace,
                program_point,
                target_abstract_environment,
                comparator,
            )?;

            type_expression = TypeExpression::Binary(ExpressionBinary {
                left: Arc::new(type_expression),
                operator,
                right: Arc::new(comparator),
            });
        }

        Ok(type_expression)
    }

    pub fn gen_expr_call(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_call: &nodes::ExprCall,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let func = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_call.func,
        )?;

        let mut positional_arguments: imbl::Vector<Arc<TypeExpression>> = imbl::Vector::new();
        for positional_argument in &expr_call.arguments.args {
            positional_arguments.push_back(Arc::new(self.gen_expr(
                namespace,
                program_point,
                target_abstract_environment,
                &positional_argument,
            )?));
        }

        let mut keyword_arguments: imbl::Vector<KeywordArgument> = imbl::Vector::new();
        for keyword_argument in &expr_call.arguments.keywords {
            let keyword_name = match &keyword_argument.arg {
                Some(identifier) => Some(self.gen_variable_name(program_point, &identifier)?),
                None => None,
            };
            let keyword_type = self.gen_expr(
                namespace,
                program_point,
                target_abstract_environment,
                &keyword_argument.value,
            )?;
            keyword_arguments.push_back(KeywordArgument {
                name: keyword_name,
                value: Arc::new(keyword_type),
            });
        }

        Ok(TypeExpression::Call(ExpressionCall {
            target: Arc::new(func),
            positional_arguments,
            keyword_arguments,
        }))
    }

    pub fn gen_expr_string_literal(
        &self,
        expr_string_literal: &nodes::ExprStringLiteral,
    ) -> TypeExpression {
        TypeExpression::LiteralString(LiteralString {
            value: Arc::new(expr_string_literal.value.to_str().to_owned()),
        })
    }

    pub fn gen_expr_bytes_literal(
        &self,
        expr_bytes_literal: &nodes::ExprBytesLiteral,
    ) -> TypeExpression {
        TypeExpression::LiteralBytes(LiteralBytes {
            value: expr_bytes_literal
                .value
                .iter()
                .flat_map(|part| part.as_slice())
                .copied()
                .collect(),
        })
    }

    pub fn gen_expr_number_literal(
        &self,
        expr_number_literal: &nodes::ExprNumberLiteral,
    ) -> TypeExpression {
        match &expr_number_literal.value {
            Number::Int(int) => match int.as_i64() {
                Some(value) => TypeExpression::LiteralInteger(LiteralInteger::Int(value)),
                None => TypeExpression::LiteralInteger(LiteralInteger::BigInt({
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
                })),
            },
            Number::Float(float) => TypeExpression::LiteralFloat(LiteralFloat { value: *float }),
            Number::Complex { real, imag } => TypeExpression::LiteralComplex(LiteralComplex {
                value: Complex64::new(*real, *imag),
            }),
        }
    }

    pub fn gen_expr_boolean_literal(
        &self,
        expr_boolean_literal: &nodes::ExprBooleanLiteral,
    ) -> TypeExpression {
        TypeExpression::LiteralBoolean(LiteralBoolean {
            value: expr_boolean_literal.value,
        })
    }

    pub fn gen_expr_none_literal(&self) -> TypeExpression {
        TypeExpression::LiteralNone
    }

    pub fn gen_expr_ellipsis_literal(&self) -> TypeExpression {
        TypeExpression::LiteralEllipsis
    }

    pub fn gen_expr_attribute(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_attribute: &nodes::ExprAttribute,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let value = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_attribute.value,
        )?;
        let attribute = self.gen_variable_name(program_point, &expr_attribute.attr)?;

        Ok(TypeExpression::Attribute(ExpressionAttribute {
            value: Arc::new(value),
            attribute,
        }))
    }

    pub fn gen_expr_subscript(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_subscript: &nodes::ExprSubscript,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let value = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_subscript.value,
        )?;
        let slice = self.gen_expr(
            namespace,
            program_point,
            target_abstract_environment,
            &expr_subscript.slice,
        )?;

        Ok(TypeExpression::Subscript(ExpressionSubscript {
            value: Arc::new(value),
            slice: Arc::new(slice),
        }))
    }

    pub fn gen_name(
        &self,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr_name: &nodes::ExprName,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let variable_name = self.gen_variable_name(program_point, &expr_name.id)?;
        let variable_location = self.gen_variable_location(expr_name.range);
        let variable_expression = TypeExpression::Variable(ExpressionVariable::new(
            variable_name.clone(),
            VariableDefinition::Before(variable_location.clone()),
        ));

        if let Some(locations) = target_abstract_environment
            .variable_locations
            .values
            .get(&variable_name)
        {
            let mut current_nodes: LatticeSet<(ConstraintNode, Guard)> = LatticeSet::default();
            for (from, guard) in target_abstract_environment.current_nodes.as_ref() {
                for location in &locations.values {
                    if location == &variable_location {
                        continue;
                    }
                    let location_constraint = ConstraintNode::Constraint(Arc::new(
                        Constraint::Type(ConstraintDefinition::include(
                            TypeExpression::Variable(ExpressionVariable::new(
                                variable_name.clone(),
                                VariableDefinition::At(location.clone()),
                            )),
                            variable_expression.clone(),
                        )),
                    ));
                    target_abstract_environment.constraint_graph.add_edge(
                        from.clone(),
                        location_constraint.clone(),
                        guard.clone(),
                    );
                    current_nodes.insert((location_constraint.clone(), Guard::default()));
                }
            }
            target_abstract_environment.current_nodes = current_nodes;
        }

        Ok(variable_expression)
    }

    pub fn gen_expr(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        target_abstract_environment: &mut AbstractEnvironment,
        expr: &nodes::Expr,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        match expr {
            nodes::Expr::BoolOp(expr_bool_op) => self.gen_expr_bool_op(
                namespace,
                program_point,
                target_abstract_environment,
                expr_bool_op,
            ),
            nodes::Expr::Named(_) => todo!(),
            nodes::Expr::BinOp(expr_bin_op) => self.gen_expr_bin_op(
                namespace,
                program_point,
                target_abstract_environment,
                expr_bin_op,
            ),
            nodes::Expr::UnaryOp(expr_unary_op) => self.gen_expr_unary_op(
                namespace,
                program_point,
                target_abstract_environment,
                expr_unary_op,
            ),
            nodes::Expr::Lambda(_) => todo!(),
            nodes::Expr::If(_) => todo!(),
            nodes::Expr::Dict(_) => todo!(),
            nodes::Expr::Set(_) => todo!(),
            nodes::Expr::ListComp(_) => todo!(),
            nodes::Expr::SetComp(_) => todo!(),
            nodes::Expr::DictComp(_) => todo!(),
            nodes::Expr::Generator(_) => todo!(),
            nodes::Expr::Await(_) => todo!(),
            nodes::Expr::Yield(_) => todo!(),
            nodes::Expr::YieldFrom(_) => todo!(),
            nodes::Expr::Compare(expr_compare) => self.gen_expr_compare(
                namespace,
                program_point,
                target_abstract_environment,
                expr_compare,
            ),
            nodes::Expr::Call(expr_call) => self.gen_expr_call(
                namespace,
                program_point,
                target_abstract_environment,
                expr_call,
            ),
            nodes::Expr::FString(_) => todo!(),
            nodes::Expr::StringLiteral(expr_string_literal) => {
                Ok(self.gen_expr_string_literal(expr_string_literal))
            }
            nodes::Expr::BytesLiteral(expr_bytes_literal) => {
                Ok(self.gen_expr_bytes_literal(expr_bytes_literal))
            }
            nodes::Expr::NumberLiteral(expr_number_literal) => {
                Ok(self.gen_expr_number_literal(expr_number_literal))
            }
            nodes::Expr::BooleanLiteral(expr_boolean_literal) => {
                Ok(self.gen_expr_boolean_literal(expr_boolean_literal))
            }
            nodes::Expr::NoneLiteral(_) => Ok(self.gen_expr_none_literal()),
            nodes::Expr::EllipsisLiteral(_) => Ok(self.gen_expr_ellipsis_literal()),
            nodes::Expr::Attribute(expr_attribute) => self.gen_expr_attribute(
                namespace,
                program_point,
                target_abstract_environment,
                expr_attribute,
            ),
            nodes::Expr::Subscript(expr_subscript) => self.gen_expr_subscript(
                namespace,
                program_point,
                target_abstract_environment,
                expr_subscript,
            ),
            nodes::Expr::Starred(_) => todo!(),
            nodes::Expr::Name(expr_name) => {
                self.gen_name(program_point, target_abstract_environment, expr_name)
            }
            nodes::Expr::List(_) => todo!(),
            nodes::Expr::Tuple(_) => todo!(),
            nodes::Expr::Slice(_) => todo!(),
            nodes::Expr::IpyEscapeCommand(_) => todo!(),
        }
    }

    pub fn gen_stmt_function_def(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt_function_def: &nodes::StmtFunctionDef,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let identifier = self.gen_variable_name(program_point, &stmt_function_def.name)?;

        let parameters = self.gen_parameters(
            ProgramPoint::Entry,
            &mut target_abstract_environment,
            &stmt_function_def.parameters,
        )?;

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt_import(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt_import: &nodes::StmtImport,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let mut current_nodes: LatticeSet<(ConstraintNode, Guard)> = LatticeSet::default();
        for alias in &stmt_import.names {
            let module_name = self.gen_module_name(program_point, &alias.name)?;

            if let Some(as_name) = &alias.asname {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_variable_location(as_name.range),
                    self.gen_variable_name(program_point, &as_name)?,
                    Arc::new(TypeExpression::Import(ExpressionImport::new(
                        module_name.clone(),
                    ))),
                );
            } else {
                let identifier = Arc::new(module_name.identifiers.first().clone());
                let location = self.gen_variable_location(alias.name.range);

                target_abstract_environment
                    .variable_locations
                    .values
                    .insert(
                        identifier.clone(),
                        LatticeSet::from_iter([location.clone()]),
                    );

                let mut expression_option = Some(Arc::new(TypeExpression::Variable(
                    ExpressionVariable::new(identifier, VariableDefinition::At(location)),
                )));

                let mut variable_location = self.gen_variable_location(alias.name.range);
                let mut i = 1;
                while let Some(expression) = expression_option {
                    let (module_identifiers, attribute_identifiers) =
                        module_name.identifiers.split_at(i);
                    let attribute_option = attribute_identifiers.first().cloned();
                    variable_location.offset += 1;
                    self.create_include_constraint(
                        &mut target_abstract_environment,
                        variable_location.clone(),
                        Arc::new(TypeExpression::Import(ExpressionImport::new(Arc::new(
                            QualifiedName::new(OneOrMany::many(Vec::from(module_identifiers))),
                        )))),
                        expression.clone(),
                    );
                    // TODO: add constraints of exceptions, pureness and mutability
                    if let Some(attribute) = attribute_option {
                        expression_option =
                            Some(Arc::new(TypeExpression::Attribute(ExpressionAttribute {
                                value: expression,
                                attribute: Arc::new(attribute),
                            })));
                    } else {
                        expression_option = None;
                    }

                    current_nodes.extend(
                        target_abstract_environment
                            .current_nodes
                            .drain(|(_, guard)| match guard {
                                Guard::Raise { .. } => true,
                                _ => false,
                            })
                            .values,
                    );

                    i = i + 1;
                }
            };

            current_nodes.extend(
                target_abstract_environment
                    .current_nodes
                    .drain(|(_, guard)| match guard {
                        Guard::Raise { .. } => true,
                        _ => false,
                    })
                    .values,
            );

            self.import_module(module_name.clone())?;
        }

        target_abstract_environment
            .current_nodes
            .extend(current_nodes.values);

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt_assign(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt_assign: &nodes::StmtAssign,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let type_expression = Arc::new(self.gen_expr(
            namespace,
            program_point,
            &mut target_abstract_environment,
            &stmt_assign.value,
        )?);

        let mut current_nodes: LatticeSet<(ConstraintNode, Guard)> = LatticeSet::default();
        for target_expr in &stmt_assign.targets {
            let Ok(target) = AssignmentTarget::try_from(target_expr) else {
                todo!("add the right error");
            };

            match target {
                AssignmentTarget::Name(target_name) => {
                    self.assign_variable(
                        &mut target_abstract_environment,
                        self.gen_variable_location(target_expr.range()),
                        Arc::new(target_name),
                        type_expression.clone(),
                    );
                }
                AssignmentTarget::Attribute { .. } => todo!(),
                AssignmentTarget::Subscript { .. } => todo!(),
                AssignmentTarget::Starred(_) => todo!(),
                AssignmentTarget::Tuple(_) => todo!(),
                AssignmentTarget::List(_) => todo!(),
            }

            current_nodes.extend(
                target_abstract_environment
                    .current_nodes
                    .drain(|(_, guard)| match guard {
                        Guard::Raise { .. } => true,
                        _ => false,
                    })
                    .values,
            );
        }

        target_abstract_environment
            .current_nodes
            .extend(current_nodes.values);

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt_ann_assign(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt_ann_assign: &nodes::StmtAnnAssign,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let Ok(target) = AssignmentTarget::try_from(stmt_ann_assign.target.as_ref()) else {
            todo!("add the right error");
        };

        let Some(value) = &stmt_ann_assign.value else {
            return Ok(target_abstract_environment);
        };

        let type_expression = Arc::new(self.gen_expr(
            namespace,
            program_point,
            &mut target_abstract_environment,
            &value,
        )?);

        match target {
            AssignmentTarget::Name(target_name) => {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_variable_location(stmt_ann_assign.target.range()),
                    Arc::new(target_name),
                    type_expression.clone(),
                );
            }
            AssignmentTarget::Attribute { .. } => todo!(),
            AssignmentTarget::Subscript { .. } => todo!(),
            AssignmentTarget::Starred(_) => todo!("impossible"),
            AssignmentTarget::Tuple(_) => todo!("impossible"),
            AssignmentTarget::List(_) => todo!("impossible"),
        }

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt_while(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt_while: &nodes::StmtWhile,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let condition_expression = Arc::new(self.gen_expr(
            namespace,
            program_point,
            &mut target_abstract_environment,
            &stmt_while.test,
        )?);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_variable_location(stmt_while.range),
            &[
                Guard::IsTrue(condition_expression.clone()),
                Guard::IsFalse(condition_expression.clone()),
                Guard::Raise {
                    expression: condition_expression.clone(),
                    exception: None,
                },
            ],
        );

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt_if(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt_if: &nodes::StmtIf,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let condition_expression = Arc::new(self.gen_expr(
            namespace,
            program_point,
            &mut target_abstract_environment,
            &stmt_if.test,
        )?);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_variable_location(stmt_if.range),
            &[
                Guard::IsTrue(condition_expression.clone()),
                Guard::IsFalse(condition_expression.clone()),
                Guard::Raise {
                    expression: condition_expression.clone(),
                    exception: None,
                },
            ],
        );

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt: &nodes::Stmt,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        match stmt {
            nodes::Stmt::FunctionDef(stmt_function_def) => {
                self.gen_stmt_function_def(namespace, program_point, stmt_function_def)
            }
            nodes::Stmt::ClassDef(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Return(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Delete(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Assign(stmt_assign) => {
                self.gen_stmt_assign(namespace, program_point, stmt_assign)
            }
            nodes::Stmt::AugAssign(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::AnnAssign(stmt_ann_assign) => {
                self.gen_stmt_ann_assign(namespace, program_point, stmt_ann_assign)
            }
            nodes::Stmt::TypeAlias(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::For(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::While(stmt_while) => {
                self.gen_stmt_while(namespace, program_point, stmt_while)
            }
            nodes::Stmt::If(stmt_if) => self.gen_stmt_if(namespace, program_point, stmt_if),
            nodes::Stmt::With(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Match(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Raise(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Try(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Assert(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Import(stmt_import) => {
                self.gen_stmt_import(namespace, program_point, &stmt_import)
            }
            nodes::Stmt::ImportFrom(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Global(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Nonlocal(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Expr(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Pass(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Break(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::Continue(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::IpyEscapeCommand(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
        }
    }
}

impl GraphAnalyser for ConstraintsBuilder<'_> {
    type Node = ProgramPoint;
    type AbstractState = AbstractEnvironment;
    type AnalysisState = Namespace<AbstractEnvironment>;
    type Error = ConstraintsBuilderError;

    fn entry_node(&self) -> Result<ProgramPoint, Self::Error> {
        Ok(ProgramPoint::Entry)
    }
    fn next_nodes(
        &self,
        program_point: &ProgramPoint,
    ) -> Result<impl Iterator<Item = &ProgramPoint>, ConstraintsBuilderError> {
        match self.cfg.successors(program_point) {
            Some(successors) => Ok(successors),
            None => Err(ConstraintsBuilderError::InvalidProgramPoint {
                program_point: program_point.clone(),
            }),
        }
    }

    fn initialise_analysis_state(
        &self,
    ) -> Result<Namespace<AbstractEnvironment>, ConstraintsBuilderError> {
        Ok(Namespace::new())
    }

    fn analyse_node(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        if let Some(NodeData::Statement(statement_data)) = self.cfg.node_data(&program_point) {
            self.gen_stmt(namespace, program_point, statement_data.statement())
        } else {
            Ok(namespace.clone_abstract_environment_or_default(program_point))
        }
    }

    fn update_abstract_state(
        &self,
        _namespace: &Namespace<AbstractEnvironment>,
        from: ProgramPoint,
        to: ProgramPoint,
        abstract_environment: &AbstractEnvironment,
    ) -> Result<Option<AbstractEnvironment>, ConstraintsBuilderError> {
        let Some(edge_datas) = self.cfg.edge_data(from, to) else {
            return Ok(None);
        };

        let mut target_abstract_environment = abstract_environment.clone();

        target_abstract_environment.current_nodes = target_abstract_environment
            .current_nodes
            .iter()
            .filter(|(current_node, guard)| match guard {
                Guard::IsTrue(_) => edge_datas.contains(&EdgeData::Conditional(true)),
                Guard::IsFalse(_) => edge_datas.contains(&EdgeData::Conditional(false)),
                Guard::Succeed(_) => edge_datas.iter().any(|edge_data| match edge_data {
                    EdgeData::Unconditional
                    | EdgeData::Conditional(_)
                    | EdgeData::Match(_)
                    | EdgeData::Break
                    | EdgeData::Continue
                    | EdgeData::Return => true,
                    EdgeData::Exception(_, _) | EdgeData::UnhandledException => false,
                }),
                Guard::Raise { .. } => edge_datas.iter().any(|edge_data| match edge_data {
                    EdgeData::Unconditional
                    | EdgeData::Conditional(_)
                    | EdgeData::Match(_)
                    | EdgeData::Break
                    | EdgeData::Continue
                    | EdgeData::Return => false,
                    EdgeData::Exception(_, _) | EdgeData::UnhandledException => true,
                }),
                Guard::Multiple(guards) => {
                    if guards.is_empty() {
                        true
                    } else {
                        todo!("Handle multiple guards {}", guards);
                    }
                }
            })
            .cloned()
            .collect();

        if to == ProgramPoint::Exit {
            for (from, guard) in target_abstract_environment.current_nodes.as_ref() {
                match guard {
                    Guard::Raise { expression, .. }
                        if edge_datas.contains(&EdgeData::UnhandledException) =>
                    {
                        let unhandled_exception_constraint = ConstraintNode::Constraint(Arc::new(
                            Constraint::Exception(ConstraintDefinition::include(
                                ExceptionExpression::Type(expression.clone()),
                                ExceptionExpression::Raised(RaisedException {
                                    program_points: imbl::Vector::new(),
                                }),
                            )),
                        ));

                        target_abstract_environment.constraint_graph.add_edge(
                            from.clone(),
                            unhandled_exception_constraint.clone(),
                            guard.clone(),
                        );
                        target_abstract_environment.constraint_graph.add_edge(
                            unhandled_exception_constraint,
                            ConstraintNode::Exit,
                            Guard::default(),
                        );
                    }
                    _ => {
                        target_abstract_environment.constraint_graph.add_edge(
                            from.clone(),
                            ConstraintNode::Exit,
                            guard.clone(),
                        );
                    }
                }
            }
        }

        Ok(Some(target_abstract_environment))
    }

    fn get_abstract_state<'a>(
        &self,
        namespace: &'a Namespace<AbstractEnvironment>,
        program_point: &ProgramPoint,
    ) -> Result<Option<&'a AbstractEnvironment>, ConstraintsBuilderError> {
        Ok(namespace.abstract_environments.get(program_point))
    }

    fn set_abstract_state(
        &self,
        namespace: &mut Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        abstract_environment: AbstractEnvironment,
    ) -> Result<(), ConstraintsBuilderError> {
        namespace
            .abstract_environments
            .insert(program_point, abstract_environment);
        Ok(())
    }

    fn merge(
        &self,
        _namespace: &Namespace<AbstractEnvironment>,
        _program_point: ProgramPoint,
        left: &AbstractEnvironment,
        right: &AbstractEnvironment,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        Ok(left.join(right))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use apygen_analysis::analysis;
    use indoc::indoc;
    use rstest::rstest;
    use std::sync::mpsc;

    fn generate_constraints(source: &str) -> (Namespace<AbstractEnvironment>, Vec<String>) {
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let (import_tx, import_rx) = mpsc::channel::<ModuleName>();

        let constraints_builder = ConstraintsBuilder::new(&cfg, &import_tx);

        let namespace = analysis(&constraints_builder).expect("constraint builder should work");

        drop(import_tx);

        let imports = import_rx
            .iter()
            .map(|module_name| module_name.join())
            .collect::<Vec<_>>();

        (namespace, imports)
    }

    #[rstest]
    #[case::import(
        "import some_module",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ some_module@(1:7)";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@(1:7)" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec!["some_module"],
    )]
    #[case::import_as(
        "import some_module as mod",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ mod@(1:22)";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ mod@(1:22)" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ mod@(1:22)" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec!["some_module"],
    )]
    #[case::import_submodule(
        "import some_module.submodule",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ some_module@(1:7)";
            "#import(some_module.submodule) ⊑ (some_module@(1:7)).submodule";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@(1:7)" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#import(some_module.submodule) ⊑ (some_module@(1:7)).submodule" [label="#succeed(#import(some_module.submodule))"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module.submodule))"];
            "#import(some_module.submodule) ⊑ (some_module@(1:7)).submodule" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec!["some_module.submodule"],
    )]
    #[case::import_module_and_submodule(
        "import some_module, some_module.submodule",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ some_module@(1:7)";
            "#import(some_module) ⊑ some_module@(1:20)";
            "#import(some_module.submodule) ⊑ (some_module@(1:20)).submodule";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@(1:7)" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#import(some_module) ⊑ some_module@(1:20)" [label="#succeed(#import(some_module))"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@(1:20)" -> "#import(some_module.submodule) ⊑ (some_module@(1:20)).submodule" [label="#succeed(#import(some_module.submodule))"];
            "#import(some_module) ⊑ some_module@(1:20)" -> "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module.submodule))"];
            "#import(some_module.submodule) ⊑ (some_module@(1:20)).submodule" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec!["some_module", "some_module.submodule"],
    )]
    #[case::multiple_import(
        "import some_module, another_module",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(another_module) ⊑ another_module@(1:20)";
            "#import(some_module) ⊑ some_module@(1:7)";
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@(1:7)" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(another_module) ⊑ another_module@(1:20)" -> "#exit" [label="{}"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#import(another_module) ⊑ another_module@(1:20)" [label="#succeed(#import(another_module))"];
            "#import(some_module) ⊑ some_module@(1:7)" -> "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" [label="#raise(#import(another_module))"];
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec!["some_module", "another_module"],
    )]
    #[case::multiple_import_override(
        "import some_module as mod, another_module as mod",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(another_module) ⊑ mod@(1:45)";
            "#import(some_module) ⊑ mod@(1:22)";
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ mod@(1:22)" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(another_module) ⊑ mod@(1:45)" -> "#exit" [label="{}"];
            "#import(some_module) ⊑ mod@(1:22)" -> "#import(another_module) ⊑ mod@(1:45)" [label="#succeed(#import(another_module))"];
            "#import(some_module) ⊑ mod@(1:22)" -> "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" [label="#raise(#import(another_module))"];
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec!["some_module", "another_module"],
    )]
    #[case::int_constant_assignment(
        "a = 42",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "42 ⊑ a@(1:0)";
            "#exceptions(42) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "42 ⊑ a@(1:0)" [label="#succeed(42)"];
            "#entry" -> "#exceptions(42) ⊑ #raised_exceptions()" [label="#raise(42)"];
            "42 ⊑ a@(1:0)" -> "#exit" [label="{}"];
            "#exceptions(42) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::bigint_constant_assignment(
        "a = 4200000000000000000000000000",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "4200000000000000000000000000 ⊑ a@(1:0)";
            "#exceptions(4200000000000000000000000000) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "4200000000000000000000000000 ⊑ a@(1:0)" [label="#succeed(4200000000000000000000000000)"];
            "#entry" -> "#exceptions(4200000000000000000000000000) ⊑ #raised_exceptions()" [label="#raise(4200000000000000000000000000)"];
            "4200000000000000000000000000 ⊑ a@(1:0)" -> "#exit" [label="{}"];
            "#exceptions(4200000000000000000000000000) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::add_operation(
        "add = 42 + 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) + (67) ⊑ add@(1:0)";
            "#exceptions((42) + (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) + (67) ⊑ add@(1:0)" [label="#succeed((42) + (67))"];
            "#entry" -> "#exceptions((42) + (67)) ⊑ #raised_exceptions()" [label="#raise((42) + (67))"];
            "(42) + (67) ⊑ add@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) + (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::sub_operation(
        "sub = 42 - 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) - (67) ⊑ sub@(1:0)";
            "#exceptions((42) - (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) - (67) ⊑ sub@(1:0)" [label="#succeed((42) - (67))"];
            "#entry" -> "#exceptions((42) - (67)) ⊑ #raised_exceptions()" [label="#raise((42) - (67))"];
            "(42) - (67) ⊑ sub@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) - (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::mult_operation(
        "mult = 42 * 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) * (67) ⊑ mult@(1:0)";
            "#exceptions((42) * (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) * (67) ⊑ mult@(1:0)" [label="#succeed((42) * (67))"];
            "#entry" -> "#exceptions((42) * (67)) ⊑ #raised_exceptions()" [label="#raise((42) * (67))"];
            "(42) * (67) ⊑ mult@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) * (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::mat_mult_operation(
        "mat_mult = 42 @ 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) @ (67) ⊑ mat_mult@(1:0)";
            "#exceptions((42) @ (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) @ (67) ⊑ mat_mult@(1:0)" [label="#succeed((42) @ (67))"];
            "#entry" -> "#exceptions((42) @ (67)) ⊑ #raised_exceptions()" [label="#raise((42) @ (67))"];
            "(42) @ (67) ⊑ mat_mult@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) @ (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::div_operation(
        "div = 42 / 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) / (67) ⊑ div@(1:0)";
            "#exceptions((42) / (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) / (67) ⊑ div@(1:0)" [label="#succeed((42) / (67))"];
            "#entry" -> "#exceptions((42) / (67)) ⊑ #raised_exceptions()" [label="#raise((42) / (67))"];
            "(42) / (67) ⊑ div@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) / (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::floor_div_operation(
        "floor_div = 42 // 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) // (67) ⊑ floor_div@(1:0)";
            "#exceptions((42) // (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) // (67) ⊑ floor_div@(1:0)" [label="#succeed((42) // (67))"];
            "#entry" -> "#exceptions((42) // (67)) ⊑ #raised_exceptions()" [label="#raise((42) // (67))"];
            "(42) // (67) ⊑ floor_div@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) // (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::mod_operation(
        "mod = 42 % 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) % (67) ⊑ mod@(1:0)";
            "#exceptions((42) % (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) % (67) ⊑ mod@(1:0)" [label="#succeed((42) % (67))"];
            "#entry" -> "#exceptions((42) % (67)) ⊑ #raised_exceptions()" [label="#raise((42) % (67))"];
            "(42) % (67) ⊑ mod@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) % (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::pow_operation(
        "pow = 42 ** 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) ** (67) ⊑ pow@(1:0)";
            "#exceptions((42) ** (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) ** (67) ⊑ pow@(1:0)" [label="#succeed((42) ** (67))"];
            "#entry" -> "#exceptions((42) ** (67)) ⊑ #raised_exceptions()" [label="#raise((42) ** (67))"];
            "(42) ** (67) ⊑ pow@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) ** (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::shl_operation(
        "shl = 42 << 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) << (67) ⊑ shl@(1:0)";
            "#exceptions((42) << (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) << (67) ⊑ shl@(1:0)" [label="#succeed((42) << (67))"];
            "#entry" -> "#exceptions((42) << (67)) ⊑ #raised_exceptions()" [label="#raise((42) << (67))"];
            "(42) << (67) ⊑ shl@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) << (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::shr_operation(
        "shr = 42 >> 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) >> (67) ⊑ shr@(1:0)";
            "#exceptions((42) >> (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) >> (67) ⊑ shr@(1:0)" [label="#succeed((42) >> (67))"];
            "#entry" -> "#exceptions((42) >> (67)) ⊑ #raised_exceptions()" [label="#raise((42) >> (67))"];
            "(42) >> (67) ⊑ shr@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) >> (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::bit_or_operation(
        "bit_or = 42 | 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) | (67) ⊑ bit_or@(1:0)";
            "#exceptions((42) | (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) | (67) ⊑ bit_or@(1:0)" [label="#succeed((42) | (67))"];
            "#entry" -> "#exceptions((42) | (67)) ⊑ #raised_exceptions()" [label="#raise((42) | (67))"];
            "(42) | (67) ⊑ bit_or@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) | (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::bit_xor_operation(
        "bit_xor = 42 ^ 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) ^ (67) ⊑ bit_xor@(1:0)";
            "#exceptions((42) ^ (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) ^ (67) ⊑ bit_xor@(1:0)" [label="#succeed((42) ^ (67))"];
            "#entry" -> "#exceptions((42) ^ (67)) ⊑ #raised_exceptions()" [label="#raise((42) ^ (67))"];
            "(42) ^ (67) ⊑ bit_xor@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) ^ (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::bit_and_operation(
        "bit_and = 42 & 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) & (67) ⊑ bit_and@(1:0)";
            "#exceptions((42) & (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) & (67) ⊑ bit_and@(1:0)" [label="#succeed((42) & (67))"];
            "#entry" -> "#exceptions((42) & (67)) ⊑ #raised_exceptions()" [label="#raise((42) & (67))"];
            "(42) & (67) ⊑ bit_and@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) & (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::and_operation(
        "and_ = 42 and 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) and (67) ⊑ and_@(1:0)";
            "#exceptions((42) and (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) and (67) ⊑ and_@(1:0)" [label="#succeed((42) and (67))"];
            "#entry" -> "#exceptions((42) and (67)) ⊑ #raised_exceptions()" [label="#raise((42) and (67))"];
            "(42) and (67) ⊑ and_@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) and (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::or_operation(
        "or_ = 42 or 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) or (67) ⊑ or_@(1:0)";
            "#exceptions((42) or (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) or (67) ⊑ or_@(1:0)" [label="#succeed((42) or (67))"];
            "#entry" -> "#exceptions((42) or (67)) ⊑ #raised_exceptions()" [label="#raise((42) or (67))"];
            "(42) or (67) ⊑ or_@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) or (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::eq_operation(
        "eq = 42 == 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) == (67) ⊑ eq@(1:0)";
            "#exceptions((42) == (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) == (67) ⊑ eq@(1:0)" [label="#succeed((42) == (67))"];
            "#entry" -> "#exceptions((42) == (67)) ⊑ #raised_exceptions()" [label="#raise((42) == (67))"];
            "(42) == (67) ⊑ eq@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) == (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::not_eq_operation(
        "not_eq = 42 != 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) != (67) ⊑ not_eq@(1:0)";
            "#exceptions((42) != (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) != (67) ⊑ not_eq@(1:0)" [label="#succeed((42) != (67))"];
            "#entry" -> "#exceptions((42) != (67)) ⊑ #raised_exceptions()" [label="#raise((42) != (67))"];
            "(42) != (67) ⊑ not_eq@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) != (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::lt_operation(
        "lt = 42 < 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) < (67) ⊑ lt@(1:0)";
            "#exceptions((42) < (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) < (67) ⊑ lt@(1:0)" [label="#succeed((42) < (67))"];
            "#entry" -> "#exceptions((42) < (67)) ⊑ #raised_exceptions()" [label="#raise((42) < (67))"];
            "(42) < (67) ⊑ lt@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) < (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::gt_operation(
        "gt = 42 > 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) > (67) ⊑ gt@(1:0)";
            "#exceptions((42) > (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) > (67) ⊑ gt@(1:0)" [label="#succeed((42) > (67))"];
            "#entry" -> "#exceptions((42) > (67)) ⊑ #raised_exceptions()" [label="#raise((42) > (67))"];
            "(42) > (67) ⊑ gt@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) > (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::lte_operation(
        "lte = 42 <= 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) <= (67) ⊑ lte@(1:0)";
            "#exceptions((42) <= (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) <= (67) ⊑ lte@(1:0)" [label="#succeed((42) <= (67))"];
            "#entry" -> "#exceptions((42) <= (67)) ⊑ #raised_exceptions()" [label="#raise((42) <= (67))"];
            "(42) <= (67) ⊑ lte@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) <= (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::gte_operation(
        "gte = 42 >= 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) >= (67) ⊑ gte@(1:0)";
            "#exceptions((42) >= (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) >= (67) ⊑ gte@(1:0)" [label="#succeed((42) >= (67))"];
            "#entry" -> "#exceptions((42) >= (67)) ⊑ #raised_exceptions()" [label="#raise((42) >= (67))"];
            "(42) >= (67) ⊑ gte@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) >= (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::is_operation(
        "is_ = 42 is 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) is (67) ⊑ is_@(1:0)";
            "#exceptions((42) is (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) is (67) ⊑ is_@(1:0)" [label="#succeed((42) is (67))"];
            "#entry" -> "#exceptions((42) is (67)) ⊑ #raised_exceptions()" [label="#raise((42) is (67))"];
            "(42) is (67) ⊑ is_@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) is (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::is_not_operation(
        "is_not = 42 is not 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) is not (67) ⊑ is_not@(1:0)";
            "#exceptions((42) is not (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) is not (67) ⊑ is_not@(1:0)" [label="#succeed((42) is not (67))"];
            "#entry" -> "#exceptions((42) is not (67)) ⊑ #raised_exceptions()" [label="#raise((42) is not (67))"];
            "(42) is not (67) ⊑ is_not@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) is not (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::in_operation(
        "in_ = 42 in 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) in (67) ⊑ in_@(1:0)";
            "#exceptions((42) in (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) in (67) ⊑ in_@(1:0)" [label="#succeed((42) in (67))"];
            "#entry" -> "#exceptions((42) in (67)) ⊑ #raised_exceptions()" [label="#raise((42) in (67))"];
            "(42) in (67) ⊑ in_@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) in (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
    )]
    #[case::not_in_operation(
        "not_in = 42 not in 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) not in (67) ⊑ not_in@(1:0)";
            "#exceptions((42) not in (67)) ⊑ #raised_exceptions()";
            "#exit";
            "#entry" -> "(42) not in (67) ⊑ not_in@(1:0)" [label="#succeed((42) not in (67))"];
            "#entry" -> "#exceptions((42) not in (67)) ⊑ #raised_exceptions()" [label="#raise((42) not in (67))"];
            "(42) not in (67) ⊑ not_in@(1:0)" -> "#exit" [label="{}"];
            "#exceptions((42) not in (67)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
        }
        "##},
        vec![],
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
        digraph "Constraints" {
            "#entry";
            "a@(4:20) ⊑ a~(8:49)";
            "a@(6:37) ⊑ a~(8:49)";
            "a~(8:49) ⊑ b@(8:45)";
            "x@(1:0) ⊑ x~(3:13)";
            "42 ⊑ a@(4:20)";
            "67 ⊑ a@(6:37)";
            "True ⊑ x@(1:0)";
            "#exceptions(a~(8:49)) ⊑ #raised_exceptions()";
            "#exceptions(x~(3:13)) ⊑ #raised_exceptions()";
            "#exceptions(42) ⊑ #raised_exceptions()";
            "#exceptions(67) ⊑ #raised_exceptions()";
            "#exceptions(True) ⊑ #raised_exceptions()";
            "#empty(3:10)";
            "#empty(4:20)";
            "#empty(6:37)";
            "#exit";
            "#entry" -> "True ⊑ x@(1:0)" [label="#succeed(True)"];
            "#entry" -> "#exceptions(True) ⊑ #raised_exceptions()" [label="#raise(True)"];
            "a@(4:20) ⊑ a~(8:49)" -> "a~(8:49) ⊑ b@(8:45)" [label="#succeed(a~(8:49))"];
            "a@(4:20) ⊑ a~(8:49)" -> "#exceptions(a~(8:49)) ⊑ #raised_exceptions()" [label="#raise(a~(8:49))"];
            "a@(6:37) ⊑ a~(8:49)" -> "a~(8:49) ⊑ b@(8:45)" [label="#succeed(a~(8:49))"];
            "a@(6:37) ⊑ a~(8:49)" -> "#exceptions(a~(8:49)) ⊑ #raised_exceptions()" [label="#raise(a~(8:49))"];
            "a~(8:49) ⊑ b@(8:45)" -> "#exit" [label="{}"];
            "x@(1:0) ⊑ x~(3:13)" -> "#empty(3:10)" [label="{}"];
            "42 ⊑ a@(4:20)" -> "a@(4:20) ⊑ a~(8:49)" [label="{}"];
            "42 ⊑ a@(4:20)" -> "a@(6:37) ⊑ a~(8:49)" [label="{}"];
            "42 ⊑ a@(4:20)" -> "#exit" [label="{}"];
            "67 ⊑ a@(6:37)" -> "a@(4:20) ⊑ a~(8:49)" [label="{}"];
            "67 ⊑ a@(6:37)" -> "a@(6:37) ⊑ a~(8:49)" [label="{}"];
            "67 ⊑ a@(6:37)" -> "#exit" [label="{}"];
            "True ⊑ x@(1:0)" -> "x@(1:0) ⊑ x~(3:13)" [label="{}"];
            "True ⊑ x@(1:0)" -> "#exit" [label="{}"];
            "#exceptions(a~(8:49)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(x~(3:13)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(42) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(67) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(True) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#empty(3:10)" -> "#exceptions(x~(3:13)) ⊑ #raised_exceptions()" [label="#raise(x~(3:13))"];
            "#empty(3:10)" -> "#empty(4:20)" [label="#is_true(x~(3:13))"];
            "#empty(3:10)" -> "#empty(6:37)" [label="#is_false(x~(3:13))"];
            "#empty(4:20)" -> "42 ⊑ a@(4:20)" [label="#succeed(42)"];
            "#empty(4:20)" -> "#exceptions(42) ⊑ #raised_exceptions()" [label="#raise(42)"];
            "#empty(6:37)" -> "67 ⊑ a@(6:37)" [label="#succeed(67)"];
            "#empty(6:37)" -> "#exceptions(67) ⊑ #raised_exceptions()" [label="#raise(67)"];
        }
        "##},
        vec![],
    )]
    #[case::simple_while_statement(
        indoc! {r##"
        a = 0

        while a < 5:
            a = a + 1

        b = a
        "##},
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "a@(1:0) ⊑ a~(3:13)";
            "a@(1:0) ⊑ a~(4:28)";
            "a@(1:0) ⊑ a~(6:39)";
            "a@(4:24) ⊑ a~(3:13)";
            "a@(4:24) ⊑ a~(4:28)";
            "a@(4:24) ⊑ a~(6:39)";
            "a~(6:39) ⊑ b@(6:35)";
            "(a~(4:28)) + (1) ⊑ a@(4:24)";
            "0 ⊑ a@(1:0)";
            "#exceptions(a~(6:39)) ⊑ #raised_exceptions()";
            "#exceptions((a~(3:13)) < (5)) ⊑ #raised_exceptions()";
            "#exceptions((a~(4:28)) + (1)) ⊑ #raised_exceptions()";
            "#exceptions(0) ⊑ #raised_exceptions()";
            "#empty(3:7)";
            "#exit";
            "#entry" -> "0 ⊑ a@(1:0)" [label="#succeed(0)"];
            "#entry" -> "#exceptions(0) ⊑ #raised_exceptions()" [label="#raise(0)"];
            "a@(1:0) ⊑ a~(3:13)" -> "#empty(3:7)" [label="{}"];
            "a@(1:0) ⊑ a~(4:28)" -> "(a~(4:28)) + (1) ⊑ a@(4:24)" [label="#succeed((a~(4:28)) + (1))"];
            "a@(1:0) ⊑ a~(4:28)" -> "#exceptions((a~(4:28)) + (1)) ⊑ #raised_exceptions()" [label="#raise((a~(4:28)) + (1))"];
            "a@(1:0) ⊑ a~(6:39)" -> "a~(6:39) ⊑ b@(6:35)" [label="#succeed(a~(6:39))"];
            "a@(1:0) ⊑ a~(6:39)" -> "#exceptions(a~(6:39)) ⊑ #raised_exceptions()" [label="#raise(a~(6:39))"];
            "a@(4:24) ⊑ a~(3:13)" -> "#empty(3:7)" [label="{}"];
            "a@(4:24) ⊑ a~(4:28)" -> "(a~(4:28)) + (1) ⊑ a@(4:24)" [label="#succeed((a~(4:28)) + (1))"];
            "a@(4:24) ⊑ a~(4:28)" -> "#exceptions((a~(4:28)) + (1)) ⊑ #raised_exceptions()" [label="#raise((a~(4:28)) + (1))"];
            "a@(4:24) ⊑ a~(6:39)" -> "a~(6:39) ⊑ b@(6:35)" [label="#succeed(a~(6:39))"];
            "a@(4:24) ⊑ a~(6:39)" -> "#exceptions(a~(6:39)) ⊑ #raised_exceptions()" [label="#raise(a~(6:39))"];
            "a~(6:39) ⊑ b@(6:35)" -> "#exit" [label="{}"];
            "(a~(4:28)) + (1) ⊑ a@(4:24)" -> "a@(1:0) ⊑ a~(3:13)" [label="{}"];
            "(a~(4:28)) + (1) ⊑ a@(4:24)" -> "a@(4:24) ⊑ a~(3:13)" [label="{}"];
            "(a~(4:28)) + (1) ⊑ a@(4:24)" -> "#exit" [label="{}"];
            "0 ⊑ a@(1:0)" -> "a@(1:0) ⊑ a~(3:13)" [label="{}"];
            "0 ⊑ a@(1:0)" -> "a@(4:24) ⊑ a~(3:13)" [label="{}"];
            "0 ⊑ a@(1:0)" -> "#exit" [label="{}"];
            "#exceptions(a~(6:39)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions((a~(3:13)) < (5)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions((a~(4:28)) + (1)) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#exceptions(0) ⊑ #raised_exceptions()" -> "#exit" [label="{}"];
            "#empty(3:7)" -> "a@(1:0) ⊑ a~(4:28)" [label="#is_true((a~(3:13)) < (5))"];
            "#empty(3:7)" -> "a@(1:0) ⊑ a~(6:39)" [label="#is_false((a~(3:13)) < (5))"];
            "#empty(3:7)" -> "a@(4:24) ⊑ a~(4:28)" [label="#is_true((a~(3:13)) < (5))"];
            "#empty(3:7)" -> "a@(4:24) ⊑ a~(6:39)" [label="#is_false((a~(3:13)) < (5))"];
            "#empty(3:7)" -> "#exceptions((a~(3:13)) < (5)) ⊑ #raised_exceptions()" [label="#raise((a~(3:13)) < (5))"];
        }
        "##},
        vec![],
    )]
    fn test_constraints_generation(
        #[case] source: &str,
        #[case] expected_dot: &str,
        #[case] expected_imports: Vec<&str>,
    ) {
        let (namespace, actual_imports) = generate_constraints(&source);
        let actual_dot = namespace.abstract_environments[&ProgramPoint::Exit]
            .constraint_graph
            .dot();

        assert_eq!(expected_dot, actual_dot,);
        assert_eq!(expected_imports, actual_imports);
    }
}
