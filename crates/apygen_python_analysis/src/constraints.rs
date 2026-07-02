use crate::abstract_environment::{
    BUILTINS_MODULE, LiteralBoolean, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInteger,
    LiteralString,
};
use crate::genkill::assignment::AssignmentTarget;
use crate::worklist::load_cfg;
use apy::OneOrMany;
use apy::v1::{GenericKind, Identifier, ParameterKind, QualifiedName};
use apygen_analysis::cfg::nodes::Number;
use apygen_analysis::cfg::{Cfg, EdgeData, NodeData, ProgramPoint, Ranged, TextRange, nodes};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::{GraphAnalyser, analysis};
use apygen_finder::filesystem::Filesystem;
use apygen_finder::pathfinder::FinderSpec;
use imbl::ordmap::Entry;
use num_bigint::BigInt;
use num_complex::Complex64;
use num_traits::Num;
use rayon::iter::ParallelBridge;
use rayon::iter::ParallelIterator;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;
use std::sync::Arc;
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
    pub fn unit(key: K, value: V) -> Self {
        Self::new(imbl::OrdMap::unit(key, value))
    }

    pub fn new(values: imbl::OrdMap<K, V>) -> Self {
        Self { values }
    }
}

impl<K: Clone + Ord, V: Clone> LatticeMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.values.insert(key, value)
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.values.remove(key)
    }

    pub fn drain(&mut self, f: impl Fn(&(K, V)) -> bool) -> Self {
        let mut drained = Self::default();

        self.values = self
            .values
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

    pub fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        self.values.extend(iter);
    }

    pub fn update(&self, key: K, value: V) -> Self {
        Self::new(self.values.update(key, value))
    }

    pub fn union(self, other: Self) -> Self {
        Self::new(self.values.union(other.values))
    }
}

impl<K: Clone + Ord, V: Clone + Lattice> LatticeMap<K, V> {
    pub fn update_join(self, key: K, value: V) -> Self {
        Self::new(
            self.values
                .update_with(key, value, |self_value, other_value| {
                    self_value.join(&other_value)
                }),
        )
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

impl<K: Ord, V> Deref for LatticeMap<K, V> {
    type Target = imbl::OrdMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<K: Ord, V> AsRef<imbl::OrdMap<K, V>> for LatticeMap<K, V> {
    fn as_ref(&self) -> &imbl::OrdMap<K, V> {
        &self.values
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
pub struct Location {
    pub line: usize,
    pub offset: usize,
}

impl Location {
    pub fn new(line: usize, offset: usize) -> Self {
        Self { line, offset }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.offset)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QualifiedLocation {
    pub module_name: ModuleName,
    pub locations: imbl::Vector<Location>,
}

impl QualifiedLocation {
    pub fn new(module_name: ModuleName, locations: imbl::Vector<Location>) -> Self {
        Self {
            module_name,
            locations,
        }
    }

    pub fn at_sublocation(&self, location: Location) -> Self {
        let mut locations = self.locations.clone();
        locations.push_back(location);
        Self::new(self.module_name.clone(), locations)
    }
}

impl Display for QualifiedLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.module_name)?;
        if !self.locations.is_empty() {
            for location in &self.locations {
                write!(f, "[{}]", location)?;
            }
        }
        Ok(())
    }
}

impl From<ModuleName> for QualifiedLocation {
    fn from(module_name: ModuleName) -> Self {
        Self::new(module_name, imbl::Vector::new())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionVariable {
    pub name: VariableName,
    pub location: QualifiedLocation,
}

impl ExpressionVariable {
    pub fn new(name: VariableName, location: QualifiedLocation) -> Self {
        Self { name, location }
    }
}

impl Display for ExpressionVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{{{}}}", self.name, self.location)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionOverride {
    pub previous: Arc<TypeExpression>,
    pub new: Arc<TypeExpression>,
}

impl ExpressionOverride {
    pub fn new(previous: Arc<TypeExpression>, new: Arc<TypeExpression>) -> Self {
        Self { previous, new }
    }
}

impl Display for ExpressionOverride {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#override(previous={}, new={})", self.previous, self.new)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionFunction {
    pub location: QualifiedLocation,

    pub is_async: bool,
}

impl ExpressionFunction {
    pub fn new(location: QualifiedLocation, is_async: bool) -> Self {
        Self { location, is_async }
    }
}

impl Display for ExpressionFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#function(location={}, async={})",
            self.location, self.is_async
        )
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
pub struct ExpressionImportFrom {
    pub module: ModuleName,
    pub attribute: VariableName,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryOperator {
    Invert,
    Not,
    UAdd,
    USub,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            UnaryOperator::Invert => "@",
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
    Override(ExpressionOverride),
    Function(ExpressionFunction),
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

impl TypeExpression {
    pub fn is_constant(&self) -> bool {
        matches!(
            self,
            TypeExpression::LiteralInteger(_)
                | TypeExpression::LiteralFloat(_)
                | TypeExpression::LiteralComplex(_)
                | TypeExpression::LiteralString(_)
                | TypeExpression::LiteralBytes(_)
                | TypeExpression::LiteralBoolean(_)
                | TypeExpression::LiteralNone
                | TypeExpression::LiteralEllipsis
        )
    }
}

impl Display for TypeExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpression::Variable(expression_variable) => write!(f, "{}", expression_variable),
            TypeExpression::Override(expression_override) => write!(f, "{}", expression_override),
            TypeExpression::Function(expression_function) => write!(f, "{}", expression_function),
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
pub struct IncludeConstraintDefinition<T> {
    pub left: Arc<T>,
    pub right: Arc<T>,
}

impl<T: Clone> IncludeConstraintDefinition<T> {
    pub fn new(left: Arc<T>, right: Arc<T>) -> Self {
        Self { left, right }
    }
}

impl<T: Display> Display for IncludeConstraintDefinition<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ⊑ {}", self.left, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IncludeConstraint {
    Type(IncludeConstraintDefinition<TypeExpression>),
    Exception(IncludeConstraintDefinition<ExceptionExpression>),
}

impl Display for IncludeConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            IncludeConstraint::Type(constraint_type) => write!(f, "{}", constraint_type),
            IncludeConstraint::Exception(constraint_exception) => {
                write!(f, "{}", constraint_exception)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstraintNode {
    Entry,
    Constraint(Arc<IncludeConstraint>),
    Empty(QualifiedLocation),
    TypeExit,
    ExceptionExit,
    Exit,
}

impl Display for ConstraintNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintNode::Entry => write!(f, "#entry"),
            ConstraintNode::Constraint(constraint) => write!(f, "{}", constraint),
            ConstraintNode::Empty(location) => write!(f, "#empty({})", location),
            ConstraintNode::TypeExit => write!(f, "#type_exit"),
            ConstraintNode::ExceptionExit => write!(f, "#exception_exit"),
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

    pub fn exists(&self, from: &ConstraintNode, to: &ConstraintNode) -> bool {
        self.edges.get(from).and_then(|tos| tos.get(to)).is_some()
    }

    pub fn dot(&self, graph_name: &str) -> String {
        let mut nodes: imbl::OrdSet<ConstraintNode> = imbl::OrdSet::new();
        let mut edges: imbl::OrdMap<(ConstraintNode, ConstraintNode), Guard> = imbl::OrdMap::new();
        for (from, tos) in &self.edges.values {
            for (to, guard) in &tos.values {
                nodes.insert(from.clone());
                nodes.insert(to.clone());
                edges.insert((from.clone(), to.clone()), guard.clone());
            }
        }

        let mut dot_representation = String::from("digraph \"");
        dot_representation.push_str(graph_name);
        dot_representation.push_str("\" {\n");
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

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbstractEnvironmentSpecification {
    pub arguments: LatticeMap<ExpressionVariable, LatticeSet<TypeExpression>>,
    pub return_type: LatticeSet<TypeExpression>,
    pub exceptions: LatticeSet<ExceptionExpression>,
}

impl Lattice for AbstractEnvironmentSpecification {
    fn includes(&self, other: &Self) -> bool {
        self.arguments.includes(&other.arguments)
            && self.return_type.includes(&other.return_type)
            && self.exceptions.includes(&other.exceptions)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            arguments: self.arguments.join(&other.arguments),
            return_type: self.return_type.join(&other.return_type),
            exceptions: self.exceptions.join(&other.exceptions),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntity {
    pub location: QualifiedLocation,
    pub program_point: ProgramPoint,
    pub kind: ProgramEntityKind,
}

impl ProgramEntity {
    pub fn new(
        location: QualifiedLocation,
        program_point: ProgramPoint,
        kind: ProgramEntityKind,
    ) -> Self {
        Self {
            location,
            program_point,
            kind,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SubProgramEntityContext {
    pub specification: AbstractEnvironmentSpecification,
    pub variable_locations: LatticeMap<VariableName, LatticeSet<QualifiedLocation>>,
}

impl SubProgramEntityContext {
    pub fn new(
        specification: AbstractEnvironmentSpecification,
        variable_locations: LatticeMap<VariableName, LatticeSet<QualifiedLocation>>,
    ) -> Self {
        Self {
            specification,
            variable_locations,
        }
    }
}

impl Lattice for SubProgramEntityContext {
    fn includes(&self, other: &Self) -> bool {
        self.specification.includes(&other.specification)
            && self.variable_locations.includes(&other.variable_locations)
    }

    fn join(&self, other: &Self) -> Self {
        Self::new(
            self.specification.join(&other.specification),
            self.variable_locations.join(&other.variable_locations),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityAbstractEnvironment {
    pub specification: AbstractEnvironmentSpecification,
    pub current_nodes: LatticeMap<ConstraintNode, Guard>,
    pub variable_locations: LatticeMap<VariableName, LatticeSet<QualifiedLocation>>,
    pub constraint_graph: ConstraintGraph,
    pub imports: LatticeSet<ModuleName>,
    pub sub_program_entities: LatticeMap<ProgramEntity, SubProgramEntityContext>,
}

impl Default for ProgramEntityAbstractEnvironment {
    fn default() -> Self {
        Self {
            specification: AbstractEnvironmentSpecification::default(),
            current_nodes: LatticeMap::unit(
                ConstraintNode::Entry,
                Guard::Multiple(LatticeSet::default()),
            ),
            variable_locations: LatticeMap::default(),
            constraint_graph: ConstraintGraph::default(),
            imports: LatticeSet::default(),
            sub_program_entities: LatticeMap::default(),
        }
    }
}

impl Lattice for ProgramEntityAbstractEnvironment {
    fn includes(&self, other: &Self) -> bool {
        self.specification.includes(&other.specification)
            && self.current_nodes.includes(&other.current_nodes)
            && self.variable_locations.includes(&other.variable_locations)
            && self.constraint_graph.includes(&other.constraint_graph)
            && self.imports.includes(&other.imports)
            && self
                .sub_program_entities
                .includes(&other.sub_program_entities)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            specification: self.specification.join(&other.specification),
            current_nodes: self.current_nodes.join(&other.current_nodes),
            variable_locations: self.variable_locations.join(&other.variable_locations),
            constraint_graph: self.constraint_graph.join(&other.constraint_graph),
            imports: self.imports.join(&other.imports),
            sub_program_entities: self.sub_program_entities.join(&other.sub_program_entities),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityAnalysisState {
    pub abstract_states: LatticeMap<ProgramPoint, ProgramEntityAbstractEnvironment>,
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

impl Lattice for ProgramEntityAnalysisState {
    fn includes(&self, other: &Self) -> bool {
        self.abstract_states.includes(&other.abstract_states)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            abstract_states: self.abstract_states.join(&other.abstract_states),
        }
    }
}

impl Display for ProgramEntityAnalysisState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.abstract_states.fmt(f)
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UsedVariables {
    pub names: LatticeMap<VariableName, LatticeSet<QualifiedLocation>>,
}

impl UsedVariables {
    pub fn new(names: LatticeMap<VariableName, LatticeSet<QualifiedLocation>>) -> Self {
        Self { names }
    }

    pub fn consume<T>(&mut self, eval: ExpressionEval<T>) -> T {
        self.names = self.names.join(&eval.variables.names);
        eval.value
    }
}

impl Lattice for UsedVariables {
    fn includes(&self, other: &Self) -> bool {
        self.names.includes(&other.names)
    }

    fn join(&self, other: &Self) -> Self {
        Self::new(self.names.join(&other.names))
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
    #[error("program point `{program_point}` is invalid")]
    InvalidProgramPoint { program_point: ProgramPoint },
    #[error("invalid bool expression `{expr:?}`")]
    InvalidExprBoolOp { expr: nodes::ExprBoolOp },
    #[error("invalid compare expression `{expr:?}`")]
    InvalidExprCompare { expr: nodes::ExprCompare },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProgramEntityKind {
    Module,
    Class,
    Function,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityAbstractParentState<'a> {
    pub state: &'a ProgramEntityAbstractEnvironment,
    pub kind: ProgramEntityKind,
    pub parent: Option<&'a ProgramEntityAbstractParentState<'a>>,
}

impl<'a> ProgramEntityAbstractParentState<'a> {
    pub fn new(
        state: &'a ProgramEntityAbstractEnvironment,
        kind: ProgramEntityKind,
        parent: Option<&'a ProgramEntityAbstractParentState<'a>>,
    ) -> Self {
        Self {
            state,
            kind,
            parent,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ConstraintsBuilder<'a> {
    pub cfg: &'a Cfg,
    pub entity: &'a ProgramEntity,
    pub abstract_parent_state: Option<&'a ProgramEntityAbstractParentState<'a>>,
}

impl<'a> ConstraintsBuilder<'a> {
    pub fn new(
        cfg: &'a Cfg,
        entity: &'a ProgramEntity,
        abstract_parent_state: Option<&'a ProgramEntityAbstractParentState<'a>>,
    ) -> ConstraintsBuilder<'a> {
        ConstraintsBuilder {
            cfg,
            entity,
            abstract_parent_state,
        }
    }

    pub fn filter_guard(&self, edge_datas: &HashSet<EdgeData>, guard: &Guard) -> Option<Guard> {
        let guard_is_matching = match guard {
            Guard::IsTrue(_) => edge_datas.contains(&EdgeData::Conditional(true)),
            Guard::IsFalse(_) => edge_datas.contains(&EdgeData::Conditional(false)),
            Guard::Succeed(_) => edge_datas
                .iter()
                .any(|edge_data| edge_data.is_normal_flow()),
            Guard::Raise { .. } => edge_datas
                .iter()
                .any(|edge_data| edge_data.is_exception_flow()),
            Guard::Multiple(guards) => {
                return if guards.is_empty() {
                    Some(guard.clone())
                } else {
                    let mut new_guards: LatticeSet<_> = guards
                        .iter()
                        .filter_map(|guard| self.filter_guard(edge_datas, guard))
                        .collect();

                    if new_guards.len() == 1 {
                        Some(
                            new_guards
                                .values
                                .remove_min()
                                .expect("new_guards is not empty"),
                        )
                    } else {
                        Some(Guard::Multiple(new_guards))
                    }
                };
            }
        };

        if guard_is_matching {
            Some(guard.clone())
        } else {
            None
        }
    }

    pub fn create_used_variables_constraints(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        used_variables: UsedVariables,
    ) {
        if used_variables.names.is_empty() {
            return;
        }

        let mut current_nodes: LatticeMap<ConstraintNode, Guard> = LatticeMap::default();

        for (used_variable_name, used_locations) in used_variables.names.as_ref() {
            if let Some(previous_locations) = abstract_environment
                .variable_locations
                .get(used_variable_name)
            {
                for previous_location in previous_locations.as_ref() {
                    for used_location in used_locations.as_ref() {
                        let node = ConstraintNode::Constraint(Arc::new(IncludeConstraint::Type(
                            IncludeConstraintDefinition::new(
                                Arc::new(TypeExpression::Variable(ExpressionVariable::new(
                                    used_variable_name.clone(),
                                    previous_location.clone(),
                                ))),
                                Arc::new(TypeExpression::Variable(ExpressionVariable::new(
                                    used_variable_name.clone(),
                                    used_location.clone(),
                                ))),
                            ),
                        )));
                        for (current_node, guard) in abstract_environment.current_nodes.as_ref() {
                            abstract_environment.constraint_graph.add_edge(
                                current_node.clone(),
                                node.clone(),
                                guard.clone(),
                            );
                        }
                        current_nodes.insert(node, Guard::default());
                    }
                }
                abstract_environment
                    .variable_locations
                    .insert(used_variable_name.clone(), used_locations.clone());
            }
        }

        abstract_environment.current_nodes = current_nodes;
    }

    pub fn create_include_constraint(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: QualifiedLocation,
        left: Arc<TypeExpression>,
        right: Arc<TypeExpression>,
    ) {
        let node = ConstraintNode::Constraint(Arc::new(IncludeConstraint::Type(
            IncludeConstraintDefinition::new(left.clone(), right.clone()),
        )));

        let mut current_nodes = LatticeMap::unit(node.clone(), Guard::default());

        if left.is_constant() {
            for (from, guard) in abstract_environment.current_nodes.as_ref() {
                abstract_environment.constraint_graph.add_edge(
                    from.clone(),
                    node.clone(),
                    guard.clone(),
                );
            }

            abstract_environment.current_nodes = current_nodes;
            return;
        }

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
            current_nodes = current_nodes.update_join(
                from.clone(),
                Guard::Raise {
                    expression: left.clone(),
                    exception: None,
                },
            );
        }

        abstract_environment.current_nodes = current_nodes;
    }

    pub fn assign_variable(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: QualifiedLocation,
        variable: VariableName,
        type_expression: Arc<TypeExpression>,
    ) {
        self.create_include_constraint(
            abstract_environment,
            location.clone(),
            type_expression,
            Arc::new(TypeExpression::Variable(ExpressionVariable::new(
                variable.clone(),
                location.clone(),
            ))),
        );

        abstract_environment
            .variable_locations
            .values
            .insert(variable, LatticeSet::unit(location));
    }

    pub fn assign_empty_constraint(
        &self,
        abstract_environment: &mut ProgramEntityAbstractEnvironment,
        location: QualifiedLocation,
        guards: LatticeSet<Guard>,
    ) {
        let node = ConstraintNode::Empty(location);

        for (from, guard) in abstract_environment.current_nodes.as_ref() {
            abstract_environment.constraint_graph.add_edge(
                from.clone(),
                node.clone(),
                guard.clone(),
            );
        }

        abstract_environment.current_nodes = LatticeMap::unit(node, Guard::Multiple(guards));
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

    pub fn gen_location(&self, range: TextRange) -> Location {
        let range_offset = range.start();
        let line = self.cfg.line_index.line_index(range_offset).get();
        let line_offset = self.cfg.line_index.line_starts()[line - 1];
        let offset = range_offset - line_offset;
        Location::new(line, offset.to_usize())
    }

    pub fn gen_qualified_location(&self, range: TextRange) -> QualifiedLocation {
        self.entity
            .location
            .at_sublocation(self.gen_location(range))
    }

    pub fn evaluate_parameter(
        &self,
        program_point: ProgramPoint,
        parameter: &nodes::Parameter,
    ) -> Result<(ExpressionVariable, Option<ExpressionEval<TypeExpression>>), ConstraintsBuilderError>
    {
        let parameter_name = self.gen_variable_name(program_point, &parameter.name)?;

        if let Some(annotation) = &parameter.annotation {
            // TODO: add support for annotations
        }

        Ok((
            ExpressionVariable::new(parameter_name, self.gen_qualified_location(parameter.range)),
            None,
        ))
    }

    pub fn evaluate_parameter_with_default(
        &self,
        program_point: ProgramPoint,
        parameter_with_default: &nodes::ParameterWithDefault,
    ) -> Result<(ExpressionVariable, Option<ExpressionEval<TypeExpression>>), ConstraintsBuilderError>
    {
        let (parameter_name, annotation_eval_option) =
            self.evaluate_parameter(program_point, &parameter_with_default.parameter)?;

        let parameter_eval_option = if let Some(default) = &parameter_with_default.default {
            let default_eval = self.evaluate_expr(
                &ProgramEntityAnalysisState::default(),
                program_point,
                &default,
            )?;

            if let Some(annotation_eval) = annotation_eval_option {
                Some(annotation_eval.merge(default_eval, |annotation, default| {
                    TypeExpression::Override(ExpressionOverride::new(
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
        program_point: ProgramPoint,
        parameters: &nodes::Parameters,
    ) -> Result<
        ExpressionEval<LatticeMap<ExpressionVariable, LatticeSet<TypeExpression>>>,
        ConstraintsBuilderError,
    > {
        let positional_only_parameters = parameters
            .posonlyargs
            .iter()
            .map(|parameter| self.evaluate_parameter_with_default(program_point, &parameter));
        let positional_or_keyword_parameters = parameters
            .args
            .iter()
            .map(|parameter| self.evaluate_parameter(program_point, &parameter.parameter));
        let var_positional_parameters = parameters
            .vararg
            .iter()
            .map(|parameter| self.evaluate_parameter(program_point, &parameter));
        let keyword_only_parameters = parameters
            .kwonlyargs
            .iter()
            .map(|parameter| self.evaluate_parameter_with_default(program_point, &parameter));
        let var_keyword_parameters = parameters
            .kwarg
            .iter()
            .map(|parameter| self.evaluate_parameter(program_point, &parameter));

        let parameter_evals = positional_only_parameters
            .chain(positional_or_keyword_parameters)
            .chain(var_positional_parameters)
            .chain(keyword_only_parameters)
            .chain(var_keyword_parameters)
            .collect::<Result<Vec<(ExpressionVariable, Option<ExpressionEval<TypeExpression>>)>, _>>()?;

        let mut used_variables = UsedVariables::default();

        let mut arguments = LatticeMap::default();

        for (variable_name, parameter_eval_option) in parameter_evals {
            let parameter_type_expression = if let Some(parameter_eval) = parameter_eval_option {
                LatticeSet::unit(used_variables.consume(parameter_eval))
            } else {
                LatticeSet::default()
            };
            arguments = arguments.update_join(variable_name, parameter_type_expression);
        }

        Ok(ExpressionEval::new(arguments, used_variables))
    }

    pub fn evaluate_expr_bool_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr_bool_op: &nodes::ExprBoolOp,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let mut values_iter = expr_bool_op.values.iter();

        let mut eval = match values_iter.next() {
            Some(value) => self.evaluate_expr(namespace, program_point, value)?,
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
            eval = eval.merge(
                self.evaluate_expr(namespace, program_point, &value)?,
                |left, right| {
                    TypeExpression::Binary(ExpressionBinary {
                        left: Arc::new(left),
                        operator: operator.clone(),
                        right: Arc::new(right),
                    })
                },
            )
        }

        Ok(eval)
    }

    pub fn evaluate_expr_bin_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr_bin_op: &nodes::ExprBinOp,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let left_eval = self.evaluate_expr(namespace, program_point, &expr_bin_op.left)?;
        let right_eval = self.evaluate_expr(namespace, program_point, &expr_bin_op.right)?;

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

        Ok(left_eval.merge(right_eval, |left, right| {
            TypeExpression::Binary(ExpressionBinary {
                left: Arc::new(left),
                operator,
                right: Arc::new(right),
            })
        }))
    }

    pub fn evaluate_expr_unary_op(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr_unary_op: &nodes::ExprUnaryOp,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let operand_eval = self.evaluate_expr(namespace, program_point, &expr_unary_op.operand)?;

        let operator = match expr_unary_op.op {
            nodes::UnaryOp::Invert => UnaryOperator::Invert,
            nodes::UnaryOp::Not => UnaryOperator::Not,
            nodes::UnaryOp::UAdd => UnaryOperator::UAdd,
            nodes::UnaryOp::USub => UnaryOperator::USub,
        };

        Ok(operand_eval.map(|operand| {
            TypeExpression::Unary(ExpressionUnary {
                operator,
                operand: Arc::new(operand),
            })
        }))
    }

    pub fn evaluate_expr_compare(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr_compare: &nodes::ExprCompare,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let mut eval = self.evaluate_expr(namespace, program_point, &expr_compare.left)?;

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

            let comparator = self.evaluate_expr(namespace, program_point, comparator)?;

            eval = eval.merge(comparator, |left, right| {
                TypeExpression::Binary(ExpressionBinary {
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
        program_point: ProgramPoint,
        expr_call: &nodes::ExprCall,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let mut func_eval = self.evaluate_expr(namespace, program_point, &expr_call.func)?;

        let mut positional_arguments: imbl::Vector<Arc<TypeExpression>> = imbl::Vector::new();
        for positional_argument in &expr_call.arguments.args {
            positional_arguments.push_back(Arc::new(
                func_eval.variables.consume(self.evaluate_expr(
                    namespace,
                    program_point,
                    &positional_argument,
                )?),
            ));
        }

        let mut keyword_arguments: imbl::Vector<KeywordArgument> = imbl::Vector::new();
        for keyword_argument in &expr_call.arguments.keywords {
            let keyword_name = match &keyword_argument.arg {
                Some(identifier) => Some(self.gen_variable_name(program_point, &identifier)?),
                None => None,
            };
            keyword_arguments.push_back(KeywordArgument {
                name: keyword_name,
                value: Arc::new(func_eval.variables.consume(self.evaluate_expr(
                    namespace,
                    program_point,
                    &keyword_argument.value,
                )?)),
            });
        }

        Ok(func_eval.map(|func| {
            TypeExpression::Call(ExpressionCall {
                target: Arc::new(func),
                positional_arguments,
                keyword_arguments,
            })
        }))
    }

    pub fn evaluate_expr_string_literal(
        &self,
        expr_string_literal: &nodes::ExprStringLiteral,
    ) -> TypeExpression {
        TypeExpression::LiteralString(LiteralString {
            value: Arc::new(expr_string_literal.value.to_str().to_owned()),
        })
    }

    pub fn evaluate_expr_bytes_literal(
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

    pub fn evaluate_expr_number_literal(
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

    pub fn evaluate_expr_boolean_literal(
        &self,
        expr_boolean_literal: &nodes::ExprBooleanLiteral,
    ) -> TypeExpression {
        TypeExpression::LiteralBoolean(LiteralBoolean {
            value: expr_boolean_literal.value,
        })
    }

    pub fn evaluate_expr_none_literal(&self) -> TypeExpression {
        TypeExpression::LiteralNone
    }

    pub fn evaluate_expr_ellipsis_literal(&self) -> TypeExpression {
        TypeExpression::LiteralEllipsis
    }

    pub fn evaluate_expr_attribute(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr_attribute: &nodes::ExprAttribute,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let value_eval = self.evaluate_expr(namespace, program_point, &expr_attribute.value)?;
        let attribute = self.gen_variable_name(program_point, &expr_attribute.attr)?;

        Ok(value_eval.map(|value| {
            TypeExpression::Attribute(ExpressionAttribute {
                value: Arc::new(value),
                attribute,
            })
        }))
    }

    pub fn evaluate_expr_subscript(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr_subscript: &nodes::ExprSubscript,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let value_eval = self.evaluate_expr(namespace, program_point, &expr_subscript.value)?;
        let slice_eval = self.evaluate_expr(namespace, program_point, &expr_subscript.slice)?;

        Ok(value_eval.merge(slice_eval, |value, slice| {
            TypeExpression::Subscript(ExpressionSubscript {
                value: Arc::new(value),
                slice: Arc::new(slice),
            })
        }))
    }

    pub fn evaluate_name(
        &self,
        program_point: ProgramPoint,
        expr_name: &nodes::ExprName,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        let variable_name = self.gen_variable_name(program_point, &expr_name.id)?;
        let location = self.gen_qualified_location(expr_name.range);

        Ok(ExpressionEval::new(
            TypeExpression::Variable(ExpressionVariable::new(
                variable_name.clone(),
                location.clone(),
            )),
            UsedVariables::new(LatticeMap::unit(variable_name, LatticeSet::unit(location))),
        ))
    }

    pub fn evaluate_expr(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        expr: &nodes::Expr,
    ) -> Result<ExpressionEval<TypeExpression>, ConstraintsBuilderError> {
        match expr {
            nodes::Expr::BoolOp(expr_bool_op) => {
                self.evaluate_expr_bool_op(namespace, program_point, expr_bool_op)
            }
            nodes::Expr::Named(_) => todo!(),
            nodes::Expr::BinOp(expr_bin_op) => {
                self.evaluate_expr_bin_op(namespace, program_point, expr_bin_op)
            }
            nodes::Expr::UnaryOp(expr_unary_op) => {
                self.evaluate_expr_unary_op(namespace, program_point, expr_unary_op)
            }
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
            nodes::Expr::Compare(expr_compare) => {
                self.evaluate_expr_compare(namespace, program_point, expr_compare)
            }
            nodes::Expr::Call(expr_call) => {
                self.evaluate_expr_call(namespace, program_point, expr_call)
            }
            nodes::Expr::FString(_) => todo!(),
            nodes::Expr::StringLiteral(expr_string_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_string_literal(expr_string_literal),
            )),
            nodes::Expr::BytesLiteral(expr_bytes_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_bytes_literal(expr_bytes_literal),
            )),
            nodes::Expr::NumberLiteral(expr_number_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_number_literal(expr_number_literal),
            )),
            nodes::Expr::BooleanLiteral(expr_boolean_literal) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_boolean_literal(expr_boolean_literal),
            )),
            nodes::Expr::NoneLiteral(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_none_literal(),
            )),
            nodes::Expr::EllipsisLiteral(_) => Ok(ExpressionEval::only_value(
                self.evaluate_expr_ellipsis_literal(),
            )),
            nodes::Expr::Attribute(expr_attribute) => {
                self.evaluate_expr_attribute(namespace, program_point, expr_attribute)
            }
            nodes::Expr::Subscript(expr_subscript) => {
                self.evaluate_expr_subscript(namespace, program_point, expr_subscript)
            }
            nodes::Expr::Starred(_) => todo!(),
            nodes::Expr::Name(expr_name) => self.evaluate_name(program_point, expr_name),
            nodes::Expr::List(_) => todo!(),
            nodes::Expr::Tuple(_) => todo!(),
            nodes::Expr::Slice(_) => todo!(),
            nodes::Expr::IpyEscapeCommand(_) => todo!(),
        }
    }

    pub fn evaluate_stmt_function_def(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_function_def: &nodes::StmtFunctionDef,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let parameters = self.gen_parameters(ProgramPoint::Entry, &stmt_function_def.parameters)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            parameters.variables,
        );

        let location = self.gen_qualified_location(stmt_function_def.name.range);

        self.assign_variable(
            &mut target_abstract_environment,
            location.clone(),
            self.gen_variable_name(program_point, &stmt_function_def.name)?,
            Arc::new(TypeExpression::Function(ExpressionFunction::new(
                location.clone(),
                stmt_function_def.is_async,
            ))),
        );

        target_abstract_environment.sub_program_entities.insert(
            ProgramEntity::new(location, program_point, ProgramEntityKind::Function),
            SubProgramEntityContext::new(
                AbstractEnvironmentSpecification {
                    arguments: parameters.value,
                    return_type: LatticeSet::default(),
                    exceptions: LatticeSet::default(),
                },
                target_abstract_environment.variable_locations.clone(),
            ),
        );

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_import(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_import: &nodes::StmtImport,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let mut current_nodes: LatticeSet<(ConstraintNode, Guard)> = LatticeSet::default();
        for alias in &stmt_import.names {
            let module_name = self.gen_module_name(program_point, &alias.name)?;

            if let Some(as_name) = &alias.asname {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_qualified_location(as_name.range),
                    self.gen_variable_name(program_point, &as_name)?,
                    Arc::new(TypeExpression::Import(ExpressionImport::new(
                        module_name.clone(),
                    ))),
                );
            } else {
                let identifier = Arc::new(module_name.identifiers.first().clone());
                let location = self.gen_qualified_location(alias.name.range);

                target_abstract_environment
                    .variable_locations
                    .values
                    .insert(identifier.clone(), LatticeSet::unit(location.clone()));

                let mut expression_option = Some(Arc::new(TypeExpression::Variable(
                    ExpressionVariable::new(identifier, location),
                )));

                let variable_location = self.gen_qualified_location(alias.name.range);
                let mut i = 1;
                while let Some(expression) = expression_option {
                    let (module_identifiers, attribute_identifiers) =
                        module_name.identifiers.split_at(i);
                    let attribute_option = attribute_identifiers.first().cloned();
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

            target_abstract_environment
                .imports
                .insert(module_name.clone());
        }

        target_abstract_environment
            .current_nodes
            .extend(current_nodes.values);

        Ok(target_abstract_environment)
    }

    pub fn evaluate_stmt_assign(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_assign: &nodes::StmtAssign,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let eval = self.evaluate_expr(namespace, program_point, &stmt_assign.value)?;

        self.create_used_variables_constraints(&mut target_abstract_environment, eval.variables);

        let type_expression = Arc::new(eval.value);

        let mut current_nodes: LatticeSet<(ConstraintNode, Guard)> = LatticeSet::default();
        for target_expr in &stmt_assign.targets {
            let Ok(target) = AssignmentTarget::try_from(target_expr) else {
                todo!("add the right error");
            };

            match target {
                AssignmentTarget::Name(target_name) => {
                    self.assign_variable(
                        &mut target_abstract_environment,
                        self.gen_qualified_location(target_expr.range()),
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

    pub fn evaluate_stmt_ann_assign(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_ann_assign: &nodes::StmtAnnAssign,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let Ok(target) = AssignmentTarget::try_from(stmt_ann_assign.target.as_ref()) else {
            todo!("add the right error");
        };

        let Some(value) = &stmt_ann_assign.value else {
            return Ok(target_abstract_environment);
        };

        let eval = self.evaluate_expr(namespace, program_point, value)?;

        self.create_used_variables_constraints(&mut target_abstract_environment, eval.variables);

        let type_expression = Arc::new(eval.value);

        match target {
            AssignmentTarget::Name(target_name) => {
                self.assign_variable(
                    &mut target_abstract_environment,
                    self.gen_qualified_location(stmt_ann_assign.target.range()),
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

    pub fn evaluate_stmt_while(
        &self,
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        stmt_while: &nodes::StmtWhile,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let condition_eval = self.evaluate_expr(namespace, program_point, &stmt_while.test)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            condition_eval.variables,
        );

        let condition_expression = Arc::new(condition_eval.value);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_qualified_location(stmt_while.range),
            LatticeSet::from_iter([
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
        stmt_if: &nodes::StmtIf,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        let mut target_abstract_environment =
            namespace.clone_abstract_environment_or_default(program_point);

        let condition_eval = self.evaluate_expr(namespace, program_point, &stmt_if.test)?;

        self.create_used_variables_constraints(
            &mut target_abstract_environment,
            condition_eval.variables,
        );

        let condition_expression = Arc::new(condition_eval.value);

        self.assign_empty_constraint(
            &mut target_abstract_environment,
            self.gen_qualified_location(stmt_if.range),
            LatticeSet::from_iter([
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
        stmt: &nodes::Stmt,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        match stmt {
            nodes::Stmt::FunctionDef(stmt_function_def) => {
                self.evaluate_stmt_function_def(namespace, program_point, stmt_function_def)
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
                self.evaluate_stmt_assign(namespace, program_point, stmt_assign)
            }
            nodes::Stmt::AugAssign(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::AnnAssign(stmt_ann_assign) => {
                self.evaluate_stmt_ann_assign(namespace, program_point, stmt_ann_assign)
            }
            nodes::Stmt::TypeAlias(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::For(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
            nodes::Stmt::While(stmt_while) => {
                self.evaluate_stmt_while(namespace, program_point, stmt_while)
            }
            nodes::Stmt::If(stmt_if) => self.evaluate_stmt_if(namespace, program_point, stmt_if),
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
                self.evaluate_stmt_import(namespace, program_point, &stmt_import)
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
    type AbstractState = ProgramEntityAbstractEnvironment;
    type AnalysisState = ProgramEntityAnalysisState;
    type Error = ConstraintsBuilderError;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(ProgramPoint::Entry))
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
    ) -> Result<ProgramEntityAnalysisState, ConstraintsBuilderError> {
        let mut analysis_state = ProgramEntityAnalysisState::new();

        let mut entry_state = ProgramEntityAbstractEnvironment::default();

        if let Some(abstract_parent_state) = self.abstract_parent_state {
            if let Some(context) = abstract_parent_state
                .state
                .sub_program_entities
                .get(self.entity)
            {
                entry_state.specification = context.specification.clone();

                for argument in entry_state.specification.arguments.keys() {
                    entry_state.variable_locations.insert(
                        argument.name.clone(),
                        LatticeSet::unit(argument.location.clone()),
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
        namespace: &ProgramEntityAnalysisState,
        program_point: ProgramPoint,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        if let Some(NodeData::Statement(statement_data)) = self.cfg.node_data(&program_point) {
            self.evaluate_stmt(namespace, program_point, statement_data.statement())
        } else {
            Ok(namespace.clone_abstract_environment_or_default(program_point))
        }
    }

    fn update_abstract_state(
        &self,
        _namespace: &ProgramEntityAnalysisState,
        from: ProgramPoint,
        to: ProgramPoint,
        abstract_environment: &ProgramEntityAbstractEnvironment,
    ) -> Result<Option<ProgramEntityAbstractEnvironment>, ConstraintsBuilderError> {
        let Some(edge_datas) = self.cfg.edge_data(from, to) else {
            return Ok(None);
        };

        let mut target_abstract_environment = abstract_environment.clone();

        target_abstract_environment.current_nodes = target_abstract_environment
            .current_nodes
            .iter()
            .filter_map(|(current_node, guard)| {
                if let Some(new_guard) = self.filter_guard(edge_datas, guard) {
                    Some((current_node.clone(), new_guard))
                } else {
                    None
                }
            })
            .collect();

        if to == ProgramPoint::Exit {
            for (from, guard) in target_abstract_environment.current_nodes.as_ref() {
                match guard {
                    Guard::Raise { expression, .. }
                        if edge_datas.contains(&EdgeData::UnhandledException) =>
                    {
                        let unhandled_exception_constraint = ConstraintNode::Constraint(Arc::new(
                            IncludeConstraint::Exception(IncludeConstraintDefinition::new(
                                Arc::new(ExceptionExpression::Type(expression.clone())),
                                Arc::new(ExceptionExpression::Raised(RaisedException {
                                    program_points: imbl::Vector::new(),
                                })),
                            )),
                        ));

                        target_abstract_environment.constraint_graph.add_edge(
                            from.clone(),
                            unhandled_exception_constraint.clone(),
                            guard.clone(),
                        );
                        target_abstract_environment.constraint_graph.add_edge(
                            unhandled_exception_constraint,
                            ConstraintNode::ExceptionExit,
                            Guard::default(),
                        );
                        target_abstract_environment.constraint_graph.add_edge(
                            ConstraintNode::ExceptionExit,
                            ConstraintNode::Exit,
                            Guard::default(),
                        );
                    }
                    _ => {
                        if edge_datas
                            .iter()
                            .all(|edge_data| matches!(edge_data, EdgeData::UnhandledException))
                        {
                            continue;
                        }
                        target_abstract_environment.constraint_graph.add_edge(
                            from.clone(),
                            ConstraintNode::TypeExit,
                            guard.clone(),
                        );
                        target_abstract_environment.constraint_graph.add_edge(
                            ConstraintNode::TypeExit,
                            ConstraintNode::Exit,
                            Guard::default(),
                        );
                    }
                }
            }
        }

        Ok(Some(target_abstract_environment))
    }

    fn get_abstract_state<'a>(
        &self,
        namespace: &'a ProgramEntityAnalysisState,
        program_point: &ProgramPoint,
    ) -> Result<Option<&'a ProgramEntityAbstractEnvironment>, ConstraintsBuilderError> {
        Ok(namespace.abstract_states.get(program_point))
    }

    fn set_abstract_state(
        &self,
        namespace: &mut ProgramEntityAnalysisState,
        program_point: ProgramPoint,
        abstract_environment: ProgramEntityAbstractEnvironment,
    ) -> Result<(), ConstraintsBuilderError> {
        namespace
            .abstract_states
            .insert(program_point, abstract_environment);
        Ok(())
    }

    fn merge(
        &self,
        _namespace: &ProgramEntityAnalysisState,
        _program_point: ProgramPoint,
        left: &ProgramEntityAbstractEnvironment,
        right: &ProgramEntityAbstractEnvironment,
    ) -> Result<ProgramEntityAbstractEnvironment, ConstraintsBuilderError> {
        Ok(left.join(right))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProgramEntityNode {
    Entry,
    Location(QualifiedLocation),
    Exit,
}

impl Display for ProgramEntityNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramEntityNode::Entry => write!(f, "Entry"),
            ProgramEntityNode::Location(location) => write!(f, "Location({})", location),
            ProgramEntityNode::Exit => write!(f, "Exit"),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramAnalysisState {
    pub nodes: LatticeMap<ProgramEntityNode, ProgramEntityAbstractEnvironment>,
    pub dependencies: LatticeMap<ProgramEntityNode, LatticeSet<ProgramEntityNode>>,
}

impl ProgramAnalysisState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(
        &mut self,
        node: ProgramEntityNode,
        analysis_state: ProgramEntityAbstractEnvironment,
    ) {
        self.nodes.insert(node.clone(), analysis_state);
    }

    pub fn add_dependency(&mut self, from: ProgramEntityNode, to: ProgramEntityNode) {
        self.dependencies.values.entry(from).or_default().insert(to);
    }

    pub fn remove_dependency(&mut self, from: ProgramEntityNode, to: ProgramEntityNode) {
        if let Entry::Occupied(mut tos) = self.dependencies.values.entry(from) {
            tos.get_mut().remove(&to);
        }
    }

    pub fn dot(&self, graph_name: &str) -> String {
        let mut edges: imbl::OrdSet<(ProgramEntityNode, ProgramEntityNode)> = imbl::OrdSet::new();
        for (from, tos) in &self.dependencies.values {
            for to in &tos.values {
                edges.insert((from.clone(), to.clone()));
            }
        }

        let mut dot_representation = String::from("digraph \"");
        dot_representation.push_str(graph_name);
        dot_representation.push_str("\" {\n");
        for node in self.nodes.values.keys() {
            dot_representation.push_str("    \"");
            dot_representation.push_str(&node.to_string());
            dot_representation.push_str("\";\n");
        }
        for (from, to) in &edges {
            dot_representation.push_str("    \"");
            dot_representation.push_str(&from.to_string());
            dot_representation.push_str("\" -> \"");
            dot_representation.push_str(&to.to_string());
            dot_representation.push_str("\";\n");
        }
        dot_representation.push_str("}\n");

        dot_representation
    }
}

impl Lattice for ProgramAnalysisState {
    fn includes(&self, other: &Self) -> bool {
        self.nodes.includes(&other.nodes) && self.dependencies.includes(&other.dependencies)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            nodes: self.nodes.join(&other.nodes),
            dependencies: self.dependencies.join(&other.dependencies),
        }
    }
}

impl Display for ProgramAnalysisState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ApyAnalysisState {{ nodes: {:?}, dependency_edges: {:?} }}",
            self.nodes, self.dependencies
        )
    }
}

pub fn import_cfg<F: Filesystem>(
    specs: &HashMap<Identifier, FinderSpec<Identifier, F>>,
    module_name: &ModuleName,
) -> Option<Cfg> {
    let mut finder_spec = specs.get(module_name.identifiers.first())?;

    for identifier in module_name.identifiers.iter().skip(1) {
        finder_spec = finder_spec.submodules.get(identifier)?;
    }

    load_cfg(&finder_spec.spec).ok()
}

#[derive(Debug, Error)]
pub enum ConstraintsError {
    #[error("failed to build constraints {0}")]
    BuildError(#[from] ConstraintsBuilderError),
}

pub fn analyse_cfg<'a>(
    entity: &'a ProgramEntity,
    cfg: &'a Cfg,
    program_entity_kind: ProgramEntityKind,
    program_entity_analysis_parent_state: Option<&'a ProgramEntityAbstractParentState<'a>>,
) -> ProgramAnalysisState {
    let constraint_builder =
        ConstraintsBuilder::new(cfg, entity, program_entity_analysis_parent_state);

    let program_entity_analysis_state =
        analysis(&constraint_builder).expect("constraint builder should work");
    let program_entity_node = ProgramEntityNode::Location(entity.location.clone());
    let program_entity_exit_abstract_state =
        &program_entity_analysis_state.abstract_states[&ProgramPoint::Exit];

    let mut program_analysis_state = ProgramAnalysisState::default();

    let sub_program_entity_analysis_parent_state = ProgramEntityAbstractParentState::new(
        &program_entity_exit_abstract_state,
        program_entity_kind,
        program_entity_analysis_parent_state,
    );
    for sub_program_entity in program_entity_exit_abstract_state
        .sub_program_entities
        .keys()
    {
        let sub_program_analysis_state = analyse_cfg(
            &sub_program_entity,
            cfg.cfgs().get(&sub_program_entity.program_point).unwrap(),
            sub_program_entity.kind,
            Some(&sub_program_entity_analysis_parent_state),
        );

        program_analysis_state = program_analysis_state.join(&sub_program_analysis_state);

        program_analysis_state.add_dependency(
            ProgramEntityNode::Location(sub_program_entity.location.clone()),
            program_entity_node.clone(),
        );
    }

    program_analysis_state.insert(
        program_entity_node,
        program_entity_exit_abstract_state.clone(),
    );

    program_analysis_state
}

pub fn analyse_program<F: Filesystem>(
    specs: HashMap<Identifier, FinderSpec<Identifier, F>>,
    initial_modules: HashSet<ModuleName>,
) -> ProgramAnalysisState {
    let builtin_module_name = Arc::new(QualifiedName::parse(BUILTINS_MODULE));

    let cfg = import_cfg(&specs, &builtin_module_name).expect("Should build CFG");

    let builtin_location = QualifiedLocation::from(builtin_module_name.clone());
    let builtin_node = ProgramEntityNode::Location(builtin_location.clone());

    let mut program_analysis = analyse_cfg(
        &ProgramEntity::new(
            builtin_location.clone(),
            ProgramPoint::Entry,
            ProgramEntityKind::Module,
        ),
        &cfg,
        ProgramEntityKind::Module,
        None,
    );

    program_analysis.add_dependency(ProgramEntityNode::Entry, builtin_node.clone());
    program_analysis.add_dependency(builtin_node.clone(), ProgramEntityNode::Exit);

    let specs_ref = &specs;

    let mut worklist = initial_modules;

    while !worklist.is_empty() {
        let builtin_parent_state = &ProgramEntityAbstractParentState::new(
            &program_analysis.nodes[&builtin_node],
            ProgramEntityKind::Module,
            None,
        );

        let new_program_analysis = worklist
            .drain()
            .par_bridge()
            .map(|module_name| {
                let cfg = import_cfg(specs_ref, &module_name).expect("Should build CFG");

                let parent_state = if module_name != builtin_module_name {
                    Some(builtin_parent_state)
                } else {
                    None
                };

                analyse_cfg(
                    &ProgramEntity::new(
                        QualifiedLocation::from(module_name),
                        ProgramPoint::Entry,
                        ProgramEntityKind::Module,
                    ),
                    &cfg,
                    ProgramEntityKind::Module,
                    parent_state,
                )
            })
            .reduce(
                || ProgramAnalysisState::new(),
                |left, right| left.join(&right),
            );

        program_analysis = program_analysis.join(&new_program_analysis);

        for (node, analysis_state) in new_program_analysis.nodes.as_ref() {
            let imports = analysis_state
                .imports
                .values
                .update(builtin_module_name.clone());

            for import in imports {
                let import_node =
                    ProgramEntityNode::Location(QualifiedLocation::from(import.clone()));

                program_analysis.add_dependency(node.clone(), import_node.clone());
                program_analysis.add_dependency(ProgramEntityNode::Exit, node.clone());
                program_analysis.remove_dependency(ProgramEntityNode::Exit, import_node.clone());

                if !program_analysis.nodes.contains_key(&import_node) {
                    worklist.insert(import.clone());
                }
            }
        }
    }

    program_analysis
}

#[cfg(test)]
mod tests {
    use super::*;
    use apygen_analysis::analysis;
    use imbl::ordset;
    use indoc::indoc;
    use rstest::rstest;

    #[rstest]
    #[case::import(
        "import some_module",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ some_module@{module[1:7]}";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@{module[1:7]}" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#type_exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset!["some_module"],
    )]
    #[case::import_as(
        "import some_module as mod",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ mod@{module[1:22]}";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ mod@{module[1:22]}" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ mod@{module[1:22]}" -> "#type_exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset!["some_module"],
    )]
    #[case::import_submodule(
        "import some_module.submodule",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ some_module@{module[1:7]}";
            "#import(some_module.submodule) ⊑ (some_module@{module[1:7]}).submodule";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@{module[1:7]}" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#import(some_module.submodule) ⊑ (some_module@{module[1:7]}).submodule" [label="#succeed(#import(some_module.submodule))"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module.submodule))"];
            "#import(some_module.submodule) ⊑ (some_module@{module[1:7]}).submodule" -> "#type_exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset!["some_module.submodule"],
    )]
    #[case::import_module_and_submodule(
        "import some_module, some_module.submodule",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(some_module) ⊑ some_module@{module[1:7]}";
            "#import(some_module) ⊑ some_module@{module[1:20]}";
            "#import(some_module.submodule) ⊑ (some_module@{module[1:20]}).submodule";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@{module[1:7]}" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#import(some_module) ⊑ some_module@{module[1:20]}" [label="#succeed(#import(some_module))"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(some_module) ⊑ some_module@{module[1:20]}" -> "#import(some_module.submodule) ⊑ (some_module@{module[1:20]}).submodule" [label="#succeed(#import(some_module.submodule))"];
            "#import(some_module) ⊑ some_module@{module[1:20]}" -> "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module.submodule))"];
            "#import(some_module.submodule) ⊑ (some_module@{module[1:20]}).submodule" -> "#type_exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions(#import(some_module.submodule)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset!["some_module", "some_module.submodule"],
    )]
    #[case::multiple_import(
        "import some_module, another_module",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(another_module) ⊑ another_module@{module[1:20]}";
            "#import(some_module) ⊑ some_module@{module[1:7]}";
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ some_module@{module[1:7]}" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(another_module) ⊑ another_module@{module[1:20]}" -> "#type_exit" [label="{}"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#import(another_module) ⊑ another_module@{module[1:20]}" [label="#succeed(#import(another_module))"];
            "#import(some_module) ⊑ some_module@{module[1:7]}" -> "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" [label="#raise(#import(another_module))"];
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset!["some_module", "another_module"],
    )]
    #[case::multiple_import_override(
        "import some_module as mod, another_module as mod",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "#import(another_module) ⊑ mod@{module[1:45]}";
            "#import(some_module) ⊑ mod@{module[1:22]}";
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()";
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#import(some_module) ⊑ mod@{module[1:22]}" [label="#succeed(#import(some_module))"];
            "#entry" -> "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" [label="#raise(#import(some_module))"];
            "#import(another_module) ⊑ mod@{module[1:45]}" -> "#type_exit" [label="{}"];
            "#import(some_module) ⊑ mod@{module[1:22]}" -> "#import(another_module) ⊑ mod@{module[1:45]}" [label="#succeed(#import(another_module))"];
            "#import(some_module) ⊑ mod@{module[1:22]}" -> "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" [label="#raise(#import(another_module))"];
            "#exceptions(#import(another_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions(#import(some_module)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset!["some_module", "another_module"],
    )]
    #[case::int_constant_assignment(
        "a = 42",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "42 ⊑ a@{module[1:0]}";
            "#type_exit";
            "#exit";
            "#entry" -> "42 ⊑ a@{module[1:0]}" [label="{}"];
            "42 ⊑ a@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::bigint_constant_assignment(
        "a = 4200000000000000000000000000",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "4200000000000000000000000000 ⊑ a@{module[1:0]}";
            "#type_exit";
            "#exit";
            "#entry" -> "4200000000000000000000000000 ⊑ a@{module[1:0]}" [label="{}"];
            "4200000000000000000000000000 ⊑ a@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::add_operation(
        "add = 42 + 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) + (67) ⊑ add@{module[1:0]}";
            "#exceptions((42) + (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) + (67) ⊑ add@{module[1:0]}" [label="#succeed((42) + (67))"];
            "#entry" -> "#exceptions((42) + (67)) ⊑ #raised_exceptions()" [label="#raise((42) + (67))"];
            "(42) + (67) ⊑ add@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) + (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::sub_operation(
        "sub = 42 - 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) - (67) ⊑ sub@{module[1:0]}";
            "#exceptions((42) - (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) - (67) ⊑ sub@{module[1:0]}" [label="#succeed((42) - (67))"];
            "#entry" -> "#exceptions((42) - (67)) ⊑ #raised_exceptions()" [label="#raise((42) - (67))"];
            "(42) - (67) ⊑ sub@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) - (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::mult_operation(
        "mult = 42 * 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) * (67) ⊑ mult@{module[1:0]}";
            "#exceptions((42) * (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) * (67) ⊑ mult@{module[1:0]}" [label="#succeed((42) * (67))"];
            "#entry" -> "#exceptions((42) * (67)) ⊑ #raised_exceptions()" [label="#raise((42) * (67))"];
            "(42) * (67) ⊑ mult@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) * (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::mat_mult_operation(
        "mat_mult = 42 @ 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) @ (67) ⊑ mat_mult@{module[1:0]}";
            "#exceptions((42) @ (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) @ (67) ⊑ mat_mult@{module[1:0]}" [label="#succeed((42) @ (67))"];
            "#entry" -> "#exceptions((42) @ (67)) ⊑ #raised_exceptions()" [label="#raise((42) @ (67))"];
            "(42) @ (67) ⊑ mat_mult@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) @ (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::div_operation(
        "div = 42 / 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) / (67) ⊑ div@{module[1:0]}";
            "#exceptions((42) / (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) / (67) ⊑ div@{module[1:0]}" [label="#succeed((42) / (67))"];
            "#entry" -> "#exceptions((42) / (67)) ⊑ #raised_exceptions()" [label="#raise((42) / (67))"];
            "(42) / (67) ⊑ div@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) / (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::floor_div_operation(
        "floor_div = 42 // 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) // (67) ⊑ floor_div@{module[1:0]}";
            "#exceptions((42) // (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) // (67) ⊑ floor_div@{module[1:0]}" [label="#succeed((42) // (67))"];
            "#entry" -> "#exceptions((42) // (67)) ⊑ #raised_exceptions()" [label="#raise((42) // (67))"];
            "(42) // (67) ⊑ floor_div@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) // (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::mod_operation(
        "mod = 42 % 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) % (67) ⊑ mod@{module[1:0]}";
            "#exceptions((42) % (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) % (67) ⊑ mod@{module[1:0]}" [label="#succeed((42) % (67))"];
            "#entry" -> "#exceptions((42) % (67)) ⊑ #raised_exceptions()" [label="#raise((42) % (67))"];
            "(42) % (67) ⊑ mod@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) % (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::pow_operation(
        "pow = 42 ** 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) ** (67) ⊑ pow@{module[1:0]}";
            "#exceptions((42) ** (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) ** (67) ⊑ pow@{module[1:0]}" [label="#succeed((42) ** (67))"];
            "#entry" -> "#exceptions((42) ** (67)) ⊑ #raised_exceptions()" [label="#raise((42) ** (67))"];
            "(42) ** (67) ⊑ pow@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) ** (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::shl_operation(
        "shl = 42 << 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) << (67) ⊑ shl@{module[1:0]}";
            "#exceptions((42) << (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) << (67) ⊑ shl@{module[1:0]}" [label="#succeed((42) << (67))"];
            "#entry" -> "#exceptions((42) << (67)) ⊑ #raised_exceptions()" [label="#raise((42) << (67))"];
            "(42) << (67) ⊑ shl@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) << (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::shr_operation(
        "shr = 42 >> 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) >> (67) ⊑ shr@{module[1:0]}";
            "#exceptions((42) >> (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) >> (67) ⊑ shr@{module[1:0]}" [label="#succeed((42) >> (67))"];
            "#entry" -> "#exceptions((42) >> (67)) ⊑ #raised_exceptions()" [label="#raise((42) >> (67))"];
            "(42) >> (67) ⊑ shr@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) >> (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::bit_or_operation(
        "bit_or = 42 | 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) | (67) ⊑ bit_or@{module[1:0]}";
            "#exceptions((42) | (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) | (67) ⊑ bit_or@{module[1:0]}" [label="#succeed((42) | (67))"];
            "#entry" -> "#exceptions((42) | (67)) ⊑ #raised_exceptions()" [label="#raise((42) | (67))"];
            "(42) | (67) ⊑ bit_or@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) | (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::bit_xor_operation(
        "bit_xor = 42 ^ 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) ^ (67) ⊑ bit_xor@{module[1:0]}";
            "#exceptions((42) ^ (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) ^ (67) ⊑ bit_xor@{module[1:0]}" [label="#succeed((42) ^ (67))"];
            "#entry" -> "#exceptions((42) ^ (67)) ⊑ #raised_exceptions()" [label="#raise((42) ^ (67))"];
            "(42) ^ (67) ⊑ bit_xor@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) ^ (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::bit_and_operation(
        "bit_and = 42 & 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) & (67) ⊑ bit_and@{module[1:0]}";
            "#exceptions((42) & (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) & (67) ⊑ bit_and@{module[1:0]}" [label="#succeed((42) & (67))"];
            "#entry" -> "#exceptions((42) & (67)) ⊑ #raised_exceptions()" [label="#raise((42) & (67))"];
            "(42) & (67) ⊑ bit_and@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) & (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::and_operation(
        "and_ = 42 and 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) and (67) ⊑ and_@{module[1:0]}";
            "#exceptions((42) and (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) and (67) ⊑ and_@{module[1:0]}" [label="#succeed((42) and (67))"];
            "#entry" -> "#exceptions((42) and (67)) ⊑ #raised_exceptions()" [label="#raise((42) and (67))"];
            "(42) and (67) ⊑ and_@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) and (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::or_operation(
        "or_ = 42 or 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) or (67) ⊑ or_@{module[1:0]}";
            "#exceptions((42) or (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) or (67) ⊑ or_@{module[1:0]}" [label="#succeed((42) or (67))"];
            "#entry" -> "#exceptions((42) or (67)) ⊑ #raised_exceptions()" [label="#raise((42) or (67))"];
            "(42) or (67) ⊑ or_@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) or (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::eq_operation(
        "eq = 42 == 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) == (67) ⊑ eq@{module[1:0]}";
            "#exceptions((42) == (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) == (67) ⊑ eq@{module[1:0]}" [label="#succeed((42) == (67))"];
            "#entry" -> "#exceptions((42) == (67)) ⊑ #raised_exceptions()" [label="#raise((42) == (67))"];
            "(42) == (67) ⊑ eq@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) == (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::not_eq_operation(
        "not_eq = 42 != 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) != (67) ⊑ not_eq@{module[1:0]}";
            "#exceptions((42) != (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) != (67) ⊑ not_eq@{module[1:0]}" [label="#succeed((42) != (67))"];
            "#entry" -> "#exceptions((42) != (67)) ⊑ #raised_exceptions()" [label="#raise((42) != (67))"];
            "(42) != (67) ⊑ not_eq@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) != (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::lt_operation(
        "lt = 42 < 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) < (67) ⊑ lt@{module[1:0]}";
            "#exceptions((42) < (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) < (67) ⊑ lt@{module[1:0]}" [label="#succeed((42) < (67))"];
            "#entry" -> "#exceptions((42) < (67)) ⊑ #raised_exceptions()" [label="#raise((42) < (67))"];
            "(42) < (67) ⊑ lt@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) < (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::gt_operation(
        "gt = 42 > 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) > (67) ⊑ gt@{module[1:0]}";
            "#exceptions((42) > (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) > (67) ⊑ gt@{module[1:0]}" [label="#succeed((42) > (67))"];
            "#entry" -> "#exceptions((42) > (67)) ⊑ #raised_exceptions()" [label="#raise((42) > (67))"];
            "(42) > (67) ⊑ gt@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) > (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::lte_operation(
        "lte = 42 <= 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) <= (67) ⊑ lte@{module[1:0]}";
            "#exceptions((42) <= (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) <= (67) ⊑ lte@{module[1:0]}" [label="#succeed((42) <= (67))"];
            "#entry" -> "#exceptions((42) <= (67)) ⊑ #raised_exceptions()" [label="#raise((42) <= (67))"];
            "(42) <= (67) ⊑ lte@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) <= (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::gte_operation(
        "gte = 42 >= 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) >= (67) ⊑ gte@{module[1:0]}";
            "#exceptions((42) >= (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) >= (67) ⊑ gte@{module[1:0]}" [label="#succeed((42) >= (67))"];
            "#entry" -> "#exceptions((42) >= (67)) ⊑ #raised_exceptions()" [label="#raise((42) >= (67))"];
            "(42) >= (67) ⊑ gte@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) >= (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::is_operation(
        "is_ = 42 is 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) is (67) ⊑ is_@{module[1:0]}";
            "#exceptions((42) is (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) is (67) ⊑ is_@{module[1:0]}" [label="#succeed((42) is (67))"];
            "#entry" -> "#exceptions((42) is (67)) ⊑ #raised_exceptions()" [label="#raise((42) is (67))"];
            "(42) is (67) ⊑ is_@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) is (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::is_not_operation(
        "is_not = 42 is not 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) is not (67) ⊑ is_not@{module[1:0]}";
            "#exceptions((42) is not (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) is not (67) ⊑ is_not@{module[1:0]}" [label="#succeed((42) is not (67))"];
            "#entry" -> "#exceptions((42) is not (67)) ⊑ #raised_exceptions()" [label="#raise((42) is not (67))"];
            "(42) is not (67) ⊑ is_not@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) is not (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::in_operation(
        "in_ = 42 in 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) in (67) ⊑ in_@{module[1:0]}";
            "#exceptions((42) in (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) in (67) ⊑ in_@{module[1:0]}" [label="#succeed((42) in (67))"];
            "#entry" -> "#exceptions((42) in (67)) ⊑ #raised_exceptions()" [label="#raise((42) in (67))"];
            "(42) in (67) ⊑ in_@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) in (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::not_in_operation(
        "not_in = 42 not in 67",
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "(42) not in (67) ⊑ not_in@{module[1:0]}";
            "#exceptions((42) not in (67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "(42) not in (67) ⊑ not_in@{module[1:0]}" [label="#succeed((42) not in (67))"];
            "#entry" -> "#exceptions((42) not in (67)) ⊑ #raised_exceptions()" [label="#raise((42) not in (67))"];
            "(42) not in (67) ⊑ not_in@{module[1:0]}" -> "#type_exit" [label="{}"];
            "#exceptions((42) not in (67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::add_same_variable(
        indoc! {r##"
        a = 4

        b = a + a
        "##},
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "a@{module[1:0]} ⊑ a@{module[3:4]}";
            "a@{module[1:0]} ⊑ a@{module[3:8]}";
            "(a@{module[3:4]}) + (a@{module[3:8]}) ⊑ b@{module[3:0]}";
            "4 ⊑ a@{module[1:0]}";
            "#exceptions((a@{module[3:4]}) + (a@{module[3:8]})) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "4 ⊑ a@{module[1:0]}" [label="{}"];
            "a@{module[1:0]} ⊑ a@{module[3:4]}" -> "(a@{module[3:4]}) + (a@{module[3:8]}) ⊑ b@{module[3:0]}" [label="#succeed((a@{module[3:4]}) + (a@{module[3:8]}))"];
            "a@{module[1:0]} ⊑ a@{module[3:4]}" -> "#exceptions((a@{module[3:4]}) + (a@{module[3:8]})) ⊑ #raised_exceptions()" [label="#raise((a@{module[3:4]}) + (a@{module[3:8]}))"];
            "a@{module[1:0]} ⊑ a@{module[3:8]}" -> "(a@{module[3:4]}) + (a@{module[3:8]}) ⊑ b@{module[3:0]}" [label="#succeed((a@{module[3:4]}) + (a@{module[3:8]}))"];
            "a@{module[1:0]} ⊑ a@{module[3:8]}" -> "#exceptions((a@{module[3:4]}) + (a@{module[3:8]})) ⊑ #raised_exceptions()" [label="#raise((a@{module[3:4]}) + (a@{module[3:8]}))"];
            "(a@{module[3:4]}) + (a@{module[3:8]}) ⊑ b@{module[3:0]}" -> "#type_exit" [label="{}"];
            "4 ⊑ a@{module[1:0]}" -> "a@{module[1:0]} ⊑ a@{module[3:4]}" [label="{}"];
            "4 ⊑ a@{module[1:0]}" -> "a@{module[1:0]} ⊑ a@{module[3:8]}" [label="{}"];
            "#exceptions((a@{module[3:4]}) + (a@{module[3:8]})) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
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
            "a@{module[4:4]} ⊑ a@{module[8:4]}";
            "a@{module[6:4]} ⊑ a@{module[8:4]}";
            "a@{module[8:4]} ⊑ b@{module[8:0]}";
            "x@{module[1:0]} ⊑ x@{module[3:3]}";
            "42 ⊑ a@{module[4:4]}";
            "67 ⊑ a@{module[6:4]}";
            "True ⊑ x@{module[1:0]}";
            "#exceptions(a@{module[8:4]}) ⊑ #raised_exceptions()";
            "#exceptions(x@{module[3:3]}) ⊑ #raised_exceptions()";
            "#empty(module[3:0])";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "True ⊑ x@{module[1:0]}" [label="{}"];
            "a@{module[4:4]} ⊑ a@{module[8:4]}" -> "a@{module[8:4]} ⊑ b@{module[8:0]}" [label="#succeed(a@{module[8:4]})"];
            "a@{module[4:4]} ⊑ a@{module[8:4]}" -> "#exceptions(a@{module[8:4]}) ⊑ #raised_exceptions()" [label="#raise(a@{module[8:4]})"];
            "a@{module[6:4]} ⊑ a@{module[8:4]}" -> "a@{module[8:4]} ⊑ b@{module[8:0]}" [label="#succeed(a@{module[8:4]})"];
            "a@{module[6:4]} ⊑ a@{module[8:4]}" -> "#exceptions(a@{module[8:4]}) ⊑ #raised_exceptions()" [label="#raise(a@{module[8:4]})"];
            "a@{module[8:4]} ⊑ b@{module[8:0]}" -> "#type_exit" [label="{}"];
            "x@{module[1:0]} ⊑ x@{module[3:3]}" -> "#empty(module[3:0])" [label="{}"];
            "42 ⊑ a@{module[4:4]}" -> "a@{module[4:4]} ⊑ a@{module[8:4]}" [label="{}"];
            "42 ⊑ a@{module[4:4]}" -> "a@{module[6:4]} ⊑ a@{module[8:4]}" [label="{}"];
            "67 ⊑ a@{module[6:4]}" -> "a@{module[4:4]} ⊑ a@{module[8:4]}" [label="{}"];
            "67 ⊑ a@{module[6:4]}" -> "a@{module[6:4]} ⊑ a@{module[8:4]}" [label="{}"];
            "True ⊑ x@{module[1:0]}" -> "x@{module[1:0]} ⊑ x@{module[3:3]}" [label="{}"];
            "#exceptions(a@{module[8:4]}) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions(x@{module[3:3]}) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#empty(module[3:0])" -> "42 ⊑ a@{module[4:4]}" [label="#is_true(x@{module[3:3]})"];
            "#empty(module[3:0])" -> "67 ⊑ a@{module[6:4]}" [label="#is_false(x@{module[3:3]})"];
            "#empty(module[3:0])" -> "#exceptions(x@{module[3:3]}) ⊑ #raised_exceptions()" [label="#raise(x@{module[3:3]})"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
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
            "a@{module[1:0]} ⊑ a@{module[3:6]}";
            "a@{module[3:6]} ⊑ a@{module[4:8]}";
            "a@{module[3:6]} ⊑ a@{module[6:4]}";
            "a@{module[4:4]} ⊑ a@{module[3:6]}";
            "a@{module[6:4]} ⊑ b@{module[6:0]}";
            "(a@{module[4:8]}) + (1) ⊑ a@{module[4:4]}";
            "0 ⊑ a@{module[1:0]}";
            "#exceptions(a@{module[6:4]}) ⊑ #raised_exceptions()";
            "#exceptions((a@{module[3:6]}) < (5)) ⊑ #raised_exceptions()";
            "#exceptions((a@{module[4:8]}) + (1)) ⊑ #raised_exceptions()";
            "#empty(module[3:0])";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "0 ⊑ a@{module[1:0]}" [label="{}"];
            "a@{module[1:0]} ⊑ a@{module[3:6]}" -> "#empty(module[3:0])" [label="{}"];
            "a@{module[3:6]} ⊑ a@{module[4:8]}" -> "(a@{module[4:8]}) + (1) ⊑ a@{module[4:4]}" [label="#succeed((a@{module[4:8]}) + (1))"];
            "a@{module[3:6]} ⊑ a@{module[4:8]}" -> "#exceptions((a@{module[4:8]}) + (1)) ⊑ #raised_exceptions()" [label="#raise((a@{module[4:8]}) + (1))"];
            "a@{module[3:6]} ⊑ a@{module[6:4]}" -> "a@{module[6:4]} ⊑ b@{module[6:0]}" [label="#succeed(a@{module[6:4]})"];
            "a@{module[3:6]} ⊑ a@{module[6:4]}" -> "#exceptions(a@{module[6:4]}) ⊑ #raised_exceptions()" [label="#raise(a@{module[6:4]})"];
            "a@{module[4:4]} ⊑ a@{module[3:6]}" -> "#empty(module[3:0])" [label="{}"];
            "a@{module[6:4]} ⊑ b@{module[6:0]}" -> "#type_exit" [label="{}"];
            "(a@{module[4:8]}) + (1) ⊑ a@{module[4:4]}" -> "a@{module[1:0]} ⊑ a@{module[3:6]}" [label="{}"];
            "(a@{module[4:8]}) + (1) ⊑ a@{module[4:4]}" -> "a@{module[4:4]} ⊑ a@{module[3:6]}" [label="{}"];
            "0 ⊑ a@{module[1:0]}" -> "a@{module[1:0]} ⊑ a@{module[3:6]}" [label="{}"];
            "0 ⊑ a@{module[1:0]}" -> "a@{module[4:4]} ⊑ a@{module[3:6]}" [label="{}"];
            "#exceptions(a@{module[6:4]}) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions((a@{module[3:6]}) < (5)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions((a@{module[4:8]}) + (1)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#empty(module[3:0])" -> "a@{module[3:6]} ⊑ a@{module[4:8]}" [label="#is_true((a@{module[3:6]}) < (5))"];
            "#empty(module[3:0])" -> "a@{module[3:6]} ⊑ a@{module[6:4]}" [label="#is_false((a@{module[3:6]}) < (5))"];
            "#empty(module[3:0])" -> "#exceptions((a@{module[3:6]}) < (5)) ⊑ #raised_exceptions()" [label="#raise((a@{module[3:6]}) < (5))"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a, b):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        digraph "Constraints" {
            "#entry";
            "add_two@{module[1:4]} ⊑ add_two@{module[4:9]}";
            "#function(location=module[1:4], async=false) ⊑ add_two@{module[1:4]}";
            "(add_two@{module[4:9]})(42, 67) ⊑ result@{module[4:0]}";
            "#exceptions(#function(location=module[1:4], async=false)) ⊑ #raised_exceptions()";
            "#exceptions((add_two@{module[4:9]})(42, 67)) ⊑ #raised_exceptions()";
            "#type_exit";
            "#exception_exit";
            "#exit";
            "#entry" -> "#function(location=module[1:4], async=false) ⊑ add_two@{module[1:4]}" [label="#succeed(#function(location=module[1:4], async=false))"];
            "#entry" -> "#exceptions(#function(location=module[1:4], async=false)) ⊑ #raised_exceptions()" [label="#raise(#function(location=module[1:4], async=false))"];
            "add_two@{module[1:4]} ⊑ add_two@{module[4:9]}" -> "(add_two@{module[4:9]})(42, 67) ⊑ result@{module[4:0]}" [label="#succeed((add_two@{module[4:9]})(42, 67))"];
            "add_two@{module[1:4]} ⊑ add_two@{module[4:9]}" -> "#exceptions((add_two@{module[4:9]})(42, 67)) ⊑ #raised_exceptions()" [label="#raise((add_two@{module[4:9]})(42, 67))"];
            "#function(location=module[1:4], async=false) ⊑ add_two@{module[1:4]}" -> "add_two@{module[1:4]} ⊑ add_two@{module[4:9]}" [label="{}"];
            "(add_two@{module[4:9]})(42, 67) ⊑ result@{module[4:0]}" -> "#type_exit" [label="{}"];
            "#exceptions(#function(location=module[1:4], async=false)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#exceptions((add_two@{module[4:9]})(42, 67)) ⊑ #raised_exceptions()" -> "#exception_exit" [label="{}"];
            "#type_exit" -> "#exit" [label="{}"];
            "#exception_exit" -> "#exit" [label="{}"];
        }
        "##},
        ordset![],
    )]
    fn test_constraints_generation(
        #[case] source: &str,
        #[case] expected_dot: &str,
        #[case] expected_imports: imbl::OrdSet<&str>,
    ) {
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let entity = ProgramEntity::new(
            QualifiedLocation::from(Arc::new(QualifiedName::parse("module"))),
            ProgramPoint::Entry,
            ProgramEntityKind::Module,
        );

        let constraints_builder = ConstraintsBuilder::new(&cfg, &entity, None);

        let analysis_state =
            analysis(&constraints_builder).expect("constraint builder should work");

        let exit_state = analysis_state
            .abstract_states
            .get(&ProgramPoint::Exit)
            .expect("exit should exist");

        let actual_dot = exit_state.constraint_graph.dot("Constraints");
        let actual_imports = &exit_state.imports.values;

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
        assert_eq!(
            expected_imports
                .into_iter()
                .map(|expected_import| Arc::new(QualifiedName::parse(expected_import)))
                .collect::<imbl::OrdSet<ModuleName>>(),
            *actual_imports
        );
    }

    #[rstest]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a, b):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        digraph "Dependency" {
            "Location(module)";
            "Location(module[1:4])";
            "Location(module[1:4])" -> "Location(module)";
        }
        "##},
    )]
    fn test_cfg_analysis(#[case] source: &str, #[case] expected_dot: &str) {
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let program_analysis_state = analyse_cfg(
            &ProgramEntity::new(
                QualifiedLocation::from(Arc::new(QualifiedName::parse("module"))),
                ProgramPoint::Entry,
                ProgramEntityKind::Module,
            ),
            &cfg,
            ProgramEntityKind::Module,
            None,
        );

        let actual_dot = program_analysis_state.dot("Dependency");

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }
}
