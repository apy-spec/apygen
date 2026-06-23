use crate::abstract_environment::{
    LiteralBoolean, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInteger, LiteralString,
};
use crate::genkill::assignment::AssignmentTarget;
use apy::OneOrMany;
use apy::v1::{GenericKind, Identifier, ParameterKind, QualifiedName};
use apygen_analysis::CfgAnalyser;
use apygen_analysis::cfg::nodes::Number;
use apygen_analysis::cfg::{Cfg, EdgeData, NodeData, ProgramPoint, nodes};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::Namespace;
use num_bigint::BigInt;
use num_complex::Complex64;
use num_traits::Num;
use std::fmt::{Debug, Display, Formatter};
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
    pub fn new(values: imbl::OrdSet<T>) -> Self {
        Self { values }
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

impl<T: Clone + Ord> FromIterator<T> for LatticeSet<T> {
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
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
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
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
pub struct ExpressionVariable {
    pub name: VariableName,
    pub program_point: ProgramPoint,
}

impl ExpressionVariable {
    pub fn new(name: VariableName, program_point: ProgramPoint) -> Self {
        Self {
            name,
            program_point,
        }
    }
}

impl Display for ExpressionVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.name, self.program_point)
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
        write!(f, "import({})", self.module)
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
pub struct ExpressionJoin {
    values: imbl::OrdSet<Arc<TypeExpression>>,
}

impl Display for ExpressionJoin {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.values.is_empty() {
            write!(f, "⊥")
        } else if self.values.len() == 1 {
            write!(
                f,
                "{}",
                self.values
                    .get_min()
                    .expect("should exist cause of the check above")
            )
        } else {
            for (i, value) in self.values.iter().enumerate() {
                if i > 0 {
                    write!(f, " ⊔ ")?;
                }
                write!(f, "({})", value)?;
            }
            Ok(())
        }
    }
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
    Join(ExpressionJoin),
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
            TypeExpression::Join(expression_join) => write!(f, "{}", expression_join),
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
            ExceptionExpression::Type(type_expression) => write!(f, "#exceptions({})", type_expression),
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
                Some(exception) => write!(f, "#fail({}, {})", expression, exception),
                None => write!(f, "#fail({})", expression),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintGuarded {
    guards: LatticeSet<Guard>,
    constraint: Arc<Constraint>,
}

impl Display for ConstraintGuarded {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} => ({})", self.guards, self.constraint)
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
    left: Arc<T>,
    kind: ConstraintKind,
    right: Arc<T>,
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
    Guarded(ConstraintGuarded),
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Type(constraint_type) => write!(f, "{}", constraint_type),
            Constraint::Exception(constraint_exception) => write!(f, "{}", constraint_exception),
            Constraint::Guarded(constraint_guarded) => write!(f, "{}", constraint_guarded),
        }
    }
}
#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbstractEnvironment {
    pub current_guards: LatticeSet<LatticeSet<Guard>>,
    pub variable_locations: LatticeMap<VariableName, LatticeSet<ProgramPoint>>,
    pub constraints: LatticeSet<Arc<Constraint>>,
}

impl Lattice for AbstractEnvironment {
    fn includes(&self, other: &Self) -> bool {
        self.current_guards.includes(&other.current_guards)
            && self.variable_locations.includes(&other.variable_locations)
            && self.constraints.includes(&other.constraints)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            current_guards: self.current_guards.join(&other.current_guards),
            variable_locations: self.variable_locations.join(&other.variable_locations),
            constraints: self.constraints.join(&other.constraints),
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

    pub fn assign_variable(
        &self,
        abstract_environment: &mut AbstractEnvironment,
        program_point: ProgramPoint,
        variable: VariableName,
    ) {
        abstract_environment
            .variable_locations
            .values
            .insert(variable, LatticeSet::from_iter([program_point]));
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

    pub fn gen_parameter(
        &self,
        program_point: ProgramPoint,
        parameter: &nodes::Parameter,
    ) -> Result<(VariableName, LatticeSet<Arc<Constraint>>), ConstraintsBuilderError> {
        let parameter_name = self.gen_variable_name(program_point, &parameter.name)?;

        let constraints: LatticeSet<Arc<Constraint>> = LatticeSet::default();

        if let Some(annotation) = &parameter.annotation {
            // TODO: add support for annotations
        }

        Ok((parameter_name, constraints))
    }

    pub fn gen_parameter_with_default(
        &self,
        program_point: ProgramPoint,
        parameter_with_default: &nodes::ParameterWithDefault,
    ) -> Result<(VariableName, LatticeSet<Arc<Constraint>>), ConstraintsBuilderError> {
        let (parameter_name, mut constraints) =
            self.gen_parameter(program_point, &parameter_with_default.parameter)?;

        if let Some(default) = &parameter_with_default.default {
            constraints
                .values
                .insert(Arc::new(Constraint::Type(ConstraintDefinition::equal(
                    TypeExpression::Variable(ExpressionVariable::new(
                        parameter_name.clone(),
                        program_point,
                    )),
                    self.gen_expr(&Namespace::default(), program_point, &default)?,
                ))));
        }

        Ok((parameter_name, constraints))
    }

    pub fn gen_parameters(
        &self,
        program_point: ProgramPoint,
        parameters: &nodes::Parameters,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        let mut abstract_environment = AbstractEnvironment::default();

        for parameter in &parameters.posonlyargs {
            let (parameter_name, constraints) =
                self.gen_parameter_with_default(program_point, &parameter)?;
            self.assign_variable(&mut abstract_environment, program_point, parameter_name);
            abstract_environment
                .constraints
                .values
                .extend(constraints.values);
        }

        for parameter in &parameters.args {
            let (parameter_name, constraints) =
                self.gen_parameter(program_point, &parameter.parameter)?;
            self.assign_variable(&mut abstract_environment, program_point, parameter_name);
            abstract_environment
                .constraints
                .values
                .extend(constraints.values);
        }

        if let Some(parameter) = &parameters.vararg {
            let (parameter_name, constraints) = self.gen_parameter(program_point, &parameter)?;
            self.assign_variable(&mut abstract_environment, program_point, parameter_name);
            abstract_environment
                .constraints
                .values
                .extend(constraints.values);
        }

        for parameter in &parameters.kwonlyargs {
            let (parameter_name, constraints) =
                self.gen_parameter_with_default(program_point, &parameter)?;
            self.assign_variable(&mut abstract_environment, program_point, parameter_name);
            abstract_environment
                .constraints
                .values
                .extend(constraints.values);
        }

        if let Some(parameter) = &parameters.kwarg {
            let (parameter_name, constraints) = self.gen_parameter(program_point, &parameter)?;
            self.assign_variable(&mut abstract_environment, program_point, parameter_name);
            abstract_environment
                .constraints
                .values
                .extend(constraints.values);
        }

        Ok(abstract_environment)
    }

    pub fn gen_expr_bool_op(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        expr_bool_op: &nodes::ExprBoolOp,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let mut values_iter = expr_bool_op.values.iter();

        let mut type_expression = match values_iter.next() {
            Some(value) => self.gen_expr(namespace, program_point, value)?,
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
                right: Arc::new(self.gen_expr(namespace, program_point, &value)?),
            });
        }

        Ok(type_expression)
    }

    pub fn gen_expr_bin_op(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        expr_bin_op: &nodes::ExprBinOp,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let left = self.gen_expr(namespace, program_point, &expr_bin_op.left)?;
        let right = self.gen_expr(namespace, program_point, &expr_bin_op.right)?;

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
        expr_unary_op: &nodes::ExprUnaryOp,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let operand = self.gen_expr(namespace, program_point, &expr_unary_op.operand)?;

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
        expr_compare: &nodes::ExprCompare,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let mut type_expression = self.gen_expr(namespace, program_point, &expr_compare.left)?;

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

            let comparator = self.gen_expr(namespace, program_point, comparator)?;

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
        expr_call: &nodes::ExprCall,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let func = self.gen_expr(namespace, program_point, &expr_call.func)?;

        let mut positional_arguments: imbl::Vector<Arc<TypeExpression>> = imbl::Vector::new();
        for positional_argument in &expr_call.arguments.args {
            positional_arguments.push_back(Arc::new(self.gen_expr(
                namespace,
                program_point,
                &positional_argument,
            )?));
        }

        let mut keyword_arguments: imbl::Vector<KeywordArgument> = imbl::Vector::new();
        for keyword_argument in &expr_call.arguments.keywords {
            let keyword_name = match &keyword_argument.arg {
                Some(identifier) => Some(self.gen_variable_name(program_point, &identifier)?),
                None => None,
            };
            let keyword_type = self.gen_expr(namespace, program_point, &keyword_argument.value)?;
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
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        Ok(TypeExpression::LiteralString(LiteralString {
            value: Arc::new(expr_string_literal.value.to_str().to_owned()),
        }))
    }

    pub fn gen_expr_bytes_literal(
        &self,
        expr_bytes_literal: &nodes::ExprBytesLiteral,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        Ok(TypeExpression::LiteralBytes(LiteralBytes {
            value: expr_bytes_literal
                .value
                .iter()
                .flat_map(|part| part.as_slice())
                .copied()
                .collect(),
        }))
    }

    pub fn gen_expr_number_literal(
        &self,
        expr_number_literal: &nodes::ExprNumberLiteral,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        Ok(match &expr_number_literal.value {
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
        })
    }

    pub fn gen_expr_boolean_literal(
        &self,
        expr_boolean_literal: &nodes::ExprBooleanLiteral,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        Ok(TypeExpression::LiteralBoolean(LiteralBoolean {
            value: expr_boolean_literal.value,
        }))
    }

    pub fn gen_expr_none_literal(&self) -> Result<TypeExpression, ConstraintsBuilderError> {
        Ok(TypeExpression::LiteralNone)
    }

    pub fn gen_expr_ellipsis_literal(&self) -> Result<TypeExpression, ConstraintsBuilderError> {
        Ok(TypeExpression::LiteralEllipsis)
    }

    pub fn gen_expr_attribute(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        expr_attribute: &nodes::ExprAttribute,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let value = self.gen_expr(namespace, program_point, &expr_attribute.value)?;
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
        expr_subscript: &nodes::ExprSubscript,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let value = self.gen_expr(namespace, program_point, &expr_subscript.value)?;
        let slice = self.gen_expr(namespace, program_point, &expr_subscript.slice)?;

        Ok(TypeExpression::Subscript(ExpressionSubscript {
            value: Arc::new(value),
            slice: Arc::new(slice),
        }))
    }

    pub fn gen_name(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        expr_name: &nodes::ExprName,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        let name = self.gen_variable_name(program_point, &expr_name.id)?;

        let Some(abstract_environment) = namespace.abstract_environments.get(&program_point) else {
            return Err(ConstraintsBuilderError::InvalidProgramPoint { program_point });
        };

        match abstract_environment.variable_locations.values.get(&name) {
            Some(locations) => {
                if locations.values.len() == 1 {
                    Ok(TypeExpression::Variable(ExpressionVariable::new(
                        name.clone(),
                        locations
                            .values
                            .get_min()
                            .expect("should exist cause of the check above")
                            .clone(),
                    )))
                } else {
                    Ok(TypeExpression::Join(ExpressionJoin {
                        values: locations
                            .values
                            .iter()
                            .map(|program_point| {
                                Arc::new(TypeExpression::Variable(ExpressionVariable::new(
                                    name.clone(),
                                    program_point.clone(),
                                )))
                            })
                            .collect(),
                    }))
                }
            }
            None => Ok(TypeExpression::Join(ExpressionJoin {
                values: imbl::OrdSet::new(),
            })),
        }
    }

    pub fn gen_expr(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        expr: &nodes::Expr,
    ) -> Result<TypeExpression, ConstraintsBuilderError> {
        match expr {
            nodes::Expr::BoolOp(expr_bool_op) => {
                self.gen_expr_bool_op(namespace, program_point, expr_bool_op)
            }
            nodes::Expr::Named(_) => todo!(),
            nodes::Expr::BinOp(expr_bin_op) => {
                self.gen_expr_bin_op(namespace, program_point, expr_bin_op)
            }
            nodes::Expr::UnaryOp(expr_unary_op) => {
                self.gen_expr_unary_op(namespace, program_point, expr_unary_op)
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
                self.gen_expr_compare(namespace, program_point, expr_compare)
            }
            nodes::Expr::Call(expr_call) => self.gen_expr_call(namespace, program_point, expr_call),
            nodes::Expr::FString(_) => todo!(),
            nodes::Expr::StringLiteral(expr_string_literal) => {
                self.gen_expr_string_literal(expr_string_literal)
            }
            nodes::Expr::BytesLiteral(expr_bytes_literal) => {
                self.gen_expr_bytes_literal(expr_bytes_literal)
            }
            nodes::Expr::NumberLiteral(expr_number_literal) => {
                self.gen_expr_number_literal(expr_number_literal)
            }
            nodes::Expr::BooleanLiteral(expr_boolean_literal) => {
                self.gen_expr_boolean_literal(expr_boolean_literal)
            }
            nodes::Expr::NoneLiteral(_) => self.gen_expr_none_literal(),
            nodes::Expr::EllipsisLiteral(_) => self.gen_expr_ellipsis_literal(),
            nodes::Expr::Attribute(expr_attribute) => {
                self.gen_expr_attribute(namespace, program_point, expr_attribute)
            }
            nodes::Expr::Subscript(expr_subscript) => {
                self.gen_expr_subscript(namespace, program_point, expr_subscript)
            }
            nodes::Expr::Starred(_) => todo!(),
            nodes::Expr::Name(expr_name) => self.gen_name(namespace, program_point, expr_name),
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

        let parameters = self.gen_parameters(ProgramPoint::Entry, &stmt_function_def.parameters)?;

        self.assign_variable(&mut target_abstract_environment, program_point, identifier);

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

        let mut variables: imbl::OrdMap<Arc<Identifier>, imbl::OrdSet<Constraint>> =
            imbl::OrdMap::new();
        for alias in &stmt_import.names {
            let module_name = self.gen_module_name(program_point, &alias.name)?;

            let mut constraints: imbl::OrdSet<Constraint> = imbl::OrdSet::new();
            let identifier = if let Some(as_name) = &alias.asname {
                let identifier = self.gen_variable_name(program_point, &as_name)?;

                constraints.insert(Constraint::Type(ConstraintDefinition::equal(
                    TypeExpression::Variable(ExpressionVariable::new(
                        identifier.clone(),
                        program_point,
                    )),
                    TypeExpression::Import(ExpressionImport::new(module_name.clone())),
                )));
                // TODO: add constraints of exceptions, pureness and mutability

                identifier
            } else {
                let identifier = Arc::new(module_name.identifiers.first().clone());

                let mut expression_option = Some(Arc::new(TypeExpression::Variable(
                    ExpressionVariable::new(identifier.clone(), program_point),
                )));

                let mut i = 1;
                while let Some(expression) = expression_option {
                    let (module_identifiers, attribute_identifiers) =
                        module_name.identifiers.split_at(i);
                    let attribute_option = attribute_identifiers.first().cloned();
                    constraints.insert(Constraint::Type(ConstraintDefinition::new(
                        expression.clone(),
                        ConstraintKind::Equal,
                        Arc::new(TypeExpression::Import(ExpressionImport::new(Arc::new(
                            QualifiedName::new(OneOrMany::many(Vec::from(module_identifiers))),
                        )))),
                    )));
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
                    i = i + 1;
                }

                identifier
            };

            self.import_module(module_name.clone())?;

            variables.insert(identifier, constraints);
        }

        for (variable, constraints) in variables {
            self.assign_variable(&mut target_abstract_environment, program_point, variable);
            target_abstract_environment
                .constraints
                .values
                .extend(constraints);
        }

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

        let type_expression =
            Arc::new(self.gen_expr(namespace, program_point, &stmt_assign.value)?);

        let mut variables: imbl::OrdMap<Arc<Identifier>, imbl::OrdSet<Arc<Constraint>>> =
            imbl::OrdMap::new();

        for target in &stmt_assign.targets {
            let Ok(target) = AssignmentTarget::try_from(target) else {
                todo!("add the right error");
            };

            match target {
                AssignmentTarget::Name(target_name) => {
                    let identifier = Arc::new(target_name);
                    let type_constraint = Arc::new(Constraint::Type(ConstraintDefinition::new(
                        Arc::new(TypeExpression::Variable(ExpressionVariable::new(
                            identifier.clone(),
                            program_point,
                        ))),
                        ConstraintKind::Equal,
                        type_expression.clone(),
                    )));
                    let exception_constraint = Arc::new(Constraint::Exception(
                        ConstraintDefinition::include(
                            ExceptionExpression::Type(type_expression.clone()),
                            ExceptionExpression::Raised(RaisedException {
                                program_points: imbl::Vector::new(),
                            }),
                        ),
                    ));

                    let (type_constraints, exception_constraints) =
                        if target_abstract_environment.current_guards.values.is_empty() {
                            (
                                imbl::OrdSet::unit(Arc::new(Constraint::Guarded(ConstraintGuarded {
                                    guards: LatticeSet::new(imbl::OrdSet::unit(Guard::Succeed(
                                        type_expression.clone(),
                                    ))),
                                    constraint: type_constraint.clone(),
                                }))),
                                imbl::OrdSet::unit(Arc::new(Constraint::Guarded(ConstraintGuarded {
                                    guards: LatticeSet::new(imbl::OrdSet::unit(Guard::Raise {
                                        expression: type_expression.clone(),
                                        exception: None,
                                    })),
                                    constraint: exception_constraint.clone(),
                                }))),
                            )
                        } else {
                            target_abstract_environment
                                .current_guards
                                .values
                                .iter()
                                .map(|guards| {
                                    (
                                        Constraint::Guarded(ConstraintGuarded {
                                            guards: LatticeSet::new(
                                                guards
                                                    .values
                                                    .update(Guard::Succeed(type_expression.clone())),
                                            ),
                                            constraint: type_constraint.clone(),
                                        }),
                                        Constraint::Guarded(ConstraintGuarded {
                                            guards: LatticeSet::new(
                                                guards
                                                    .values
                                                    .update(Guard::Raise {
                                                        expression: type_expression.clone(),
                                                        exception: None,
                                                    }),
                                            ),
                                            constraint: exception_constraint.clone(),
                                        })
                                    )
                                })
                                .collect()
                        };

                    variables.insert(identifier, type_constraints.union(exception_constraints));
                }
                AssignmentTarget::Attribute { .. } => todo!(),
                AssignmentTarget::Subscript { .. } => todo!(),
                AssignmentTarget::Starred(_) => todo!(),
                AssignmentTarget::Tuple(_) => todo!(),
                AssignmentTarget::List(_) => todo!(),
            }
        }

        target_abstract_environment.current_guards.values.clear();

        for (variable, constraints) in variables {
            self.assign_variable(&mut target_abstract_environment, program_point, variable);
            target_abstract_environment
                .constraints
                .values
                .extend(constraints);
        }

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

        match target {
            AssignmentTarget::Name(target_name) => {
                let identifier: VariableName = Arc::new(target_name);
                if let Some(value) = &stmt_ann_assign.value {
                    target_abstract_environment
                        .constraints
                        .values
                        .insert(Arc::new(Constraint::Type(ConstraintDefinition::equal(
                            TypeExpression::Variable(ExpressionVariable::new(
                                identifier.clone(),
                                program_point,
                            )),
                            self.gen_expr(namespace, program_point, value.as_ref())?,
                        ))));
                    self.assign_variable(
                        &mut target_abstract_environment,
                        program_point,
                        identifier,
                    );
                }
            }
            AssignmentTarget::Attribute { .. } => todo!(),
            AssignmentTarget::Subscript { .. } => todo!(),
            AssignmentTarget::Starred(_) => todo!("impossible"),
            AssignmentTarget::Tuple(_) => todo!("impossible"),
            AssignmentTarget::List(_) => todo!("impossible"),
        }

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

        let condition_expression =
            Arc::new(self.gen_expr(namespace, program_point, &stmt_if.test)?);

        let mut values: imbl::OrdSet<LatticeSet<Guard>> = imbl::OrdSet::new();

        for if_guard in [
            Guard::IsTrue(condition_expression.clone()),
            Guard::IsFalse(condition_expression.clone()),
            Guard::Raise {
                expression: condition_expression.clone(),
                exception: None,
            },
        ] {
            let guards = target_abstract_environment
                .current_guards
                .values
                .iter()
                .map(|guards| LatticeSet::new(guards.values.update(if_guard.clone())))
                .collect::<imbl::OrdSet<LatticeSet<Guard>>>();

            if guards.is_empty() {
                values.insert(LatticeSet::new(imbl::OrdSet::unit(if_guard)));
            } else {
                values.extend(guards);
            }
        }

        target_abstract_environment.current_guards.values = values;

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
            nodes::Stmt::While(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
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

impl CfgAnalyser<AbstractEnvironment, Namespace<AbstractEnvironment>> for ConstraintsBuilder<'_> {
    type Error = ConstraintsBuilderError;

    fn successors(
        &self,
        program_point: &ProgramPoint,
    ) -> Result<impl Iterator<Item=ProgramPoint>, ConstraintsBuilderError> {
        match self.cfg.successors(program_point) {
            Some(successors) => Ok(successors.cloned()),
            None => Err(ConstraintsBuilderError::InvalidProgramPoint {
                program_point: program_point.clone(),
            }),
        }
    }

    fn initialise_abstract_environments(
        &self,
    ) -> Result<Namespace<AbstractEnvironment>, ConstraintsBuilderError> {
        Ok(Namespace::new())
    }

    fn analyse_program_point(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        if let Some(NodeData::Statement(statement_data)) = self.cfg.node_data(&program_point) {
            self.gen_stmt(namespace, program_point, statement_data.statement())
        } else {
            Ok(AbstractEnvironment::default())
        }
    }

    fn update_abstract_environment(
        &self,
        _namespace: &Namespace<AbstractEnvironment>,
        abstract_environment: &AbstractEnvironment,
        from: ProgramPoint,
        to: ProgramPoint,
    ) -> Result<Option<AbstractEnvironment>, ConstraintsBuilderError> {
        let Some(edge_datas) = self.cfg.edge_data(from, to) else {
            return Ok(None);
        };

        let mut target_abstract_environment = abstract_environment.clone();

        target_abstract_environment.current_guards.values = target_abstract_environment
            .current_guards
            .values
            .into_iter()
            .filter_map(|guards| {
                let filtered_guards = LatticeSet::new(
                    guards
                        .values
                        .into_iter()
                        .filter(|guard| match guard {
                            Guard::IsTrue(_) => edge_datas.contains(&EdgeData::Conditional(true)),
                            Guard::IsFalse(_) => edge_datas.contains(&EdgeData::Conditional(false)),
                            Guard::Succeed(_) => {
                                edge_datas.iter().any(|edge_data| match edge_data {
                                    EdgeData::Unconditional
                                    | EdgeData::Conditional(_)
                                    | EdgeData::Match(_)
                                    | EdgeData::Break
                                    | EdgeData::Continue
                                    | EdgeData::Return => true,
                                    EdgeData::Exception(_, _) | EdgeData::UnhandledException => {
                                        false
                                    }
                                })
                            }
                            Guard::Raise { .. } => {
                                edge_datas.iter().any(|edge_data| match edge_data {
                                    EdgeData::Unconditional
                                    | EdgeData::Conditional(_)
                                    | EdgeData::Match(_)
                                    | EdgeData::Break
                                    | EdgeData::Continue
                                    | EdgeData::Return => false,
                                    EdgeData::Exception(_, _) | EdgeData::UnhandledException => {
                                        true
                                    }
                                })
                            }
                        })
                        .collect::<imbl::OrdSet<Guard>>(),
                );
                if filtered_guards.values.is_empty() {
                    None
                } else {
                    Some(filtered_guards)
                }
            })
            .collect();

        Ok(Some(target_abstract_environment))
    }

    fn get_abstract_environment(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
    ) -> Result<Option<AbstractEnvironment>, ConstraintsBuilderError> {
        Ok(namespace.abstract_environments.get(&program_point).cloned())
    }

    fn set_abstract_environment(
        &self,
        namespace: &mut Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        abstract_environment: &AbstractEnvironment,
    ) -> Result<(), ConstraintsBuilderError> {
        namespace
            .abstract_environments
            .insert(program_point, abstract_environment.clone());
        Ok(())
    }

    fn includes(
        &self,
        _namespace: &Namespace<AbstractEnvironment>,
        _program_point: ProgramPoint,
        including: &AbstractEnvironment,
        included: &AbstractEnvironment,
    ) -> Result<bool, ConstraintsBuilderError> {
        Ok(including.includes(included))
    }

    fn join(
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
    use apygen_analysis::worklist;
    use rstest::rstest;
    use std::sync::mpsc;

    fn source_code(text: &str) -> String {
        text.trim()
            .lines()
            .map(|line| line.strip_prefix("        ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n")
            .to_owned()
    }

    fn generate_constraints(source: &str) -> (Namespace<AbstractEnvironment>, Vec<String>) {
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let (import_tx, import_rx) = mpsc::channel::<ModuleName>();

        let constraints_builder = ConstraintsBuilder::new(&cfg, &import_tx);

        let namespace = worklist(&constraints_builder).expect("constraint builder should work");

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
        "{some_module@Point(0) = import(some_module)}",
        vec!["some_module"],
    )]
    #[case::import_as(
        "import some_module as mod",
        "{mod@Point(0) = import(some_module)}",
        vec!["some_module"],
    )]
    #[case::multiple_import(
        "import some_module, another_module",
        "{another_module@Point(0) = import(another_module), some_module@Point(0) = import(some_module)}",
        vec!["some_module", "another_module"],
    )]
    #[case::multiple_import_override(
        "import some_module as mod, another_module as mod",
        "{mod@Point(0) = import(another_module)}",
        vec!["some_module", "another_module"],
    )]
    #[case::int_constant_assignment(
        "a = 42",
        "{{#succeed(42)} => (a@Point(0) = 42), {#fail(42)} => (#exceptions(42) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::int_constant_assignment(
        "a = 4200000000000000000000000000",
        "{{#succeed(4200000000000000000000000000)} => (a@Point(0) = 4200000000000000000000000000), {#fail(4200000000000000000000000000)} => (#exceptions(4200000000000000000000000000) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::add_operation(
        "add = 42 + 67",
        "{{#succeed((42) + (67))} => (add@Point(0) = (42) + (67)), {#fail((42) + (67))} => (#exceptions((42) + (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::sub_operation(
        "sub = 42 - 67",
        "{{#succeed((42) - (67))} => (sub@Point(0) = (42) - (67)), {#fail((42) - (67))} => (#exceptions((42) - (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::mult_operation(
        "mult = 42 * 67",
        "{{#succeed((42) * (67))} => (mult@Point(0) = (42) * (67)), {#fail((42) * (67))} => (#exceptions((42) * (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::mat_mult_operation(
        "mat_mult = 42 @ 67",
        "{{#succeed((42) @ (67))} => (mat_mult@Point(0) = (42) @ (67)), {#fail((42) @ (67))} => (#exceptions((42) @ (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::div_operation(
        "div = 42 / 67",
        "{{#succeed((42) / (67))} => (div@Point(0) = (42) / (67)), {#fail((42) / (67))} => (#exceptions((42) / (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::floor_div_operation(
        "floor_div = 42 // 67",
        "{{#succeed((42) // (67))} => (floor_div@Point(0) = (42) // (67)), {#fail((42) // (67))} => (#exceptions((42) // (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::mod_operation(
        "mod = 42 % 67",
        "{{#succeed((42) % (67))} => (mod@Point(0) = (42) % (67)), {#fail((42) % (67))} => (#exceptions((42) % (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::pow_operation(
        "pow = 42 ** 67",
        "{{#succeed((42) ** (67))} => (pow@Point(0) = (42) ** (67)), {#fail((42) ** (67))} => (#exceptions((42) ** (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::shl_operation(
        "shl = 42 << 67",
        "{{#succeed((42) << (67))} => (shl@Point(0) = (42) << (67)), {#fail((42) << (67))} => (#exceptions((42) << (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::shr_operation(
        "shr = 42 >> 67",
        "{{#succeed((42) >> (67))} => (shr@Point(0) = (42) >> (67)), {#fail((42) >> (67))} => (#exceptions((42) >> (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::bit_or_operation(
        "bit_or = 42 | 67",
        "{{#succeed((42) | (67))} => (bit_or@Point(0) = (42) | (67)), {#fail((42) | (67))} => (#exceptions((42) | (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::bit_xor_operation(
        "bit_xor = 42 ^ 67",
        "{{#succeed((42) ^ (67))} => (bit_xor@Point(0) = (42) ^ (67)), {#fail((42) ^ (67))} => (#exceptions((42) ^ (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::bit_and_operation(
        "bit_and = 42 & 67",
        "{{#succeed((42) & (67))} => (bit_and@Point(0) = (42) & (67)), {#fail((42) & (67))} => (#exceptions((42) & (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::and_operation(
        "and_ = 42 and 67",
        "{{#succeed((42) and (67))} => (and_@Point(0) = (42) and (67)), {#fail((42) and (67))} => (#exceptions((42) and (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::or_operation(
        "or_ = 42 or 67",
        "{{#succeed((42) or (67))} => (or_@Point(0) = (42) or (67)), {#fail((42) or (67))} => (#exceptions((42) or (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::eq_operation(
        "eq = 42 == 67",
        "{{#succeed((42) == (67))} => (eq@Point(0) = (42) == (67)), {#fail((42) == (67))} => (#exceptions((42) == (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::not_eq_operation(
        "not_eq = 42 != 67",
        "{{#succeed((42) != (67))} => (not_eq@Point(0) = (42) != (67)), {#fail((42) != (67))} => (#exceptions((42) != (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::lt_operation(
        "lt = 42 < 67",
        "{{#succeed((42) < (67))} => (lt@Point(0) = (42) < (67)), {#fail((42) < (67))} => (#exceptions((42) < (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::gt_operation(
        "gt = 42 > 67",
        "{{#succeed((42) > (67))} => (gt@Point(0) = (42) > (67)), {#fail((42) > (67))} => (#exceptions((42) > (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::lte_operation(
        "lte = 42 <= 67",
        "{{#succeed((42) <= (67))} => (lte@Point(0) = (42) <= (67)), {#fail((42) <= (67))} => (#exceptions((42) <= (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::gte_operation(
        "gte = 42 >= 67",
        "{{#succeed((42) >= (67))} => (gte@Point(0) = (42) >= (67)), {#fail((42) >= (67))} => (#exceptions((42) >= (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::is_operation(
        "is_ = 42 is 67",
        "{{#succeed((42) is (67))} => (is_@Point(0) = (42) is (67)), {#fail((42) is (67))} => (#exceptions((42) is (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::is_not_operation(
        "is_not = 42 is not 67",
        "{{#succeed((42) is not (67))} => (is_not@Point(0) = (42) is not (67)), {#fail((42) is not (67))} => (#exceptions((42) is not (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::in_operation(
        "in_ = 42 in 67",
        "{{#succeed((42) in (67))} => (in_@Point(0) = (42) in (67)), {#fail((42) in (67))} => (#exceptions((42) in (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::not_in_operation(
        "not_in = 42 not in 67",
        "{{#succeed((42) not in (67))} => (not_in@Point(0) = (42) not in (67)), {#fail((42) not in (67))} => (#exceptions((42) not in (67)) ⊑ #raised_exceptions())}",
        vec![],
    )]
    #[case::not_in_operation(
        &source_code(
        r#"
        x = True

        if x:
            a = 42
        else:
            a = 67

        b = a
        "#,
        ),
        "{{#is_true(x@Point(0)), #succeed(42)} => (a@Point(2) = 42), {#is_true(x@Point(0)), #fail(42)} => (#exceptions(42) ⊑ #raised_exceptions()), {#is_false(x@Point(0)), #succeed(67)} => (a@Point(3) = 67), {#is_false(x@Point(0)), #fail(67)} => (#exceptions(67) ⊑ #raised_exceptions()), {#succeed(True)} => (x@Point(0) = True), {#succeed((a@Point(2)) ⊔ (a@Point(3)))} => (b@Point(4) = (a@Point(2)) ⊔ (a@Point(3))), {#fail(True)} => (#exceptions(True) ⊑ #raised_exceptions()), {#fail((a@Point(2)) ⊔ (a@Point(3)))} => (#exceptions((a@Point(2)) ⊔ (a@Point(3))) ⊑ #raised_exceptions())}",
        vec![],
    )]
    fn test_constraints_generation(
        #[case] source: &str,
        #[case] expected_constraints: &str,
        #[case] expected_imports: Vec<&str>,
    ) {
        let (namespace, imports) = generate_constraints(&source);

        assert_eq!(
            namespace.abstract_environments[&ProgramPoint::Exit]
                .constraints
                .to_string(),
            expected_constraints
        );
        assert_eq!(imports, expected_imports);
    }
}
