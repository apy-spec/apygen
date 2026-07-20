use crate::analysis::fmt::fmt_display_sequence;
use crate::primitives::literals::{
    LiteralBool, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInt, LiteralStr,
};
pub use apy::v1::{GenericKind, Identifier, ParameterKind, QualifiedName};
use std::fmt::{Display, Formatter};
use std::sync::Arc;

pub type ModuleName = Arc<QualifiedName>;
pub type VariableName = Arc<Identifier>;

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

    pub fn at_parent_location(&self) -> Option<Self> {
        let mut locations = self.locations.clone();
        locations.pop_back()?;
        Some(Self::new(self.module_name.clone(), locations))
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
    pub location: Location,
    pub program_entity: QualifiedLocation,
}

impl ExpressionVariable {
    pub fn new(name: VariableName, location: Location, program_entity: QualifiedLocation) -> Self {
        Self {
            name,
            location,
            program_entity,
        }
    }
}

impl Display for ExpressionVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}@{{{}[{}]}}",
            self.name, self.program_entity, self.location
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionAnnotated {
    pub annotation: Arc<Expression>,
}

impl ExpressionAnnotated {
    pub fn new(annotation: Arc<Expression>) -> Self {
        Self { annotation }
    }
}

impl Display for ExpressionAnnotated {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#annotated({})", self.annotation)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionOverride {
    pub previous: Arc<Expression>,
    pub new: Arc<Expression>,
}

impl ExpressionOverride {
    pub fn new(previous: Arc<Expression>, new: Arc<Expression>) -> Self {
        Self { previous, new }
    }
}

impl Display for ExpressionOverride {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#override(previous={}, new={})", self.previous, self.new)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityIdentifier {
    pub qualified_location: QualifiedLocation,

    pub name: VariableName,
}

impl ProgramEntityIdentifier {
    pub fn new(qualified_location: QualifiedLocation, name: VariableName) -> Self {
        Self {
            qualified_location,
            name,
        }
    }
}

impl Display for ProgramEntityIdentifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.name, self.qualified_location)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionFunction {
    pub identifier: ProgramEntityIdentifier,

    pub is_async: bool,
}

impl ExpressionFunction {
    pub fn new(identifier: ProgramEntityIdentifier, is_async: bool) -> Self {
        Self {
            identifier,
            is_async,
        }
    }
}

impl Display for ExpressionFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#function(identifier={}, async={})",
            self.identifier, self.is_async
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionClass {
    pub identifier: ProgramEntityIdentifier,
}

impl ExpressionClass {
    pub fn new(identifier: ProgramEntityIdentifier) -> Self {
        Self { identifier }
    }
}

impl Display for ExpressionClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#class(identifier={})", self.identifier)
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
    pub value: Arc<Expression>,
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
    pub target: Arc<Expression>,
    pub positional_arguments: imbl::Vector<Arc<Expression>>,
    pub keyword_arguments: imbl::Vector<KeywordArgument>,
}

impl Display for ExpressionCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})(", self.target)?;
        fmt_display_sequence(f, self.positional_arguments.iter())?;
        if !self.keyword_arguments.is_empty() {
            f.write_str(", ")?;
            fmt_display_sequence(f, self.keyword_arguments.iter())?;
        }
        f.write_str(")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionAttribute {
    pub value: Arc<Expression>,
    pub attribute: VariableName,
}

impl Display for ExpressionAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}).{}", self.value, self.attribute)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionSubscript {
    pub value: Arc<Expression>,
    pub slice: Arc<Expression>,
}

impl Display for ExpressionSubscript {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})[{}]", self.value, self.slice)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionGeneric {
    pub kind: GenericKind,

    pub bound: Arc<Expression>,

    pub constraints: imbl::Vector<Arc<Expression>>,

    pub default: Option<Arc<Expression>>,

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

impl BinaryOperator {
    pub fn symbol(&self) -> &'static str {
        match self {
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
        }
    }

    /// References:
    /// - https://docs.python.org/3/reference/datamodel.html#emulating-numeric-types
    pub fn method_name(&self) -> Option<&'static str> {
        match self {
            BinaryOperator::Add => Some("add"),
            BinaryOperator::Sub => Some("sub"),
            BinaryOperator::Mult => Some("mul"),
            BinaryOperator::MatMult => Some("matmul"),
            BinaryOperator::Div => Some("truediv"),
            BinaryOperator::FloorDiv => Some("floordiv"),
            BinaryOperator::Mod => Some("mod"),
            BinaryOperator::Pow => Some("pow"),
            BinaryOperator::LShift => Some("lshift"),
            BinaryOperator::RShift => Some("rshift"),
            BinaryOperator::BitOr => Some("or"),
            BinaryOperator::BitXor => Some("xor"),
            BinaryOperator::BitAnd => Some("and"),
            BinaryOperator::And => None,
            BinaryOperator::Or => None,
            BinaryOperator::Eq => Some("eq"),
            BinaryOperator::NotEq => Some("ne"),
            BinaryOperator::Lt => Some("lt"),
            BinaryOperator::LtE => Some("le"),
            BinaryOperator::Gt => Some("gt"),
            BinaryOperator::GtE => Some("ge"),
            BinaryOperator::Is => None,
            BinaryOperator::IsNot => None,
            BinaryOperator::In => Some("contains"),
            BinaryOperator::NotIn => None,
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.symbol())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionBinary {
    pub left: Arc<Expression>,
    pub operator: BinaryOperator,
    pub right: Arc<Expression>,
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
    pub operand: Arc<Expression>,
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
pub enum Expression {
    Variable(ExpressionVariable),
    Annotated(ExpressionAnnotated),
    Override(ExpressionOverride),
    Function(ExpressionFunction),
    Class(ExpressionClass),
    Import(ExpressionImport),
    Attribute(ExpressionAttribute),
    Subscript(ExpressionSubscript),
    Call(ExpressionCall),
    Unary(ExpressionUnary),
    Binary(ExpressionBinary),
    LiteralInteger(LiteralInt),
    LiteralFloat(LiteralFloat),
    LiteralComplex(LiteralComplex),
    LiteralString(LiteralStr),
    LiteralBytes(LiteralBytes),
    LiteralBoolean(LiteralBool),
    LiteralNone,
    LiteralEllipsis,
}

impl Expression {
    pub fn is_constant(&self) -> bool {
        matches!(
            self,
            Expression::LiteralInteger(_)
                | Expression::LiteralFloat(_)
                | Expression::LiteralComplex(_)
                | Expression::LiteralString(_)
                | Expression::LiteralBytes(_)
                | Expression::LiteralBoolean(_)
                | Expression::LiteralNone
                | Expression::LiteralEllipsis
        )
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Variable(expression_variable) => write!(f, "{}", expression_variable),
            Expression::Annotated(expression_annotated) => write!(f, "{}", expression_annotated),
            Expression::Override(expression_override) => write!(f, "{}", expression_override),
            Expression::Function(expression_function) => write!(f, "{}", expression_function),
            Expression::Class(expression_class) => write!(f, "{}", expression_class),
            Expression::Import(expression_import) => write!(f, "{}", expression_import),
            Expression::Attribute(expression_attribute) => {
                write!(f, "{}", expression_attribute)
            }
            Expression::Subscript(expression_subscript) => {
                write!(f, "{}", expression_subscript)
            }
            Expression::Call(expression_call) => write!(f, "{}", expression_call),
            Expression::Unary(expression_unary) => write!(f, "{}", expression_unary),
            Expression::Binary(expression_binary) => write!(f, "{}", expression_binary),
            Expression::LiteralInteger(literal_integer) => write!(f, "{}", literal_integer),
            Expression::LiteralFloat(literal_float) => write!(f, "{}", literal_float),
            Expression::LiteralComplex(literal_complex) => write!(f, "{}", literal_complex),
            Expression::LiteralString(literal_string) => write!(f, "{}", literal_string),
            Expression::LiteralBytes(literal_bytes) => write!(f, "{}", literal_bytes),
            Expression::LiteralBoolean(literal_boolean) => write!(f, "{}", literal_boolean),
            Expression::LiteralNone => write!(f, "None"),
            Expression::LiteralEllipsis => write!(f, "..."),
        }
    }
}
