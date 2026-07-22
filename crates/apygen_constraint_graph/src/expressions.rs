use crate::analysis::fmt::fmt_display_sequence;
pub use crate::identifiers::{
    EmptyCollectionError, Identifier, Location, ModuleName, NamedQualifiedLocation, Namespace,
    OneOrMany, ParseIdentifierError, ParseQualifiedNameError, QualifiedName, VariableName,
};
pub use crate::primitives::literals::{
    LiteralBool, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInt, LiteralStr,
};

pub use apy::v1::{GenericKind, ParameterKind};

use std::fmt::{Display, Formatter};
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionVariable {
    pub named_qualified_location: NamedQualifiedLocation,
}

impl ExpressionVariable {
    pub fn new(named_qualified_location: NamedQualifiedLocation) -> Self {
        Self {
            named_qualified_location,
        }
    }
}

impl Display for ExpressionVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}@{{{}[{}]}}",
            self.named_qualified_location.name,
            self.named_qualified_location.namespace,
            self.named_qualified_location.location
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionForwardVariable {
    pub name: VariableName,
    pub location: Location,
}

impl ExpressionForwardVariable {
    pub fn new(name: VariableName, location: Location) -> Self {
        Self {
            name,
            location,
        }
    }
}

impl Display for ExpressionForwardVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{{{}}}", self.name, self.location)
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
pub struct ExpressionFunction {
    pub program_entity: NamedQualifiedLocation,

    pub is_async: bool,
}

impl ExpressionFunction {
    pub fn new(program_entity: NamedQualifiedLocation, is_async: bool) -> Self {
        Self {
            program_entity,
            is_async,
        }
    }
}

impl Display for ExpressionFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#function(identifier={}, async={})",
            self.program_entity, self.is_async
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionClass {
    pub program_entity: NamedQualifiedLocation,
}

impl ExpressionClass {
    pub fn new(program_entity: NamedQualifiedLocation) -> Self {
        Self { program_entity }
    }
}

impl Display for ExpressionClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#class(identifier={})", self.program_entity)
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
    ForwardVariable(ExpressionForwardVariable),
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
            Expression::ForwardVariable(expression_forward_variable) => write!(f, "{}", expression_forward_variable),
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
