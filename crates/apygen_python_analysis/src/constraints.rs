use crate::abstract_environment::{
    LiteralBoolean, LiteralBytes, LiteralComplex, LiteralFloat, LiteralInteger, LiteralString,
};
use crate::genkill::assignment::AssignmentTarget;
use apy::OneOrMany;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::CfgAnalyser;
use apygen_analysis::cfg::nodes::Number;
use apygen_analysis::cfg::{Cfg, NodeData, ProgramPoint, nodes};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::Namespace;
use num_bigint::BigInt;
use num_complex::Complex64;
use num_traits::Num;
use std::sync::Arc;
use std::sync::mpsc::{SendError, Sender};
use thiserror::Error;

pub type ModuleName = Arc<QualifiedName>;
pub type VariableName = Arc<Identifier>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GuardId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopeId(pub usize);

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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionUninitialisedVariable {
    pub name: VariableName,
}

impl ExpressionUninitialisedVariable {
    pub fn new(name: VariableName) -> Self {
        Self { name }
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeywordArgument {
    pub name: Option<VariableName>,
    pub value: Arc<TypeExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionCall {
    pub target: Arc<TypeExpression>,
    pub positional_arguments: imbl::Vector<Arc<TypeExpression>>,
    pub keyword_arguments: imbl::Vector<KeywordArgument>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionAttribute {
    pub value: Arc<TypeExpression>,
    pub attribute: VariableName,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionSubscript {
    pub value: Arc<TypeExpression>,
    pub slice: Arc<TypeExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionImportFrom {
    pub module: ModuleName,
    pub attribute: VariableName,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionGuarded {
    guard: Arc<TypeExpression>,
    expression: Arc<TypeExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionJoin {
    values: imbl::OrdSet<Arc<Constraint>>,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionBinary {
    left: Arc<TypeExpression>,
    operator: BinaryOperator,
    right: Arc<TypeExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryOperator {
    Invert,
    Not,
    UAdd,
    USub,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionUnary {
    operator: UnaryOperator,
    operand: Arc<TypeExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeExpression {
    Variable(ExpressionVariable),
    UninitialisedVariable(ExpressionUninitialisedVariable),
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
    Guarded(ExpressionGuarded),
    Join(ExpressionJoin),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExceptionExpression {
    Scope(ScopeId),
    Type(Arc<TypeExpression>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScopeExpression {
    Id(ScopeId),
    FixedPoint(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstraintKind {
    Include,
    Equal,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintDefinition<T: Clone> {
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constraint {
    Type(ConstraintDefinition<TypeExpression>),
    Exception(ConstraintDefinition<ExceptionExpression>),
    Scope(ConstraintDefinition<ScopeExpression>),
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbstractEnvironment {
    pub guards: imbl::OrdSet<Arc<Constraint>>,
    pub variables: imbl::OrdMap<VariableName, imbl::OrdSet<ProgramPoint>>,
    pub contraints: imbl::OrdSet<Arc<Constraint>>,
}

impl Lattice for AbstractEnvironment {
    fn includes(&self, other: &Self) -> bool {
        other.guards.is_subset(&self.guards)
            && other
                .variables
                .is_submap_by(&self.variables, |other_locations, self_locations| {
                    self_locations
                        .iter()
                        .all(|self_location| other_locations.contains(self_location))
                })
            && other.contraints.is_subset(&self.contraints)
    }

    fn join(&self, other: &Self) -> Self {
        let mut guards = self.guards.clone();
        guards.extend(other.guards.iter().cloned());

        let mut variables = self.variables.clone();
        for (variable, locations) in &other.variables {
            match variables.entry(variable.clone()) {
                imbl::ordmap::Entry::Vacant(entry) => {
                    entry.insert(locations.clone());
                }
                imbl::ordmap::Entry::Occupied(mut entry) => {
                    entry.get_mut().extend(locations.iter().cloned());
                }
            }
        }

        let mut contraints = self.contraints.clone();
        contraints.extend(other.contraints.iter().cloned());

        Self {
            guards,
            variables,
            contraints,
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

        let Some(last_location) = abstract_environment
            .variables
            .get(&name)
            .and_then(|locations| locations.get_max())
            .copied()
        else {
            return Ok(TypeExpression::UninitialisedVariable(
                ExpressionUninitialisedVariable::new(name),
            ));
        };

        Ok(TypeExpression::Variable(ExpressionVariable::new(
            name,
            last_location,
        )))
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
            match target_abstract_environment.variables.entry(variable) {
                imbl::ordmap::Entry::Vacant(entry) => {
                    entry.insert(imbl::ordset![program_point]);
                }
                imbl::ordmap::Entry::Occupied(mut entry) => {
                    entry.get_mut().insert(program_point);
                }
            }
            target_abstract_environment.contraints.extend(constraints);
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

        let type_expression = self.gen_expr(namespace, program_point, &stmt_assign.value)?;

        let mut variables: imbl::OrdMap<Arc<Identifier>, imbl::OrdSet<Constraint>> =
            imbl::OrdMap::new();

        for target in &stmt_assign.targets {
            let Ok(target) = AssignmentTarget::try_from(target) else {
                todo!("add the right error");
            };

            match target {
                AssignmentTarget::Name(target_name) => {
                    let identifier = Arc::new(target_name);
                    variables.insert(
                        identifier.clone(),
                        imbl::OrdSet::from_iter([Constraint::Type(ConstraintDefinition::equal(
                            TypeExpression::Variable(ExpressionVariable::new(
                                identifier,
                                program_point,
                            )),
                            type_expression.clone(),
                        ))]),
                    );
                }
                AssignmentTarget::Attribute { .. } => todo!(),
                AssignmentTarget::Subscript { .. } => todo!(),
                AssignmentTarget::Starred(_) => todo!(),
                AssignmentTarget::Tuple(_) => todo!(),
                AssignmentTarget::List(_) => todo!(),
            }
        }

        for (variable, constraints) in variables {
            match target_abstract_environment.variables.entry(variable) {
                imbl::ordmap::Entry::Vacant(entry) => {
                    entry.insert(imbl::ordset![program_point]);
                }
                imbl::ordmap::Entry::Occupied(mut entry) => {
                    entry.get_mut().insert(program_point);
                }
            }
            target_abstract_environment.contraints.extend(constraints);
        }

        Ok(target_abstract_environment)
    }

    pub fn gen_stmt(
        &self,
        namespace: &Namespace<AbstractEnvironment>,
        program_point: ProgramPoint,
        stmt: &nodes::Stmt,
    ) -> Result<AbstractEnvironment, ConstraintsBuilderError> {
        match stmt {
            nodes::Stmt::FunctionDef(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
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
            nodes::Stmt::AnnAssign(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
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
            nodes::Stmt::If(_) => {
                Ok(namespace.clone_abstract_environment_or_default(program_point))
            }
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
    ) -> Result<impl Iterator<Item = ProgramPoint>, ConstraintsBuilderError> {
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
        _from: ProgramPoint,
        _to: ProgramPoint,
    ) -> Result<Option<AbstractEnvironment>, ConstraintsBuilderError> {
        Ok(Some(abstract_environment.clone()))
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
        abstract_environment: &AbstractEnvironment,
        program_point: ProgramPoint,
    ) -> Result<(), ConstraintsBuilderError> {
        namespace
            .abstract_environments
            .insert(program_point, abstract_environment.clone());
        Ok(())
    }

    fn includes(
        &self,
        _namespace: &Namespace<AbstractEnvironment>,
        including: &AbstractEnvironment,
        included: &AbstractEnvironment,
    ) -> Result<bool, ConstraintsBuilderError> {
        Ok(including.includes(included))
    }

    fn join(
        &self,
        _namespace: &Namespace<AbstractEnvironment>,
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
    use std::str::FromStr;
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

    fn program_points(namespace: &Namespace<AbstractEnvironment>) -> Vec<ProgramPoint> {
        let mut program_points = namespace
            .abstract_environments
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        program_points.sort();
        program_points
    }

    fn variable_expr(name: &str, program_point: usize) -> TypeExpression {
        TypeExpression::Variable(ExpressionVariable::new(
            Arc::new(Identifier::parse(name)),
            ProgramPoint::Point(program_point),
        ))
    }

    fn import_expr(module: &str) -> TypeExpression {
        TypeExpression::Import(ExpressionImport::new(Arc::new(QualifiedName::parse(
            module,
        ))))
    }

    fn literal_int_expr(value: i64) -> TypeExpression {
        TypeExpression::LiteralInteger(LiteralInteger::Int(value))
    }

    fn literal_bigint_expr(value: &str) -> TypeExpression {
        TypeExpression::LiteralInteger(LiteralInteger::BigInt(
            BigInt::from_str(value).expect("value should be a valid integer"),
        ))
    }

    fn binary_operation(
        left: TypeExpression,
        operator: BinaryOperator,
        right: TypeExpression,
    ) -> TypeExpression {
        TypeExpression::Binary(ExpressionBinary {
            left: Arc::new(left),
            operator,
            right: Arc::new(right),
        })
    }

    fn equal_constraint(left: TypeExpression, right: TypeExpression) -> Constraint {
        Constraint::Type(ConstraintDefinition::equal(left, right))
    }

    #[test]
    fn test_import() {
        let source = source_code(
            r#"
        import some_module
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert_eq!(imports, ["some_module"]);

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 1);

        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([equal_constraint(
                variable_expr("some_module", 0),
                import_expr("some_module"),
            )])
        );
    }

    #[test]
    fn test_import_as() {
        let source = source_code(
            r#"
        import some_module as mod
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert_eq!(imports, ["some_module"]);

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 1);

        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([equal_constraint(
                variable_expr("mod", 0),
                import_expr("some_module"),
            )])
        );
    }

    #[test]
    fn test_multiple_import() {
        let source = source_code(
            r#"
        import some_module, another_module
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert_eq!(imports, ["some_module", "another_module"]);

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 2);

        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([
                equal_constraint(variable_expr("some_module", 0), import_expr("some_module"),),
                equal_constraint(
                    variable_expr("another_module", 0),
                    import_expr("another_module"),
                )
            ])
        );
    }

    #[test]
    fn test_multiple_import_override() {
        let source = source_code(
            r#"
        import some_module as mod, another_module as mod
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert_eq!(imports, ["some_module", "another_module"]);

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 1);

        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([equal_constraint(
                variable_expr("mod", 0),
                import_expr("another_module"),
            ),])
        );
    }

    #[test]
    fn test_int_constant_assignment() {
        let source = source_code(
            r#"
        a = 42
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert!(imports.is_empty());

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 1);

        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([equal_constraint(variable_expr("a", 0), literal_int_expr(42))])
        );
    }

    #[test]
    fn test_big_int_constant_assignment() {
        let source = source_code(
            r#"
        a = 4200000000000000000000000000
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert!(imports.is_empty());

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 1);

        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([equal_constraint(
                variable_expr("a", 0),
                literal_bigint_expr("4200000000000000000000000000")
            )])
        );
    }

    #[test]
    fn test_binary_operation() {
        let source = source_code(
            r#"
        left = 42
        right = 67
        add = left + right
        sub = left - right
        mult = left * right
        mat_mult = left @ right
        div = left / right
        floor_div = left // right
        mod = left % right
        pow = left ** right
        shl = left << right
        shr = left >> right
        bit_or = left | right
        bit_xor = left ^ right
        bit_and = left & right

        and_ = left and right
        or_ = left or right

        eq = left == right
        not_eq = left != right
        lt = left < right
        gt = left > right
        lte = left <= right
        gte = left >= right
        is_ = left is right
        is_not = left is not right
        in_ = left in right
        not_in = left not in right
        "#,
        );

        let (namespace, imports) = generate_constraints(&source);

        assert!(imports.is_empty());

        assert_eq!(
            program_points(&namespace),
            [
                ProgramPoint::Entry,
                ProgramPoint::Point(0),
                ProgramPoint::Point(1),
                ProgramPoint::Point(2),
                ProgramPoint::Point(3),
                ProgramPoint::Point(4),
                ProgramPoint::Point(5),
                ProgramPoint::Point(6),
                ProgramPoint::Point(7),
                ProgramPoint::Point(8),
                ProgramPoint::Point(9),
                ProgramPoint::Point(10),
                ProgramPoint::Point(11),
                ProgramPoint::Point(12),
                ProgramPoint::Point(13),
                ProgramPoint::Point(14),
                ProgramPoint::Point(15),
                ProgramPoint::Point(16),
                ProgramPoint::Point(17),
                ProgramPoint::Point(18),
                ProgramPoint::Point(19),
                ProgramPoint::Point(20),
                ProgramPoint::Point(21),
                ProgramPoint::Point(22),
                ProgramPoint::Point(23),
                ProgramPoint::Point(24),
                ProgramPoint::Point(25),
                ProgramPoint::Point(26),
                ProgramPoint::Exit
            ]
        );

        let abstract_environment = &namespace.abstract_environments[&ProgramPoint::Exit];

        assert_eq!(abstract_environment.variables.len(), 27);

        let left = variable_expr("left", 0);
        let right = variable_expr("right", 1);
        assert_eq!(
            abstract_environment.contraints,
            imbl::OrdSet::from_iter([
                equal_constraint(left.clone(), literal_int_expr(42)),
                equal_constraint(right.clone(), literal_int_expr(67)),
                equal_constraint(
                    variable_expr("add", 2),
                    binary_operation(left.clone(), BinaryOperator::Add, right.clone())
                ),
                equal_constraint(
                    variable_expr("sub", 3),
                    binary_operation(left.clone(), BinaryOperator::Sub, right.clone())
                ),
                equal_constraint(
                    variable_expr("mult", 4),
                    binary_operation(left.clone(), BinaryOperator::Mult, right.clone())
                ),
                equal_constraint(
                    variable_expr("mat_mult", 5),
                    binary_operation(left.clone(), BinaryOperator::MatMult, right.clone())
                ),
                equal_constraint(
                    variable_expr("div", 6),
                    binary_operation(left.clone(), BinaryOperator::Div, right.clone())
                ),
                equal_constraint(
                    variable_expr("floor_div", 7),
                    binary_operation(left.clone(), BinaryOperator::FloorDiv, right.clone())
                ),
                equal_constraint(
                    variable_expr("mod", 8),
                    binary_operation(left.clone(), BinaryOperator::Mod, right.clone())
                ),
                equal_constraint(
                    variable_expr("pow", 9),
                    binary_operation(left.clone(), BinaryOperator::Pow, right.clone())
                ),
                equal_constraint(
                    variable_expr("shl", 10),
                    binary_operation(left.clone(), BinaryOperator::LShift, right.clone())
                ),
                equal_constraint(
                    variable_expr("shr", 11),
                    binary_operation(left.clone(), BinaryOperator::RShift, right.clone())
                ),
                equal_constraint(
                    variable_expr("bit_or", 12),
                    binary_operation(left.clone(), BinaryOperator::BitOr, right.clone())
                ),
                equal_constraint(
                    variable_expr("bit_xor", 13),
                    binary_operation(left.clone(), BinaryOperator::BitXor, right.clone())
                ),
                equal_constraint(
                    variable_expr("bit_and", 14),
                    binary_operation(left.clone(), BinaryOperator::BitAnd, right.clone())
                ),
                equal_constraint(
                    variable_expr("and_", 15),
                    binary_operation(left.clone(), BinaryOperator::And, right.clone())
                ),
                equal_constraint(
                    variable_expr("or_", 16),
                    binary_operation(left.clone(), BinaryOperator::Or, right.clone())
                ),
                equal_constraint(
                    variable_expr("eq", 17),
                    binary_operation(left.clone(), BinaryOperator::Eq, right.clone())
                ),
                equal_constraint(
                    variable_expr("not_eq", 18),
                    binary_operation(left.clone(), BinaryOperator::NotEq, right.clone())
                ),
                equal_constraint(
                    variable_expr("lt", 19),
                    binary_operation(left.clone(), BinaryOperator::Lt, right.clone())
                ),
                equal_constraint(
                    variable_expr("gt", 20),
                    binary_operation(left.clone(), BinaryOperator::Gt, right.clone())
                ),
                equal_constraint(
                    variable_expr("lte", 21),
                    binary_operation(left.clone(), BinaryOperator::LtE, right.clone())
                ),
                equal_constraint(
                    variable_expr("gte", 22),
                    binary_operation(left.clone(), BinaryOperator::GtE, right.clone())
                ),
                equal_constraint(
                    variable_expr("is_", 23),
                    binary_operation(left.clone(), BinaryOperator::Is, right.clone())
                ),
                equal_constraint(
                    variable_expr("is_not", 24),
                    binary_operation(left.clone(), BinaryOperator::IsNot, right.clone())
                ),
                equal_constraint(
                    variable_expr("in_", 25),
                    binary_operation(left.clone(), BinaryOperator::In, right.clone())
                ),
                equal_constraint(
                    variable_expr("not_in", 26),
                    binary_operation(left.clone(), BinaryOperator::NotIn, right.clone())
                )
            ])
        );
    }
}
