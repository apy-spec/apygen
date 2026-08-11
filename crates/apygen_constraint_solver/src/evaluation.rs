use crate::analysis::abstract_state::AbstractState;
use crate::analysis::fmt::fmt_set;
use crate::analysis::lattice::Join;
use crate::constraint_graph::expressions::{
    BinaryOperator, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionFunction, ExpressionImport, ExpressionOverride,
    ExpressionSubscript, ExpressionUnary, ExpressionVariableDefinition,
    ExpressionVariableReference, Parameter, SmolStr,
};
use crate::dependent_graph::DependentGraph;
use crate::evaluation::literal_class::method_resolution_order;
use crate::identifiers::smol_str::format_smolstr;
use crate::identifiers::{Location, NamedQualifiedLocation, Namespace};
use crate::inference::{
    BUILTINS_MODULE, Base, ClassType, Completeness, Deferred, DefinedVariables, Exception,
    ExceptionOrigin, FunctionType, ImportedModuleType, LiteralClass, LiteralFunction,
    LiteralImportedModule, LiteralMethod, NamespaceEvaluation, ProgramEvaluation, Pureness,
    RaisedExceptions, Source, Sourced, Type, TypeInstance, TypeLiteral,
};
use apygen_analysis::fmt::{fmt_display_iterator, fmt_iterator};
use apygen_constraint_graph::expressions::ParameterKind;
use apygen_inference::LiteralTuple;
use apygen_primitives::literals::LiteralStr;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::sync::Arc;
use thiserror::Error;

pub mod literal_boolean;
pub mod literal_bytes;
pub mod literal_class;
pub mod literal_complex;
pub mod literal_ellipsis;
pub mod literal_float;
pub mod literal_integer;
pub mod literal_none;
pub mod literal_string;
pub mod type_literal;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Join)]
pub struct EvaluationState {
    pub types: imbl::OrdMap<Arc<Expression>, Deferred<Sourced<Type>, Expression>>,
    pub return_value: Option<Deferred<Sourced<Type>, Expression>>,
    pub raised_exceptions: Deferred<RaisedExceptions, Expression>,
    pub defined_variables: DefinedVariables,
    pub type_variables: imbl::OrdMap<SmolStr, imbl::OrdSet<(Arc<Namespace>, Location)>>,
}

impl EvaluationState {
    pub fn get_variable_type(
        &self,
        variable_name: &SmolStr,
        locations: &imbl::OrdSet<(Arc<Namespace>, Location)>,
    ) -> Option<Deferred<Sourced<Type>, Expression>> {
        let mut ty = Deferred::known(Sourced::specified(Type::Never));
        for (namespace, location) in locations {
            let variable = Expression::VariableDefinition(ExpressionVariableDefinition::new(
                NamedQualifiedLocation::new(
                    variable_name.clone(),
                    location.clone(),
                    namespace.clone(),
                ),
            ));
            ty = ty.join(&self.types.get(&variable).cloned()?);
        }
        Some(ty)
    }

    pub fn get_type_attribute(
        &self,
        name: &SmolStr,
    ) -> Option<Deferred<Sourced<Type>, Expression>> {
        self.type_variables
            .get(name)
            .map(|locations| self.get_variable_type(name, locations).unwrap_or_default())
    }
}

impl Display for EvaluationState {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            for (expression, eval) in &self.types {
                writeln!(f, "{} = {}", expression, eval)?;
            }
            writeln!(f, "#variables = {}", self.defined_variables)?;
            writeln!(f, "#raise = {}", self.raised_exceptions)?;
            if let Some(return_value) = &self.return_value {
                writeln!(f, "#return = {}", return_value)?;
            }
            Ok(())
        } else {
            f.write_str("(evaluations: ")?;
            fmt_set(f, self.types.iter(), |f, (expression, eval)| {
                write!(f, "{}: {}", expression, eval)
            })?;
            if let Some(return_value) = &self.return_value {
                writeln!(f, ", return: {}", return_value)?;
            } else {
                f.write_str(", return: None")?;
            }
            write!(
                f,
                ", raised: {}, defined_variables: {})",
                self.raised_exceptions, self.defined_variables
            )
        }
    }
}

impl NamespaceEvaluation for EvaluationState {
    type Expression = Expression;

    fn attributes(
        &self,
    ) -> impl Iterator<Item = (&SmolStr, Deferred<Sourced<Type>, Self::Expression>)> {
        self.defined_variables
            .names
            .iter()
            .map(|(variable_name, locations)| {
                (
                    variable_name,
                    self.get_variable_type(variable_name, locations)
                        .unwrap_or_default(),
                )
            })
    }

    fn get_attribute(&self, name: &SmolStr) -> Option<Deferred<Sourced<Type>, Self::Expression>> {
        self.defined_variables
            .names
            .get(name)
            .map(|locations| self.get_variable_type(name, locations).unwrap_or_default())
    }

    fn raised_exceptions(&self) -> &Deferred<RaisedExceptions, Self::Expression> {
        &self.raised_exceptions
    }

    fn return_value(&self) -> &Option<Deferred<Sourced<Type>, Self::Expression>> {
        &self.return_value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct BoundArguments {
    pub variables: BTreeMap<Parameter, Sourced<Type>>,
}

impl BoundArguments {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Display for BoundArguments {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_iterator(f, self.variables.iter(), ", ", |f, (identifier, ty)| {
            write!(f, "{} = {}", identifier.name, ty)
        })
    }
}

#[derive(Error, Debug)]
pub enum BindError {
    #[error("Missing positional argument")]
    MissingPositionalArgument,
    #[error("Missing positional or keyword argument")]
    MissingPositionalOrKeywordArgument,
    #[error("Missing keyword argument")]
    MissingKeywordArgument,
    #[error("Too many positional arguments provided")]
    TooManyPositionalArguments,
    #[error("Unexpected keyword argument provided")]
    UnexpectedKeywordArgument,
    #[error("Multiple values for the same parameter provided")]
    MultipleValuesForParameter,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Arguments {
    pub positional: Vec<Type>,
    pub keyword: BTreeMap<SmolStr, Type>,
}

impl Arguments {
    pub fn new() -> Self {
        Self {
            positional: Vec::new(),
            keyword: BTreeMap::new(),
        }
    }

    pub fn with_self(mut self, self_type: Type) -> Self {
        self.positional.insert(0, self_type);
        self
    }

    pub fn add_positional_argument(mut self, argument: Type) -> Self {
        self.positional.push(argument);
        self
    }

    pub fn add_keyword_argument(mut self, identifier: SmolStr, argument: Type) -> Self {
        self.keyword.insert(identifier, argument);
        self
    }

    pub fn bind(&self, parameters: Vec<Parameter>) -> Result<BoundArguments, BindError> {
        let mut bindings = BoundArguments::new();
        let mut positional_iter = self.positional.iter().cloned();
        for parameter in &parameters {
            match parameter.kind {
                ParameterKind::PositionalOnly => {
                    if let Some(argument) = positional_iter.next() {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument));
                    } else if !parameter.is_optional {
                        return Err(BindError::MissingPositionalArgument);
                    }
                }
                ParameterKind::PositionalOrKeyword => {
                    if let Some(argument) = positional_iter.next() {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if let Some(argument) = self.keyword.get(parameter.name.name()) {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if !parameter.is_optional {
                        return Err(BindError::MissingPositionalOrKeywordArgument);
                    }
                }
                ParameterKind::VarPositional => {
                    let arguments = if self.positional.is_empty() {
                        imbl::vector![Arc::new(Type::Literal(Arc::new(TypeLiteral::Tuple(
                            LiteralTuple {
                                value: imbl::Vector::new()
                            }
                        ))))]
                    } else {
                        let mut var_positional_arguments = Type::Never;

                        while let Some(argument) = positional_iter.next() {
                            var_positional_arguments = var_positional_arguments.join(&argument);
                        }

                        imbl::vector![Arc::new(var_positional_arguments)]
                    };

                    let ty = Type::Any; // TODO: fix

                    bindings
                        .variables
                        .insert(parameter.clone(), Sourced::inferred(ty));
                }
                ParameterKind::KeywordOnly => {
                    if bindings.variables.contains_key(&parameter) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    if let Some(argument) = self.keyword.get(parameter.name.name()) {
                        bindings
                            .variables
                            .insert(parameter.clone(), Sourced::inferred(argument.clone()));
                    } else if !parameter.is_optional {
                        return Err(BindError::MissingKeywordArgument);
                    }
                }
                ParameterKind::VarKeyword => {
                    if bindings.variables.contains_key(&parameter) {
                        return Err(BindError::MultipleValuesForParameter);
                    }

                    let mut var_keyword_arguments = Type::Never;

                    for (key, argument) in &self.keyword {
                        if !parameters.iter().any(|p| p.name.name() == key) {
                            var_keyword_arguments = var_keyword_arguments.join(argument);
                        }
                    }

                    let str_literal = Arc::new(Type::new_literal(TypeLiteral::String(
                        LiteralStr::from("str"),
                    )));

                    let arguments = imbl::vector![str_literal, Arc::new(var_keyword_arguments)];

                    let ty = Type::Any; // TODO: fix

                    bindings
                        .variables
                        .insert(parameter.clone(), Sourced::inferred(ty));
                }
            }
        }

        if positional_iter.next().is_some() {
            return Err(BindError::TooManyPositionalArguments);
        }

        if self.keyword.keys().any(|key| {
            !bindings
                .variables
                .keys()
                .any(|variable| variable.name.name() == key)
        }) {
            return Err(BindError::UnexpectedKeywordArgument);
        }

        Ok(bindings)
    }
}

impl Display for Arguments {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_display_iterator(f, self.positional.iter(), ", ")?;
        if !self.keyword.is_empty() {
            fmt_iterator(f, self.keyword.iter(), ", ", |f, (identifier, ty)| {
                write!(f, "{}={}", identifier, ty)
            })?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Call<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> {
    pub target: Arc<Namespace>,
    pub context: S,
    pub arguments: BoundArguments,
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Call<S> {
    pub fn new(target: Arc<Namespace>, context: S, arguments: BoundArguments) -> Self {
        Self {
            target,
            context,
            arguments,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub struct Definition {
    pub parameters: imbl::Vector<(Parameter, Option<Deferred<Sourced<Type>, Expression>>)>,
    pub exceptions: Deferred<RaisedExceptions, Expression>,
    pub return_value: Option<Deferred<Sourced<Type>, Expression>>,
}

impl Definition {
    pub fn new(
        parameters: imbl::Vector<(Parameter, Option<Deferred<Sourced<Type>, Expression>>)>,
        exceptions: Deferred<RaisedExceptions, Expression>,
        return_value: Option<Deferred<Sourced<Type>, Expression>>,
    ) -> Self {
        Self {
            parameters,
            exceptions,
            return_value,
        }
    }
}

#[derive(Clone, Join)]
pub struct PyEffects<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> {
    pub exceptions: RaisedExceptions,
    pub pureness: Pureness,
    pub completeness: Completeness,
    pub calls: imbl::OrdSet<Call<S>>,
    pub definitions: imbl::OrdSet<(Namespace, Definition)>,
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> PyEffects<S> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_exceptions(mut self, exceptions: RaisedExceptions) -> Self {
        self.exceptions = exceptions;
        self
    }

    pub fn with_pureness(mut self, pureness: Pureness) -> Self {
        self.pureness = pureness;
        self
    }

    pub fn with_completeness(mut self, completeness: Completeness) -> Self {
        self.completeness = completeness;
        self
    }

    pub fn with_calls(mut self, calls: imbl::OrdSet<Call<S>>) -> Self {
        self.calls = calls;
        self
    }

    pub fn with_definitions(mut self, definitions: imbl::OrdSet<(Namespace, Definition)>) -> Self {
        self.definitions = definitions;
        self
    }

    pub fn consume<T>(&mut self, eval: PyValueEval<T, S>) -> T
    where
        S: Clone + Ord,
    {
        self.exceptions = self.exceptions.join(&eval.effects.exceptions);
        self.pureness = self.pureness.join(&eval.effects.pureness);
        self.completeness = self.completeness.join(&eval.effects.completeness);
        self.calls = self.calls.join(&eval.effects.calls);
        self.definitions = self.definitions.join(&eval.effects.definitions);
        eval.value
    }
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Default for PyEffects<S> {
    fn default() -> Self {
        Self {
            exceptions: Default::default(),
            pureness: Default::default(),
            completeness: Default::default(),
            calls: Default::default(),
            definitions: Default::default(),
        }
    }
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Display for PyEffects<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} - {} - {})",
            self.exceptions, self.pureness, self.completeness
        )
    }
}

#[derive(Clone, Join)]
pub struct PyValueEval<T, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> {
    pub value: T,
    pub effects: PyEffects<S>,
}

impl<T, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> PyValueEval<T, S> {
    pub fn new(value: T, effects: PyEffects<S>) -> Self {
        PyValueEval { value, effects }
    }

    pub fn with_default_effects(value: T) -> Self {
        PyValueEval::new(value, PyEffects::default())
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> PyValueEval<U, S> {
        PyValueEval {
            value: f(self.value),
            effects: self.effects,
        }
    }

    pub fn extend_effects(mut self, effects: &PyEffects<S>) -> Self
    where
        S: Clone + Ord,
    {
        self.effects = self.effects.join(effects);
        self
    }
}

impl<T: Default, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Default
    for PyValueEval<T, S>
{
    fn default() -> Self {
        Self::new(Default::default(), Default::default())
    }
}

impl<T: Display, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Display
    for PyValueEval<T, S>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ➤ {})", self.value, self.effects)
    }
}

pub type PyTypeEval<S> = PyValueEval<Sourced<Type>, S>;

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> PyTypeEval<S> {
    pub fn never() -> Self {
        PyTypeEval::with_default_effects(Sourced::inferred(Type::Never))
    }

    pub fn raise(exception: Exception) -> Self {
        PyTypeEval::new(
            Sourced::inferred(Type::NoReturn),
            PyEffects::new().with_exceptions(RaisedExceptions::raise(exception)),
        )
    }

    pub fn unknown() -> Self {
        PyTypeEval::new(
            Sourced::inferred(Type::Any),
            PyEffects::new()
                .with_exceptions(RaisedExceptions::raise(Exception::any()))
                .with_pureness(Pureness::Impure)
                .with_completeness(Completeness::Partial),
        )
    }
}

#[macro_export]
macro_rules! is_sourced_type_unreachable {
    ($ty:expr) => {
        matches!($ty.data, Type::Never | Type::NoReturn)
    };
}

#[macro_export]
macro_rules! pytype_consume_or_return_ok {
    ($effects:expr, $eval:expr) => {{
        let ty = $effects.consume($eval);

        if matches!(ty.source, Source::Inferred) && is_sourced_type_unreachable!(ty) {
            return Ok(PyTypeEval::new(ty, $effects));
        }

        ty
    }};
}

pub fn gen_bool_value(ty: &Type) -> Option<bool> {
    match ty {
        Type::Any => None,
        Type::Never => None,
        Type::NoReturn => None,
        Type::Instance(_) => None,
        Type::Union(_) => None,
        Type::Intersection(_) => None,
        Type::Literal(literal_value) => type_literal::as_boolean(literal_value.as_ref()),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EdgeCall {
    pub location: Location,
    pub context: ProgramEvaluation<EvaluationState>,
    pub arguments: BoundArguments,
}

impl EdgeCall {
    pub fn new(
        location: Location,
        context: ProgramEvaluation<EvaluationState>,
        arguments: BoundArguments,
    ) -> Self {
        Self {
            location,
            context,
            arguments,
        }
    }
}

impl Display for EdgeCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at {}", self.arguments, self.location)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EdgeKind {
    Definition,
    Call(EdgeCall),
}

impl Display for EdgeKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            EdgeKind::Definition => f.write_str("Definition"),
            EdgeKind::Call(call) => write!(f, "Call({})", call),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum EvaluatorMode {
    Normal,
    Annotation,
}

#[derive(Debug, Clone, Error)]
pub enum EvaluationError {
    #[error("the expression uses a deferred expression")]
    Deferred,
    #[error("the expression is an invalid annotation")]
    InvalidAnnotation,
    #[error("failed to get the reference to the qualified name {module}.{id}")]
    QualifiedNameReferenceError { module: SmolStr, id: SmolStr },
    #[error("failed to get the reference to the namespace {0}")]
    NamespaceReferenceError(Namespace),
}

pub struct ExpressionEvaluator<
    'a,
    S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
> {
    pub mode: EvaluatorMode,
    pub namespace: &'a Namespace,
    pub abstract_state: &'a S,
    pub namespace_dependent_graph: &'a dyn DependentGraph<
        Node = Namespace,
        NodeData = Definition,
        EdgeData = imbl::OrdSet<EdgeKind>,
    >,
    pub expression: Option<&'a Expression>,
}

impl<'a, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord>
    ExpressionEvaluator<'a, S>
{
    pub fn new(
        mode: EvaluatorMode,
        namespace: &'a Namespace,
        abstract_state: &'a S,
        namespace_dependent_graph: &'a dyn DependentGraph<
            Node = Namespace,
            NodeData = Definition,
            EdgeData = imbl::OrdSet<EdgeKind>,
        >,
        expression: Option<&'a Expression>,
    ) -> Self {
        Self {
            mode,
            namespace,
            abstract_state,
            namespace_dependent_graph,
            expression,
        }
    }

    pub fn with_namespace(&self, namespace: &'a Namespace) -> Self {
        Self::new(
            self.mode,
            namespace,
            self.abstract_state,
            self.namespace_dependent_graph,
            self.expression,
        )
    }

    pub fn with_mode(&self, mode: EvaluatorMode) -> Self {
        Self::new(
            mode,
            self.namespace,
            self.abstract_state,
            self.namespace_dependent_graph,
            self.expression,
        )
    }

    pub fn extract_deferred<T: Clone>(
        deferred: Deferred<T, Expression>,
    ) -> Result<T, EvaluationError> {
        match deferred.to_value() {
            Some(sourced) => Ok(sourced),
            None => Err(EvaluationError::Deferred),
        }
    }

    pub fn find_type(&self, module: &SmolStr, name: &SmolStr) -> Result<Type, EvaluationError> {
        match TypeInstance::from_qualified_name(self.abstract_state, module, name) {
            Some(type_instance) => Ok(Type::Instance(type_instance)),
            None => Err(EvaluationError::QualifiedNameReferenceError {
                module: module.clone(),
                id: name.clone(),
            }),
        }
    }

    pub fn evaluate_expression_variable_definition(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_variable_definition: &'a ExpressionVariableDefinition,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let namespace = expression_variable_definition.namespace();

        let Some(evaluation_state) = self.abstract_state.get(namespace) else {
            return Err(EvaluationError::NamespaceReferenceError(
                namespace.as_ref().clone(),
            ));
        };

        Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
            evaluation_state
                .types
                .get(&Expression::VariableDefinition(
                    expression_variable_definition.clone(),
                ))
                .cloned()
                .unwrap_or_default(),
        )?))
    }

    pub fn evaluate_expression_variable_reference(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_variable_reference: &'a ExpressionVariableReference,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        if let Some(evaluation_state) = self.abstract_state.get(&self.namespace) {
            if let Some(deferred_ty) = if matches!(self.mode, EvaluatorMode::Normal) {
                evaluation_state.get_attribute(&expression_variable_reference.name)
            } else {
                evaluation_state.get_type_attribute(&expression_variable_reference.name)
            } {
                return Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
                    deferred_ty,
                )?));
            }
        };

        if let Some(parent_namespace) = self.namespace.parent() {
            return self
                .with_namespace(parent_namespace.as_ref())
                .evaluate_expression_variable_reference(
                    known_evaluations,
                    expression_variable_reference,
                );
        };

        if *self.namespace.module_name() != BUILTINS_MODULE {
            return self
                .with_namespace(&Namespace::Module(BUILTINS_MODULE))
                .evaluate_expression_variable_reference(
                    known_evaluations,
                    expression_variable_reference,
                );
        }

        if matches!(self.mode, EvaluatorMode::Normal) {
            Ok(PyTypeEval::raise(Exception::new(
                Sourced::inferred(
                    self.find_type(&BUILTINS_MODULE, &SmolStr::new_static("NameError"))?,
                ),
                ExceptionOrigin::Specified, // TODO: fix origin
            )))
        } else {
            Err(EvaluationError::InvalidAnnotation)
        }
    }

    pub fn evaluate_expression_annotated(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_annotated: &'a ExpressionAnnotated,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let annotation_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.with_mode(EvaluatorMode::Annotation)
                .evaluate_expression(known_evaluations, &expression_annotated.annotation)?
        );

        let Type::Literal(type_literal) = annotation_sourced_ty.data else {
            return Err(EvaluationError::InvalidAnnotation);
        };

        let base = match type_literal.as_ref() {
            TypeLiteral::Class(literal_class) => Base::Class(literal_class.clone()),
            TypeLiteral::TypeAlias(literal_type_alias) => {
                Base::TypeAlias(literal_type_alias.clone())
            }
            TypeLiteral::Generic(literal_generic) => Base::Generic(literal_generic.clone()),
            _ => return Err(EvaluationError::InvalidAnnotation),
        };

        Ok(PyTypeEval::new(
            Sourced::specified(Type::Instance(TypeInstance {
                base,
                arguments: imbl::Vector::new(),
            })),
            effects,
        ))
    }

    pub fn evaluate_expression_override(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_override: &'a ExpressionOverride,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        self.evaluate_expression(known_evaluations, &expression_override.previous)
    }

    pub fn evaluate_expression_function(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_function: &'a ExpressionFunction,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let mut parameters = imbl::Vector::new();
        for (parameter, expression) in &expression_function.parameters {
            parameters.push_back((
                parameter.clone(),
                if let Some(expression) = expression {
                    Some(
                        if let Ok(eval) = self.evaluate_expression(known_evaluations, expression) {
                            Deferred::known(pytype_consume_or_return_ok!(effects, eval))
                        } else {
                            Deferred::unknown(imbl::OrdSet::unit(expression.clone()))
                        },
                    )
                } else {
                    None
                },
            ))
        }

        let mut raised_exceptions = Deferred::known(RaisedExceptions::default());
        for expression in &expression_function.exceptions {
            if let Ok(eval) = self.evaluate_expression(known_evaluations, expression) {
                raised_exceptions.value.exceptions.insert(Exception::new(
                    pytype_consume_or_return_ok!(effects, eval),
                    ExceptionOrigin::Specified,
                ));
            } else {
                raised_exceptions.expressions.insert(expression.clone());
            }
        }

        let return_value = if let Some(return_value) = &expression_function.return_value {
            Some(
                if let Ok(eval) = self.evaluate_expression(known_evaluations, return_value) {
                    Deferred::known(pytype_consume_or_return_ok!(effects, eval))
                } else {
                    Deferred::unknown(imbl::OrdSet::unit(return_value.clone()))
                },
            )
        } else {
            None
        };

        Ok(PyTypeEval::new(
            Sourced::inferred(Type::new_literal(TypeLiteral::Function(LiteralFunction {
                value: Arc::new(FunctionType {
                    program_entity: expression_function.program_entity.clone(),
                    generics: Default::default(),
                    is_async: expression_function.is_async,
                }),
            }))),
            effects.with_definitions(imbl::OrdSet::unit((
                Namespace::NamedProgramEntity(expression_function.program_entity.clone()),
                Definition::new(parameters, raised_exceptions, return_value),
            ))),
        ))
    }

    pub fn evaluate_expression_class(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_class: &'a ExpressionClass,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let class_namespace =
            Namespace::NamedProgramEntity(expression_class.program_entity.clone());

        Ok(PyTypeEval::new(
            Sourced::inferred(Type::new_literal(TypeLiteral::Class(LiteralClass {
                value: Arc::new(ClassType {
                    program_entity: expression_class.program_entity.clone(),
                    generics: Default::default(),
                    bases: Default::default(),
                    keyword_arguments: Default::default(),
                    is_abstract: false,
                }),
            }))),
            PyEffects::new()
                .with_definitions(imbl::OrdSet::unit((class_namespace, Definition::default()))),
        ))
    }

    pub fn evaluate_expression_import(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_import: &'a ExpressionImport,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let namespace = Namespace::Module(expression_import.module.clone());

        if self.abstract_state.contains(&namespace) {
            Ok(PyTypeEval::with_default_effects(Sourced::inferred(
                Type::new_literal(TypeLiteral::ImportedModule(LiteralImportedModule {
                    value: Arc::new(ImportedModuleType {
                        module: expression_import.module.clone(),
                    }),
                })),
            )))
        } else {
            Ok(PyTypeEval::unknown())
        }
    }

    /// References: https://docs.python.org/3/howto/descriptor.html
    fn evaluate_attributes(
        &mut self,
        value_ty: &Type,
        name: &SmolStr,
        instance_arguments: Option<&imbl::Vector<Arc<Type>>>,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        match value_ty {
            Type::Instance(type_instance) => self.evaluate_attributes(
                &type_instance.base.as_type(),
                name,
                Some(&type_instance.arguments),
            ),
            Type::Union(type_union) => {
                let mut eval = PyTypeEval::never();
                for ty in type_union.types() {
                    eval = eval.join(&self.evaluate_attributes(ty, name, None)?);
                }
                Ok(eval)
            }
            Type::Intersection(type_intersection) => {
                let mut eval = PyTypeEval::never();
                for ty in type_intersection {
                    eval = eval.join(&self.evaluate_attributes(ty, name, None)?);
                }
                Ok(eval)
            }
            Type::Literal(type_literal) => match type_literal.as_ref() {
                TypeLiteral::Class(literal_class) => {
                    // TODO: add support for descriptors
                    let Some(mro) = method_resolution_order(literal_class) else {
                        return Ok(PyTypeEval::raise(Exception::new(
                            Sourced::inferred(Type::Any),
                            ExceptionOrigin::Specified, // TODO: fix origin
                        )));
                    };

                    for class in mro {
                        let class_namespace =
                            Namespace::NamedProgramEntity(class.value.program_entity.clone());

                        let Some(evaluation_state) = self.abstract_state.get(&class_namespace)
                        else {
                            return Err(EvaluationError::Deferred);
                        };

                        let Some(deferred_ty) = evaluation_state.get_attribute(name) else {
                            continue;
                        };

                        let mut sourced_ty = Self::extract_deferred(deferred_ty)?;

                        if let Type::Literal(type_literal) = &sourced_ty.data {
                            if let TypeLiteral::Function(literal_function) = type_literal.as_ref() {
                                if let Some(arguments) = instance_arguments {
                                    sourced_ty = Sourced::inferred(Type::new_literal(
                                        TypeLiteral::Method(LiteralMethod {
                                            class: class.value.clone(),
                                            function: literal_function.value.clone(),
                                            arguments: arguments.clone(),
                                        }),
                                    ));
                                }
                            }
                        };

                        return Ok(PyTypeEval::with_default_effects(sourced_ty));
                    }

                    Ok(PyTypeEval::unknown())
                }
                _ => {
                    let Some(type_instance) = type_literal.as_type_instance(self.abstract_state)
                    else {
                        let (module, class_name) = type_literal.type_name();
                        return Err(EvaluationError::QualifiedNameReferenceError {
                            module,
                            id: SmolStr::new_static(class_name),
                        });
                    };
                    self.evaluate_attributes(&Type::Instance(type_instance), name, None)
                }
            },
            _ => Ok(PyTypeEval::unknown()), // TODO: add missing cases
        }
    }

    pub fn evaluate_expression_attribute(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_attribute: &'a ExpressionAttribute,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let value_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_attribute.value)?
        );

        self.evaluate_attributes(
            &value_sourced_ty.data,
            &expression_attribute.attribute,
            None,
        )
    }

    pub fn evaluate_expression_subscript(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_subscript: &'a ExpressionSubscript,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let value_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_subscript.value)?
        );
        let get_item_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_attributes(
                &value_sourced_ty.data,
                &SmolStr::new_static("__getitem__"),
                None,
            )?
        );
        let slice_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_subscript.slice)?
        );

        let sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_call(
                known_evaluations,
                &get_item_sourced_ty.data,
                Arguments::new().add_positional_argument(slice_sourced_ty.data)
            )?
        );

        Ok(PyTypeEval::new(sourced_ty, effects))
    }

    pub fn evaluate_call(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        ty: &Type,
        arguments: Arguments,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let Type::Literal(literal) = ty else {
            return Ok(PyTypeEval::unknown()); // TODO: add support for unions, etc
        };

        match literal.as_ref() {
            TypeLiteral::Function(literal_function) => {
                let function_namespace =
                    Namespace::NamedProgramEntity(literal_function.value.program_entity.clone());

                let Some(evaluation_state) = self.abstract_state.get(&function_namespace) else {
                    return Ok(PyTypeEval::unknown());
                };

                let bound_arguments = arguments
                    .bind(
                        self.namespace_dependent_graph
                            .get_node_data(&function_namespace)
                            .unwrap()
                            .parameters
                            .iter()
                            .map(|(parameter, _)| parameter.clone())
                            .collect::<Vec<_>>(),
                    )
                    .unwrap_or_default();

                Ok(PyTypeEval::new(
                    Sourced::inferred(if let Some(return_value) = &evaluation_state.return_value {
                        Self::extract_deferred(return_value.clone())?.data.clone()
                    } else {
                        Type::Any
                    }),
                    PyEffects::new()
                        .with_exceptions(Self::extract_deferred(
                            evaluation_state.raised_exceptions.clone(),
                        )?)
                        .with_calls(imbl::OrdSet::unit(Call::new(
                            Arc::new(function_namespace),
                            self.abstract_state.clone(),
                            bound_arguments,
                        ))),
                ))
            }
            TypeLiteral::Method(literal_method) => self.evaluate_call(
                known_evaluations,
                &Type::Literal(Arc::new(TypeLiteral::Function(LiteralFunction {
                    value: literal_method.function.clone(),
                }))),
                arguments.with_self(Type::Literal(Arc::new(TypeLiteral::Class(LiteralClass {
                    value: literal_method.class.clone(),
                })))),
            ),
            TypeLiteral::Class(literal_class) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::Instance(TypeInstance {
                    base: Base::Class(literal_class.clone()),
                    arguments: imbl::Vector::new(),
                })),
            )),
            _ => Ok(PyTypeEval::unknown()), // TODO: add support for classes, etc
        }
    }

    pub fn evaluate_expression_call(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_call: &'a ExpressionCall,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_call.target)?
        );

        let mut arguments = Arguments::new();

        for argument in &expression_call.positional_arguments {
            let argument_sourced_ty = pytype_consume_or_return_ok!(
                effects,
                self.evaluate_expression(known_evaluations, &argument)?
            );

            arguments.positional.push(argument_sourced_ty.data);
        }
        for keyword_argument in &expression_call.keyword_arguments {
            if let Some(name) = &keyword_argument.name {
                let keyword_argument_sourced_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_expression(known_evaluations, &keyword_argument.value)?
                );

                arguments
                    .keyword
                    .insert(name.clone(), keyword_argument_sourced_ty.data);
            }
        }

        self.evaluate_call(known_evaluations, &sourced_ty.data, arguments)
    }

    pub fn evaluate_expression_unary(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_unary: &'a ExpressionUnary,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let operand_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_unary.operand)?
        );

        let sourced_ty = match operand_sourced_ty.data {
            Type::Literal(type_literal) => {
                pytype_consume_or_return_ok!(
                    effects,
                    type_literal::call_unary_op(type_literal.as_ref(), expression_unary.operator)
                )
            }
            Type::Never | Type::NoReturn => unreachable!("operand_ty should not be unreachable"),
            _ => return Ok(PyTypeEval::unknown()), // TODO: add other cases
        };

        Ok(PyTypeEval::new(sourced_ty, effects))
    }

    pub fn evaluate_binary_operation(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        left_ty: &Type,
        operator: BinaryOperator,
        right_ty: &Type,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        match (left_ty, right_ty) {
            (Type::Literal(left), Type::Literal(right)) => Ok(type_literal::call_binary_op(
                left.as_ref(),
                operator,
                right.as_ref(),
            )),
            (Type::Instance(_), _) => {
                let mut effects = PyEffects::new();

                let Some(method_name) = operator.method_name() else {
                    return Ok(PyTypeEval::unknown()); // TODO: fix
                };

                let method_sourced_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_attributes(
                        left_ty,
                        &format_smolstr!("__{}__", method_name),
                        None
                    )?
                );

                let return_type = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_call(
                        known_evaluations,
                        &method_sourced_ty.data,
                        Arguments::new().add_positional_argument(right_ty.clone()),
                    )?
                );

                Ok(PyTypeEval::new(return_type, effects))
            }
            (_, Type::Instance(_)) => {
                let mut effects = PyEffects::new();

                let Some(method_name) = operator.method_name() else {
                    return Ok(PyTypeEval::unknown()); // TODO: fix
                };

                let method_sourced_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_attributes(
                        right_ty,
                        &format_smolstr!("__r{}__", method_name),
                        None
                    )?
                );

                let return_type = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_call(
                        known_evaluations,
                        &method_sourced_ty.data,
                        Arguments::new().add_positional_argument(left_ty.clone()),
                    )?
                );

                Ok(PyTypeEval::new(return_type, effects))
            }
            (Type::Union(left_type_union), Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in left_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        known_evaluations,
                        ty,
                        operator,
                        right_ty,
                    )?);
                }
                for ty in right_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        known_evaluations,
                        left_ty,
                        operator,
                        ty,
                    )?);
                }
                Ok(type_eval)
            }
            (Type::Union(left_type_union), _) => {
                let mut type_eval = PyTypeEval::never();
                for ty in left_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        known_evaluations,
                        ty,
                        operator,
                        right_ty,
                    )?);
                }
                Ok(type_eval)
            }
            (_, Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in right_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        known_evaluations,
                        left_ty,
                        operator,
                        ty,
                    )?);
                }
                Ok(type_eval)
            }
            (Type::Any, _) | (_, Type::Any) => Ok(PyTypeEval::unknown()),
            (Type::Never, _) | (_, Type::Never) | (Type::NoReturn, _) | (_, Type::NoReturn) => {
                unreachable!()
            }
            _ => Ok(PyTypeEval::unknown()), // TODO: add support for the rest
        }
    }

    pub fn evaluate_expression_binary(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression_binary: &'a ExpressionBinary,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let left_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_binary.left)?
        );
        let right_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(known_evaluations, &expression_binary.right)?
        );

        let sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_binary_operation(
                known_evaluations,
                &left_sourced_ty.data,
                expression_binary.operator,
                &right_sourced_ty.data
            )?
        );

        Ok(PyTypeEval::new(sourced_ty, effects))
    }

    pub fn evaluate_expression(
        &mut self,
        known_evaluations: &mut BTreeMap<Namespace, BTreeMap<Expression, PyTypeEval<S>>>,
        expression: &'a Expression,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        if let Some(expressions) = known_evaluations.get(self.namespace) {
            if let Some(eval) = expressions.get(expression) {
                return Ok(eval.clone());
            }
        }

        let Some(evaluation_state) = self.abstract_state.get(self.namespace) else {
            return Err(EvaluationError::NamespaceReferenceError(
                self.namespace.clone(),
            ));
        };

        if let Some(deferred_ty) = evaluation_state.types.get(expression) {
            if let Some(evaluation_expression) = self.expression {
                if evaluation_expression == expression {
                    return Err(EvaluationError::Deferred);
                }
            }

            self.expression = Some(expression);

            let mut effects = PyEffects::new();
            let mut sourced_ty = deferred_ty.value.clone();

            for deferred_expression in &deferred_ty.expressions {
                if let Ok(deferred_eval) =
                    self.evaluate_expression(known_evaluations, deferred_expression)
                {
                    sourced_ty = sourced_ty.join(&effects.consume(deferred_eval));
                } else {
                    self.expression = None;

                    return Err(EvaluationError::Deferred);
                }
            }

            let eval = PyTypeEval::new(sourced_ty, effects);

            known_evaluations
                .entry(self.namespace.clone())
                .or_default()
                .insert(expression.clone(), eval.clone());

            self.expression = None;

            return Ok(eval);
        }

        match expression {
            Expression::VariableDefinition(expression_variable) => {
                self.evaluate_expression_variable_definition(known_evaluations, expression_variable)
            }
            Expression::VariableReference(expression_forward_variable) => self
                .evaluate_expression_variable_reference(
                    known_evaluations,
                    expression_forward_variable,
                ),
            Expression::Annotated(expression_annotated) => {
                self.evaluate_expression_annotated(known_evaluations, expression_annotated)
            }
            Expression::Override(expression_override) => {
                self.evaluate_expression_override(known_evaluations, expression_override)
            }
            Expression::Function(expression_function) => {
                self.evaluate_expression_function(known_evaluations, expression_function)
            }
            Expression::Class(expression_class) => {
                self.evaluate_expression_class(known_evaluations, expression_class)
            }
            Expression::Import(expression_import) => {
                self.evaluate_expression_import(known_evaluations, expression_import)
            }
            Expression::Attribute(expression_attribute) => {
                self.evaluate_expression_attribute(known_evaluations, expression_attribute)
            }
            Expression::Subscript(expression_subscript) => {
                self.evaluate_expression_subscript(known_evaluations, expression_subscript)
            }
            Expression::Call(expression_call) => {
                self.evaluate_expression_call(known_evaluations, expression_call)
            }
            Expression::Unary(expression_unary) => {
                self.evaluate_expression_unary(known_evaluations, expression_unary)
            }
            Expression::Binary(expression_binary) => {
                self.evaluate_expression_binary(known_evaluations, expression_binary)
            }
            Expression::LiteralInteger(literal_integer) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_integer_literal(literal_integer.clone())),
            )),
            Expression::LiteralFloat(literal_float) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_float_literal(literal_float.clone())),
            )),
            Expression::LiteralComplex(literal_complex) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_complex_literal(literal_complex.clone())),
            )),
            Expression::LiteralString(literal_string) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_string_literal(literal_string.clone())),
            )),
            Expression::LiteralBytes(literal_bytes) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_bytes_literal(literal_bytes.clone())),
            )),
            Expression::LiteralBoolean(literal_boolean) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_boolean_literal(literal_boolean.clone())),
            )),
            Expression::LiteralNone => Ok(PyTypeEval::with_default_effects(Sourced::inferred(
                Type::new_literal(TypeLiteral::None),
            ))),
            Expression::LiteralEllipsis => Ok(PyTypeEval::with_default_effects(Sourced::inferred(
                Type::new_literal(TypeLiteral::Ellipsis),
            ))),
        }
    }
}
