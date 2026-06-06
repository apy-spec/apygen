pub mod literal_boolean;
pub mod literal_bytes;
pub mod literal_class;
pub mod literal_complex;
pub mod literal_ellipsis;
pub mod literal_float;
pub mod literal_function;
pub mod literal_integer;
pub mod literal_none;
pub mod literal_string;
pub mod type_instance;
pub mod type_literal;

use crate::abstract_environment::{
    AbstractEnvironment, Completeness, Exception, LiteralList, LiteralTuple, Pureness,
    RaisedExceptions, Type, TypeInstance, TypeLiteral, resolve_local_attribute,
};
use crate::analysis::cfg::nodes;
use crate::analysis::namespace::Location;
use crate::genkill::assignment::AssignmentTarget;
use crate::genkill::calls::Arguments;
use crate::genkill::literals::{
    gen_expr_boolean_literal, gen_expr_bytes_literal, gen_expr_ellipsis_literal,
    gen_expr_none_literal, gen_expr_number_literal, gen_expr_string_literal,
};
use crate::worklist::WorklistContext;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::cfg::nodes::{
    Expr, ExprAttribute, ExprBinOp, ExprBoolOp, ExprCall, ExprName, ExprSubscript, ExprUnaryOp,
    Operator,
};
use apygen_analysis::lattice::{Lattice, NamespacesLattice};
use apygen_analysis::namespace::Namespaces;
use std::collections::BTreeMap;
use std::sync::Arc;

#[derive(Debug, Default)]
pub struct PyEffects {
    pub exceptions: RaisedExceptions,
    pub pureness: Pureness,
    pub completeness: Completeness,
}

impl PyEffects {
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

    pub fn consume<T>(&mut self, eval: PyValueEval<T>) -> T {
        self.exceptions = self.exceptions.join(&eval.effects.exceptions);
        self.pureness = self.pureness.join(&eval.effects.pureness);
        self.completeness = self.completeness.join(&eval.effects.completeness);
        eval.value
    }
}

impl Lattice for PyEffects {
    fn includes(&self, other: &Self) -> bool {
        self.exceptions.includes(&other.exceptions)
            && self.pureness.includes(&other.pureness)
            && self.completeness.includes(&other.completeness)
    }

    fn join(&self, other: &Self) -> Self {
        PyEffects {
            exceptions: self.exceptions.join(&other.exceptions),
            pureness: self.pureness.join(&other.pureness),
            completeness: self.completeness.join(&other.completeness),
        }
    }
}

#[derive(Debug)]
pub struct PyValueEval<T> {
    pub value: T,
    pub effects: PyEffects,
}

impl<T> PyValueEval<T> {
    pub fn new(value: T, effects: PyEffects) -> Self {
        PyValueEval { value, effects }
    }

    pub fn with_default_effects(value: T) -> Self {
        PyValueEval::new(value, PyEffects::default())
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> PyValueEval<U> {
        PyValueEval {
            value: f(self.value),
            effects: self.effects,
        }
    }

    pub fn extend_effects(mut self, effects: &PyEffects) -> Self {
        self.effects = self.effects.join(effects);
        self
    }
}

impl<L: NamespacesLattice<QualifiedName, AbstractEnvironment>>
    NamespacesLattice<QualifiedName, AbstractEnvironment> for PyValueEval<L>
{
    type Error = L::Error;

    fn includes(
        &self,
        namespaces: &impl Namespaces<QualifiedName, AbstractEnvironment>,
        other: &Self,
    ) -> Result<bool, Self::Error> {
        Ok(self.value.includes(namespaces, &other.value)? && self.effects.includes(&other.effects))
    }

    fn join(
        &self,
        namespaces: &impl Namespaces<QualifiedName, AbstractEnvironment>,
        other: &Self,
    ) -> Result<Self, Self::Error> {
        Ok(PyValueEval {
            value: self.value.join(namespaces, &other.value)?,
            effects: self.effects.join(&other.effects),
        })
    }
}

pub type PyTypeEval = PyValueEval<Type>;

impl PyTypeEval {
    pub fn never() -> Self {
        PyTypeEval::new(Type::Never, PyEffects::default())
    }

    pub fn raise(exception: Exception) -> Self {
        PyTypeEval::new(
            Type::NoReturn,
            PyEffects {
                exceptions: RaisedExceptions::raise(exception),
                pureness: Pureness::Impure,
                completeness: Completeness::Partial,
            },
        )
    }

    pub fn unknown() -> Self {
        PyTypeEval::new(
            Type::Any,
            PyEffects {
                exceptions: RaisedExceptions::raise(Exception::any()),
                pureness: Pureness::Impure,
                completeness: Completeness::Partial,
            },
        )
    }
}

macro_rules! is_type_unreachable {
    ($ty:expr) => {
        matches!($ty, Type::Never | Type::NoReturn)
    };
}

macro_rules! pytype_return_unreachable {
    ($effects:expr, $ty:expr) => {
        if is_type_unreachable!($ty) {
            return PyTypeEval::new($ty, $effects);
        }
    };
}

macro_rules! pytype_consume_or_return {
    ($effects:expr, $eval:expr) => {{
        let ty = $effects.consume($eval);

        pytype_return_unreachable!($effects, ty);

        ty
    }};
}

pub fn gen_bool_value(ty: &Type) -> Option<bool> {
    match ty {
        Type::Any => None,
        Type::Never => None,
        Type::NoReturn => None,
        Type::Instance { .. } => None,
        Type::Union(_) => None,
        Type::Intersection(_) => None,
        Type::Literal(literal_value) => type_literal::as_boolean(literal_value.as_ref()),
    }
}

pub fn gen_expr_collection(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expressions: &Vec<nodes::Expr>,
) -> PyValueEval<Option<Vec<Type>>> {
    let mut types: Vec<Type> = Vec::new();
    let mut effects = PyEffects::default();

    for expression in expressions {
        let ty = effects.consume(gen_expr(context, environment_location, expression));

        if is_type_unreachable!(ty) {
            return PyValueEval::new(None, effects);
        }

        types.push(ty);
    }

    PyValueEval::new(Some(types), effects)
}

pub fn gen_expr_list(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_list: &nodes::ExprList,
) -> PyTypeEval {
    // SOUNDNESS: A list can either be literal (if all its elements are literals)
    //            or non-literal (if any of its element is non-literal).
    //            Its creation can be non-pure, partial or raise exceptions
    //            if any of its elements is non-pure, partial or can raise exceptions respectively.
    gen_expr_collection(context, environment_location, &expr_list.elts).map(|list_types_option| {
        let Some(list_types) = list_types_option else {
            return Type::NoReturn;
        };

        let mut literal_values: imbl::Vector<Arc<TypeLiteral>> = imbl::Vector::new();
        let mut non_literal_types: Vec<Arc<Type>> = Vec::new();

        for list_type in list_types {
            match list_type {
                Type::Literal(literal_value) => literal_values.push_back(literal_value),
                non_literal_type => non_literal_types.push(Arc::new(non_literal_type)),
            };
        }

        if non_literal_types.is_empty() {
            Type::new_literal(TypeLiteral::List(LiteralList {
                value: literal_values,
            }))
        } else {
            Type::Instance(TypeInstance::builtins_list(Arc::new(Type::new_union(
                literal_values
                    .into_iter()
                    .map(|literal_value| Arc::new(Type::Literal(literal_value)))
                    .chain(non_literal_types.into_iter()),
            ))))
        }
    })
}

pub fn gen_expr_set(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_set: &nodes::ExprSet,
) -> PyTypeEval {
    // SOUNDNESS: A set can either be literal (if all its elements are literals)
    //            or non-literal (if any of its element is non-literal).
    //            Its creation can be non-pure, partial or raise exceptions
    //            if any of its elements is non-pure, partial or can raise exceptions respectively.
    gen_expr_collection(context, environment_location, &expr_set.elts).map(|set_types_option| {
        let Some(set_types) = set_types_option else {
            return Type::NoReturn;
        };

        let mut literal_values: imbl::Vector<Arc<TypeLiteral>> = imbl::Vector::new();
        let mut non_literal_types: Vec<Arc<Type>> = Vec::new();

        for list_type in set_types {
            match list_type {
                Type::Literal(literal_value) => literal_values.push_back(literal_value),
                non_literal_type => non_literal_types.push(Arc::new(non_literal_type)),
            };
        }

        if non_literal_types.is_empty() {
            Type::new_literal(TypeLiteral::List(LiteralList {
                value: literal_values,
            }))
        } else {
            Type::Instance(TypeInstance::builtins_list(Arc::new(Type::new_union(
                literal_values
                    .into_iter()
                    .map(|literal_value| Arc::new(Type::Literal(literal_value)))
                    .chain(non_literal_types.into_iter()),
            ))))
        }
    })
}

pub fn gen_expr_tuple(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_tuple: &nodes::ExprTuple,
) -> PyTypeEval {
    // SOUNDNESS: A tuple can either be literal (if all its elements are literals)
    //            or non-literal (if any of its element is non-literal).
    //            Its creation can be non-pure, partial or raise exceptions
    //            if any of its elements is non-pure, partial or can raise exceptions respectively.
    gen_expr_collection(context, environment_location, &expr_tuple.elts).map(|tuple_types_option| {
        let Some(tuple_types) = tuple_types_option else {
            return Type::NoReturn;
        };

        let tuple_types: Vec<Type> = tuple_types.into_iter().collect();

        if tuple_types.iter().all(|ty| matches!(ty, Type::Literal(_))) {
            let tuple_values = tuple_types
                .into_iter()
                .map(|ty| match ty {
                    Type::Literal(literal_value) => literal_value,
                    _ => unreachable!("The if condition ensures that all types are literals"),
                })
                .collect();
            Type::new_literal(TypeLiteral::Tuple(LiteralTuple {
                value: tuple_values,
            }))
        } else {
            Type::Instance(TypeInstance::builtins_tuple(
                tuple_types.into_iter().map(|ty| Arc::new(ty)),
            ))
        }
    })
}

pub fn gen_name(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_name: &ExprName,
) -> PyTypeEval {
    let Ok(identifier) = Identifier::try_parse(expr_name.id.as_ref()) else {
        return PyTypeEval::unknown();
    };

    match resolve_local_attribute(
        &context.namespaces,
        environment_location.clone(),
        &identifier,
    ) {
        Ok((_, _, local_attribute)) => {
            PyTypeEval::with_default_effects(local_attribute.attribute_type.data.as_ref().clone())
        }
        Err(_) => PyTypeEval::unknown(),
    }
}

pub fn gen_bool_op(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_bool_op: &ExprBoolOp,
) -> PyTypeEval {
    let mut expr_iter = expr_bool_op.values.iter();

    let expr = expr_iter
        .next()
        .expect("A boolean operation must have at least one operand");
    let mut effects = PyEffects::new();

    let mut ty = pytype_consume_or_return!(effects, gen_expr(context, environment_location, expr));

    for next_expr in expr_iter {
        let next_ty =
            pytype_consume_or_return!(effects, gen_expr(context, environment_location, next_expr));

        if let Some(bool) = gen_bool_value(&ty) {
            if (expr_bool_op.op == nodes::BoolOp::And && !bool)
                || (expr_bool_op.op == nodes::BoolOp::Or && bool)
            {
                break;
            }
            ty = next_ty;
        } else {
            ty = ty.join(&context.namespaces, &next_ty).unwrap(); // TODO: remove unwrap
        }
    }

    PyTypeEval::new(ty, effects)
}

/// References:
/// - https://docs.python.org/3/reference/datamodel.html#emulating-numeric-types
pub fn gen_operator_name(operator: nodes::Operator) -> &'static str {
    match operator {
        Operator::Add => "add",
        Operator::Sub => "sub",
        Operator::Mult => "mul",
        Operator::MatMult => "matmul",
        Operator::Div => "truediv",
        Operator::Mod => "mod",
        Operator::Pow => "pow",
        Operator::LShift => "lshift",
        Operator::RShift => "rshift",
        Operator::BitOr => "or",
        Operator::BitXor => "xor",
        Operator::BitAnd => "and",
        Operator::FloorDiv => "floordiv",
    }
}

pub fn as_type_instances(ty: &Type) -> Vec<TypeInstance> {
    match ty {
        Type::Any => vec![TypeInstance::typing("Any")],
        Type::Never => vec![TypeInstance::typing("Never")],
        Type::NoReturn => vec![TypeInstance::typing("NoReturn")],
        Type::Instance(type_instance) => vec![type_instance.clone()],
        Type::Union(union) => union
            .types()
            .iter()
            .flat_map(|ty| as_type_instances(ty.as_ref()))
            .collect(),
        Type::Intersection(intersection) => intersection
            .iter()
            .flat_map(|ty| as_type_instances(ty.as_ref()))
            .collect(),
        Type::Literal(literal) => vec![type_literal::as_type_instance(literal.as_ref())],
    }
}

pub fn call_operator(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    left: &Type,
    operator: nodes::Operator,
    right: &Type,
) -> PyTypeEval {
    let operator_name = gen_operator_name(operator);

    let mut effects = PyEffects::new();
    let mut ty = Type::Never;

    for left_instance in as_type_instances(left) {
        let normal_ty = effects.consume(type_instance::call_method(
            context,
            environment_location,
            &left_instance,
            &Identifier::parse(&format!("__{operator_name}__")),
            vec![Arc::new(right.clone())],
            BTreeMap::new(),
        ));
        ty = ty.join(&context.namespaces, &normal_ty).unwrap(); // TODO: remove unwrap
    }

    pytype_return_unreachable!(effects, ty);

    for right_instance in as_type_instances(right) {
        let reverse_ty = effects.consume(type_instance::call_method(
            context,
            environment_location,
            &right_instance,
            &Identifier::parse(&format!("__r{operator_name}__")),
            vec![Arc::new(left.clone())],
            BTreeMap::new(),
        ));
        ty = ty.join(&context.namespaces, &reverse_ty).unwrap(); // TODO: remove unwrap
    }

    PyTypeEval::new(ty, effects)
}

pub fn call_binary_op(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    left: &Type,
    operator: nodes::Operator,
    right: &Type,
) -> PyTypeEval {
    match (left, right) {
        (Type::Literal(left), Type::Literal(right)) => {
            type_literal::call_binary_op(context, left.as_ref(), operator, right.as_ref())
        }
        (Type::Any, _) | (_, Type::Any) => PyTypeEval::unknown(),
        _ => call_operator(context, environment_location, left, operator, right),
    }
}

pub fn gen_bin_op(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_bin_op: &ExprBinOp,
) -> PyTypeEval {
    let mut effects = PyEffects::new();

    let left_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_bin_op.left)
    );
    let right_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_bin_op.right)
    );

    let ty = pytype_consume_or_return!(
        effects,
        call_binary_op(
            context,
            environment_location,
            &left_ty,
            expr_bin_op.op,
            &right_ty,
        )
    );

    PyTypeEval::new(ty, effects)
}

pub fn gen_unary_op(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_unary_op: &ExprUnaryOp,
) -> PyTypeEval {
    let mut effects = PyEffects::new();

    let target_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_unary_op.operand)
    );

    let ty = match target_ty {
        Type::Any => Type::Any,
        Type::Instance { .. } => Type::Any,
        Type::Union(_) => Type::Any,
        Type::Intersection(_) => Type::Any,
        Type::Literal(type_literal) => {
            pytype_consume_or_return!(
                effects,
                type_literal::call_unary_op(type_literal.as_ref(), expr_unary_op.op)
            )
        }
        Type::Never | Type::NoReturn => unreachable!("target should not be unreachable"),
    };

    PyTypeEval::new(ty, effects)
}

pub fn gen_arguments(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    arguments: &nodes::Arguments,
) -> PyValueEval<Option<Arguments>> {
    let mut effects = PyEffects::new();

    let mut data = Arguments::new();

    for argument in &arguments.args {
        let argument_ty = effects.consume(gen_expr(context, environment_location, argument));

        if is_type_unreachable!(argument_ty) {
            return PyValueEval::new(None, effects);
        }

        data.positional.push(Arc::new(argument_ty));
    }
    for keyword_argument in &arguments.keywords {
        if let Some(name) = &keyword_argument.arg {
            let keyword_argument_ty = effects.consume(gen_expr(
                context,
                environment_location,
                &keyword_argument.value,
            ));

            if is_type_unreachable!(keyword_argument_ty) {
                return PyValueEval::new(None, effects);
            }

            data.keyword.insert(
                Arc::new(Identifier::parse(&name.id)),
                Arc::new(keyword_argument_ty),
            );
        }
    }

    PyValueEval::new(Some(data), effects)
}

pub fn gen_call(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_call: &ExprCall,
) -> PyTypeEval {
    let mut effects = PyEffects::new();

    let func_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_call.func)
    );

    let Type::Literal(literal) = func_ty else {
        return PyTypeEval::unknown().extend_effects(&effects);
    };

    match literal.as_ref() {
        TypeLiteral::Function(literal_function) => {
            match effects.consume(gen_arguments(
                context,
                environment_location,
                &expr_call.arguments,
            )) {
                Some(arguments) => literal_function::call(
                    context,
                    environment_location,
                    literal_function,
                    &arguments,
                ),
                None => PyTypeEval::new(Type::NoReturn, effects),
            }
        }
        TypeLiteral::Class(literal_class) => {
            match AssignmentTarget::try_from(expr_call.func.as_ref()) {
                Ok(AssignmentTarget::Name(name)) => {
                    match effects.consume(gen_arguments(
                        context,
                        environment_location,
                        &expr_call.arguments,
                    )) {
                        Some(arguments) => literal_class::call(
                            context,
                            environment_location,
                            &name,
                            literal_class,
                            &arguments,
                        ),
                        None => PyTypeEval::new(Type::NoReturn, effects),
                    }
                }
                _ => PyTypeEval::unknown().extend_effects(&effects),
            }
        }
        _ => PyTypeEval::unknown().extend_effects(&effects),
    }
}

pub fn gen_attribute(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_attribute: &ExprAttribute,
) -> PyTypeEval {
    let mut effects = PyEffects::new();

    let target_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_attribute.value)
    );

    let target_attribute_option = match target_ty {
        Type::Instance(type_instance) => type_instance::get_instance_attribute(
            &context.namespaces,
            &type_instance,
            &Identifier::parse(&expr_attribute.attr.id),
        )
        .ok(),
        Type::Literal(type_literal) => match type_literal.as_ref() {
            TypeLiteral::Class(literal_class) => literal_class::resolve_class_attribute(
                &context.namespaces,
                literal_class,
                &Identifier::parse(&expr_attribute.attr.id),
            ),
            _ => None,
        },
        _ => None,
    };

    let Some(target_attribute) = target_attribute_option else {
        return PyTypeEval::unknown().extend_effects(&effects);
    };

    let Ok(target_local_attribute) = target_attribute.resolve(&context.namespaces) else {
        return PyTypeEval::unknown().extend_effects(&effects);
    };

    PyTypeEval::new(
        target_local_attribute.attribute_type.data.as_ref().clone(),
        effects,
    )
}

pub fn gen_subscript(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expr_subscript: &ExprSubscript,
) -> PyTypeEval {
    let mut effects = PyEffects::new();

    let target_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_subscript.value)
    );
    let slice_ty = pytype_consume_or_return!(
        effects,
        gen_expr(context, environment_location, &expr_subscript.slice)
    );

    let ty = pytype_consume_or_return!(effects, PyValueEval::unknown());  // TODO: fix subscript

    PyTypeEval::new(ty, effects)
}

pub fn gen_expr(
    context: &mut WorklistContext,
    environment_location: &Location<QualifiedName>,
    expression: &nodes::Expr,
) -> PyTypeEval {
    match expression {
        Expr::BoolOp(expr_bool_op) => gen_bool_op(context, environment_location, expr_bool_op),
        Expr::Named(_) => PyTypeEval::unknown(),
        Expr::BinOp(expr_bin_op) => gen_bin_op(context, environment_location, expr_bin_op),
        Expr::UnaryOp(expr_unary_op) => gen_unary_op(context, environment_location, expr_unary_op),
        Expr::Lambda(_) => PyTypeEval::unknown(),
        Expr::If(_) => PyTypeEval::unknown(),
        Expr::Dict(_) => PyTypeEval::unknown(),
        Expr::Set(expr_set) => gen_expr_set(context, environment_location, expr_set),
        Expr::ListComp(_) => PyTypeEval::unknown(),
        Expr::SetComp(_) => PyTypeEval::unknown(),
        Expr::DictComp(_) => PyTypeEval::unknown(),
        Expr::Generator(_) => PyTypeEval::unknown(),
        Expr::Await(_) => PyTypeEval::unknown(),
        Expr::Yield(_) => PyTypeEval::unknown(),
        Expr::YieldFrom(_) => PyTypeEval::unknown(),
        Expr::Compare(_) => PyTypeEval::unknown(),
        Expr::Call(expr_call) => gen_call(context, environment_location, expr_call),
        Expr::FString(_) => PyTypeEval::unknown(),
        Expr::StringLiteral(expr_string_literal) => {
            PyTypeEval::with_default_effects(gen_expr_string_literal(expr_string_literal))
        }
        Expr::BytesLiteral(expr_bytes_literal) => {
            PyTypeEval::with_default_effects(gen_expr_bytes_literal(expr_bytes_literal))
        }
        Expr::NumberLiteral(expr_number_literal) => {
            PyTypeEval::with_default_effects(gen_expr_number_literal(expr_number_literal))
        }
        Expr::BooleanLiteral(expr_boolean_literal) => {
            PyTypeEval::with_default_effects(gen_expr_boolean_literal(expr_boolean_literal))
        }
        Expr::NoneLiteral(_) => PyTypeEval::with_default_effects(gen_expr_none_literal()),
        Expr::EllipsisLiteral(_) => PyTypeEval::with_default_effects(gen_expr_ellipsis_literal()),
        Expr::Attribute(expr_attribute) => {
            gen_attribute(context, environment_location, expr_attribute)
        }
        Expr::Subscript(expr_subscript) => {
            gen_subscript(context, environment_location, expr_subscript)
        }
        Expr::Starred(_) => PyTypeEval::unknown(),
        Expr::Name(expr_name) => gen_name(context, environment_location, expr_name),
        Expr::List(expr_list) => gen_expr_list(context, environment_location, expr_list),
        Expr::Tuple(expr_tuple) => gen_expr_tuple(context, environment_location, expr_tuple),
        Expr::Slice(_) => PyTypeEval::unknown(),
        Expr::IpyEscapeCommand(_) => PyTypeEval::unknown(),
    }
}
