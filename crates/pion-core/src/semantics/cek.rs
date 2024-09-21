use core::panic;

use super::{Closure, Elim, LocalValues, MetaValues, Value};
use crate::syntax::{Expr, FunArg, Plicity};

type Stack<'core> = Vec<Frame<'core>>;

fn push_frame<'core>(mut stack: Stack<'core>, frame: Frame<'core>) -> Stack<'core> {
    stack.push(frame);
    stack
}

fn push_local<'core>(mut locals: LocalValues<'core>, value: Value<'core>) -> LocalValues<'core> {
    locals.push(value);
    locals
}

#[derive(Debug)]
enum State<'core> {
    /// A compound expression was reached (ie evaluation takes multiple steps):
    /// evaluate `expr` in `locals` and then continue with `stack`.
    Compound(Expr<'core>, LocalValues<'core>, Stack<'core>),

    /// An atomic expression was reached (ie evaluation can be done in a single
    /// step): pop the stack and continue.
    Atomic(Value<'core>, LocalValues<'core>, Stack<'core>),
}

#[derive(Debug)]
enum Frame<'core> {
    LetBody(Expr<'core>),
    FunAppArg(FunArg<&'core Expr<'core>>),
    ApplyClosure(Plicity, Value<'core>),
}

#[derive(Debug)]
enum Step<'core> {
    Done(Value<'core>),
    More(State<'core>),
}

fn step<'core>(metas: &MetaValues<'core>, state: State<'core>) -> Step<'core> {
    match state {
        State::Compound(expr, locals, stack) => {
            let state = match expr {
                Expr::Error => State::Atomic(Value::Error, locals, stack),
                Expr::Bool(b) => State::Atomic(Value::Bool(b), locals, stack),
                Expr::Int(n) => State::Atomic(Value::Int(n), locals, stack),
                Expr::Char(c) => State::Atomic(Value::Char(c), locals, stack),
                Expr::String(s) => State::Atomic(Value::String(s), locals, stack),
                Expr::PrimVar(var) => State::Atomic(Value::prim_var(var), locals, stack),
                Expr::LocalVar(var) => match locals.get_relative(var) {
                    None => panic!("Unbound local variable: {var:?}"),
                    Some(value) => State::Atomic(value.clone(), locals, stack),
                },
                Expr::MetaVar(var) => match metas.get_absolute(var) {
                    None => panic!("Unbound meta variable: {var:?}"),
                    Some(None) => State::Atomic(Value::meta_var(var), locals, stack),
                    Some(Some(value)) => State::Atomic(value.clone(), locals, stack),
                },
                Expr::FunType { param, body } => {
                    let value = Value::FunType {
                        param,
                        body: Closure::new(locals.clone(), body),
                    };
                    State::Atomic(value, locals, stack)
                }
                Expr::FunLit { param, body } => {
                    let value = Value::FunLit {
                        param,
                        body: Closure::new(locals.clone(), body),
                    };
                    State::Atomic(value, locals, stack)
                }

                Expr::Let { binding, body } => State::Compound(
                    *binding.rhs,
                    locals,
                    push_frame(stack, Frame::LetBody(*body)),
                ),
                Expr::FunApp { fun, arg } => {
                    State::Compound(*fun, locals, push_frame(stack, Frame::FunAppArg(arg)))
                }
            };
            Step::More(state)
        }
        State::Atomic(value, locals, mut stack) => {
            let Some(frame) = stack.pop() else {
                return Step::Done(value);
            };
            let state = match frame {
                Frame::LetBody(body) => State::Compound(body, push_local(locals, value), stack),
                Frame::FunAppArg(arg) => State::Compound(
                    *arg.expr,
                    LocalValues::new(),
                    push_frame(stack, Frame::ApplyClosure(arg.plicity, value)),
                ),
                Frame::ApplyClosure(plicity, callee) => match callee {
                    Value::Error => State::Atomic(Value::Error, locals, stack),
                    Value::Neutral(head, mut spine) => {
                        spine.push(Elim::FunApp(FunArg::new(plicity, value)));
                        let value = Value::Neutral(head, spine);
                        State::Atomic(value, locals, stack)
                    }
                    Value::FunLit { param, body } => {
                        assert_eq!(
                            param.plicity, plicity,
                            "Mismatched plicity: {param:?} vs {plicity:?}"
                        );
                        let Closure { local_values, body } = body;
                        State::Compound(*body, push_local(local_values, value), stack)
                    }
                    _ => panic!("Cannot apply non-function value: {callee:?}"),
                },
            };
            Step::More(state)
        }
    }
}

pub fn eval<'core>(
    expr: &Expr<'core>,
    locals: LocalValues<'core>,
    metas: &MetaValues<'core>,
) -> Value<'core> {
    let mut state = State::Compound(*expr, locals, Vec::new());
    loop {
        match step(metas, state) {
            Step::Done(value) => return value,
            Step::More(next_state) => state = next_state,
        }
    }
}
