//! The static value domain of the partial evaluator.
use crate::affine::Form;
use crate::core::{Family, Utf16};
use egg::Id;
use oxc_ast::ast::{Expression, FormalParameters, FunctionBody};
use oxc_semantic::SymbolId;
use std::collections::HashMap;
use std::rc::Rc;

/// What a symbolic term is known to be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Str,
    List,
    /// Some value that is never undefined, of no known type.
    Defined,
    /// Possibly undefined.
    Any,
}

/// A value during lowering: known, symbolic, or split on whether one read is present.
#[derive(Clone)]
pub enum Val<'a> {
    Undef,
    NaN,
    /// Evaluation throws, as reading a property of undefined does.
    Throw,
    Bool(bool),
    /// An integer: known when the form has no atoms.
    Num(Form),
    Str(Utf16),
    /// A list of known length.
    List(Rc<Vec<Val<'a>>>),
    /// A symbolic list holding at most one element.
    Short(Rc<Short<'a>>),
    Fun(Rc<Fun<'a>>),
    Term(Id, Ty),
    Split(Rc<Split<'a>>),
}

/// A value that depends on whether `read` is present: `absent` where it is missing, and
/// `present` in terms of the element variable `elem` where it is not.
#[derive(Clone)]
pub struct Split<'a> {
    pub read: Id,
    pub elem: Id,
    pub absent: Val<'a>,
    pub present: Val<'a>,
    /// The flow that first changed the absent side from undefined.
    pub family: Family,
    /// The read's index came from another collection's walker.
    pub drift: bool,
}

/// A symbolic list of length at most one: `read` is its element slot, and where present the
/// element is `elem` and survives filtering when `keep` is true.
#[derive(Clone)]
pub struct Short<'a> {
    pub list: Id,
    pub read: Id,
    pub var: Id,
    pub elem: Val<'a>,
    pub keep: Val<'a>,
}

/// A function value: its parameters, body, and the bindings it closed over.
pub struct Fun<'a> {
    pub params: &'a FormalParameters<'a>,
    pub body: Body<'a>,
    pub env: Env<'a>,
}

#[derive(Clone, Copy)]
pub enum Body<'a> {
    Expr(&'a Expression<'a>),
    Block(&'a FunctionBody<'a>),
}

pub type Env<'a> = HashMap<SymbolId, Val<'a>>;

impl Val<'_> {
    pub fn int(n: i64) -> Self {
        Self::Num(Form::constant(n))
    }
    pub fn empty() -> Self {
        Self::List(Rc::new(Vec::new()))
    }
    /// Whether this is a known value lowering can compute with.
    pub fn is_known(&self) -> bool {
        match self {
            Self::Num(f) => f.known().is_some(),
            Self::Undef | Self::NaN | Self::Bool(_) | Self::Str(_) => true,
            _ => false,
        }
    }
}
