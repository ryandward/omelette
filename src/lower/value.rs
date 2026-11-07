//! The static value domain of the partial evaluator.
use crate::affine::Form;
use crate::core::{Family, Kind, Utf16};
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
    List(Items),
    /// Some value that is never undefined, of no known type.
    Defined,
    /// Possibly undefined.
    Any,
}

/// Whether every element of a list is defined: by the model's precondition on a free list,
/// or because every value put into the list is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Items {
    Defined,
    Any,
}

impl Items {
    pub fn of(defined: bool) -> Self {
        if defined { Self::Defined } else { Self::Any }
    }
    /// The elements of a list built from lists with these elements.
    #[must_use]
    pub fn both(self, other: Self) -> Self {
        Self::of(self == Self::Defined && other == Self::Defined)
    }
    /// The type of one element.
    pub fn ty(self) -> Ty {
        match self {
            Self::Defined => Ty::Defined,
            Self::Any => Ty::Any,
        }
    }
    /// The kind of an element binder.
    pub fn kind(self) -> Kind {
        match self {
            Self::Defined => Kind::Elem,
            Self::Any => Kind::Item,
        }
    }
}

/// A symbolic list term and what is known of its elements.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Seq {
    pub id: Id,
    pub items: Items,
}

impl Seq {
    pub fn val<'a>(self) -> Val<'a> {
        Val::Term(self.id, Ty::List(self.items))
    }
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
    /// The flow that wrote the absent side (see [`Family::then`]).
    pub family: Family,
    /// The read's index came from another collection's walker.
    pub drift: bool,
    /// The elements of the list read, which give `elem` its type.
    pub items: Items,
}

/// A symbolic list of length at most one: `read` is its element slot, whose binder `var`
/// ranges over `items`, and where present the element is `elem` and survives filtering when
/// `keep` is true.
#[derive(Clone)]
pub struct Short<'a> {
    pub list: Seq,
    pub read: Id,
    pub var: Id,
    pub items: Items,
    pub elem: Val<'a>,
    pub keep: Val<'a>,
    /// The slot's index came from another collection's walker.
    pub drift: bool,
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
    /// The same lowered value: structural identity, not JavaScript equality, so `NaN` is
    /// identical to itself; a list is an object, identical only to itself.
    pub fn identical(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Undef, Self::Undef) | (Self::NaN, Self::NaN) | (Self::Throw, Self::Throw) => true,
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Num(a), Self::Num(b)) => a == b,
            (Self::Str(a), Self::Str(b)) => a == b,
            (Self::List(a), Self::List(b)) => Rc::ptr_eq(a, b),
            (Self::Short(a), Self::Short(b)) => Rc::ptr_eq(a, b),
            (Self::Fun(a), Self::Fun(b)) => Rc::ptr_eq(a, b),
            (Self::Split(a), Self::Split(b)) => Rc::ptr_eq(a, b),
            (Self::Term(a, _), Self::Term(b, _)) => a == b,
            _ => false,
        }
    }
    /// What is known of the elements of a list value.
    pub fn items(&self) -> Option<Items> {
        match self {
            Self::List(items) => Some(Items::of(items.iter().all(Val::defined))),
            Self::Short(s) => Some(s.list.items),
            Self::Term(_, Ty::List(items)) => Some(*items),
            _ => None,
        }
    }
    /// Whether evaluating this value throws in some world.
    pub fn may_throw(&self) -> bool {
        match self {
            Self::Throw => true,
            Self::Split(s) => s.absent.may_throw() || s.present.may_throw(),
            Self::List(items) => items.iter().any(Val::may_throw),
            _ => false,
        }
    }
    /// Whether this value is never undefined.
    pub fn defined(&self) -> bool {
        match self {
            Self::Undef | Self::Throw | Self::Split(_) | Self::Term(_, Ty::Any) => false,
            Self::NaN | Self::Bool(_) | Self::Num(_) | Self::Str(_) | Self::List(_) | Self::Short(_) | Self::Fun(_) | Self::Term(..) => true,
        }
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
