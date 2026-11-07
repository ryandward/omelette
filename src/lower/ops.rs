//! JavaScript operators on lowered values: typed dispatch, coercion, and splits.
use super::Lowerer;
use super::value::{Split, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Utf16};
use egg::Id;
use std::rc::Rc;

/// Binary operators lowering dispatches by type.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Bin {
    Add,
    Sub,
    Mul,
    Lt,
    Le,
    Eq,
}

/// An operation applied on each side of a split.
pub type Op<'a, 'l, 'f> = dyn FnMut(&mut Lowerer<'a, 'l>, Val<'a>, Val<'a>) -> Val<'a> + 'f;
pub type Op1<'a, 'l, 'f> = dyn FnMut(&mut Lowerer<'a, 'l>, Val<'a>) -> Val<'a> + 'f;
/// What follows the evaluation of some values.
pub type Then<'a, 'l, 'f> = dyn FnMut(&mut Lowerer<'a, 'l>, Vec<Val<'a>>) -> Val<'a> + 'f;

impl<'a, 'l> Lowerer<'a, 'l> {
    /// Rebuild a split from new sides, composing `family` into the split's flow if this
    /// operation changed the absent side.
    pub fn resplit(&mut self, s: &Split<'a>, absent: Val<'a>, present: Val<'a>, family: Family) -> Val<'a> {
        // Both worlds give one value: it does not depend on the read.
        if absent.identical(&present) || (absent.is_known() && present.is_known() && same(&absent, &present) == Some(true)) {
            return absent;
        }
        let family = match &absent {
            Val::Undef | Val::Throw => Family::Propagate,
            unchanged if unchanged.identical(&s.absent) => s.family,
            _ => s.family.then(family),
        };
        let s = Split { absent, present, family, ..s.clone() };
        Val::Split(Rc::new(s))
    }
    /// Resolve splits on `read` to one side: absent, or present.
    pub fn assume(&mut self, v: Val<'a>, read: Id, present: bool) -> Val<'a> {
        let Val::Split(s) = v else { return v };
        if s.read == read {
            let side = if present { s.present.clone() } else { s.absent.clone() };
            return self.assume(side, read, present);
        }
        let absent = self.assume(s.absent.clone(), read, present);
        let kept = self.assume(s.present.clone(), read, present);
        self.resplit(&s, absent, kept, s.family)
    }
    /// Apply `op` on every pair of sides of the splits in `a` and `b`, each in its world: the
    /// split's read narrowed, so a function called there sees the read decided.
    pub fn lift2(&mut self, a: Val<'a>, b: Val<'a>, family: Family, op: &mut Op<'a, 'l, '_>) -> Val<'a> {
        let (s, flipped) = match (&a, &b) {
            (Val::Split(s), _) => (s.clone(), false),
            (_, Val::Split(s)) => (s.clone(), true),
            _ => return op(self, a, b),
        };
        let other = if flipped { a } else { b };
        let (absent, present) = self.fork(
            &mut |l, present| {
                let (world, mine) = if present { (Val::Term(s.elem, s.items.ty()), s.present.clone()) } else { (Val::Undef, s.absent.clone()) };
                l.within(s.read, world, |l| {
                    let other = l.assume(other.clone(), s.read, present);
                    if flipped { l.lift2(other, mine, family, op) } else { l.lift2(mine, other, family, op) }
                })
            },
            &super::refs::Join::Read(s.clone()),
        );
        self.resplit(&s, absent, present, family)
    }
    pub fn lift(&mut self, v: Val<'a>, family: Family, op: &mut Op1<'a, 'l, '_>) -> Val<'a> {
        self.lift2(v, Val::Undef, family, &mut |l, v, _| op(l, v))
    }
    /// Continue with `vals` once they are evaluated: `then` runs on them as they are, and
    /// every world in which one of them throws then throws.
    pub fn strict(&mut self, vals: Vec<Val<'a>>, then: &mut Then<'a, 'l, '_>) -> Val<'a> {
        if vals.iter().any(|v| matches!(v, Val::Throw)) {
            return Val::Throw;
        }
        let raising: Vec<Val<'a>> = vals.iter().filter(|v| self.may_raise(v)).cloned().collect();
        let before = self.state.clone();
        let out = then(self, vals);
        // What follows runs, and has effects, only where nothing before it threw.
        if !self.state.same(&before) {
            let mut after = std::mem::replace(&mut self.state, before.clone());
            for mask in &raising {
                after = self.guard(&before, after, mask);
            }
            self.state = after;
        }
        raising.into_iter().fold(out, |out, mask| self.mask(out, &mask))
    }
    /// `out` where `mask` does not throw, and a throw where it does.
    fn mask(&mut self, out: Val<'a>, mask: &Val<'a>) -> Val<'a> {
        if matches!(mask, Val::Term(..) | Val::Ref(_))
            && let Some(test) = self.throws_when(mask)
        {
            return self.select(&test, Val::Throw, out);
        }
        self.lift2(out, mask.clone(), Family::Propagate, &mut |l, out, mask| match mask {
            Val::Throw => Val::Throw,
            Val::Term(..) | Val::Ref(_) if l.may_raise(&mask) => l.mask(out, &mask),
            _ => out,
        })
    }
    /// A value under the current narrowing: each split on a read a branch decided resolves
    /// to that side, as a read lowered there would.
    pub fn settle(&mut self, v: Val<'a>) -> Val<'a> {
        let Val::Split(s) = v else { return v };
        if let Some(present) = self.narrow.get(&s.read).map(|n| !matches!(n, Val::Undef)) {
            let side = if present { s.present.clone() } else { s.absent.clone() };
            return self.settle(side);
        }
        let (absent, present) = (self.settle(s.absent.clone()), self.settle(s.present.clone()));
        if absent.identical(&s.absent) && present.identical(&s.present) {
            Val::Split(s)
        } else {
            self.resplit(&s, absent, present, s.family)
        }
    }
}

/// JavaScript strict equality of two known values.
pub fn same(a: &Val<'_>, b: &Val<'_>) -> Option<bool> {
    Some(match (a, b) {
        (Val::Undef, Val::Undef) => true,
        (Val::Bool(x), Val::Bool(y)) => x == y,
        (Val::Str(x), Val::Str(y)) => x == y,
        (Val::Num(x), Val::Num(y)) => x.known()? == y.known()?,
        _ if a.is_known() && b.is_known() => false,
        _ => return None,
    })
}

/// A value that may be undefined without being a split read.
fn unknown(v: &Val<'_>) -> bool {
    matches!(v, Val::Term(_, Ty::Any))
}

impl<'a> Lowerer<'a, '_> {
    pub fn binary(&mut self, op: Bin, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        let undecided = op == Bin::Eq && (unknown(&a) || unknown(&b));
        let family = if undecided { Family::Undecided } else { Family::Sink };
        self.lift2(a, b, family, &mut |l, a, b| {
            if matches!(a, Val::Throw) || matches!(b, Val::Throw) {
                return Val::Throw;
            }
            l.consume(&a);
            l.consume(&b);
            match op {
                Bin::Add => l.add(a, b),
                Bin::Sub | Bin::Mul => l.arith(op, &a, &b),
                Bin::Lt | Bin::Le => l.order(op == Bin::Lt, &a, &b),
                Bin::Eq => l.strict_eq(&a, &b),
            }
        })
    }
    /// `a + b`: concatenation when an operand is a string or a list, and otherwise numeric
    /// addition with booleans coerced.
    fn add(&mut self, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        let (a, b) = (self.deref(a), self.deref(b));
        if is_text(&a) || is_text(&b) || a.items().is_some() || b.items().is_some() {
            let (a, b) = (self.to_text(a), self.to_text(b));
            return self.concat(&a, &b);
        }
        self.arith(Bin::Add, &a, &b)
    }
    fn arith(&mut self, op: Bin, a: &Val<'a>, b: &Val<'a>) -> Val<'a> {
        let (Some(lhs), Some(rhs)) = (numeric(a), numeric(b)) else {
            // `undefined` and `NaN` make arithmetic NaN, but `+` concatenates when the other
            // operand may be a string.
            let poisoned = match op {
                Bin::Add => (poisons(a) && numeric_typed(b)) || (poisons(b) && numeric_typed(a)),
                _ => poisons(a) || poisons(b),
            };
            return if poisoned { Val::NaN } else { self.dynamic(op_name(op), &[a, b], Ty::Defined) };
        };
        let form = match op {
            Bin::Sub => lhs.plus(&rhs, -1),
            Bin::Mul => match (lhs.known(), rhs.known()) {
                (Some(factor), _) => rhs.scale(factor),
                (_, Some(factor)) => lhs.scale(factor),
                _ => return self.product(&lhs, &rhs),
            },
            _ => lhs.plus(&rhs, 1),
        };
        match form {
            Some(f) if exact(&f) => Val::Num(f),
            _ => self.dynamic(op_name(op), &[a, b], Ty::Defined),
        }
    }
    fn product(&mut self, x: &Form, y: &Form) -> Val<'a> {
        let (x, y) = (self.b.form(x), self.b.form(y));
        Val::Num(Form::atom(self.b.add(Core::Mul([x, y]))))
    }
    /// `a < b` (strict) or `a <= b`.
    fn order(&mut self, strict: bool, a: &Val<'a>, b: &Val<'a>) -> Val<'a> {
        let gap = numeric(a).zip(numeric(b)).and_then(|(x, y)| y.plus(&x, -1)?.plus(&Form::constant(i64::from(strict)), -1));
        if let Some(d) = gap.filter(exact) {
            return self.b.nonnegative(&d);
        }
        if poisons(a) || poisons(b) {
            return Val::Bool(false);
        }
        if let (Val::Str(x), Val::Str(y)) = (a, b) {
            let (x, y) = (x.units(), y.units());
            return Val::Bool(if strict { x < y } else { x <= y });
        }
        self.dynamic(if strict { "<" } else { "<=" }, &[a, b], Ty::Bool)
    }
}

impl<'a> Lowerer<'a, '_> {
    pub fn strict_eq(&mut self, a: &Val<'a>, b: &Val<'a>) -> Val<'a> {
        if let Some(known) = same(a, b).or_else(|| identical_object(a, b)) {
            return Val::Bool(known);
        }
        let gap = numeric_only(a).zip(numeric_only(b)).and_then(|(x, y)| y.plus(&x, -1));
        if let Some((up, down)) = gap.filter(exact).and_then(|g| Some((g.scale(-1)?, g))) {
            let (up, down) = (self.b.nonnegative(&up), self.b.nonnegative(&down));
            return self.and(up, down);
        }
        if distinct_types(a, b) {
            return Val::Bool(false);
        }
        let (x, y) = (self.emit(a), self.emit(b));
        Val::Term(self.b.add(Core::Eq([x, y])), Ty::Bool)
    }
    pub fn and(&mut self, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        match (&a, &b) {
            (Val::Bool(false), _) | (_, Val::Bool(true)) => a,
            (Val::Bool(true), _) | (_, Val::Bool(false)) => b,
            _ => {
                let (x, y) = (self.emit(&a), self.emit(&b));
                Val::Term(self.b.add(Core::And([x, y])), Ty::Bool)
            }
        }
    }
    pub fn not(&mut self, v: Val<'a>) -> Val<'a> {
        self.lift(v, Family::Sink, &mut |l, v| match l.truthy(v) {
            Val::Bool(b) => Val::Bool(!b),
            Val::Throw => Val::Throw,
            t => {
                let id = l.emit(&t);
                Val::Term(l.b.add(Core::Not(id)), Ty::Bool)
            }
        })
    }
    /// JavaScript truthiness of a value that is not a split.
    pub fn truthy(&mut self, v: Val<'a>) -> Val<'a> {
        self.consume(&v);
        match v {
            Val::Undef | Val::NaN => Val::Bool(false),
            Val::Bool(_) | Val::Throw | Val::Term(_, Ty::Bool) | Val::Split(_) => v,
            Val::Num(f) => match f.known() {
                Some(n) => Val::Bool(n != 0),
                None => self.nonzero(&f),
            },
            Val::Str(s) => Val::Bool(!s.units().is_empty()),
            Val::List(_) | Val::Short(_) | Val::Fun(_) | Val::Term(_, Ty::List(_)) | Val::Ref(_) => Val::Bool(true),
            Val::Term(_, Ty::Str) => {
                let eq = self.strict_eq(&v, &Val::Str(Utf16::new([])));
                self.not(eq)
            }
            Val::Term(_, Ty::Defined | Ty::Any) => self.dynamic("truthy", &[&v], Ty::Bool),
        }
    }
    fn nonzero(&mut self, f: &Form) -> Val<'a> {
        let above = f.plus(&Form::constant(1), -1).map(|g| self.b.nonnegative(&g));
        let below = f.scale(-1).and_then(|g| g.plus(&Form::constant(1), -1)).map(|g| self.b.nonnegative(&g));
        match (above, below) {
            (Some(x), Some(y)) => {
                let (x, y) = (self.emit(&x), self.emit(&y));
                Val::Term(self.b.add(Core::Or([x, y])), Ty::Bool)
            }
            _ => self.dynamic("truthy", &[&Val::Num(f.clone())], Ty::Bool),
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    pub fn to_text(&mut self, v: Val<'a>) -> Val<'a> {
        let text = |s: &str| Val::Str(Utf16::new(s.encode_utf16()));
        let v = self.deref(v);
        match v {
            Val::Str(_) | Val::Term(_, Ty::Str) | Val::Throw => v,
            Val::Undef => text("undefined"),
            Val::NaN => text("NaN"),
            Val::Bool(b) => text(if b { "true" } else { "false" }),
            Val::Num(ref f) if f.known().is_some() => text(&f.constant.to_string()),
            // A list's text is its elements joined by commas.
            Val::List(ref items) => self.join_items(items, None),
            _ => self.dynamic("string", &[&v], Ty::Str),
        }
    }
    pub fn concat(&mut self, a: &Val<'a>, b: &Val<'a>) -> Val<'a> {
        match (a, b) {
            (Val::Throw, _) | (_, Val::Throw) => Val::Throw,
            (Val::Str(x), Val::Str(y)) => Val::Str(x.concat(*y)),
            _ => {
                let (x, y) = (self.emit(a), self.emit(b));
                Val::Term(self.b.add(Core::Concat([x, y])), Ty::Str)
            }
        }
    }
    /// An operation lowering resolved to no known type; it never yields undefined.
    pub fn dynamic(&mut self, name: &str, args: &[&Val<'a>], ty: Ty) -> Val<'a> {
        let mut children = vec![self.b.text(Utf16::new(name.encode_utf16()))];
        children.extend(args.iter().map(|v| self.emit(v)));
        let node = if ty == Ty::Any { Core::DynUndef(children.into()) } else { Core::Dyn(children.into()) };
        Val::Term(self.b.add(node), ty)
    }
}

fn op_name(op: Bin) -> &'static str {
    match op {
        Bin::Add => "+",
        Bin::Sub => "-",
        Bin::Mul => "*",
        Bin::Lt => "<",
        Bin::Le => "<=",
        Bin::Eq => "===",
    }
}

fn is_text(v: &Val<'_>) -> bool {
    matches!(v, Val::Str(_) | Val::Term(_, Ty::Str))
}

/// Operands whose arithmetic is NaN.
fn poisons(v: &Val<'_>) -> bool {
    matches!(v, Val::Undef | Val::NaN)
}

/// Operands `+` adds rather than concatenates.
fn numeric_typed(v: &Val<'_>) -> bool {
    matches!(v, Val::Undef | Val::NaN | Val::Bool(_) | Val::Num(_) | Val::Term(_, Ty::Bool))
}

/// Strict equality of two objects lowering built: the same object, or two different ones.
fn identical_object(a: &Val<'_>, b: &Val<'_>) -> Option<bool> {
    use super::value::RefKey;
    let fresh = |v: &Val<'_>| matches!(v, Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)));
    match (a, b) {
        (Val::List(x), Val::List(y)) => Some(Rc::ptr_eq(x, y)),
        (Val::Fun(x), Val::Fun(y)) => Some(Rc::ptr_eq(x, y)),
        (Val::Ref(x), Val::Ref(y)) if x == y => Some(true),
        // A choice may be either of its alternatives.
        (Val::Ref(RefKey::Choice(_)), _) | (_, Val::Ref(RefKey::Choice(_))) => None,
        // A local array is a new object, and so is an array just built.
        (Val::Ref(RefKey::Local(_) | RefKey::Place(..)), Val::Ref(_)) | (Val::Ref(_), Val::Ref(RefKey::Local(_) | RefKey::Place(..))) => Some(false),
        (Val::Ref(_), v) | (v, Val::Ref(_)) if fresh(v) => Some(false),
        _ => None,
    }
}

/// The integer a value coerces to, when arithmetic on it stays affine.
fn numeric(v: &Val<'_>) -> Option<Form> {
    match v {
        Val::Num(f) => Some(f.clone()),
        Val::Bool(b) => Some(Form::constant(i64::from(*b))),
        _ => None,
    }
}

fn numeric_only(v: &Val<'_>) -> Option<Form> {
    match v {
        Val::Num(f) => Some(f.clone()),
        _ => None,
    }
}

/// Values whose JavaScript types differ, so strict equality is false.
fn distinct_types(a: &Val<'_>, b: &Val<'_>) -> bool {
    let class = |v: &Val<'_>| match v {
        Val::Num(_) | Val::NaN => Some(0),
        Val::Str(_) | Val::Term(_, Ty::Str) => Some(1),
        Val::Bool(_) | Val::Term(_, Ty::Bool) => Some(2),
        Val::Undef => Some(3),
        Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) | Val::Ref(_) => Some(4),
        Val::Term(_, Ty::Defined) => Some(5),
        _ => None,
    };
    match (class(a), class(b)) {
        (Some(5), Some(3)) | (Some(3), Some(5)) => true,
        (Some(5), _) | (_, Some(5)) => false,
        (Some(x), Some(y)) => x != y,
        _ => false,
    }
}

/// JavaScript numbers are exact integers only up to 2^53 - 1 in magnitude, so a form whose
/// constant or coefficient lies beyond that is not folded.
fn exact(f: &Form) -> bool {
    const SAFE: i64 = 9_007_199_254_740_991;
    std::iter::once(f.constant).chain(f.terms.values().copied()).all(|v| v.abs() <= SAFE)
}
