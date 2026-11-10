//! JavaScript operators on lowered values: typed dispatch, coercion, and splits.
use super::Lowerer;
use super::value::{Split, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Shape, Utf16};
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
    /// Apply `op` to a literal list in each world of the reads its elements depend on, so
    /// an operation that is not element by element never sees a possibly missing read.
    pub fn settled(&mut self, items: &Rc<Vec<Val<'a>>>, family: Family, op: &mut Op1<'a, 'l, '_>) -> Val<'a> {
        let Some((k, s)) = items.iter().enumerate().find_map(|(k, v)| if let Val::Split(s) = v { Some((k, s.clone())) } else { None }) else {
            return op(self, Val::List(items.clone()));
        };
        let (absent, present) = self.fork(
            &mut |l, present| {
                let (world, side) = if present { (Val::Term(s.elem, s.items.ty()), s.present.clone()) } else { (Val::Undef, s.absent.clone()) };
                l.within(s.read, world, |l| {
                    let copy = items.iter().enumerate().map(|(j, v)| if j == k { side.clone() } else { l.assume(v.clone(), s.read, present) }).collect();
                    l.settled(&Rc::new(copy), family, op)
                })
            },
            &super::refs::Join::Read(s.clone()),
        );
        self.resplit(&s, absent, present, family)
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
        // The contents decide the operation; an array keeps its identity into its text, so a
        // cycle in it is written once.
        let (x, y) = (self.deref(a.clone()), self.deref(b.clone()));
        let object = |v: &Val<'_>| v.items().is_some() || matches!(v, Val::Record(_));
        if is_text(&x) || is_text(&y) || object(&x) || object(&y) {
            let (a, b) = (self.to_text(a), self.to_text(b));
            return self.concat(&a, &b);
        }
        self.arith(Bin::Add, &x, &y)
    }
    fn arith(&mut self, op: Bin, a: &Val<'a>, b: &Val<'a>) -> Val<'a> {
        // Arithmetic reads a known string or list as the number it spells.
        let mut known = |v: &Val<'a>| {
            if matches!(v, Val::Str(_) | Val::Record(_) | Val::Term(_, Ty::Bool)) || v.items().is_some() { self.to_number(v.clone()) } else { v.clone() }
        };
        let (a, b) = (&known(a), &known(b));
        let (Some(lhs), Some(rhs)) = (numeric(a), numeric(b)) else {
            // `undefined` and `NaN` make arithmetic NaN, but `+` concatenates when the other
            // operand may be a string.
            let poisoned = match op {
                Bin::Add => (poisons(a) && numeric_typed(b)) || (poisons(b) && numeric_typed(a)),
                _ => poisons(a) || poisons(b),
            };
            let shape = arithmetic(op, self.shape(a), self.shape(b));
            return if poisoned { Val::NaN } else { self.shaped(op_name(op), &[a, b], Ty::Defined, shape) };
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
            _ => {
                let shape = arithmetic(op, self.shape(a), self.shape(b));
                self.shaped(op_name(op), &[a, b], Ty::Defined, shape)
            }
        }
    }
    fn product(&mut self, x: &Form, y: &Form) -> Val<'a> {
        let (x, y) = (self.b.form(x), self.b.form(y));
        Val::Num(Form::atom(self.b.add(Core::Mul([x, y]))))
    }
    /// `a < b` (strict) or `a <= b`.
    fn order(&mut self, strict: bool, a: &Val<'a>, b: &Val<'a>) -> Val<'a> {
        // A list compares as its text; a known string against a number, as its number.
        let (x, y) = (self.deref(a.clone()), self.deref(b.clone()));
        let object = |v: &Val<'_>| v.items().is_some() || matches!(v, Val::Record(_));
        if object(&x) || object(&y) {
            let text = |l: &mut Self, v: &Val<'a>, contents: Val<'a>| if object(&contents) { l.to_text(v.clone()) } else { contents };
            let (a, b) = (text(self, a, x), text(self, b, y));
            return self.lift2(a, b, Family::Sink, &mut |l, a, b| l.order(strict, &a, &b));
        }
        let (a, b) = (x, y);
        let number = |v: &Val<'_>| matches!(v, Val::Num(_) | Val::NaN | Val::Bool(_) | Val::Undef);
        if (matches!(a, Val::Str(_)) && number(&b)) || (matches!(b, Val::Str(_)) && number(&a)) {
            let numeric = |l: &mut Self, v: Val<'a>| if matches!(v, Val::Str(_)) { l.to_number(v) } else { v };
            let (a, b) = (numeric(self, a), numeric(self, b));
            return self.order(strict, &a, &b);
        }
        let (a, b) = (&a, &b);
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
    /// `SameValueZero`, as `includes` compares: strict equality, except that `NaN` is itself.
    /// Where either side cannot be `NaN`, that is strict equality.
    pub fn same_value_zero(&mut self, a: Val<'a>, b: &Val<'a>) -> Val<'a> {
        self.lift2(a, b.clone(), Family::Sink, &mut |l, a, b| {
            let may_be_nan = |l: &Self, v: &Val<'a>| !matches!(v, Val::Num(_)) && l.shape(v).meets(Shape::NUM);
            if !may_be_nan(l, &a) || !may_be_nan(l, &b) {
                return l.binary(Bin::Eq, a, b);
            }
            match (&a, &b) {
                (Val::NaN, Val::NaN) => Val::Bool(true),
                _ => l.dynamic("same", &[&a, &b], Ty::Bool),
            }
        })
    }
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
        // A declared or widened answer's truth is its exact value's.
        if let Val::Term(id, _) = &v
            && let Some(exact) = self.exact.get(id).cloned()
        {
            return self.truthy(exact);
        }
        self.consume(&v);
        match v {
            Val::Undef | Val::NaN => Val::Bool(false),
            Val::Bool(_) | Val::Throw | Val::Term(_, Ty::Bool) | Val::Split(_) => v,
            Val::Num(f) => match f.known() {
                Some(n) => Val::Bool(n != 0),
                None => self.nonzero(&f),
            },
            Val::Str(s) => Val::Bool(!s.units().is_empty()),
            Val::List(_) | Val::Short(_) | Val::Fun(_) | Val::Builtin(_) | Val::Record(_) | Val::Term(_, Ty::List(_)) | Val::Ref(_) => Val::Bool(true),
            Val::Term(_, Ty::Str) => {
                let eq = self.strict_eq(&v, &Val::Str(Utf16::new([])));
                self.not(eq)
            }
            // Objects, arrays, and functions are truthy; `undefined` is not.
            Val::Term(..) if self.shape(&v).within(Shape::LIST.or(Shape::OBJ).or(Shape::FUN)) => Val::Bool(true),
            Val::Term(..) if self.shape(&v) == Shape::UNDEF => Val::Bool(false),
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
    /// The JavaScript types a lowered value can have.
    pub fn shape(&self, v: &Val<'a>) -> Shape {
        use crate::core::Known;
        match v {
            Val::Undef => Shape::UNDEF,
            Val::NaN | Val::Num(_) => Shape::NUM,
            Val::Throw => Shape::NONE,
            Val::Bool(_) => Shape::BOOL,
            Val::Str(_) => Shape::STR,
            Val::List(_) | Val::Short(_) | Val::Ref(_) => Shape::LIST,
            Val::Fun(_) | Val::Builtin(_) => Shape::FUN,
            Val::Record(_) => Shape::OBJ,
            Val::Split(s) => self.shape(&s.absent).or(self.shape(&s.present)),
            Val::Term(id, ty) => self.b.shape(*id).and(ty.shape()),
        }
    }
    pub fn to_text(&mut self, v: Val<'a>) -> Val<'a> {
        let text = |s: &str| Val::Str(Utf16::new(s.encode_utf16()));
        // An array being written already writes as empty text where it holds itself, as
        // engines join a cyclic array.
        if let Val::Ref(key) = v {
            if self.joining.contains(&key) {
                return text("");
            }
            self.joining.push(key);
            let contents = self.deref(v);
            let out = self.to_text(contents);
            self.joining.pop();
            return out;
        }
        let v = self.deref(v);
        match v {
            Val::Str(_) | Val::Term(_, Ty::Str) | Val::Throw => v,
            Val::Term(_, Ty::Bool) => self.select(&v, text("true"), text("false")),
            Val::Undef => text("undefined"),
            Val::NaN => text("NaN"),
            Val::Bool(b) => text(if b { "true" } else { "false" }),
            Val::Num(ref f) if f.known().is_some() => text(&f.constant.to_string()),
            // A record writes as the text every plain object does, unless it says otherwise.
            Val::Record(ref fields) => {
                let own = ["toString", "valueOf"].iter().any(|n| fields.iter().any(|(k, _)| *k == Utf16::new(n.encode_utf16())));
                if own { self.unsupported() } else { text("[object Object]") }
            }
            // A list's text is its elements joined by commas.
            Val::List(ref items) => self.join_items(items, None),
            Val::Short(ref s) => self.short_method(s, "join", &[]),
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
    /// An operation lowering resolved to no known value, of static type `ty`.
    pub fn dynamic(&mut self, name: &'static str, args: &[&Val<'a>], ty: Ty) -> Val<'a> {
        let shape = match ty {
            Ty::Bool => Shape::BOOL,
            Ty::Str => Shape::STR,
            Ty::List(_) => Shape::LIST,
            Ty::Defined => Shape::DEFINED,
            Ty::Any => Shape::ALL,
        };
        self.shaped(name, args, ty, shape)
    }
    /// [`Self::dynamic`], producing only values of `shape`.
    pub fn shaped(&mut self, name: &'static str, args: &[&Val<'a>], ty: Ty, shape: Shape) -> Val<'a> {
        // A read that may be missing, held inside a list or a record, would reach an operation
        // lowering does not model unlifted: the expression's value is then unknown.
        if args.iter().any(|a| nested_read(a)) {
            self.opaque = true;
        }
        // An operation's name is one of a few, each interned once.
        let named = if let Some(&id) = self.names.get(name) {
            id
        } else {
            let id = self.b.text(Utf16::new(name.encode_utf16()));
            self.names.insert(name, id);
            id
        };
        let mut children = vec![named, self.b.add(Core::Kinds(shape))];
        children.extend(args.iter().map(|v| self.emit(v)));
        let node = if shape.meets(Shape::UNDEF) { Core::DynUndef(children.into()) } else { Core::Dyn(children.into()) };
        Val::Term(self.b.add(node), ty)
    }
}

/// What arithmetic produces: a number, or for `+` a string when it concatenates.
fn arithmetic(op: Bin, a: Shape, b: Shape) -> Shape {
    // `+` concatenates when an operand is, or converts to, a string.
    let textual = Shape::STR.or(Shape::LIST).or(Shape::OBJ).or(Shape::FUN);
    if op == Bin::Add && (a.meets(textual) || b.meets(textual)) { Shape::NUM.or(Shape::STR) } else { Shape::NUM }
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
        (Val::Record(x), Val::Record(y)) => Some(Rc::ptr_eq(x, y)),
        // A record just built is no array and no other object.
        (Val::Record(_), v) | (v, Val::Record(_)) if fresh(v) || matches!(v, Val::Ref(_)) => Some(false),
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
        Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) | Val::Ref(_) | Val::Record(_) => Some(4),
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

/// Whether a value holds, inside a list or a record, a read that may be missing.
fn nested_read(v: &Val<'_>) -> bool {
    fn inside(v: &Val<'_>) -> bool {
        match v {
            Val::Split(_) => true,
            Val::List(items) => items.iter().any(inside),
            Val::Record(fields) => fields.iter().any(|(_, v)| inside(v)),
            _ => false,
        }
    }
    match v {
        Val::List(items) => items.iter().any(inside),
        Val::Record(fields) => fields.iter().any(|(_, v)| inside(v)),
        _ => false,
    }
}
