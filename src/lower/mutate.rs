//! In-place mutation: how a mutating method or an assignment updates an array's contents,
//! and which mutations someone outside the expression can observe.
use super::Lowerer;
use super::expr::Arm;
use super::ops::Bin;
use super::value::{Items, Seq, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Mutator, Utf16};
use oxc_ast::ast::{AssignmentExpression, AssignmentTarget, Expression, SimpleAssignmentTarget, UpdateExpression};
use oxc_syntax::operator::{AssignmentOperator, UpdateOperator};
use std::rc::Rc;

/// Where an assignment writes: an element, or a named property.
#[derive(Clone)]
pub enum Key<'a> {
    Index(Val<'a>),
    Name(&'a str),
}

impl<'a> Lowerer<'a, '_> {
    /// `receiver.m(...args)`. The receiver's contents update, and the mutation is logged
    /// unless only the expression holds the receiver.
    pub fn mutate(&mut self, receiver: Val<'a>, m: Mutator, args: &[Val<'a>]) -> Val<'a> {
        match receiver {
            Val::Split(_) => self.lift(receiver, Family::Propagate, &mut |l, r| l.mutate(r, m, args)),
            Val::Undef | Val::Throw => Val::Throw,
            Val::Ref(_) => {
                let stored: Vec<Val<'a>> = args.iter().map(|v| self.own(v.clone())).collect();
                let contents = self.deref(receiver.clone());
                let (result, after) = if buries(&contents, &stored) { self.unknown_update(m) } else { self.update(m, contents, &stored) };
                if matches!(result, Val::Throw) {
                    return Val::Throw;
                }
                self.assign(&receiver, after);
                self.log(m, &receiver, &stored);
                if returns_receiver(m) { receiver } else { result }
            }
            v if v.items().is_some() => {
                // An array without identity is one just built: wherever an array can be held,
                // lowering gives it a reference, so nothing else holds this one.
                let (result, after) = self.update(m, v, args);
                if returns_receiver(m) && !matches!(result, Val::Throw) { after } else { result }
            }
            Val::Term(_, Ty::Defined | Ty::Any) => {
                // An object of unknown type: the mutation is logged by who holds it, and its
                // result is unknown.
                self.untracked(m, &receiver, args);
                let mut parts = vec![&receiver];
                parts.extend(args);
                self.dynamic(m.name(), &parts, Ty::Any)
            }
            Val::Fun(_) | Val::Builtin(_) => self.unsupported(),
            _ => Val::Throw,
        }
    }
    /// A mutation of an object the store does not track. The caller's objects, and arrays a
    /// map built for each element, are distinct from every array the store holds; an object
    /// of unknown holder may be one of them, so then no array's contents are known afterward.
    fn untracked(&mut self, m: Mutator, target: &Val<'a>, stored: &[Val<'a>]) {
        let owner = self.owner(target);
        self.log(m, target, stored);
        if !matches!(self.b.node(owner), Core::External | Core::Internal) {
            self.clobber();
        }
    }
    /// A mutation whose effect on a symbolic list's contents would hold another array only as
    /// a snapshot: its result and the contents after it are unknown.
    fn unknown_update(&mut self, m: Mutator) -> (Val<'a>, Val<'a>) {
        let after = self.unknown_list();
        let result = match m {
            Mutator::Push | Mutator::Unshift => self.dynamic("length", &[&after], Ty::Defined),
            Mutator::Splice => self.unknown_list(),
            _ => Val::Undef,
        };
        (result, after)
    }
    /// A mutating method's result, and the array's contents after it.
    fn update(&mut self, m: Mutator, c: Val<'a>, args: &[Val<'a>]) -> (Val<'a>, Val<'a>) {
        match m {
            Mutator::Push | Mutator::Unshift => {
                let added = Val::List(Rc::new(args.to_vec()));
                let after = if m == Mutator::Push { self.append(c, added) } else { self.append(added, c) };
                (self.length(after.clone()), after)
            }
            Mutator::Pop => self.take(c, true),
            Mutator::Shift => self.take(c, false),
            Mutator::Reverse => (Val::Undef, self.reversed(c)),
            Mutator::Sort => self.sorted(c, args.first().unwrap_or(&Val::Undef)),
            Mutator::Splice => self.spliced(&c, args),
            Mutator::Fill => match (&c, args) {
                (Val::List(items), [v]) => (Val::Undef, Val::List(Rc::new(vec![v.clone(); items.len()]))),
                _ => (Val::Undef, self.unknown_after(m, &c, args)),
            },
            Mutator::CopyWithin | Mutator::Assign | Mutator::Delete => (Val::Undef, self.unknown_after(m, &c, args)),
        }
    }
    /// `pop` (the last element) or `shift` (the first), and what remains.
    fn take(&mut self, c: Val<'a>, last: bool) -> (Val<'a>, Val<'a>) {
        if let Val::Split(_) = c {
            let taken = self.lift(c.clone(), Family::Propagate, &mut |l, c| l.take(c, last).0);
            let rest = self.lift(c, Family::Propagate, &mut |l, c| l.take(c, last).1);
            return (taken, rest);
        }
        match c {
            Val::List(items) => {
                let mut rest = items.to_vec();
                let taken = if last { rest.pop() } else if rest.is_empty() { None } else { Some(rest.remove(0)) };
                (taken.unwrap_or(Val::Undef), Val::List(Rc::new(rest)))
            }
            Val::Short(s) => (self.short_element(&s), Val::empty()),
            Val::Term(id, Ty::List(items)) => {
                let seq = Seq { id, items };
                let len = Form::atom(self.b.add(Core::Len(id)));
                let end = len.plus(&Form::constant(1), -1).unwrap_or_default();
                let (index, from, to) = if last { (end.clone(), Form::constant(0), end) } else { (Form::constant(0), Form::constant(1), len) };
                let taken = self.element(seq, &index);
                (taken, self.slice(seq, Some(Val::Num(from)), Some(Val::Num(to))))
            }
            c => (self.unsupported(), c),
        }
    }
    fn reversed(&mut self, c: Val<'a>) -> Val<'a> {
        match c {
            Val::Split(_) => self.lift(c, Family::Propagate, &mut |l, c| l.reversed(c)),
            Val::List(items) => Val::List(Rc::new(items.iter().rev().cloned().collect())),
            Val::Term(id, Ty::List(items)) => Seq { id: self.b.add(Core::Reverse(id)), items }.val(),
            c => c,
        }
    }
    /// `sort(cmp)`: a literal list of known values in JavaScript's default order, and
    /// otherwise a sort term. A comparator that is not a function throws.
    fn sorted(&mut self, c: Val<'a>, cmp: &Val<'a>) -> (Val<'a>, Val<'a>) {
        if !matches!(cmp, Val::Undef | Val::Fun(_) | Val::Term(_, Ty::Defined | Ty::Any)) {
            return (Val::Throw, c);
        }
        if let Val::Split(_) = c {
            return (Val::Undef, self.lift(c, Family::Propagate, &mut |l, c| l.sorted(c, cmp).1));
        }
        // A list of at most one element is already in order, and the comparator never runs.
        if matches!(&c, Val::List(items) if items.len() < 2) {
            return (Val::Undef, c);
        }
        if let Val::List(ref items) = c
            && items.iter().any(|v| matches!(v, Val::Split(_)))
        {
            let items = items.clone();
            return (Val::Undef, self.settled(&items, Family::Propagate, &mut |l, c| l.sorted(c, cmp).1));
        }
        let list = match c {
            Val::List(ref items) if matches!(cmp, Val::Undef) => match default_order(items) {
                Some(sorted) => return (Val::Undef, Val::List(Rc::new(sorted))),
                None => self.seq(items),
            },
            Val::List(ref items) => self.seq(items),
            Val::Term(id, Ty::List(items)) => Seq { id, items },
            c => return (Val::Undef, c),
        };
        let f = self.comparator(cmp, list);
        (Val::Undef, Seq { id: self.b.add(Core::Sort([f, list.id])), items: list.items }.val())
    }
    /// A comparator's lambda over two fresh elements, lowered once for every pair it sees.
    fn comparator(&mut self, cmp: &Val<'a>, list: Seq) -> egg::Id {
        match cmp {
            Val::Undef => self.b.add(Core::Undef),
            Val::Fun(_) => {
                let (a, b) = (self.b.element(list.items), self.b.element(list.items));
                self.members.extend([(a, list.id), (b, list.id)]);
                let args = vec![Val::Term(a, list.items.ty()), Val::Term(b, list.items.ty())];
                // A comparator runs only on a list of two or more.
                let out = self.repeat(list.id, 2, |l| l.apply(cmp.clone(), args));
                let body = self.emit(&out);
                self.b.add(Core::Lam(vec![a, b, body].into()))
            }
            other => {
                let lam = self.emit(other);
                self.clobber();
                lam
            }
        }
    }
    /// `splice(start, count, ...items)`: the removed elements, and what remains.
    fn spliced(&mut self, c: &Val<'a>, args: &[Val<'a>]) -> (Val<'a>, Val<'a>) {
        if let Val::List(items) = c
            && let Some((start, count)) = splice_bounds(items.len(), args)
        {
            let mut rest = items.to_vec();
            let removed: Vec<Val<'a>> = rest.splice(start..start + count, args.iter().skip(2).cloned()).collect();
            return (Val::List(Rc::new(removed)), Val::List(Rc::new(rest)));
        }
        let mut parts = vec![c];
        parts.extend(args);
        let removed = self.dynamic("spliced", &parts, Ty::List(Items::ANY));
        (removed, self.unknown_after(Mutator::Splice, c, args))
    }
    /// Contents after a mutation lowering does not compute: a list of unknown elements.
    fn unknown_after(&mut self, m: Mutator, c: &Val<'a>, args: &[Val<'a>]) -> Val<'a> {
        let mut parts = vec![c];
        parts.extend(args);
        self.dynamic(m.name(), &parts, Ty::List(Items::ANY))
    }
}

impl<'a> Lowerer<'a, '_> {
    /// `target = value`, and its arithmetic and logical compound forms, on an element or a
    /// property.
    pub fn assignment(&mut self, a: &'a AssignmentExpression<'a>) -> Val<'a> {
        let Some((object, key)) = self.target(&a.left) else { return self.unsupported() };
        let value = match a.operator {
            AssignmentOperator::Assign => self.expr(&a.right),
            op => {
                let old = self.get(object.clone(), &key);
                match op {
                    AssignmentOperator::Addition => self.compound(Bin::Add, old, &a.right),
                    AssignmentOperator::Subtraction => self.compound(Bin::Sub, old, &a.right),
                    AssignmentOperator::Multiplication => self.compound(Bin::Mul, old, &a.right),
                    AssignmentOperator::LogicalNullish => self.coalesce(old, Arm::Expr(&a.right)),
                    AssignmentOperator::LogicalOr => self.short_circuit(old, Arm::Expr(&a.right), true),
                    AssignmentOperator::LogicalAnd => self.short_circuit(old, Arm::Expr(&a.right), false),
                    _ => return self.unsupported(),
                }
            }
        };
        self.store_at(object, &key, value)
    }
    fn compound(&mut self, op: Bin, old: Val<'a>, right: &'a Expression<'a>) -> Val<'a> {
        let right = self.expr(right);
        self.binary(op, old, right)
    }
    /// `++` and `--` on an element or a property.
    pub fn increment(&mut self, u: &'a UpdateExpression<'a>) -> Val<'a> {
        let Some((object, key)) = self.simple_target(&u.argument) else { return self.unsupported() };
        let old = self.get(object.clone(), &key);
        let old = self.binary(Bin::Sub, old, Val::int(0));
        let step = if u.operator == UpdateOperator::Increment { Bin::Add } else { Bin::Sub };
        let new = self.binary(step, old.clone(), Val::int(1));
        let stored = self.store_at(object, &key, new);
        if u.prefix { stored } else { self.strict(vec![stored], &mut |_, _| old.clone()) }
    }
    /// `delete target`: an element removed leaves a hole lowering does not model.
    pub fn delete(&mut self, target: &'a Expression<'a>) -> Val<'a> {
        let (object, key) = match target.without_parentheses() {
            Expression::ComputedMemberExpression(m) if !m.optional => (self.expr(&m.object), Key::Index(self.expr(&m.expression))),
            Expression::StaticMemberExpression(m) if !m.optional => (self.expr(&m.object), Key::Name(m.property.name.as_str())),
            _ => return self.unsupported(),
        };
        let key = match key {
            Key::Index(k) => k,
            Key::Name(name) => Val::Str(Utf16::new(name.encode_utf16())),
        };
        self.strict(vec![object, key], &mut |l, mut vals| {
            let (object, key) = (vals.remove(0), vals.remove(0));
            l.erase(object, &key)
        })
    }
    fn erase(&mut self, object: Val<'a>, key: &Val<'a>) -> Val<'a> {
        match object {
            Val::Split(_) => self.lift(object, Family::Propagate, &mut |l, o| l.erase(o, key)),
            Val::Undef | Val::Throw => Val::Throw,
            Val::Ref(_) => {
                let contents = self.deref(object.clone());
                let after = self.unknown_after(Mutator::Delete, &contents, std::slice::from_ref(key));
                self.assign(&object, after);
                self.log(Mutator::Delete, &object, &[]);
                Val::Bool(true)
            }
            Val::Term(_, Ty::Defined | Ty::Any) => {
                self.untracked(Mutator::Delete, &object, &[]);
                Val::Bool(true)
            }
            _ => Val::Bool(true),
        }
    }
    /// The object and key an assignment target names, evaluated.
    fn target(&mut self, t: &'a AssignmentTarget<'a>) -> Option<(Val<'a>, Key<'a>)> {
        match t {
            AssignmentTarget::ComputedMemberExpression(m) if !m.optional => Some((self.expr(&m.object), Key::Index(self.expr(&m.expression)))),
            AssignmentTarget::StaticMemberExpression(m) if !m.optional => Some((self.expr(&m.object), Key::Name(m.property.name.as_str()))),
            _ => None,
        }
    }
    fn simple_target(&mut self, t: &'a SimpleAssignmentTarget<'a>) -> Option<(Val<'a>, Key<'a>)> {
        match t {
            SimpleAssignmentTarget::ComputedMemberExpression(m) if !m.optional => Some((self.expr(&m.object), Key::Index(self.expr(&m.expression)))),
            SimpleAssignmentTarget::StaticMemberExpression(m) if !m.optional => Some((self.expr(&m.object), Key::Name(m.property.name.as_str()))),
            _ => None,
        }
    }
    fn get(&mut self, object: Val<'a>, key: &Key<'a>) -> Val<'a> {
        match key {
            Key::Index(k) => self.read(object, k.clone()),
            Key::Name(name) => self.property(object, name),
        }
    }
    /// Write `value` once the object, key, and value are evaluated; the assignment's value.
    fn store_at(&mut self, object: Val<'a>, key: &Key<'a>, value: Val<'a>) -> Val<'a> {
        let index = match key {
            Key::Index(k) => k.clone(),
            Key::Name(_) => Val::Undef,
        };
        self.strict(vec![object, index, value], &mut |l, mut vals| {
            let (object, index, value) = (vals.remove(0), vals.remove(0), vals.remove(0));
            let key = match key {
                Key::Index(_) => Key::Index(index),
                Key::Name(name) => Key::Name(name),
            };
            l.set(object, &key, value)
        })
    }
    fn set(&mut self, object: Val<'a>, key: &Key<'a>, value: Val<'a>) -> Val<'a> {
        match object {
            Val::Split(_) => self.lift(object, Family::Propagate, &mut |l, o| l.set(o, key, value.clone())),
            Val::Undef | Val::Throw => Val::Throw,
            // An array's length must be a non-negative integer.
            Val::Ref(_) if matches!(key, Key::Name("length")) && invalid_length(&value) => Val::Throw,
            Val::Ref(_) => {
                let value = self.own(value);
                let contents = self.deref(object.clone());
                let after = if buries(&contents, std::slice::from_ref(&value)) { self.unknown_list() } else { self.written(contents, key, &value) };
                self.assign(&object, after);
                self.log(Mutator::Assign, &object, std::slice::from_ref(&value));
                value
            }
            Val::Term(_, Ty::Defined | Ty::Any) => {
                self.untracked(Mutator::Assign, &object, std::slice::from_ref(&value));
                value
            }
            // An array just built, which nothing else holds.
            v if v.items().is_some() => value,
            _ => self.unsupported(),
        }
    }
    /// An array's contents after writing `value` at `key`.
    fn written(&mut self, c: Val<'a>, key: &Key<'a>, value: &Val<'a>) -> Val<'a> {
        let known = |v: &Val<'a>| match v {
            Val::Num(f) => f.known(),
            _ => None,
        };
        match (key, c) {
            (Key::Name("length"), _) if known(value) == Some(0) => Val::empty(),
            (Key::Name("length"), Val::List(items)) if known(value).is_some_and(|n| usize::try_from(n).is_ok_and(|n| n <= items.len())) => {
                let n = known(value).and_then(|n| usize::try_from(n).ok()).unwrap_or(0);
                Val::List(Rc::new(items[..n].to_vec()))
            }
            (Key::Name(name), c) if *name != "length" => c,
            (Key::Index(k), c) if known(k).is_some_and(|k| k < 0) => c,
            (Key::Index(k), Val::List(items)) if known(k).and_then(|k| usize::try_from(k).ok()).is_some_and(|k| k <= items.len()) => {
                let k = known(k).and_then(|k| usize::try_from(k).ok()).unwrap_or(0);
                let mut items = items.to_vec();
                if k == items.len() { items.push(value.clone()) } else { items[k] = value.clone() }
                Val::List(Rc::new(items))
            }
            (key, c) => {
                let at = match key {
                    Key::Index(k) => k.clone(),
                    Key::Name(name) => Val::Str(Utf16::new(name.encode_utf16())),
                };
                self.unknown_after(Mutator::Assign, &c, &[at, value.clone()])
            }
        }
    }
}

/// Whether storing these values into these contents would put an array with identity inside a
/// term, where only its contents at this moment survive.
fn buries(contents: &Val<'_>, stored: &[Val<'_>]) -> bool {
    !matches!(contents, Val::List(_)) && stored.iter().any(super::refs::holds_ref)
}

/// A value that is certainly not a valid array length.
fn invalid_length(v: &Val<'_>) -> bool {
    match v {
        Val::Num(f) => f.known().is_some_and(|n| n < 0),
        Val::Undef | Val::NaN => true,
        _ => false,
    }
}

/// Whether the method returns its receiver: `sort`, `reverse`, `fill`, and `copyWithin`.
fn returns_receiver(m: Mutator) -> bool {
    matches!(m, Mutator::Sort | Mutator::Reverse | Mutator::Fill | Mutator::CopyWithin)
}

/// JavaScript's default sort of known values: by their text in UTF-16 code units, stably,
/// with `undefined` last.
fn default_order<'a>(items: &[Val<'a>]) -> Option<Vec<Val<'a>>> {
    let text = |v: &Val<'_>| -> Option<Vec<u16>> {
        Some(match v {
            Val::Str(s) => s.units(),
            Val::Num(f) => f.known()?.to_string().encode_utf16().collect(),
            Val::Bool(b) => b.to_string().encode_utf16().collect(),
            Val::NaN => "NaN".encode_utf16().collect(),
            _ => return None,
        })
    };
    let mut keyed = Vec::new();
    let mut undefined = Vec::new();
    for v in items {
        match v {
            Val::Undef => undefined.push(v.clone()),
            v => keyed.push((text(v)?, v.clone())),
        }
    }
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    Some(keyed.into_iter().map(|(_, v)| v).chain(undefined).collect())
}

/// `splice`'s start and delete count on a list of known length, when the arguments are known.
fn splice_bounds(len: usize, args: &[Val<'_>]) -> Option<(usize, usize)> {
    let len = i64::try_from(len).ok()?;
    let integer = |v: Option<&Val<'_>>| match v {
        None | Some(Val::Undef) => Some(0),
        Some(Val::Num(f)) => f.known(),
        _ => None,
    };
    let start = integer(args.first())?;
    let start = if start < 0 { (len + start).max(0) } else { start.min(len) };
    let count = match args.len() {
        0 => 0,
        1 => len - start,
        _ => integer(args.get(1))?.clamp(0, len - start),
    };
    Some((usize::try_from(start).ok()?, usize::try_from(count).ok()?))
}
