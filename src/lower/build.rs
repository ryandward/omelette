//! Interned construction of core terms and emission of lowered values.
use super::value::{Split, Val};
use crate::affine::Form;
use crate::core::{Core, Kind, Utf16, Variable};
use egg::{Id, Language, RecExpr, Symbol};
use std::collections::HashMap;

#[derive(Default)]
pub struct Builder {
    out: RecExpr<Core>,
    intern: HashMap<Core, Id>,
    fresh: u32,
}

impl Builder {
    pub fn add(&mut self, node: Core) -> Id {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = self.out.add(node.clone());
        self.intern.insert(node, id);
        id
    }
    pub fn int(&mut self, n: i64) -> Id {
        self.add(Core::Int(n))
    }
    pub fn boolean(&mut self, b: bool) -> Id {
        self.add(if b { Core::True } else { Core::False })
    }
    pub fn var(&mut self, kind: Kind, name: &str) -> Id {
        self.shaped_var(kind, name, kind.shape())
    }
    pub fn shaped_var(&mut self, kind: Kind, name: &str, shape: crate::core::Shape) -> Id {
        let name = Symbol::from(name);
        self.add(Core::Var(Variable { kind, name, shape }))
    }
    /// A binder no other term mentions.
    pub fn fresh(&mut self, kind: Kind) -> Id {
        self.fresh += 1;
        let name = format!("@{}", self.fresh);
        self.var(kind, &name)
    }
    /// A construct lowering does not model, kept distinct from every other.
    pub fn unsupported(&mut self) -> Id {
        self.fresh += 1;
        let tag = self.int(i64::from(self.fresh));
        self.add(Core::Unsupported(tag))
    }
    /// The canonical term of an affine sum: atoms in id order, constants folded.
    pub fn form(&mut self, form: &Form) -> Id {
        if let Some(n) = form.known() {
            return self.int(n);
        }
        if let Some(atom) = form.single() {
            return atom;
        }
        let mut children = vec![self.int(form.constant)];
        for (&atom, &c) in &form.terms {
            children.push(self.int(c));
            children.push(atom);
        }
        self.add(Core::Lin(children.into()))
    }
    /// `0 <= form`, decided when the form is known.
    pub fn nonnegative(&mut self, form: &Form) -> Val<'static> {
        if let Some(n) = form.known() {
            return Val::Bool(n >= 0);
        }
        let zero = self.int(0);
        let sum = self.form(form);
        Val::Term(self.add(Core::Le([zero, sum])), super::value::Ty::Bool)
    }
    pub fn node(&self, id: Id) -> &Core {
        &self.out[id]
    }
    /// Whether the term `id` mentions the term `var`.
    pub fn mentions(&self, id: Id, var: Id) -> bool {
        id == var || self.out[id].children().iter().any(|&c| self.mentions(c, var))
    }
    pub fn finish(&self, root: Id) -> RecExpr<Core> {
        self.out[root].build_recexpr(|id| self.out[id].clone())
    }
}

impl Builder {
    /// The term for a value. A function escaping as data is not modeled.
    pub fn emit(&mut self, v: &Val<'_>) -> Id {
        match v {
            Val::Undef => self.add(Core::Undef),
            Val::NaN => self.add(Core::NaN),
            Val::Throw => self.add(Core::Throw),
            Val::Bool(b) => self.boolean(*b),
            Val::Num(f) => self.form(f),
            Val::Str(s) => self.add(Core::Str(*s)),
            Val::List(items) => self.list(items),
            Val::Short(short) => short.list.id,
            Val::Fun(_) => self.unsupported(),
            // The global itself: a function the graph knows only by name.
            Val::Builtin(b) => self.var(Kind::Fun, b.name()),
            Val::Term(id, _) => *id,
            Val::Split(s) => self.split(s),
            Val::Ref(_) => unreachable!("lowering resolves references before emitting"),
        }
    }
    fn list(&mut self, items: &[Val<'_>]) -> Id {
        let nil = self.add(Core::Nil);
        items.iter().rev().fold(nil, |tail, item| {
            let head = self.emit(item);
            self.add(Core::Cons([head, tail]))
        })
    }
    fn split(&mut self, s: &Split<'_>) -> Id {
        // Nothing happened to the read: it is still undefined where missing and the element
        // where present.
        let passes = matches!(s.present, Val::Term(id, _) if id == s.elem);
        if matches!(s.absent, Val::Undef) && passes {
            return s.read;
        }
        let absent = self.emit(&s.absent);
        let present = self.emit(&s.present);
        let flow = self.add(Core::Flow(s.family));
        let lam = self.add(Core::Lam(vec![s.elem, present].into()));
        let has = self.has(s.read);
        self.add(Core::Maybe([flow, absent, lam, s.read, has]))
    }
    /// The presence test of a read node.
    pub fn has(&mut self, read: Id) -> Id {
        let Core::Read(children) = self.out[read] else { unreachable!("a split's read is a read node") };
        self.add(Core::Has(children))
    }
    pub fn text(&mut self, s: Utf16) -> Id {
        self.add(Core::Str(s))
    }
}
