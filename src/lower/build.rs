//! Interned construction of core terms and emission of lowered values.
use super::value::{Items, Split, Val};
use crate::affine::Form;
use crate::core::{Core, Kind, Known, Shape, Utf16, Variable, items_of, shape_of};
use egg::{Id, Language, RecExpr, Symbol};
use std::collections::HashMap;

#[derive(Default)]
pub struct Builder {
    out: RecExpr<Core>,
    intern: HashMap<Core, Id>,
    fresh: u32,
    /// Each term's shape and, for a list, its elements' shape, as the analysis computes them.
    facts: Vec<(Shape, Shape)>,
}

impl Known for Builder {
    fn shape(&self, id: Id) -> Shape {
        self.facts[usize::from(id)].0
    }
    fn items(&self, id: Id) -> Shape {
        self.facts[usize::from(id)].1
    }
    fn returns(&self, lam: Id) -> (Shape, Shape) {
        match &self.out[lam] {
            Core::Lam(children) => children.last().map_or((Shape::ALL, Shape::ALL), |&body| self.facts[usize::from(body)]),
            _ => (Shape::ALL, Shape::ALL),
        }
    }
    fn declared(&self, id: Id) -> Option<Shape> {
        if let Core::Kinds(s) = self.out[id] { Some(s) } else { None }
    }
}

impl Builder {
    pub fn add(&mut self, node: Core) -> Id {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let facts = (shape_of(&node, self), items_of(&node, self));
        let id = self.out.add(node.clone());
        self.facts.push(facts);
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
        self.fresh_shaped(kind, kind.shape())
    }
    /// A fresh binder whose values have `shape`.
    pub fn fresh_shaped(&mut self, kind: Kind, shape: Shape) -> Id {
        self.fresh += 1;
        let name = format!("@{}", self.fresh);
        self.shaped_var(kind, &name, shape)
    }
    /// A fresh binder for an element of a list with these elements.
    pub fn element(&mut self, items: Items) -> Id {
        self.fresh_shaped(items.kind(), items.0)
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
    /// Whether the term depends on a read that may be missing.
    pub fn reads(&self, id: Id) -> bool {
        let (mut seen, mut stack) = (std::collections::HashSet::new(), vec![id]);
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            match &self.out[id] {
                Core::Read(_) | Core::Maybe(_) | Core::Elim(_) | Core::Escape(_) => return true,
                n => stack.extend(n.children()),
            }
        }
        false
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
    /// A list's cells. A read at another collection's coordinate that is still undefined
    /// where missing leaves a hole there, however the list was built.
    fn list(&mut self, items: &[Val<'_>]) -> Id {
        let nil = self.add(Core::Nil);
        items.iter().rev().fold(nil, |tail, item| {
            let head = self.emit(item);
            let head = match item {
                Val::Split(s) if s.drift && matches!(s.absent, Val::Undef) => {
                    let has = self.has(s.read);
                    self.add(Core::Escape([head, has]))
                }
                _ => head,
            };
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
