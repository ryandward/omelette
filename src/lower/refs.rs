//! References: arrays with identity, their contents in the store, the log of mutations
//! someone outside the expression can observe, and how both follow lowering's worlds.
use super::Lowerer;
use super::ops::Op;
use super::value::{Items, RefKey, Split, Ty, Val};
use crate::core::{Core, Kind, Mutator};
use egg::Id;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// What lowering has learned along one path: each written reference's current contents, the
/// local arrays someone outside now holds, the observable mutations so far (a list of
/// `mutate` terms), and how many times code lowering cannot see has run, after which no
/// array's contents are known.
#[derive(Clone)]
pub struct State<'a> {
    pub cells: Rc<HashMap<RefKey, Val<'a>>>,
    pub escaped: Rc<HashSet<RefKey>>,
    pub log: Val<'a>,
    pub epoch: u32,
}

impl State<'_> {
    pub fn new() -> Self {
        Self { cells: Rc::default(), escaped: Rc::default(), log: Val::empty(), epoch: 0 }
    }
    pub fn same(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.cells, &other.cells)
            && Rc::ptr_eq(&self.escaped, &other.escaped)
            && self.log.identical(&other.log)
            && self.epoch == other.epoch
    }
}

impl<'a> Lowerer<'a, '_> {
    /// An array's current contents: what the store holds for a reference, or the value itself.
    pub fn deref(&mut self, v: Val<'a>) -> Val<'a> {
        let Val::Ref(key) = v else { return v };
        if let Some(contents) = self.state.cells.get(&key) {
            return contents.clone();
        }
        match key {
            RefKey::Input(name) if self.state.epoch == 0 => Val::Term(self.b.var(Kind::List, name.as_str()), Ty::List(Items::Defined)),
            RefKey::Input(name) => {
                let (var, epoch) = (Val::Term(self.b.var(Kind::List, name.as_str()), Ty::Any), Val::int(i64::from(self.state.epoch)));
                self.dynamic("havoc", &[&var, &epoch], Ty::List(Items::Any))
            }
            RefKey::Choice(n) => {
                let (test, a, b) = self.choices[n].clone();
                let (a, b) = (self.deref(a), self.deref(b));
                self.select(&test, a, b)
            }
            RefKey::Local(_) => unreachable!("a local reference is stored when it is made"),
        }
    }
    /// Give a fresh array an identity, so a mutation through any of its names reaches all of
    /// them. A split gives each side's array its own.
    pub fn own(&mut self, v: Val<'a>) -> Val<'a> {
        match v {
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => {
                self.next_ref += 1;
                let key = RefKey::Local(self.next_ref);
                self.write(key, v);
                Val::Ref(key)
            }
            Val::Split(s) => {
                let (absent, present) = (self.own(s.absent.clone()), self.own(s.present.clone()));
                Val::Split(Rc::new(Split { absent, present, ..(*s).clone() }))
            }
            v => v,
        }
    }
    /// An array lowering recomputes at a fixed place, such as a mapped list's element, keeps
    /// one identity there.
    pub fn held(&mut self, place: (Id, Id), v: Val<'a>) -> Val<'a> {
        if !matches!(v, Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_))) {
            return v;
        }
        if let Some(&key) = self.places.get(&place)
            && self.state.cells.contains_key(&key)
        {
            return Val::Ref(key);
        }
        let owned = self.own(v);
        if let Val::Ref(key) = owned {
            self.places.insert(place, key);
        }
        owned
    }
    pub fn write(&mut self, key: RefKey, contents: Val<'a>) {
        Rc::make_mut(&mut self.state.cells).insert(key, contents);
    }
    /// Store new contents through a reference. A choice updates each alternative where the
    /// test picks it.
    pub fn assign(&mut self, target: &Val<'a>, contents: Val<'a>) {
        match target {
            Val::Ref(RefKey::Choice(n)) => {
                let (test, a, b) = self.choices[*n].clone();
                let (old_a, old_b) = (self.deref(a.clone()), self.deref(b.clone()));
                let new_a = self.select(&test, contents.clone(), old_a);
                let new_b = self.select(&test, old_b, contents);
                self.assign(&a, new_a);
                self.assign(&b, new_b);
            }
            Val::Ref(key) => self.write(*key, contents),
            _ => {}
        }
    }
    /// One of two references, chosen by a symbolic test.
    pub fn choice(&mut self, test: Val<'a>, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        self.choices.push((test, a, b));
        Val::Ref(RefKey::Choice(self.choices.len() - 1))
    }
    /// The term for a value, every reference in it replaced by its current contents.
    pub fn emit(&mut self, v: &Val<'a>) -> Id {
        if !holds_ref(v) {
            return self.b.emit(v);
        }
        let resolved = self.resolve(v.clone());
        self.b.emit(&resolved)
    }
    fn resolve(&mut self, v: Val<'a>) -> Val<'a> {
        match v {
            Val::Ref(_) => {
                let contents = self.deref(v);
                self.resolve(contents)
            }
            Val::List(items) if items.iter().any(holds_ref) => Val::List(Rc::new(items.iter().map(|v| self.resolve(v.clone())).collect())),
            Val::Split(s) if holds_ref(&s.absent) || holds_ref(&s.present) => {
                let (absent, present) = (self.resolve(s.absent.clone()), self.resolve(s.present.clone()));
                Val::Split(Rc::new(Split { absent, present, ..(*s).clone() }))
            }
            v => v,
        }
    }
    /// The array a method's callback receives as its third argument: the receiver itself.
    pub fn this_or(&self, contents: Val<'a>) -> Val<'a> {
        self.this.clone().unwrap_or(contents)
    }
}

impl<'a, 'l> Lowerer<'a, 'l> {
    /// Lower two alternatives, `side(false)` and `side(true)`, from the same state, then join
    /// what each wrote and logged.
    pub fn fork(&mut self, side: &mut dyn FnMut(&mut Self, bool) -> Val<'a>, join: &mut Op<'a, 'l, '_>) -> (Val<'a>, Val<'a>) {
        let base = self.state.clone();
        let a = side(self, false);
        let after_a = std::mem::replace(&mut self.state, base.clone());
        let b = side(self, true);
        let after_b = std::mem::replace(&mut self.state, base.clone());
        if !(after_a.same(&base) && after_b.same(&base)) {
            self.state = self.merge(after_a, after_b, join);
        }
        (a, b)
    }
    /// Join two states that grew from the current one.
    fn merge(&mut self, a: State<'a>, b: State<'a>, join: &mut Op<'a, 'l, '_>) -> State<'a> {
        let keys: HashSet<RefKey> = a.cells.keys().chain(b.cells.keys()).copied().collect();
        let mut cells = (*self.state.cells).clone();
        for key in keys {
            let merged = match (a.cells.get(&key), b.cells.get(&key)) {
                (Some(x), Some(y)) if x.identical(y) => x.clone(),
                // An array allocated on one side only: nothing on the other side holds it.
                (Some(x), None) | (None, Some(x)) if matches!(key, RefKey::Local(_)) && !self.state.cells.contains_key(&key) => x.clone(),
                (x, y) => {
                    let (x, y) = (x.cloned(), y.cloned());
                    let x = x.unwrap_or_else(|| self.deref(Val::Ref(key)));
                    let y = y.unwrap_or_else(|| self.deref(Val::Ref(key)));
                    join(self, x, y)
                }
            };
            cells.insert(key, merged);
        }
        let escaped = a.escaped.union(&b.escaped).copied().collect();
        let log = if a.log.identical(&b.log) { a.log } else { join(self, a.log, b.log) };
        State { cells: Rc::new(cells), escaped: Rc::new(escaped), log, epoch: a.epoch.max(b.epoch) }
    }
    /// Lower a callback that runs once per element of `list`, any number of times: what it
    /// wrote to arrays that outlive it is unknown afterward, and what it logged happens only
    /// where the list is non-empty.
    pub fn repeat(&mut self, list: Id, body: impl FnOnce(&mut Self) -> Val<'a>) -> Val<'a> {
        let base = self.state.clone();
        let out = body(self);
        if self.state.same(&base) {
            return out;
        }
        let after = std::mem::replace(&mut self.state, base.clone());
        let outlive = |k: &RefKey| base.cells.contains_key(k) || matches!(k, RefKey::Input(_));
        let written: Vec<RefKey> =
            after.cells.iter().filter(|(k, v)| outlive(k) && base.cells.get(k).is_none_or(|old| !old.identical(v))).map(|(k, _)| *k).collect();
        self.state.cells = after.cells;
        self.state.escaped = after.escaped;
        for key in written {
            let unknown = self.unknown_list();
            self.write(key, unknown);
        }
        if !after.log.identical(&base.log) {
            let len = crate::affine::Form::atom(self.b.add(Core::Len(list)));
            let nonempty = self.b.nonnegative(&len.plus(&crate::affine::Form::constant(1), -1).unwrap_or_default());
            self.state.log = self.select(&nonempty, after.log, base.log);
        }
        out
    }
    /// Lower something only to learn about it, leaving the store, the log, and opacity as they
    /// were.
    pub fn speculate<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let (state, opaque) = (self.state.clone(), self.opaque);
        let out = body(self);
        (self.state, self.opaque) = (state, opaque);
        out
    }
    /// Code lowering cannot see ran: it may have changed any array, so none has known contents
    /// afterward, and the expression's value is unknown.
    pub fn clobber(&mut self) {
        self.opaque = true;
        let keys: Vec<RefKey> = self.state.cells.keys().copied().collect();
        for key in keys {
            let unknown = self.unknown_list();
            self.write(key, unknown);
        }
        self.state.epoch += 1;
    }
    /// Contents lowering no longer knows.
    fn unknown_list(&mut self) -> Val<'a> {
        self.next_ref += 1;
        let tag = Val::int(i64::from(self.next_ref));
        self.dynamic("havoc", &[&tag], Ty::List(Items::Any))
    }
}

impl<'a> Lowerer<'a, '_> {
    /// The term for who holds the array or object `v` reaches: someone outside the
    /// expression, the expression itself, or unknown; for a choice, an `if` over its
    /// alternatives' holders.
    pub fn owner(&mut self, target: &Val<'a>) -> Id {
        match target {
            Val::Ref(RefKey::Input(_)) => self.b.add(Core::External),
            Val::Ref(key @ RefKey::Local(_)) if self.state.escaped.contains(key) => self.b.add(Core::External),
            Val::Ref(RefKey::Local(_)) | Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => self.b.add(Core::Internal),
            Val::Ref(RefKey::Choice(n)) => {
                let (test, yes, no) = self.choices[*n].clone();
                let (test, yes, no) = (self.emit(&test), self.owner(&yes), self.owner(&no));
                if yes == no { yes } else { self.b.add(Core::If([test, yes, no])) }
            }
            Val::Term(id, _) => self.origin(*id),
            _ => self.b.add(Core::Unowned),
        }
    }
    /// Who holds a value of unknown type: the caller for a free variable, and for an element
    /// whoever holds the elements of its list.
    fn origin(&mut self, id: Id) -> Id {
        let holder = match self.b.node(id) {
            Core::Var(v) if v.kind == Kind::Any => Core::External,
            Core::Var(_) => self.members.get(&id).map_or(Core::Unowned, |&list| self.elements(list)),
            Core::At([list, _]) => self.elements(*list),
            _ => Core::Unowned,
        };
        self.b.add(holder)
    }
    /// Who holds the elements of a list term: the caller for its own lists' elements, the
    /// expression for a map that builds each, and unknown otherwise.
    fn elements(&self, list: Id) -> Core {
        match self.b.node(list) {
            Core::Var(v) if v.kind == Kind::List => Core::External,
            Core::Map(_) if self.fresh.contains(&list) => Core::Internal,
            Core::Slice([l, _, _]) | Core::Filter([_, l]) | Core::Sort([_, l]) | Core::Reverse(l) => self.elements(*l),
            Core::Flat(l) if self.elements(*l) == Core::External => Core::External,
            Core::Append([a, b]) if self.elements(*a) == self.elements(*b) => self.elements(*a),
            _ => Core::Unowned,
        }
    }
    /// Record a mutation of what `target` reaches, unless only the expression holds it. What
    /// it stores there becomes reachable from outside when someone outside holds the target.
    pub fn log(&mut self, m: Mutator, target: &Val<'a>, stored: &[Val<'a>]) {
        let owner = self.owner(target);
        if matches!(self.b.node(owner), Core::Internal) {
            return;
        }
        if matches!(self.b.node(owner), Core::External) {
            let mut keys = Vec::new();
            for v in stored {
                self.locals_in(v, &mut keys);
            }
            Rc::make_mut(&mut self.state.escaped).extend(keys);
        }
        let op = self.b.add(Core::Op(m));
        let entry = Val::Term(self.b.add(Core::Mutate([op, owner])), Ty::Defined);
        let log = std::mem::replace(&mut self.state.log, Val::empty());
        self.state.log = self.append(log, Val::List(Rc::new(vec![entry])));
    }
    /// The local arrays a value reaches, directly or through other arrays.
    fn locals_in(&mut self, v: &Val<'a>, out: &mut Vec<RefKey>) {
        match v {
            Val::Ref(key @ RefKey::Local(_)) if !out.contains(key) => {
                out.push(*key);
                let contents = self.deref(v.clone());
                self.locals_in(&contents, out);
            }
            Val::List(items) => items.iter().for_each(|v| self.locals_in(v, out)),
            Val::Split(s) => {
                self.locals_in(&s.absent, out);
                self.locals_in(&s.present, out);
            }
            _ => {}
        }
    }
}

fn holds_ref(v: &Val<'_>) -> bool {
    match v {
        Val::Ref(_) => true,
        Val::List(items) => items.iter().any(holds_ref),
        Val::Split(s) => holds_ref(&s.absent) || holds_ref(&s.present),
        _ => false,
    }
}
