//! References: arrays with identity, their contents in the store, the log of mutations
//! someone outside the expression can observe, and how all of it follows lowering's worlds.
use super::Lowerer;
use super::value::{Items, RefKey, Split, Ty, Val};
use crate::core::{Core, Family, Kind, Mutator};
use egg::Id;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// What lowering has learned along one path: each written reference's current contents, who
/// holds each local array that escaped (an owner term), the observable mutations so far (a
/// list of `mutate` terms), and how many times code lowering cannot see has run, after which
/// no array's contents are known.
#[derive(Clone)]
pub struct State<'a> {
    pub cells: Rc<HashMap<RefKey, Val<'a>>>,
    pub escaped: Rc<HashMap<RefKey, Val<'a>>>,
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

/// How two alternatives' states join: by the split on a read (`false` is the absent side),
/// or by a symbolic test, under which the first alternative is taken where the test is
/// `first_if`.
pub enum Join<'a> {
    Read(Rc<Split<'a>>),
    Test { test: Val<'a>, first_if: bool },
}

impl<'a> Lowerer<'a, '_> {
    /// An array's current contents: what the store holds for a reference, or the value itself.
    /// What an input list's elements are: what its declaration says, or defined.
    fn input_items(&self, name: &str) -> Items {
        match self.declared.get(name) {
            Some(super::declare::Declared::List(items)) => Items(*items),
            _ => Items::DEFINED,
        }
    }
    pub fn deref(&mut self, v: Val<'a>) -> Val<'a> {
        let Val::Ref(key) = v else { return v };
        if let Some(contents) = self.state.cells.get(&key) {
            // A merge stores a choice between the alternatives' contents.
            let contents = contents.clone();
            return self.deref(contents);
        }
        match key {
            RefKey::Input(name) if self.state.epoch == 0 => {
                let items = self.input_items(name.as_str());
                Val::Term(self.b.shaped_var(Kind::List, name.as_str(), items.0), Ty::List(items))
            }
            RefKey::Input(name) => {
                let items = self.input_items(name.as_str());
                let var = Val::Term(self.b.shaped_var(Kind::List, name.as_str(), items.0), Ty::Any);
                let epoch = Val::int(i64::from(self.state.epoch));
                self.dynamic("havoc", &[&var, &epoch], Ty::List(Items::ANY))
            }
            RefKey::Choice(n) => {
                let (test, a, b) = self.choices[n].clone();
                let (a, b) = (self.deref(a), self.deref(b));
                self.select_contents(&test, a, b)
            }
            RefKey::Local(_) | RefKey::Place(..) => unreachable!("a local reference is stored when it is made"),
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
    /// one identity there, in every world.
    pub fn held(&mut self, place: (Id, Id), v: Val<'a>) -> Val<'a> {
        if !matches!(v, Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_))) {
            return v;
        }
        let key = RefKey::Place(place.0, place.1);
        if !self.state.cells.contains_key(&key) {
            self.write(key, v);
        }
        Val::Ref(key)
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
            Val::Ref(key) => {
                self.write(*key, contents);
                // A term that holds this array's old contents is now stale, and lowering
                // cannot say which arrays read through it.
                if self.embedded.contains(key) {
                    self.clobber();
                }
            }
            _ => {}
        }
    }
    /// One of two values chosen by a symbolic test, each with an identity, so a mutation
    /// through the choice reaches the one picked.
    pub fn choice(&mut self, test: Val<'a>, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        let (a, b) = (self.own(a), self.own(b));
        self.choices.push((test, a, b));
        Val::Ref(RefKey::Choice(self.choices.len() - 1))
    }
    /// The term for a value, every reference in it replaced by its current contents. An
    /// array that contains itself has no finite term.
    pub fn emit(&mut self, v: &Val<'a>) -> Id {
        if filtered(v) {
            let v = self.slots(v.clone());
            return self.emit(&v);
        }
        if !holds_ref(v) {
            return self.b.emit(v);
        }
        let outermost = self.resolving.is_empty();
        let resolved = self.resolve(v.clone());
        if outermost {
            self.resolved.clear();
        }
        self.b.emit(&resolved)
    }
    /// A value with every short list that a filter may empty written as its slot: empty where
    /// its read is missing, and where present, the element or nothing as the filter decides.
    /// A filter that drops a present element makes the same empty list as a missing read.
    fn slots(&mut self, v: Val<'a>) -> Val<'a> {
        match v {
            Val::Short(s) if !matches!(s.keep, Val::Bool(true)) => {
                self.over_slot(&s, Family::Container, &Val::empty(), &mut |_, e| Val::List(Rc::new(vec![e])))
            }
            Val::List(items) if items.iter().any(filtered) => Val::List(Rc::new(items.iter().map(|v| self.slots(v.clone())).collect())),
            Val::Record(fields) if fields.iter().any(|(_, v)| filtered(v)) => {
                Val::Record(Rc::new(fields.iter().map(|(k, v)| (*k, self.slots(v.clone()))).collect()))
            }
            Val::Split(s) if filtered(&s.absent) || filtered(&s.present) => {
                let (absent, present) = (self.slots(s.absent.clone()), self.slots(s.present.clone()));
                Val::Split(Rc::new(Split { absent, present, ..(*s).clone() }))
            }
            v => v,
        }
    }
    /// A value with every reference replaced by its contents. The arrays being resolved are
    /// one stack across nested emissions (a choice's contents emit its alternatives), so a
    /// cycle through any of them is found.
    fn resolve(&mut self, v: Val<'a>) -> Val<'a> {
        match v {
            Val::Ref(key) if self.resolving.contains(&key) => {
                self.opaque = true;
                self.unknown_list()
            }
            // The store does not change while a value resolves, so each array resolves once:
            // an array reached along many paths would otherwise resolve once per path.
            Val::Ref(key) if self.resolved.contains_key(&key) => self.resolved[&key].clone(),
            Val::Ref(key) => {
                // A term now holds this array's contents as they are.
                self.embedded.insert(key);
                self.resolving.push(key);
                let contents = self.deref(v);
                let out = self.resolve(contents);
                self.resolving.pop();
                self.resolved.insert(key, out.clone());
                out
            }
            Val::List(items) if items.iter().any(holds_ref) => Val::List(Rc::new(items.iter().map(|v| self.resolve(v.clone())).collect())),
            Val::Record(fields) if fields.iter().any(|(_, v)| holds_ref(v)) => {
                Val::Record(Rc::new(fields.iter().map(|(k, v)| (*k, self.resolve(v.clone()))).collect()))
            }
            Val::Split(s) if holds_ref(&s.absent) || holds_ref(&s.present) => {
                let (absent, present) = (self.resolve(s.absent.clone()), self.resolve(s.present.clone()));
                Val::Split(Rc::new(Split { absent, present, ..(*s).clone() }))
            }
            v => v,
        }
    }
    /// A value with every array that `outer` does not hold replaced by its contents, so it
    /// outlives the state those arrays live in.
    pub fn detach(&mut self, v: Val<'a>, outer: &HashMap<RefKey, Val<'a>>, choices: usize) -> Val<'a> {
        match v {
            Val::Ref(RefKey::Choice(n)) if n >= choices => {
                let contents = self.deref(v);
                self.detach(contents, outer, choices)
            }
            Val::Ref(key @ (RefKey::Local(_) | RefKey::Place(..))) if !outer.contains_key(&key) => {
                let contents = self.resolve(v);
                self.detach(contents, outer, choices)
            }
            Val::List(items) if items.iter().any(holds_ref) => Val::List(Rc::new(items.iter().map(|v| self.detach(v.clone(), outer, choices)).collect())),
            Val::Record(fields) if fields.iter().any(|(_, v)| holds_ref(v)) => {
                Val::Record(Rc::new(fields.iter().map(|(k, v)| (*k, self.detach(v.clone(), outer, choices))).collect()))
            }
            Val::Split(s) if holds_ref(&s.absent) || holds_ref(&s.present) => {
                let (absent, present) = (self.detach(s.absent.clone(), outer, choices), self.detach(s.present.clone(), outer, choices));
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

impl<'a> Lowerer<'a, '_> {
    /// Lower two alternatives, `side(false)` and `side(true)`, from the same state, then join
    /// what each wrote and logged.
    pub fn fork(&mut self, side: &mut dyn FnMut(&mut Self, bool) -> Val<'a>, join: &Join<'a>) -> (Val<'a>, Val<'a>) {
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
    /// Join two values under a fork's join. Under a test, arrays with identity stay values: a
    /// choice between copies of each side's contents.
    pub fn join(&mut self, join: &Join<'a>, first: Val<'a>, second: Val<'a>) -> Val<'a> {
        match join {
            Join::Read(s) => self.resplit(s, first, second, Family::Propagate),
            Join::Test { test, first_if } => {
                let (yes, no) = if *first_if { (first, second) } else { (second, first) };
                if holds_ref(&yes) || holds_ref(&no) {
                    let (yes, no) = (self.copy(yes), self.copy(no));
                    self.choice(test.clone(), yes, no)
                } else {
                    self.select(test, yes, no)
                }
            }
        }
    }
    /// A new local array holding these contents.
    fn copy(&mut self, contents: Val<'a>) -> Val<'a> {
        self.next_ref += 1;
        let key = RefKey::Local(self.next_ref);
        self.write(key, contents);
        Val::Ref(key)
    }
    /// [`Self::merge`], for callers outside this module.
    pub fn merge_states(&mut self, a: State<'a>, b: State<'a>, join: &Join<'a>) -> State<'a> {
        self.merge(a, b, join)
    }
    /// The state `after`, in the worlds where `mask` does not throw, and `before` where it does.
    pub fn guard(&mut self, before: &State<'a>, after: State<'a>, mask: &Val<'a>) -> State<'a> {
        match mask {
            Val::Throw => before.clone(),
            Val::Split(s) if self.may_raise(mask) => {
                let absent = self.guard(before, after.clone(), &s.absent);
                let present = self.guard(before, after, &s.present);
                self.state = before.clone();
                self.merge(absent, present, &Join::Read(s.clone()))
            }
            Val::Term(..) | Val::Ref(RefKey::Choice(_)) => match self.throws_when(mask) {
                Some(test) => {
                    self.state = before.clone();
                    self.merge(after, before.clone(), &Join::Test { test, first_if: false })
                }
                None => after,
            },
            _ => after,
        }
    }
    /// Whether evaluating a value throws in some world: a throw, or a conditional that picks
    /// one, on some side of its splits.
    pub fn may_raise(&self, v: &Val<'a>) -> bool {
        match v {
            Val::Throw => true,
            Val::Split(s) => self.may_raise(&s.absent) || self.may_raise(&s.present),
            Val::List(items) => items.iter().any(|v| self.may_raise(v)),
            Val::Term(id, _) => self.term_may_throw(*id),
            Val::Ref(RefKey::Choice(n)) => {
                let (_, yes, no) = &self.choices[*n];
                self.may_raise(yes) || self.may_raise(no)
            }
            _ => false,
        }
    }
    fn term_may_throw(&self, id: Id) -> bool {
        match self.b.node(id) {
            Core::Throw => true,
            Core::If([_, yes, no]) => self.term_may_throw(*yes) || self.term_may_throw(*no),
            _ => false,
        }
    }
    /// A value an operation consumes without carrying its throws: one that throws under a
    /// symbolic test (unlike a split, whose throwing world every operation keeps) leaves
    /// nothing known after it.
    pub fn consume(&mut self, v: &Val<'a>) {
        if matches!(v, Val::Ref(RefKey::Choice(_)) | Val::Term(..)) && self.may_raise(v) {
            self.clobber();
        }
    }
    /// Where a value throws because a conditional (or a choice) picks a `throw`: the
    /// condition, as a boolean.
    pub fn throws_when(&mut self, v: &Val<'a>) -> Option<Val<'a>> {
        match v {
            Val::Throw => Some(Val::Bool(true)),
            Val::Ref(RefKey::Choice(n)) => {
                let (test, yes, no) = self.choices[*n].clone();
                self.either(&test, &yes, &no)
            }
            Val::Term(id, _) => self.term_throws_when(*id),
            _ => None,
        }
    }
    fn term_throws_when(&mut self, id: Id) -> Option<Val<'a>> {
        match *self.b.node(id) {
            Core::Throw => Some(Val::Bool(true)),
            Core::If([c, yes, no]) => {
                let (yes, no) = (self.term_throws_when(yes), self.term_throws_when(no));
                if yes.is_none() && no.is_none() {
                    return None;
                }
                let (yes, no) = (yes.unwrap_or(Val::Bool(false)), no.unwrap_or(Val::Bool(false)));
                Some(self.select_contents(&Val::Term(c, Ty::Bool), yes, no))
            }
            _ => None,
        }
    }
    fn either(&mut self, test: &Val<'a>, yes: &Val<'a>, no: &Val<'a>) -> Option<Val<'a>> {
        let (yes, no) = (self.throws_when(yes), self.throws_when(no));
        if yes.is_none() && no.is_none() {
            return None;
        }
        let (yes, no) = (yes.unwrap_or(Val::Bool(false)), no.unwrap_or(Val::Bool(false)));
        Some(self.select_contents(test, yes, no))
    }
    /// Join two states that grew from the current one.
    fn merge(&mut self, a: State<'a>, b: State<'a>, join: &Join<'a>) -> State<'a> {
        let keys: HashSet<RefKey> = a.cells.keys().chain(b.cells.keys()).copied().collect();
        let mut cells = (*self.state.cells).clone();
        for key in keys {
            let merged = match (a.cells.get(&key), b.cells.get(&key)) {
                (Some(x), Some(y)) if x.identical(y) => x.clone(),
                // An array allocated on one side only: nothing on the other side holds it.
                (Some(x), None) | (None, Some(x)) if !matches!(key, RefKey::Input(_)) && !self.state.cells.contains_key(&key) => x.clone(),
                (x, y) => {
                    let (x, y) = (x.cloned(), y.cloned());
                    let x = x.unwrap_or_else(|| self.deref(Val::Ref(key)));
                    let y = y.unwrap_or_else(|| self.deref(Val::Ref(key)));
                    // The copies a test join makes live in the merged store.
                    let saved = std::mem::replace(&mut self.state.cells, Rc::new(cells));
                    let merged = self.join(join, x, y);
                    cells = Rc::unwrap_or_clone(std::mem::replace(&mut self.state.cells, saved));
                    merged
                }
            };
            cells.insert(key, merged);
        }
        let keys: HashSet<RefKey> = a.escaped.keys().chain(b.escaped.keys()).copied().collect();
        let mut escaped = HashMap::new();
        for key in keys {
            let (x, y) = (self.holder(&a, key), self.holder(&b, key));
            let merged = if x.identical(&y) { x } else { self.join(join, x, y) };
            escaped.insert(key, merged);
        }
        let log = if a.log.identical(&b.log) { a.log } else { self.join(join, a.log, b.log) };
        State { cells: Rc::new(cells), escaped: Rc::new(escaped), log, epoch: a.epoch.max(b.epoch) }
    }
    /// Who holds a local array along one path: its escape's owner, or the expression.
    fn holder(&mut self, state: &State<'a>, key: RefKey) -> Val<'a> {
        state.escaped.get(&key).cloned().unwrap_or_else(|| Val::Term(self.b.add(Core::Internal), Ty::Defined))
    }
    /// Lower a callback that runs any number of times, and only while `list` has at least
    /// `least` elements: what it wrote to arrays that outlive it is unknown afterward, and
    /// what it logged or let escape happens only where the list is that long.
    pub fn repeat(&mut self, list: Id, least: i64, body: impl FnOnce(&mut Self) -> Val<'a>) -> Val<'a> {
        self.repeat_keeping(list, least, None, body)
    }
    /// [`Self::repeat`], except that `kept`, whose contents `body` leaves as what every run
    /// together makes them, keeps them.
    pub fn repeat_keeping(&mut self, list: Id, least: i64, kept: Option<RefKey>, body: impl FnOnce(&mut Self) -> Val<'a>) -> Val<'a> {
        let base = self.state.clone();
        let out = body(self);
        if self.state.same(&base) {
            return out;
        }
        let after = std::mem::replace(&mut self.state, base.clone());
        let outlive = |k: &RefKey| base.cells.contains_key(k) || matches!(k, RefKey::Input(_));
        let written: Vec<RefKey> = after
            .cells
            .iter()
            .filter(|(k, v)| outlive(k) && Some(**k) != kept && base.cells.get(k).is_none_or(|old| !old.identical(v)))
            .map(|(k, _)| *k)
            .collect();
        self.state.cells = after.cells.clone();
        self.state.epoch = after.epoch;
        // What the callback stored may hold a read that may be missing, and an unknown list
        // would hide it: where it does, the expression's value is unknown.
        if written.iter().any(|k| after.cells.get(k).is_some_and(|v| self.reads(v, &after))) {
            self.opaque = true;
        }
        for key in written {
            let unknown = self.unknown_list();
            self.write(key, unknown);
        }
        let len = crate::affine::Form::atom(self.b.add(Core::Len(list)));
        let long = self.b.nonnegative(&len.plus(&crate::affine::Form::constant(least), -1).unwrap_or_default());
        let join = Join::Test { test: long, first_if: true };
        self.state.escaped = self.merge_escapes(&after, &base, &join);
        if !after.log.identical(&base.log) {
            self.state.log = self.join(&join, after.log, base.log);
        }
        out
    }
    fn merge_escapes(&mut self, after: &State<'a>, base: &State<'a>, join: &Join<'a>) -> Rc<HashMap<RefKey, Val<'a>>> {
        let mut escaped = (*base.escaped).clone();
        for key in after.escaped.keys() {
            let (x, y) = (self.holder(after, *key), self.holder(base, *key));
            let merged = if x.identical(&y) { x } else { self.join(join, x, y) };
            escaped.insert(*key, merged);
        }
        Rc::new(escaped)
    }
    /// Lower something only to learn about it, leaving the store, the log, and opacity as they
    /// were.
    pub fn speculate<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        self.probe(body).0
    }
    /// [`Self::speculate`], and whether the lowered code had effects.
    pub fn probe<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> (T, bool) {
        let (state, opaque) = (self.state.clone(), self.opaque);
        let out = body(self);
        let pure = self.state.same(&state) && self.opaque == opaque;
        (self.state, self.opaque) = (state, opaque);
        (out, pure)
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
    /// Whether lowering since the store `before` (and opacity `opaque`) had an effect outside
    /// what it lowered: a write to an array that outlives it, a logged mutation, an escape,
    /// or something lowering does not model. A new array is no such effect.
    pub fn effects_since(&self, before: &State<'a>, opaque: bool) -> bool {
        !self.written_since(before).is_empty()
            || !self.state.log.identical(&before.log)
            || !Rc::ptr_eq(&self.state.escaped, &before.escaped)
            || self.opaque != opaque
    }
    /// The arrays that outlive a callback and that it wrote, from the store before it.
    pub fn written_since(&self, base: &State<'a>) -> Vec<RefKey> {
        let outlive = |k: &RefKey| base.cells.contains_key(k) || matches!(k, RefKey::Input(_));
        let mut keys: Vec<RefKey> = self
            .state
            .cells
            .iter()
            .filter(|(k, v)| outlive(k) && base.cells.get(k).is_none_or(|old| !old.identical(v)))
            .map(|(k, _)| *k)
            .collect();
        keys.sort_by_key(|k| format!("{k:?}"));
        keys
    }
    /// Whether a value depends on a read that may be missing, through arrays it holds too.
    fn reads(&self, v: &Val<'a>, state: &State<'a>) -> bool {
        let mut open = Vec::new();
        self.reads_in(v, state, &mut open)
    }
    fn reads_in(&self, v: &Val<'a>, state: &State<'a>, open: &mut Vec<RefKey>) -> bool {
        match v {
            Val::Split(_) | Val::Short(_) => true,
            Val::List(items) => items.iter().any(|v| self.reads_in(v, state, open)),
            Val::Record(fields) => fields.iter().any(|(_, v)| self.reads_in(v, state, open)),
            Val::Term(id, _) => self.b.reads(*id),
            Val::Ref(k) if !open.contains(k) => {
                open.push(*k);
                let held = match k {
                    RefKey::Choice(n) => {
                        let (_, yes, no) = &self.choices[*n];
                        self.reads_in(yes, state, open) || self.reads_in(no, state, open)
                    }
                    k => state.cells.get(k).is_some_and(|c| self.reads_in(c, state, open)),
                };
                open.pop();
                held
            }
            _ => false,
        }
    }
    pub fn unknown_list(&mut self) -> Val<'a> {
        self.next_ref += 1;
        let tag = Val::int(i64::from(self.next_ref));
        self.dynamic("havoc", &[&tag], Ty::List(Items::ANY))
    }
}

impl<'a> Lowerer<'a, '_> {
    /// The term for who holds the array or object `target` reaches: someone outside the
    /// expression, the expression itself, or unknown; for a choice, an `if` over its
    /// alternatives' holders.
    pub fn owner(&mut self, target: &Val<'a>) -> Id {
        match target {
            Val::Ref(RefKey::Input(_)) => self.b.add(Core::External),
            Val::Ref(key @ (RefKey::Local(_) | RefKey::Place(..))) => {
                match self.state.escaped.get(key).cloned() {
                    Some(holder) => self.emit(&holder),
                    None => self.b.add(Core::Internal),
                }
            }
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => self.b.add(Core::Internal),
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
    /// expression for a map that builds each, the base's holder for a map that returns its
    /// element, and unknown otherwise.
    fn elements(&self, list: Id) -> Core {
        match self.b.node(list) {
            Core::Var(v) if v.kind == Kind::List => Core::External,
            Core::Map(_) if self.fresh.contains(&list) => Core::Internal,
            Core::Map([_, l]) if self.passes.contains(&list) => self.elements(*l),
            Core::Slice([l, _, _]) | Core::Filter([_, l]) | Core::Sort([_, l]) | Core::Reverse(l) => self.elements(*l),
            Core::Flat(l) if self.elements(*l) == Core::External => Core::External,
            Core::Append([a, b]) if self.elements(*a) == self.elements(*b) => self.elements(*a),
            _ => Core::Unowned,
        }
    }
    /// Record a mutation of what `target` reaches, unless only the expression holds it. What
    /// it stores there is held by whoever holds the target from then on.
    pub fn log(&mut self, m: Mutator, target: &Val<'a>, stored: &[Val<'a>]) {
        let owner = self.owner(target);
        if matches!(self.b.node(owner), Core::Internal) {
            return;
        }
        let mut keys = Vec::new();
        for v in stored {
            self.locals_in(v, &mut keys);
        }
        let external = self.b.add(Core::External);
        for key in keys {
            let already = self.state.escaped.get(&key).is_some_and(|h| matches!(h, Val::Term(id, _) if *id == external));
            if !already {
                Rc::make_mut(&mut self.state.escaped).insert(key, Val::Term(owner, Ty::Defined));
            }
        }
        let op = self.b.add(Core::Op(m));
        let entry = Val::Term(self.b.add(Core::Mutate([op, owner])), Ty::Defined);
        let log = std::mem::replace(&mut self.state.log, Val::empty());
        self.state.log = self.append(log, Val::List(Rc::new(vec![entry])));
    }
    /// The local arrays a value reaches, directly or through other arrays and choices.
    fn locals_in(&mut self, v: &Val<'a>, out: &mut Vec<RefKey>) {
        match v {
            Val::Ref(key @ (RefKey::Local(_) | RefKey::Place(..))) if !out.contains(key) => {
                out.push(*key);
                let contents = self.state.cells.get(key).cloned().unwrap_or(Val::Undef);
                self.locals_in(&contents, out);
            }
            Val::Ref(RefKey::Choice(n)) => {
                let (_, yes, no) = self.choices[*n].clone();
                self.locals_in(&yes, out);
                self.locals_in(&no, out);
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

pub fn holds_ref(v: &Val<'_>) -> bool {
    match v {
        Val::Ref(_) => true,
        Val::List(items) => items.iter().any(holds_ref),
        Val::Record(fields) => fields.iter().any(|(_, v)| holds_ref(v)),
        Val::Split(s) => holds_ref(&s.absent) || holds_ref(&s.present),
        _ => false,
    }
}

/// Whether a value holds a short list a filter may empty.
fn filtered(v: &Val<'_>) -> bool {
    match v {
        Val::Short(s) => !matches!(s.keep, Val::Bool(true)),
        Val::List(items) => items.iter().any(filtered),
        Val::Record(fields) => fields.iter().any(|(_, v)| filtered(v)),
        Val::Split(s) => filtered(&s.absent) || filtered(&s.present),
        _ => false,
    }
}
