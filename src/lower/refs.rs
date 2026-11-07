//! References: arrays with identity, their contents in the store, and emission through it.
use super::Lowerer;
use super::value::{Items, RefKey, Split, Ty, Val};
use crate::core::Kind;
use egg::Id;
use std::collections::HashMap;
use std::rc::Rc;

/// What lowering has learned along one path: each written reference's current contents.
#[derive(Clone, Default)]
pub struct State<'a> {
    pub cells: Rc<HashMap<RefKey, Val<'a>>>,
}

impl<'a> Lowerer<'a, '_> {
    /// An array's current contents: what the store holds for a reference, or the value itself.
    pub fn deref(&mut self, v: Val<'a>) -> Val<'a> {
        let Val::Ref(key) = v else { return v };
        if let Some(contents) = self.state.cells.get(&key) {
            return contents.clone();
        }
        match key {
            RefKey::Input(name) => Val::Term(self.b.var(Kind::List, name.as_str()), Ty::List(Items::Defined)),
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
    pub fn write(&mut self, key: RefKey, contents: Val<'a>) {
        Rc::make_mut(&mut self.state.cells).insert(key, contents);
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

fn holds_ref(v: &Val<'_>) -> bool {
    match v {
        Val::Ref(_) => true,
        Val::List(items) => items.iter().any(holds_ref),
        Val::Split(s) => holds_ref(&s.absent) || holds_ref(&s.present),
        _ => false,
    }
}
