//! Lists: reads, lengths, appends, and lists of at most one element.
use super::Lowerer;
use super::value::{Short, Split, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Kind};
use egg::Id;
use std::rc::Rc;

impl<'a> Lowerer<'a, '_> {
    /// `list[index]`.
    pub fn read(&mut self, list: Val<'a>, index: Val<'a>) -> Val<'a> {
        self.lift2(list, index, Family::Propagate, &mut |l, list, index| l.read_plain(list, &index))
    }
    fn read_plain(&mut self, list: Val<'a>, index: &Val<'a>) -> Val<'a> {
        let Val::Num(f) = index else {
            return match (&list, index) {
                (Val::Throw | Val::Undef, _) | (_, Val::Throw) => Val::Throw,
                (_, Val::Undef) => Val::Undef,
                _ => self.unsupported(),
            };
        };
        match list {
            Val::Undef | Val::Throw => Val::Throw,
            Val::List(items) => {
                if let Some(k) = f.known() {
                    return usize::try_from(k).ok().and_then(|k| items.get(k).cloned()).unwrap_or(Val::Undef);
                }
                let id = self.b.emit(&Val::List(items));
                self.element(id, f)
            }
            Val::Short(s) => match f.known() {
                Some(0) => self.short_element(&s),
                Some(_) => Val::Undef,
                None => self.element(s.list, f),
            },
            Val::Term(id, Ty::List) => self.element(id, f),
            Val::Str(text) => match f.known().and_then(|k| usize::try_from(k).ok()) {
                Some(k) => text.units().get(k).map_or(Val::Undef, |&u| Val::Str(crate::core::Utf16::new([u]))),
                None => self.unsupported(),
            },
            _ => self.unsupported(),
        }
    }
    /// A read of a symbolic list: proven when the index is a walker's own coordinate on its
    /// own receiver, and otherwise split, marked as drift if the index came from a walker.
    pub fn element(&mut self, list: Id, index: &Form) -> Val<'a> {
        let idx = self.b.form(index);
        if index.single().is_some_and(|i| self.coords.get(&i) == Some(&list)) {
            return Val::Term(self.b.add(Core::At([list, idx])), Ty::Defined);
        }
        let read = self.b.add(Core::Read([list, idx]));
        let drift = index.terms.keys().any(|a| self.coords.contains_key(a));
        self.split_read(read, drift)
    }
    pub fn split_read(&mut self, read: Id, drift: bool) -> Val<'a> {
        if let Some(v) = self.narrow.get(&read) {
            return v.clone();
        }
        let elem = self.elem(read);
        let present = Val::Term(elem, Ty::Defined);
        let family = Family::Propagate;
        Val::Split(Rc::new(Split { read, elem, absent: Val::Undef, present, family, drift }))
    }
    /// The element binder of a read, shared by every split on it.
    pub fn elem(&mut self, read: Id) -> Id {
        if let Some(&e) = self.elems.get(&read) {
            return e;
        }
        let e = self.b.fresh(Kind::Elem);
        self.elems.insert(read, e);
        e
    }
    /// The element of a list of at most one element: absent, or the element if kept.
    pub fn short_element(&mut self, s: &Short<'a>) -> Val<'a> {
        let slot = self.split_read(s.read, false);
        let (elem, keep) = (s.elem.clone(), s.keep.clone());
        self.worlds(slot, Family::Propagate, &mut |l, v| match v {
            Val::Undef => Val::Undef,
            _ => l.select(&keep, elem.clone(), Val::Undef),
        })
    }
    /// A list of at most one element whose slot is `list[0]`.
    pub fn short(&mut self, list: Id) -> Val<'a> {
        let zero = self.b.int(0);
        let read = self.b.add(Core::Read([list, zero]));
        let var = self.elem(read);
        let elem = Val::Term(var, Ty::Defined);
        Val::Short(Rc::new(Short { list, read, var, elem, keep: Val::Bool(true) }))
    }
}

impl<'a> Lowerer<'a, '_> {
    pub fn property(&mut self, object: Val<'a>, name: &str) -> Val<'a> {
        if name != "length" {
            return self.unsupported();
        }
        self.lift(object, Family::Propagate, &mut |l, v| l.length(v))
    }
    fn length(&mut self, v: Val<'a>) -> Val<'a> {
        match v {
            Val::Undef | Val::Throw => Val::Throw,
            Val::List(items) => Val::int(i64::try_from(items.len()).unwrap_or(i64::MAX)),
            Val::Str(s) => Val::int(i64::try_from(s.units().len()).unwrap_or(i64::MAX)),
            Val::Short(s) => self.short_length(&s),
            Val::Term(id, Ty::List) => Val::Num(Form::atom(self.b.add(Core::Len(id)))),
            v => match self.dynamic("length", &[&v], Ty::Defined) {
                Val::Term(id, _) => Val::Num(Form::atom(id)),
                other => other,
            },
        }
    }
    /// One when the slot is present and kept, zero otherwise: the unit of counting.
    fn short_length(&mut self, s: &Short<'a>) -> Val<'a> {
        let slot = self.split_read(s.read, false);
        let keep = s.keep.clone();
        self.worlds(slot, Family::Unit, &mut |l, v| match v {
            Val::Undef => Val::int(0),
            _ => l.select(&keep, Val::int(1), Val::int(0)),
        })
    }
    /// `[...a, ...b]`.
    pub fn append(&mut self, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        self.lift2(a, b, Family::Propagate, &mut |l, a, b| match (spreadable(a), spreadable(b)) {
            (Some(Val::List(x)), Some(Val::List(y))) => Val::List(Rc::new(x.iter().chain(y.iter()).cloned().collect())),
            (Some(Val::List(x)), Some(y)) if x.is_empty() => y,
            (Some(x), Some(Val::List(y))) if y.is_empty() => x,
            (Some(x), Some(y)) => {
                let (x, y) = (l.b.emit(&x), l.b.emit(&y));
                Val::Term(l.b.add(Core::Append([x, y])), Ty::List)
            }
            _ => Val::Throw,
        })
    }
}

/// A value spread into an array: a list, or a known string's characters. Anything else
/// throws.
fn spreadable(v: Val<'_>) -> Option<Val<'_>> {
    match v {
        Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List) => Some(v),
        Val::Str(s) => Some(Val::List(Rc::new(s.units().into_iter().map(|u| Val::Str(crate::core::Utf16::new([u]))).collect()))),
        _ => None,
    }
}
