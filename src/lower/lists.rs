//! Lists: reads, lengths, appends, and lists of at most one element.
use super::Lowerer;
use super::value::{Items, Seq, Short, Split, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family};
use egg::Id;
use std::rc::Rc;

impl<'a> Lowerer<'a, '_> {
    /// `list[index]`.
    pub fn read(&mut self, list: Val<'a>, index: Val<'a>) -> Val<'a> {
        self.lift2(list, index, Family::Propagate, &mut |l, list, index| l.read_plain(list, &index))
    }
    fn read_plain(&mut self, list: Val<'a>, index: &Val<'a>) -> Val<'a> {
        let list = self.deref(list);
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
                    let item = usize::try_from(k).ok().and_then(|k| items.get(k).cloned());
                    return item.map_or(Val::Undef, |v| self.settle(v));
                }
                let list = self.seq(&items);
                self.element(list, f)
            }
            Val::Short(s) => match f.known() {
                Some(0) => self.short_element(&s),
                Some(_) => Val::Undef,
                None => self.element(s.list, f),
            },
            Val::Term(id, Ty::List(items)) => self.element(Seq { id, items }, f),
            Val::Str(text) => match f.known().and_then(|k| usize::try_from(k).ok()) {
                Some(k) => text.units().get(k).map_or(Val::Undef, |&u| Val::Str(crate::core::Utf16::new([u]))),
                None => self.unsupported(),
            },
            _ => self.unsupported(),
        }
    }
    /// A read of a symbolic list: proven in range at a walker's index over a list no longer
    /// than this one, or at either end while a walker over such a list runs, since its
    /// callback runs only on a non-empty list. Otherwise split, and marked as drift if the
    /// index came from a walker.
    pub fn element(&mut self, list: Seq, index: &Form) -> Val<'a> {
        if let Some((f, base)) = self.maps.get(&list.id).cloned() {
            return self.mapped(&f, base, list.id, index);
        }
        let idx = self.b.form(index);
        if self.in_range(list.id, index) {
            return Val::Term(self.b.add(Core::At([list.id, idx])), list.items.ty());
        }
        let read = self.b.add(Core::Read([list.id, idx]));
        let drift = index.terms.keys().any(|a| self.coords.contains_key(a));
        self.split_read(read, drift, list.items)
    }
    /// Whether `list[index]` is proven in range by the walkers around it.
    pub fn in_range(&mut self, list: Id, index: &Form) -> bool {
        if index.single().and_then(|i| self.coords.get(&i).copied()).is_some_and(|l| self.no_longer(l, list)) {
            return true;
        }
        let len = Form::atom(self.b.add(Core::Len(list)));
        let end = index.known() == Some(0) || len.plus(&Form::constant(1), -1).as_ref() == Some(index);
        end && self.walking.clone().into_iter().any(|l| self.no_longer(l, list))
    }
    /// Whether `inner` provably has no more elements than `outer`: a map keeps its list's
    /// length, a filter or slice keeps at most it, and an append or a full copy at least it.
    fn no_longer(&self, inner: Id, outer: Id) -> bool {
        if inner == outer {
            return true;
        }
        if let Core::Map([_, l]) | Core::Filter([_, l]) | Core::Slice([l, _, _]) = self.b.node(inner)
            && self.no_longer(*l, outer)
        {
            return true;
        }
        match self.b.node(outer) {
            Core::Map([_, l]) => self.no_longer(inner, *l),
            Core::Append([a, b]) => self.no_longer(inner, *a) || self.no_longer(inner, *b),
            Core::Slice([l, a, z]) => {
                let copy = matches!(self.b.node(*a), Core::Int(0)) && matches!(self.b.node(*z), Core::Len(m) if m == l);
                copy && self.no_longer(inner, *l)
            }
            _ => false,
        }
    }
    /// An element of `base.map(f)`: `f` applied to the element of `base` where present, as
    /// map calls it: with the element, its index, and `base`, which is non-empty there.
    fn mapped(&mut self, f: &Val<'a>, base: Seq, list: Id, index: &Form) -> Val<'a> {
        let slot = self.element(base, index);
        let (f, place) = (f.clone(), (list, self.b.form(index)));
        let index = index.clone();
        self.worlds(slot, Family::Propagate, &mut |l, x| match x {
            Val::Undef => Val::Undef,
            x => {
                // The map already ran the callback on this element, effects and all.
                let out = l.speculate(|l| {
                    l.walking.push(base.id);
                    let out = l.apply(f.clone(), vec![x, Val::Num(index.clone()), base.val()]);
                    l.walking.pop();
                    out
                });
                l.held(place, out)
            }
        })
    }
    /// The list a chain of maps starts from.
    pub fn base_of(&self, mut list: Seq) -> Seq {
        while let Some((_, base)) = self.maps.get(&list.id) {
            list = *base;
        }
        list
    }
    pub fn split_read(&mut self, read: Id, drift: bool, items: Items) -> Val<'a> {
        if let Some(v) = self.narrow.get(&read) {
            return v.clone();
        }
        let elem = self.elem(read, items);
        let present = Val::Term(elem, items.ty());
        let family = Family::Propagate;
        Val::Split(Rc::new(Split { read, elem, absent: Val::Undef, present, family, drift, items }))
    }
    /// The element binder of a read, shared by every split on it.
    pub fn elem(&mut self, read: Id, items: Items) -> Id {
        if let Some(&e) = self.elems.get(&read) {
            return e;
        }
        let e = self.b.fresh(items.kind());
        self.elems.insert(read, e);
        if let Core::Read([list, _]) = self.b.node(read) {
            self.members.insert(e, *list);
        }
        e
    }
    /// A literal list as a term.
    pub fn seq(&mut self, items: &Rc<Vec<Val<'a>>>) -> Seq {
        let list = Val::List(items.clone());
        let elements = list.items().unwrap_or(Items::Any);
        Seq { id: self.emit(&list), items: elements }
    }
    /// The element of a list of at most one element: absent, or the element if kept.
    pub fn short_element(&mut self, s: &Short<'a>) -> Val<'a> {
        let slot = self.split_read(s.read, s.drift, s.items);
        let (elem, keep) = (s.elem.clone(), s.keep.clone());
        self.worlds(slot, Family::Propagate, &mut |l, v| match v {
            Val::Undef => Val::Undef,
            _ => l.select(&keep, elem.clone(), Val::Undef),
        })
    }
    /// A list of at most one element whose slot is `list[0]`.
    pub fn short(&mut self, list: Seq, drift: bool) -> Val<'a> {
        let zero = self.b.int(0);
        let read = self.b.add(Core::Read([list.id, zero]));
        let var = self.elem(read, list.items);
        let elem = Val::Term(var, list.items.ty());
        let items = list.items;
        Val::Short(Rc::new(Short { list, read, var, items, elem, keep: Val::Bool(true), drift }))
    }
}

impl<'a> Lowerer<'a, '_> {
    /// `object.name`: reading any property of undefined throws; of the rest only `length`
    /// is modeled.
    pub fn property(&mut self, object: Val<'a>, name: &str) -> Val<'a> {
        self.lift(object, Family::Propagate, &mut |l, v| match v {
            Val::Undef | Val::Throw => Val::Throw,
            v if name == "length" => l.length(v),
            _ => l.unsupported(),
        })
    }
    /// `v.length`: an integer for lists and strings, undefined for numbers and booleans, and
    /// possibly undefined for a value of unknown type.
    pub fn length(&mut self, v: Val<'a>) -> Val<'a> {
        let v = self.deref(v);
        match v {
            Val::Undef | Val::Throw => Val::Throw,
            Val::List(items) => Val::int(i64::try_from(items.len()).unwrap_or(i64::MAX)),
            Val::Str(s) => Val::int(i64::try_from(s.units().len()).unwrap_or(i64::MAX)),
            Val::Short(s) => self.short_length(&s),
            Val::Term(id, Ty::List(_)) => Val::Num(Form::atom(self.b.add(Core::Len(id)))),
            Val::Term(_, Ty::Str) => match self.dynamic("length", &[&v], Ty::Defined) {
                Val::Term(id, _) => Val::Num(Form::atom(id)),
                other => other,
            },
            Val::NaN | Val::Bool(_) | Val::Num(_) | Val::Term(_, Ty::Bool) => Val::Undef,
            Val::Fun(_) => self.unsupported(),
            v => self.dynamic("length", &[&v], Ty::Any),
        }
    }
    /// One when the slot is present and kept, zero otherwise. Unfiltered, that is the
    /// list's length term; filtered, zero is the unit a filter's count absorbs absence into.
    fn short_length(&mut self, s: &Short<'a>) -> Val<'a> {
        if matches!(s.keep, Val::Bool(true)) {
            return Val::Num(Form::atom(self.b.add(Core::Len(s.list.id))));
        }
        let slot = self.split_read(s.read, s.drift, s.items);
        let keep = s.keep.clone();
        self.worlds(slot, Family::Unit, &mut |l, v| match v {
            Val::Undef => Val::int(0),
            _ => l.select(&keep, Val::int(1), Val::int(0)),
        })
    }
    /// `[...a, ...b]`.
    pub fn append(&mut self, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        self.lift2(a, b, Family::Propagate, &mut |l, a, b| {
            let (a, b) = (l.iterate(a), l.iterate(b));
            match (a.items(), b.items()) {
                _ if matches!(a, Val::Throw) => a,
                _ if matches!(b, Val::Throw) => b,
                (Some(x), Some(y)) => match (a, b) {
                    (Val::List(x), Val::List(y)) => Val::List(Rc::new(x.iter().chain(y.iter()).cloned().collect())),
                    (Val::List(x), y) if x.is_empty() => y,
                    (x, Val::List(y)) if y.is_empty() => x,
                    (a, b) => {
                        let (a, b) = (l.emit(&a), l.emit(&b));
                        Seq { id: l.b.add(Core::Append([a, b])), items: x.both(y) }.val()
                    }
                },
                _ => unreachable!("iterate yields a list or a throw"),
            }
        })
    }
    /// The elements iteration yields: a list's own, a string's code points, a throw for a
    /// value that is not iterable, and for a value of unknown type, which may not be
    /// iterable, an uninterpreted list that leaves the expression opaque.
    pub fn iterate(&mut self, v: Val<'a>) -> Val<'a> {
        match v {
            Val::Ref(_) => {
                let contents = self.deref(v);
                self.iterate(contents)
            }
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) | Val::Throw => v,
            Val::Str(s) => Val::List(Rc::new(code_points(&s.units()).into_iter().map(Val::Str).collect())),
            Val::Term(_, Ty::Str) => self.dynamic("iterate", &[&v], Ty::List(Items::Defined)),
            Val::Undef | Val::NaN | Val::Bool(_) | Val::Num(_) | Val::Fun(_) | Val::Term(_, Ty::Bool) => Val::Throw,
            Val::Term(_, Ty::Defined | Ty::Any) | Val::Split(_) => {
                let spread = self.dynamic("iterate", &[&v], Ty::List(Items::Any));
                self.clobber();
                spread
            }
        }
    }
}

/// A string's code points: a surrogate pair is one.
fn code_points(units: &[u16]) -> Vec<crate::core::Utf16> {
    let mut out = Vec::new();
    let mut k = 0;
    while k < units.len() {
        let pair = (0xD800..0xDC00).contains(&units[k]) && units.get(k + 1).is_some_and(|u| (0xDC00..0xE000).contains(u));
        let width = if pair { 2 } else { 1 };
        out.push(crate::core::Utf16::new(units[k..k + width].iter().copied()));
        k += width;
    }
    out
}
