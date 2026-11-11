//! Folds that keep an element. Where each step leaves a path of the accumulator as it was or
//! sets it to a term of the element alone, the path ends as that term of some element, or as
//! the seed where no step set it: the seed stands for an element that may not exist, as a
//! fallback does for a read.
use super::Lowerer;
use super::value::{Seq, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Kind, Known, Shape, Utf16};
use egg::Id;

/// What a seeded fold answers, as lowering can say it.
pub enum Seeded<'a> {
    /// No path keeps an element: a count, a flag, or an aggregate of the old value and the
    /// element, as a sum is. The fold term says it.
    Plain,
    /// A path keeps an element in a way lowering does not model.
    Undecided,
    /// The whole answer keeps an element: that element's term, or the seed.
    Whole(Val<'a>),
    /// The answer is a record, and these fields keep an element: each that element's term, or
    /// the seed's field.
    Fields(Vec<(Utf16, Val<'a>)>),
}

/// What a fold makes of one path of its answer.
enum Path {
    Plain,
    /// It ends as this term of some element, or as what the seed held there.
    Keeps(Id),
    Undecided,
}

/// One value a path may take in a step: what it held before, or a term.
#[derive(Clone, Copy)]
enum Arm {
    Kept,
    Term(Id),
}

/// A fold callback's binders: the accumulator, the element, and the index.
#[derive(Clone, Copy)]
pub struct Binders {
    pub acc: Id,
    pub x: Id,
    pub i: Id,
}

impl<'a> Lowerer<'a, '_> {
    /// A seeded fold over `list` whose callback answers `body` over the binders `b`.
    pub fn seeded(&mut self, list: Seq, b: Binders, body: Id, seed: &Val<'a>) -> Seeded<'a> {
        let arms = self.steps(body, &|t| t == b.acc, b);
        let built: Vec<Option<Vec<(Utf16, Id)>>> = arms.iter().map(|&a| if a == b.acc { None } else { self.b.fields(a) }).collect();
        let records = arms.iter().zip(&built).all(|(&a, f)| a == b.acc || f.is_some()) && built.iter().any(Option::is_some);
        if !records {
            // A record the callback builds beside an answer of another kind: its fields are not
            // followed, so an element in one is undecided.
            if arms.iter().any(|&a| self.b.fields(a).is_some() && self.b.mentions(a, b.x)) {
                return Seeded::Undecided;
            }
            let steps: Vec<Arm> = arms.iter().map(|&a| if a == b.acc { Arm::Kept } else { Arm::Term(a) }).collect();
            return match self.path(&steps, &|t| t == b.acc, b) {
                Path::Plain => Seeded::Plain,
                Path::Undecided => Seeded::Undecided,
                Path::Keeps(term) => Seeded::Whole(self.kept(list, b.x, term, seed)),
            };
        }
        let mut names: Vec<Utf16> = Vec::new();
        for (name, _) in built.iter().flatten().flatten() {
            if !names.contains(name) {
                names.push(*name);
            }
        }
        let mut kept = Vec::new();
        for name in names {
            // In a step, the field is the accumulator's own where the callback passes the
            // accumulator on, the record's field where it builds one, and undefined where its
            // record has no such field.
            let mut steps = Vec::new();
            for record in &built {
                match record {
                    None => steps.push(Arm::Kept),
                    Some(fields) => match fields.iter().find(|(n, _)| *n == name) {
                        Some(&(_, value)) => steps.extend(self.steps(value, &|t| self.b.is_field_of(t, b.acc, name), b).into_iter().map(Arm::Term)),
                        None => steps.push(Arm::Term(self.b.add(Core::Undef))),
                    },
                }
            }
            let own = |t: Id| self.b.is_field_of(t, b.acc, name);
            match self.path(&steps, &own, b) {
                Path::Plain => {}
                Path::Undecided => return Seeded::Undecided,
                Path::Keeps(term) => {
                    let Val::Record(fields) = seed else { return Seeded::Undecided };
                    let fallback = self.field(fields, name);
                    kept.push((name, self.kept(list, b.x, term, &fallback)));
                }
            }
        }
        if kept.is_empty() { Seeded::Plain } else { Seeded::Fields(kept) }
    }

    /// The values a path may take in a step, through the callback's conditionals on the
    /// accumulator or the index. A conditional on neither is a value of the element alone. A
    /// conditional on the path's own truthiness that keeps it or sets it to a boolean is `||` or
    /// `&&` folded over the list, as `some` and `every` are: one aggregate, not a choice.
    fn steps(&self, id: Id, own: &dyn Fn(Id) -> bool, b: Binders) -> Vec<Id> {
        let Core::If([test, yes, no]) = *self.b.node(id) else { return vec![id] };
        if !self.b.mentions(id, b.acc) && !self.b.mentions(id, b.i) {
            return vec![id];
        }
        let on_own = own(test) || self.b.truthy_of(test).is_some_and(own);
        let boolean = |t: Id| self.b.shape(t).within(Shape::BOOL);
        if on_own && ((own(yes) && boolean(no)) || (own(no) && boolean(yes))) {
            return vec![id];
        }
        let mut steps = self.steps(yes, own, b);
        steps.extend(self.steps(no, own, b));
        steps
    }
    /// What a path ends as, from the values its steps give it. `own` picks out the path's old
    /// value: a term holding it and the element aggregates them, as a sum does.
    fn path(&self, steps: &[Arm], own: &dyn Fn(Id) -> bool, b: Binders) -> Path {
        let (mut element, mut beside, mut aggregate) = (None, false, false);
        for &step in steps {
            let Arm::Term(t) = step else { continue };
            if own(t) {
                continue;
            }
            let carries = self.b.mentions(t, b.x);
            let old = self.b.mentions_where(t, own);
            let state = self.b.mentions(t, b.acc) || self.b.mentions(t, b.i);
            match (carries, old, state) {
                (true, true, _) => aggregate = true,
                // The element alone: the same term in every arm that sets it, or undecided.
                (true, false, false) if element.is_none_or(|e| e == t) => element = Some(t),
                // An element beside the count or other state, or two terms of it.
                (true, false, _) => return Path::Undecided,
                (false, _, _) => beside = true,
            }
        }
        match element {
            None => Path::Plain,
            // A step that sets the path to something else, or folds the old value in, makes
            // the end something other than an element or the seed.
            Some(_) if beside || aggregate => Path::Undecided,
            Some(t) => Path::Keeps(t),
        }
    }

    /// The term `term` of some element of `list`, where `x` stands for the element, or
    /// `fallback` where none is kept: a read at an index no one knows, with `fallback` where it
    /// is missing.
    fn kept(&mut self, list: Seq, x: Id, term: Id, fallback: &Val<'a>) -> Val<'a> {
        let k = self.b.fresh(Kind::Index);
        let slot = self.element(list, &Form::atom(k));
        self.worlds(slot, Family::Unit, &mut |l, v| match v {
            Val::Undef => fallback.clone(),
            Val::Term(e, ty) if term == x => Val::Term(e, ty),
            Val::Term(e, _) => Val::Term(l.b.replace(term, x, e), Ty::Any),
            _ => l.unsupported(),
        })
    }
}
