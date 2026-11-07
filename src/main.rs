// TS expression -> (frontend/dump.ts) S-expression -> egg saturation -> cheat query.
// egg owns the e-graph, hash-consing, congruence, matching and scheduling. This file holds the
// ECMAScript semantics as rewrites, one e-class analysis (free variables, constants, intervals and
// the affine normal form of integer arithmetic), the
// let-substitution applier, and the query.
use egg::*;
use std::collections::{BTreeMap, HashSet};
use std::process::Command;
use std::time::Duration;

type G = EGraph<SymbolLang, Js>;

#[derive(Debug, Clone, PartialEq)]
enum Const { Int(i64), Bool(bool) }
impl std::fmt::Display for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self { Const::Int(v) => write!(f, "{v}"), Const::Bool(b) => write!(f, "{b}") }
    }
}

#[derive(Default)]
struct Js { clashes: Vec<String> }

// Affine normal form of an integer class: k + sum(c * atom), atoms are e-classes with no form of
// their own, keyed by canonical id. Two classes with the same form get the same canonical e-node in
// `modify`, and hash-consing merges them. This replaces comm/assoc/neg/sub rewriting entirely.
#[derive(Debug, Clone, PartialEq)]
struct Form { k: i64, t: BTreeMap<Id, i64> }
impl Form {
    fn konst(k: i64) -> Form { Form { k, t: BTreeMap::new() } }
    fn atom(a: Id) -> Form { Form { k: 0, t: BTreeMap::from([(a, 1)]) } }
    fn add(&self, o: &Form) -> Option<Form> {
        let mut t = self.t.clone();
        for (a, c) in &o.t { let e = t.entry(*a).or_insert(0); *e = e.checked_add(*c)?; }
        t.retain(|_, c| *c != 0);
        Some(Form { k: self.k.checked_add(o.k)?, t })
    }
    fn scale(&self, s: i64) -> Option<Form> {
        let mut t = BTreeMap::new();
        for (a, c) in &self.t { if *c != 0 && s != 0 { t.insert(*a, c.checked_mul(s)?); } }
        Some(Form { k: self.k.checked_mul(s)?, t })
    }
    // Re-key on canonical ids, substituting an atom that has since gained a form of its own.
    fn canon(&self, eg: &G) -> Option<Form> {
        let mut f = self.clone();
        for _ in 0..8 {
            let mut out = Form::konst(f.k);
            let mut changed = false;
            for (a, c) in &f.t {
                let r = eg.find(*a);
                let sub = match &eg[r].data.form { Some(g) if !g.t.contains_key(&r) && g.t.keys().all(|x| eg.find(*x) != r) => { changed = true; g.clone() } _ => { changed |= r != *a; Form::atom(r) } };
                out = out.add(&sub.scale(*c)?)?;
            }
            f = out;
            if !changed { break; }
        }
        Some(f)
    }
    fn interval(&self, eg: &G) -> (Option<i64>, Option<i64>) {
        let (mut lo, mut hi) = (Some(self.k), Some(self.k));
        for (a, c) in &self.t {
            let d = &eg[eg.find(*a)].data;
            let (l, h) = if *c > 0 { (d.lo, d.hi) } else { (d.hi, d.lo) };
            lo = lo.zip(l).and_then(|(x, y)| x.checked_add(y.checked_mul(*c)?));
            hi = hi.zip(h).and_then(|(x, y)| x.checked_add(y.checked_mul(*c)?));
        }
        (lo, hi)
    }
}
// The form of a child: its own, or the child itself as an atom. A form that mentions its own class
// (x = x + y, left by a merge) is no definition of x, so x stays an atom.
fn form_of(eg: &G, c: Id) -> Form {
    let r = eg.find(c);
    eg[r].data.form.as_ref().and_then(|f| f.canon(eg)).filter(|f| !f.t.contains_key(&r)).unwrap_or(Form::atom(r))
}
fn node_form(eg: &G, n: &SymbolLang) -> Option<Form> {
    let f = |i: usize| form_of(eg, n.children[i]);
    match (n.op.as_str(), n.children.len()) {
        (s, 0) => s.parse::<i64>().ok().map(Form::konst),
        ("+", 2) => f(0).add(&f(1)),
        ("-", 2) => f(0).add(&f(1).scale(-1)?),
        ("neg", 1) => f(0).scale(-1),
        ("*", 2) => { let (a, b) = (f(0), f(1)); if a.t.is_empty() { b.scale(a.k) } else if b.t.is_empty() { a.scale(b.k) } else { None } }
        _ => None,
    }
}
// The canonical e-node of a form: atoms in id order, right-nested, constant last.
fn build(eg: &mut G, f: &Form) -> Id {
    let mut terms: Vec<Id> = vec![];
    for (a, c) in &f.t {
        terms.push(match c {
            1 => *a,
            -1 => eg.add(SymbolLang::new("neg", vec![*a])),
            _ => { let k = eg.add(SymbolLang::leaf(c.to_string())); eg.add(SymbolLang::new("*", vec![k, *a])) }
        });
    }
    if f.k != 0 || terms.is_empty() { terms.push(eg.add(SymbolLang::leaf(f.k.to_string()))); }
    let mut acc = terms.pop().unwrap();
    while let Some(t) = terms.pop() { acc = eg.add(SymbolLang::new("+", vec![t, acc])); }
    acc
}

#[derive(Debug)]
struct Data { free: HashSet<Id>, constant: Option<Const>, lo: Option<i64>, hi: Option<i64>, form: Option<Form> }

// Integer interval of an e-node from its children's intervals (None = unbounded on that side).
// The only non-structural fact is that rel(k, n) lies in [0, n].
fn interval(eg: &G, n: &SymbolLang) -> (Option<i64>, Option<i64>) {
    let iv = |i: usize| { let d = &eg[n.children[i]].data; (d.lo, d.hi) };
    match (n.op.as_str(), n.children.len()) {
        (s, 0) => match s.parse::<i64>() { Ok(v) => (Some(v), Some(v)), _ => (None, None) },
        ("len", 1) => (Some(0), None),
        ("min", 2) => { let (a, b) = (iv(0), iv(1)); (a.0.zip(b.0).map(|(x, y)| x.min(y)), match (a.1, b.1) { (Some(x), Some(y)) => Some(x.min(y)), (x, y) => x.or(y) }) }
        ("max", 2) => { let (a, b) = (iv(0), iv(1)); (match (a.0, b.0) { (Some(x), Some(y)) => Some(x.max(y)), (x, y) => x.or(y) }, a.1.zip(b.1).map(|(x, y)| x.max(y))) }
        ("if", 3) => { let (a, b) = (iv(1), iv(2)); (a.0.zip(b.0).map(|(x, y)| x.min(y)), a.1.zip(b.1).map(|(x, y)| x.max(y))) }
        ("rel", 2) => (Some(0), iv(1).1),
        _ => match node_form(eg, n) { Some(f) => f.interval(eg), None => (None, None) },
    }
}

fn eval(eg: &G, n: &SymbolLang) -> Option<Const> {
    let c = |i: usize| eg[n.children[i]].data.constant.clone();
    let int = |i: usize| match c(i) { Some(Const::Int(v)) => Some(v), _ => None };
    let boo = |i: usize| match c(i) { Some(Const::Bool(v)) => Some(v), _ => None };
    // b - a as a form, bounded by the atoms' intervals: decides a comparison without rewriting it.
    let diff = || { let d = form_of(eg, n.children[1]).add(&form_of(eg, n.children[0]).scale(-1)?)?; Some(d.interval(eg)) };
    let decide = |t: &dyn Fn(i64) -> bool, f: &dyn Fn(i64) -> bool| { let (l, h) = diff()?; if l.map_or(false, |l| t(l)) { Some(Const::Bool(true)) } else if h.map_or(false, |h| f(h)) { Some(Const::Bool(false)) } else { None } };
    match (n.op.as_str(), n.children.len()) {
        (s, 0) => s.parse::<i64>().ok().map(Const::Int).or(match s { "true" => Some(Const::Bool(true)), "false" => Some(Const::Bool(false)), _ => None }),
        ("+" | "-" | "neg" | "*", _) => node_form(eg, n).filter(|f| f.t.is_empty()).map(|f| Const::Int(f.k)),
        ("<", 2) => decide(&|l| l >= 1, &|h| h <= 0),
        ("<=", 2) => decide(&|l| l >= 0, &|h| h < 0),
        ("==i", 2) => { let (l, h) = diff()?; if l == Some(0) && h == Some(0) { Some(Const::Bool(true)) } else if l.map_or(false, |l| l > 0) || h.map_or(false, |h| h < 0) { Some(Const::Bool(false)) } else { None } }
        ("===", 2) => Some(Const::Bool(c(0)? == c(1)?)),
        ("min", 2) => Some(Const::Int(int(0)?.min(int(1)?))),
        ("max", 2) => Some(Const::Int(int(0)?.max(int(1)?))),
        ("!", 1) => Some(Const::Bool(!boo(0)?)),
        ("&&", 2) => if boo(0) == Some(false) || boo(1) == Some(false) { Some(Const::Bool(false)) } else { Some(Const::Bool(boo(0)? && boo(1)?)) },
        ("||", 2) => if boo(0) == Some(true) || boo(1) == Some(true) { Some(Const::Bool(true)) } else { Some(Const::Bool(boo(0)? || boo(1)?)) },
        _ => None,
    }
}

impl Analysis<SymbolLang> for Js {
    type Data = Data;
    fn make(eg: &G, n: &SymbolLang) -> Data {
        let f = |i: &Id| eg[*i].data.free.clone();
        let mut free = HashSet::new();
        match (n.op.as_str(), n.children.as_slice()) {
            ("var", [v]) => { free.insert(*v); }
            ("lam", [v, b]) => { free.extend(f(b)); free.remove(v); }
            ("let", [v, e, b]) => { free.extend(f(b)); free.remove(v); free.extend(f(e)); }
            _ => for ch in &n.children { free.extend(f(ch)); },
        }
        let constant = eval(eg, n);
        let form = node_form(eg, n);
        let (lo, hi) = match constant { Some(Const::Int(v)) => (Some(v), Some(v)), _ => interval(eg, n) };
        Data { free, constant, lo, hi, form }
    }
    // Free variables intersect on merge: if any member of the class does without a variable, the
    // value does not depend on it. That is what makes `acc - acc` drop `acc`.
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        let before = to.free.len();
        to.free.retain(|i| from.free.contains(i));
        let d = DidMerge(before != to.free.len(), to.free.len() != from.free.len());
        let mut clash = None;
        let d2 = merge_option(&mut to.constant, from.constant, |a, b| { if *a != b { clash = Some(format!("{a} = {b}")); } DidMerge(false, false) });
        if let Some(c) = clash { self.clashes.push(c); }
        // Intervals intersect on merge.
        let lo = match (to.lo, from.lo) { (Some(a), Some(b)) => Some(a.max(b)), (a, b) => a.or(b) };
        let hi = match (to.hi, from.hi) { (Some(a), Some(b)) => Some(a.min(b)), (a, b) => a.or(b) };
        let d3 = DidMerge((lo, hi) != (to.lo, to.hi), (lo, hi) != (from.lo, from.hi));
        if let (Some(l), Some(h)) = (lo, hi) { if l > h { self.clashes.push(format!("empty interval [{l}, {h}]")); } }
        to.lo = lo; to.hi = hi;
        // Forms: a form beats none, and fewer atoms beat more.
        let d4 = match (&to.form, from.form) {
            (_, None) => DidMerge(false, to.form.is_some()),
            (None, Some(g)) => { to.form = Some(g); DidMerge(true, false) }
            (Some(f), Some(g)) => if g.t.len() < f.t.len() { to.form = Some(g); DidMerge(true, false) } else { DidMerge(false, *f != g) },
        };
        d | d2 | d3 | d4
    }
    fn modify(eg: &mut G, id: Id) {
        if let (Some(l), Some(h), None) = (eg[id].data.lo, eg[id].data.hi, &eg[id].data.constant) {
            if l == h { let k = eg.add(SymbolLang::leaf(l.to_string())); eg.union(id, k); }
        }
        if let Some(c) = eg[id].data.constant.clone() {
            let k = eg.add(SymbolLang::leaf(c.to_string()));
            eg.union(id, k);
            return;
        }
        // The class's arithmetic in affine normal form, as one canonical e-node.
        if let Some(f) = eg[id].data.form.clone().and_then(|f| f.canon(eg)) {
            let me = eg.find(id);
            match f.t.get(&me) {
                None => { let c = build(eg, &f); eg.union(id, c); }
                // x = x + r: the rest is zero.
                Some(1) => {
                    let mut r = f.clone();
                    r.t.remove(&me);
                    let c = build(eg, &r);
                    let z = eg.add(SymbolLang::leaf("0"));
                    eg.union(c, z);
                }
                Some(_) => {}
            }
        }
        // Comparisons in one shape: a < b is 0 <= b - a - 1, a <= b is 0 <= b - a.
        let cmps: Vec<SymbolLang> = eg[id].nodes.iter().filter(|n| matches!(n.op.as_str(), "<" | "<=")).cloned().collect();
        for n in cmps {
            let off = if n.op.as_str() == "<" { -1 } else { 0 };
            let Some(d) = form_of(eg, n.children[1]).add(&form_of(eg, n.children[0]).scale(-1).unwrap_or(Form::konst(0))).and_then(|d| d.add(&Form::konst(off))) else { continue };
            let z = eg.add(SymbolLang::leaf("0"));
            let c = build(eg, &d);
            let k = eg.add(SymbolLang::new("<=", vec![z, c]));
            eg.union(id, k);
        }
    }
}

// (let v e body): substitute by pushing the let one e-node down, for every e-node in body's class,
// renaming a lambda that would capture a free variable of e. Adapted from egg's lambda test, with
// one generic case in place of a rule per operator.
struct LetPush { v: Var, e: Var, body: Var }
impl Applier<SymbolLang, Js> for LetPush {
    fn apply_one(&self, eg: &mut G, eclass: Id, subst: &Subst, _: Option<&PatternAst<SymbolLang>>, _: Symbol) -> Vec<Id> {
        let (v, e, body) = (subst[self.v], subst[self.e], subst[self.body]);
        let mut out: Vec<Id> = vec![];
        if !eg[body].data.free.contains(&v) {
            out.push(body);
        } else {
            let nodes = eg[body].nodes.clone();
            let lett = |eg: &mut G, x: Id| eg.add(SymbolLang::new("let", vec![v, e, x]));
            for n in nodes {
                match (n.op.as_str(), n.children.as_slice()) {
                    ("var", [x]) => out.push(if eg.find(*x) == eg.find(v) { e } else { body }),
                    ("lam", [x, b]) => {
                        if eg.find(*x) == eg.find(v) { out.push(body); continue; }
                        if eg[e].data.free.contains(x) {
                            let fresh = eg.add(SymbolLang::leaf(format!("_{}", usize::from(eclass))));
                            let fv = eg.add(SymbolLang::new("var", vec![fresh]));
                            let ren = eg.add(SymbolLang::new("let", vec![*x, fv, *b]));
                            let inner = lett(eg, ren);
                            out.push(eg.add(SymbolLang::new("lam", vec![fresh, inner])));
                        } else {
                            let inner = lett(eg, *b);
                            out.push(eg.add(SymbolLang::new("lam", vec![*x, inner])));
                        }
                    }
                    ("let", [x, e2, b2]) => {
                        if eg[e].data.free.contains(x) { continue; }
                        let e2s = lett(eg, *e2);
                        let b2s = if eg.find(*x) == eg.find(v) { *b2 } else { lett(eg, *b2) };
                        out.push(eg.add(SymbolLang::new("let", vec![*x, e2s, b2s])));
                    }
                    (_, []) => out.push(body),
                    _ => {
                        let kids = n.children.iter().map(|c| lett(eg, *c)).collect();
                        out.push(eg.add(SymbolLang::new(n.op, kids)));
                    }
                }
            }
        }
        out.into_iter().filter(|&id| eg.union(eclass, id)).map(|_| eclass).collect()
    }
}

// I1's seeding direction, reporting a change only when the index? e-node is new (egg 0.9's
// multi-pattern applier reports every match as a change, so a run with it never saturates).
struct Seed;
impl Applier<SymbolLang, Js> for Seed {
    fn apply_one(&self, eg: &mut G, _: Id, s: &Subst, _: Option<&PatternAst<SymbolLang>>, _: Symbol) -> Vec<Id> {
        let (xs, k) = (s["?xs".parse().unwrap()], s["?k".parse().unwrap()]);
        let n = SymbolLang::new("index?", vec![xs, k]);
        if eg.lookup(n.clone()).is_some() { return vec![]; }
        vec![eg.add(n)]
    }
}
// M1: union ?r with (maybe ?z ?m), reporting only real merges.
struct M1;
impl Applier<SymbolLang, Js> for M1 {
    fn apply_matches(&self, eg: &mut G, matches: &[SearchMatches<SymbolLang>], _: Symbol) -> Vec<Id> {
        let (r, z, m): (Var, Var, Var) = ("?r".parse().unwrap(), "?z".parse().unwrap(), "?m".parse().unwrap());
        let mut changed = vec![];
        for mat in matches {
            for s in &mat.substs {
                let mb = eg.add(SymbolLang::new("maybe", vec![s[z], s[m]]));
                if eg.union(s[r], mb) { changed.push(s[r]); }
            }
        }
        changed
    }
    fn apply_one(&self, _: &mut G, _: Id, _: &Subst, _: Option<&PatternAst<SymbolLang>>, _: Symbol) -> Vec<Id> { vec![] }
}

// The width of a relative range: for n >= 0 and b >= a, rel(b, n) - rel(a, n) <= b - a (rel is
// clamping, and a negative start lands at n + a >= a). The applier adds b - a, and once saturation
// has folded it to a constant d >= 0 it records the bound as the equality x = min(x, d).
struct RelWidth;
impl Applier<SymbolLang, Js> for RelWidth {
    fn apply_one(&self, eg: &mut G, eclass: Id, s: &Subst, _: Option<&PatternAst<SymbolLang>>, _: Symbol) -> Vec<Id> {
        let (a, b) = (s["?a".parse().unwrap()], s["?b".parse().unwrap()]);
        let w = eg.add(SymbolLang::new("-", vec![b, a]));
        let Some(Const::Int(d)) = eg[w].data.constant.clone() else { return vec![] };
        if d < 0 { return vec![]; }
        let k = eg.add(SymbolLang::leaf(d.to_string()));
        let m = eg.add(SymbolLang::new("min", vec![eclass, k]));
        if eg.union(eclass, m) { vec![eclass] } else { vec![] }
    }
}
// A list whose length lies in [0, 1] is either empty or its own first element:
// xs = (if (< 0 (len xs)) (cons (at xs 0) nil) nil). Fires only on a proven bound, not on a shape.
struct Short;
impl Applier<SymbolLang, Js> for Short {
    fn apply_one(&self, eg: &mut G, eclass: Id, s: &Subst, _: Option<&PatternAst<SymbolLang>>, _: Symbol) -> Vec<Id> {
        let xs = s["?xs".parse().unwrap()];
        let (lo, hi) = (eg[eclass].data.lo, eg[eclass].data.hi);
        if lo.map_or(true, |l| l < 0) || hi.map_or(true, |h| h > 1) { return vec![]; }
        let zero = eg.add(SymbolLang::leaf("0"));
        let nil = eg.add(SymbolLang::leaf("nil"));
        let one = |eg: &mut G| { let h = eg.add(SymbolLang::new("at", vec![xs, zero])); eg.add(SymbolLang::new("cons", vec![h, nil])) };
        // A decided length gets its one shape, not a conditional with a dead branch: the dead
        // branch of (if false (cons ..) nil) would still be unfolded by at-if forever.
        let e = match (lo, hi) {
            (Some(0), Some(0)) => nil,
            (Some(1), Some(1)) => one(eg),
            _ => { let c = eg.add(SymbolLang::new("<", vec![zero, eclass])); let o = one(eg); eg.add(SymbolLang::new("if", vec![c, o, nil])) }
        };
        if eg.union(xs, e) { vec![xs] } else { vec![] }
    }
}

// Every slice has a width: seed (len xs) for a sublist so the width bound has a node to land on,
// whoever consumes the slice. Reports a change only when the node is new.
struct Width;
impl Applier<SymbolLang, Js> for Width {
    fn apply_one(&self, eg: &mut G, eclass: Id, _: &Subst, _: Option<&PatternAst<SymbolLang>>, _: Symbol) -> Vec<Id> {
        let n = SymbolLang::new("len", vec![eclass]);
        if eg.lookup(n.clone()).is_some() { return vec![]; }
        eg.add(n);
        vec![]
    }
}

fn not_free(acc: &str, body: &str) -> impl Fn(&mut G, Id, &Subst) -> bool {
    let (acc, body): (Var, Var) = (acc.parse().unwrap(), body.parse().unwrap());
    move |eg, _, s| !eg[s[body]].data.free.contains(&s[acc])
}
fn is_int(v: &str) -> impl Fn(&mut G, Id, &Subst) -> bool {
    let v: Var = v.parse().unwrap();
    move |eg, _, s| matches!(eg[s[v]].data.constant, Some(Const::Int(_)))
}

// Both sides are integers (a form, an interval or an integer constant), so === is integer equality.
fn both_int(a: &str, b: &str) -> impl Fn(&mut G, Id, &Subst) -> bool {
    let (a, b): (Var, Var) = (a.parse().unwrap(), b.parse().unwrap());
    let int = |eg: &G, id: Id| { let d = &eg[id].data; d.form.is_some() || d.lo.is_some() || d.hi.is_some() || matches!(d.constant, Some(Const::Int(_))) };
    move |eg, _, s| int(eg, s[a]) && int(eg, s[b])
}

fn rules() -> Vec<Rewrite<SymbolLang, Js>> {
    let mut r: Vec<Rewrite<SymbolLang, Js>> = vec![
        // --- syntax forms to their ECMAScript meaning, one form per rule ---
        rewrite!("length"; "(prop ?xs length)" => "(len ?xs)"),
        rewrite!("elem"; "(elem ?xs ?k)" => "(index? ?xs ?k)"),
        rewrite!("arr-cons"; "(arr-cons ?h ?t)" => "(cons ?h ?t)"),
        rewrite!("arr-spread"; "(arr-spread ?xs ?t)" => "(append ?xs ?t)"),
        rewrite!("coalesce"; "(coalesce ?a ?b)" => "(maybe ?b ?a)"),
        rewrite!("default"; "(default ?m ?d)" => "(maybe ?d ?m)"),
        rewrite!("slice2"; "(mcall slice ?xs ?a ?b)" => "(sublist ?xs (rel ?a (len ?xs)) (rel ?b (len ?xs)))"),
        rewrite!("slice1"; "(mcall slice ?xs ?a)" => "(sublist ?xs (rel ?a (len ?xs)) (len ?xs))"),
        rewrite!("slice0"; "(mcall slice ?xs)" => "?xs"),
        rewrite!("rel"; "(rel ?k ?n)" => "(if (< ?k 0) (max (+ ?n ?k) 0) (min ?k ?n))"),
        rewrite!("at-method"; "(mcall at ?xs ?k)" => "(index? ?xs (if (< ?k 0) (+ (len ?xs) ?k) ?k))"),
        rewrite!("reduce2"; "(mcall reduce ?xs ?f ?z)" => "(foldl ?f ?z ?xs)"),
        rewrite!("reduce1"; "(mcall reduce ?xs ?f)" => "(if (< 0 (len ?xs)) (foldl ?f (at ?xs 0) (sublist ?xs 1 (len ?xs))) throw)"),
        rewrite!("map-method"; "(mcall map ?xs ?f)" => "(map ?f ?xs)"),
        // filter calls back with (element, index); filteri carries the index.
        rewrite!("filter"; "(mcall filter ?xs ?f)" => "(filteri ?f 0 ?xs)"),
        rewrite!("concat"; "(mcall concat ?xs ?ys)" => "(append ?xs ?ys)"),
        rewrite!("toReversed"; "(mcall toReversed ?xs)" => "(reverse ?xs)"),
        rewrite!("truthy-len"; "(truthy (len ?xs))" => "(< 0 (len ?xs))"),
        // --- binding ---
        rewrite!("beta"; "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rewrite!("let"; "(let ?v ?e ?body)" => { LetPush { v: "?v".parse().unwrap(), e: "?e".parse().unwrap(), body: "?body".parse().unwrap() } }),
        // --- integer order (arithmetic itself is the affine normal form in the analysis) ---
        rewrite!("not-lt"; "(! (< ?a ?b))" => "(<= ?b ?a)"),
        rewrite!("not-le"; "(! (<= ?a ?b))" => "(< ?b ?a)"),
        rewrite!("eqi"; "(==i ?a ?b)" => "(&& (<= ?a ?b) (<= ?b ?a))"),
        rewrite!("min-comm"; "(min ?a ?b)" => "(min ?b ?a)"),
        rewrite!("max-comm"; "(max ?a ?b)" => "(max ?b ?a)"),
        // --- booleans and conditionals ---
        rewrite!("not-not"; "(! (! ?a))" => "?a"),
        rewrite!("and-t1"; "(&& true ?a)" => "?a"),
        rewrite!("and-t2"; "(&& ?a true)" => "?a"),
        rewrite!("and-idem"; "(&& ?a ?a)" => "?a"),
        rewrite!("or-f1"; "(|| false ?a)" => "?a"),
        rewrite!("or-f2"; "(|| ?a false)" => "?a"),
        rewrite!("if-t"; "(if true ?a ?b)" => "?a"),
        rewrite!("if-f"; "(if false ?a ?b)" => "?b"),
        rewrite!("if-same"; "(if ?c ?a ?a)" => "?a"),
        rewrite!("if-bool"; "(if ?c true false)" => "?c"),
        rewrite!("if-notbool"; "(if ?c false true)" => "(! ?c)"),
        rewrite!("if-not"; "(if (! ?c) ?a ?b)" => "(if ?c ?b ?a)"),
        rewrite!("if-then"; "(if ?c (if ?c ?a ?b) ?d)" => "(if ?c ?a ?d)"),
        rewrite!("if-else"; "(if ?c ?a (if ?c ?b ?d))" => "(if ?c ?a ?d)"),
        // --- strict equality with undefined ---
        rewrite!("eq-comm"; "(=== ?a ?b)" => "(=== ?b ?a)"),
        rewrite!("eq-int"; "(=== ?a ?b)" => "(==i ?a ?b)" if both_int("?a", "?b")),
        rewrite!("le-not"; "(<= ?a ?b)" => "(! (< ?b ?a))"),
        rewrite!("eq-at-undef"; "(=== (at ?xs ?k) undef)" => "false"),
        rewrite!("eq-if"; "(=== (if ?c ?a ?b) ?d)" => "(if ?c (=== ?a ?d) (=== ?b ?d))"),
        // --- lists, by length and indexed read (every `at` rule carries its own bounds test) ---
        rewrite!("index?"; "(index? ?xs ?k)" => "(if (&& (<= 0 ?k) (< ?k (len ?xs))) (at ?xs ?k) undef)"),
        rewrite!("len-nil"; "(len nil)" => "0"),
        rewrite!("len-nonneg"; "(<= 0 (len ?xs))" => "true"),
        rewrite!("len-not-neg"; "(< (len ?xs) 0)" => "false"),
        rewrite!("len-cons"; "(len (cons ?h ?t))" => "(+ 1 (len ?t))"),
        rewrite!("len-append"; "(len (append ?a ?b))" => "(+ (len ?a) (len ?b))"),
        rewrite!("len-sublist"; "(len (sublist ?xs ?s ?e))" => "(max (- ?e ?s) 0)"),
        rewrite!("len-map"; "(len (map ?f ?xs))" => "(len ?xs)"),
        rewrite!("len-reverse"; "(len (reverse ?xs))" => "(len ?xs)"),
        rewrite!("append-nil1"; "(append nil ?b)" => "?b"),
        rewrite!("append-nil2"; "(append ?a nil)" => "?a"),
        rewrite!("append-cons"; "(append (cons ?h ?t) ?b)" => "(cons ?h (append ?t ?b))"),
        rewrite!("at-nil"; "(at nil ?k)" => "oob"),
        rewrite!("at-cons"; "(at (cons ?h ?t) ?k)" => "(if (< 0 ?k) (at ?t (- ?k 1)) (if (==i ?k 0) ?h oob))"),
        rewrite!("at-append"; "(at (append ?a ?b) ?k)" => "(if (< ?k 0) oob (if (< ?k (len ?a)) (at ?a ?k) (at ?b (- ?k (len ?a)))))"),
        rewrite!("at-sublist"; "(at (sublist ?xs ?s ?e) ?k)" => "(if (&& (<= 0 ?k) (< ?k (- ?e ?s))) (at ?xs (+ ?s ?k)) oob)"),
        rewrite!("at-map"; "(at (map ?f ?xs) ?k)" => "(if (&& (<= 0 ?k) (< ?k (len ?xs))) (app ?f (at ?xs ?k)) oob)"),
        rewrite!("at-reverse"; "(at (reverse ?xs) ?k)" => "(if (&& (<= 0 ?k) (< ?k (len ?xs))) (at ?xs (- (- (len ?xs) 1) ?k)) oob)"),
        rewrite!("filteri-nil"; "(filteri ?f ?k nil)" => "nil"),
        rewrite!("filteri-cons"; "(filteri ?f ?k (cons ?h ?t))" => "(if (truthy (app (app ?f ?h) ?k)) (cons ?h (filteri ?f (+ ?k 1) ?t)) (filteri ?f (+ ?k 1) ?t))"),
        rewrite!("filteri-if"; "(filteri ?f ?k (if ?c ?a ?b))" => "(if ?c (filteri ?f ?k ?a) (filteri ?f ?k ?b))"),
        rewrite!("index?-if"; "(index? (if ?c ?a ?b) ?k)" => "(if ?c (index? ?a ?k) (index? ?b ?k))"),
        // --- fold ---
        rewrite!("foldl-nil"; "(foldl ?f ?z nil)" => "?z"),
        rewrite!("foldl-cons"; "(foldl ?f ?z (cons ?h ?t))" => "(foldl ?f (app (app ?f ?z) ?h) ?t)"),
        rewrite!("foldl-if"; "(foldl ?f ?z (if ?c ?a ?b))" => "(if ?c (foldl ?f ?z ?a) (foldl ?f ?z ?b))"),
        // F4, the one lemma (induction on the list): a step whose body does not depend on the
        // accumulator returns its last element's image, or the seed when there is none.
        rewrite!("F4"; "(foldl (lam ?acc (lam ?x ?body)) ?z ?xs)" => "(if (< 0 (len ?xs)) (let ?x (at ?xs (- (len ?xs) 1)) ?body) ?z)" if not_free("?acc", "?body")),
        // --- maybe: (maybe z m) is m, or z where m is undefined ---
        rewrite!("maybe-undef"; "(maybe ?z undef)" => "?z"),
        rewrite!("maybe-of-undef"; "(maybe undef ?m)" => "?m"),
        rewrite!("maybe-oob"; "(maybe ?z oob)" => "oob"),
        rewrite!("maybe-idem"; "(maybe ?z (maybe ?z ?m))" => "(maybe ?z ?m)"),
        rewrite!("maybe-at"; "(maybe ?z (at ?xs ?k))" => "(at ?xs ?k)"),
        rewrite!("maybe-num"; "(maybe ?z ?n)" => "?n" if is_int("?n")),
        // No maybe-if: M1 already builds (maybe z m) from the conditional, and distributing maybe over
        // every if e-node in m's class fanned out to 19k applications once if-not and le-not existed.
        rewrite!("eq-num-undef"; "(=== ?n undef)" => "false" if is_int("?n")),
    ];
    r.push(Rewrite::new("rel-width", "(- (rel ?b ?n) (rel ?a ?n))".parse::<Pattern<SymbolLang>>().unwrap(), RelWidth).unwrap());
    r.push(Rewrite::new("width-seed", "(sublist ?xs ?s ?e)".parse::<Pattern<SymbolLang>>().unwrap(), Width).unwrap());
    r.push(Rewrite::new("short-list", "(len ?xs)".parse::<Pattern<SymbolLang>>().unwrap(), Short).unwrap());
    r.push(rewrite!("append-if"; "(append (if ?c ?a ?b) ?t)" => "(if ?c (append ?a ?t) (append ?b ?t))"));
    r.push(rewrite!("at-if"; "(at (if ?c ?a ?b) ?k)" => "(if ?c (at ?a ?k) (at ?b ?k))"));
    // A condition that is already a boolean is its own truthiness.
    for b in ["(< ?a ?b)", "(<= ?a ?b)", "(=== ?a ?b)", "(==i ?a ?b)", "(! ?a)", "(&& ?a ?b)", "(|| ?a ?b)", "true", "false"] {
        let lhs: Pattern<SymbolLang> = format!("(truthy {b})").parse().unwrap();
        let rhs: Pattern<SymbolLang> = b.parse().unwrap();
        r.push(Rewrite::new(format!("truthy {b}"), lhs, rhs).unwrap());
    }
    // I1, seeding: a total read at(xs, k) adds its partial twin index?(xs, k), whose own rule
    // unfolds back to this same at. One index? per at; the pair closes.
    let at: Pattern<SymbolLang> = "(at ?xs ?k)".parse().unwrap();
    r.push(Rewrite::new("I1-seed", at, Seed).unwrap());
    // M1: a conditional that picks a read or a default, beside the read's own absence, is that
    // absence eliminated with the default.
    // With z = undef both patterns name the same class; maybe-of-undef then folds the union back
    // into that class instead of letting (maybe undef (maybe undef ...)) grow.
    let m1: MultiPattern<SymbolLang> = "?r = (if ?c (at ?xs ?k) ?z), ?m = (if ?c (at ?xs ?k) undef)".parse().unwrap();
    r.push(Rewrite::new("M1", m1, M1).unwrap());
    r
}

const SYNTAX: [&str; 10] = ["mcall", "prop", "truthy", "unknown", "app", "coalesce", "default", "arr-cons", "arr-spread", "elem"];
struct SemCost;
impl CostFunction<SymbolLang> for SemCost {
    type Cost = u64;
    fn cost<C: FnMut(Id) -> u64>(&mut self, n: &SymbolLang, mut costs: C) -> u64 {
        let own = if SYNTAX.contains(&n.op.as_str()) { 1000 } else { 1 };
        n.children.iter().fold(own, |a, c| a.saturating_add(costs(*c)))
    }
}

fn has(eg: &G, id: Id, op: &str) -> bool { eg[id].nodes.iter().any(|n| n.op.as_str() == op) }

fn run(src: &str, show_all: bool) {
    println!("\n{}\n{src}", "=".repeat(100));
    let out = Command::new("node").arg(concat!(env!("CARGO_MANIFEST_DIR"), "/frontend/dump.ts")).arg(src).output().expect("node");
    let sexpr = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if sexpr.is_empty() { println!("dumper failed: {}", String::from_utf8_lossy(&out.stderr)); return; }
    println!("dumped:  {sexpr}");
    let expr: RecExpr<SymbolLang> = sexpr.parse().unwrap();
    let runner = Runner::<SymbolLang, Js>::default()
        .with_iter_limit(60).with_node_limit(60_000).with_time_limit(Duration::from_secs(20))
        .with_expr(&expr).run(&rules());
    let eg = &runner.egraph;
    let root = eg.find(runner.roots[0]);
    let secs: f64 = runner.iterations.iter().map(|it| it.total_time).sum();
    println!("egg:     {} iterations, {} e-nodes, {} e-classes, {:.1} ms, stop: {:?}", runner.iterations.len(), eg.total_size(), eg.number_of_classes(), secs * 1e3, runner.stop_reason.as_ref().unwrap());
    let ex = Extractor::new(eg, AstSize);
    let best = |id: Id| ex.find_best(id).1.to_string();
    println!("root:    {}", best(root));
    if std::env::var("ROOTDBG").is_ok() {
        for n in &eg[root].nodes { println!("  root node: ({} {})", n.op, n.children.iter().map(|k| format!("[{}]", best(*k))).collect::<Vec<_>>().join(" ")); }
    }
    let mut applied: std::collections::BTreeMap<String, usize> = Default::default();
    for it in &runner.iterations { for (k, v) in &it.applied { *applied.entry(k.to_string()).or_default() += v; } }
    if std::env::var("RULES").is_ok() {
        println!("applied: {applied:?}");
        for (k, it) in runner.iterations.iter().enumerate() { println!("  iter {k}: nodes {} classes {} applied {:?}", it.egraph_nodes, it.egraph_classes, it.applied); }
    }

    if std::env::var("ATS").is_ok() {
        for c in eg.classes() { for n in &c.nodes { if matches!(n.op.as_str(), "at" | "len") { println!("  c{} [{:?}, {:?}]: ({} {})", c.id, c.data.lo, c.data.hi, n.op, n.children.iter().map(|k| best(*k)).collect::<Vec<_>>().join(" ")); } } }
    }
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    let mut order = vec![];
    while let Some(c) = stack.pop() {
        let c = eg.find(c);
        if !seen.insert(c) { continue; }
        order.push(c);
        for n in &eg[c].nodes { stack.extend(n.children.iter().copied()); }
    }
    // The cheat query: (maybe z m) with m an undetermined absence born of an indexed read, and z
    // a value the program wrote (not undefined, and not the IR's own oob or throw).
    let mut hits = vec![];
    let mut unknown = false;
    // A class under the root that holds only source syntax got no meaning from any rule (a method,
    // property or callee the engine does not model). Its value is unknown, so "no cheat" would be a
    // guess: such a run is UNDECIDED.
    // Read the root through its cheapest meaning, where a syntax e-node costs far more than any
    // semantic one: a syntax node survives in that reading only where no rule gave it a meaning.
    // (Walking every reachable class instead would count a lambda body from before substitution.)
    let sem = Extractor::new(eg, SemCost);
    let reading = sem.find_best(root).1;
    let mut opaque: Vec<String> = vec![];
    for n in reading.as_ref() {
        if SYNTAX.contains(&n.op.as_str()) { opaque.push(n.build_recexpr(|i| reading[i].clone()).to_string()); }
    }
    for &c in &order {
        for n in &eg[c].nodes {
            if n.op.as_str() == "unknown" { unknown = true; }
            if n.op.as_str() != "maybe" { continue; }
            let (z, m) = (eg.find(n.children[0]), eg.find(n.children[1]));
            if std::env::var("DEBUG").is_ok() { let ops: Vec<String> = eg[m].nodes.iter().map(|x| x.op.to_string()).collect(); println!("  maybe in c{c}: z={} m=c{m} {:?} best {}", best(z), ops, best(m)); }
            let born = has(eg, m, "index?");
            let determined = has(eg, m, "undef") || has(eg, m, "at") || has(eg, m, "oob") || eg[m].data.constant.is_some();
            let written = !has(eg, z, "undef") && !has(eg, z, "oob") && !has(eg, z, "throw");
            if born && !determined && written {
                let reads: Vec<String> = eg[m].nodes.iter().filter(|x| x.op.as_str() == "index?").map(|x| format!("(index? {} {})", best(x.children[0]), best(x.children[1]))).collect();
                hits.push(format!("e-class {c}: (maybe {} {})   reads {}", best(z), best(m), reads.join(" = ")));
            }
        }
    }
    let mut clashes = runner.egraph.analysis.clashes.clone();
    for c in eg.classes() {
        let ops: HashSet<&str> = c.nodes.iter().map(|n| n.op.as_str()).collect();
        if (ops.contains("undef") && (c.data.constant.is_some() || ops.contains("at"))) || (ops.contains("nil") && ops.contains("cons")) { clashes.push(format!("e-class {}", c.id)); }
    }
    println!("consistency: {}", if clashes.is_empty() { "ok".to_string() } else { format!("UNSOUND {clashes:?}") });
    if !hits.is_empty() {
        println!("verdict: CHEAT");
        for h in hits.iter().take(4) { println!("  {h}"); }
    } else if unknown {
        println!("verdict: UNDECIDED (an unknown syntax form is under the root)");
    } else if !opaque.is_empty() {
        opaque.sort_by_key(|x| x.len());
        println!("verdict: UNDECIDED (no rule gives a meaning to {})", opaque[0]);
    } else if !matches!(runner.stop_reason, Some(StopReason::Saturated)) {
        println!("verdict: UNDECIDED (stopped at a limit before saturating; no finding yet)");
    } else {
        println!("verdict: no cheat");
    }
    if show_all {
        println!("e-classes reachable from the root ({}):", order.len());
        order.sort();
        for c in order {
            let ns: Vec<String> = eg[c].nodes.iter().map(|n| if n.children.is_empty() { n.op.to_string() } else { format!("({} {})", n.op, n.children.iter().map(|k| format!("c{}", eg.find(*k))).collect::<Vec<_>>().join(" ")) }).collect();
            let iv = match (eg[c].data.lo, eg[c].data.hi) { (None, None) => String::new(), (l, h) => format!("  in [{}, {}]", l.map_or("-inf".into(), |v| v.to_string()), h.map_or("+inf".into(), |v| v.to_string())) };
            println!("  {}c{c}{iv}  best {}\n      {}", if c == root { "*" } else { " " }, best(c), ns.join("\n      "));
        }
    }
}

// All expressions in one e-graph: congruence decides which of them are the same value.
fn joint(srcs: &[String]) {
    let mut runner = Runner::<SymbolLang, Js>::default().with_iter_limit(60).with_node_limit(60_000).with_time_limit(Duration::from_secs(30));
    for src in srcs {
        let out = Command::new("node").arg(concat!(env!("CARGO_MANIFEST_DIR"), "/frontend/dump.ts")).arg(src).output().expect("node");
        let expr: RecExpr<SymbolLang> = String::from_utf8_lossy(&out.stdout).trim().parse().unwrap();
        runner = runner.with_expr(&expr);
    }
    let runner = runner.run(&rules());
    let eg = &runner.egraph;
    let secs: f64 = runner.iterations.iter().map(|it| it.total_time).sum();
    println!("one e-graph, {} roots: {} iterations, {} e-nodes, {} e-classes, {:.1} ms, stop: {:?}", srcs.len(), runner.iterations.len(), eg.total_size(), eg.number_of_classes(), secs * 1e3, runner.stop_reason.as_ref().unwrap());
    let mut applied: std::collections::BTreeMap<String, usize> = Default::default();
    for it in &runner.iterations { for (k, v) in &it.applied { *applied.entry(k.to_string()).or_default() += v; } }
    println!("rules that merged something: {}", applied.iter().map(|(k, v)| format!("{k} x{v}")).collect::<Vec<_>>().join(", "));
    let clashes = &eg.analysis.clashes;
    println!("consistency: {}", if clashes.is_empty() { "ok".to_string() } else { format!("UNSOUND {clashes:?}") });
    let ex = Extractor::new(eg, AstSize);
    let best = |id: Id| ex.find_best(id).1.to_string();
    let show = |c: Id| {
        let d = &eg[c].data;
        let iv = match (d.lo, d.hi) { (None, None) => String::new(), (l, h) => format!("  in [{}, {}]", l.map_or("-inf".into(), |v| v.to_string()), h.map_or("+inf".into(), |v| v.to_string())) };
        let ns: Vec<String> = eg[c].nodes.iter().map(|n| if n.children.is_empty() { n.op.to_string() } else { format!("({} {})", n.op, n.children.iter().map(|k| format!("c{}", eg.find(*k))).collect::<Vec<_>>().join(" ")) }).collect();
        // A class reached through if-then/maybe-if can hold hundreds of conditional e-nodes that
        // restate it under its own condition; list the rest whole and count those.
        let (conds, rest): (Vec<String>, Vec<String>) = ns.into_iter().partition(|x| x.starts_with("(if ") && x.contains(&format!(" c{c})")) || x.starts_with("(if ") && x.contains(&format!(" c{c} ")));
        let tail = if conds.is_empty() { String::new() } else { format!("\n      + {} (if ..) e-nodes with this class as a branch", conds.len()) };
        println!("  c{c}{iv}  best {}\n      {}{tail}", best(c), rest.join("\n      "));
    };
    let roots: Vec<Id> = runner.roots.iter().map(|r| eg.find(*r)).collect();
    println!("\nroots:");
    for (src, r) in srcs.iter().zip(&roots) { println!("  c{r}  <- {src}"); }
    let mut classes: Vec<Id> = roots.clone();
    classes.dedup();
    classes.sort(); classes.dedup();
    for r in &classes {
        let members: Vec<usize> = roots.iter().enumerate().filter(|(_, x)| *x == r).map(|(i, _)| i + 1).collect();
        println!("\ne-class c{r} holds roots {members:?}:");
        show(*r);
        // The cheat witness inside the class, and the classes it is built from.
        for n in &eg[*r].nodes {
            if n.op.as_str() != "maybe" { continue; }
            let (z, m) = (eg.find(n.children[0]), eg.find(n.children[1]));
            let Some(read) = eg[m].nodes.iter().find(|x| x.op.as_str() == "index?" && eg[x.children[1]].data.constant == Some(Const::Int(0))) else { continue };
            if eg[z].data.constant != Some(Const::Int(0)) || m == *r || has(eg, m, "at") { continue; }
            let xs = eg.find(read.children[0]);
            println!("\n  witness: (maybe c{z} c{m}), and c{m} holds (index? c{xs} c{}). The read, the list, its length, the condition and the element:", eg.find(read.children[1]));
            show(m);
            show(xs);
            if let Some(l) = eg.lookup(SymbolLang::new("len", vec![xs])) { show(eg.find(l)); }
            for x in &eg[m].nodes { if x.op.as_str() == "if" { show(eg.find(x.children[0])); show(eg.find(x.children[1])); break; } }
            break;
        }
    }
    if let Ok(ids) = std::env::var("SHOW") { for i in ids.split(',') { show(eg.find(Id::from(i.parse::<usize>().unwrap()))); } }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let show_all = args.iter().any(|a| a == "--all");
    let exprs: Vec<String> = args.iter().filter(|a| !a.starts_with("--")).cloned().collect();
    if args.iter().any(|a| a == "--joint") { joint(&exprs); return; }
    if exprs.is_empty() {
        for e in [
            "widths.slice(i, i + 1).reduce((_, x) => x, 0)",
            "widths.slice(i, i + 1).reduce((acc, x) => x + (acc - acc), 0)",
            "(([x = 0]) => x)(widths.slice(i, i + 1))",
            "[0, ...xs][xs.length]",
            "widths.reduce((a, b) => a + b, 0)",
            "widths.reduce((a, b) => a + b, 0) + widths.length",
        ] { run(e, false); }
    } else {
        for e in exprs { run(&e, show_all); }
    }
}
