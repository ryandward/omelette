//! Equational laws over the core IR. No rule simulates JavaScript.
use super::analysis::{Const, Facts, Graph, class_form, form_of, int};
use crate::affine::Form;
use crate::core::Core;
use egg::{Applier, Id, PatternAst, Rewrite, Subst, Symbol, Var, rewrite as rw};
use std::sync::OnceLock;

pub type Rule = Rewrite<Core, Facts>;

pub fn rules() -> &'static [Rule] {
    static RULES: OnceLock<Vec<Rule>> = OnceLock::new();
    RULES.get_or_init(|| [logic(), lists(), witnesses()].into_iter().flatten().collect())
}

fn var(name: &str) -> Var {
    name.parse().expect("a pattern variable")
}

/// Boolean identities, conditionals, and integer normal forms.
fn logic() -> Vec<Rule> {
    vec![
        rw!("and-true"; "(and true ?a)" => "?a"),
        rw!("and-true-2"; "(and ?a true)" => "?a"),
        rw!("and-false"; "(and false ?a)" => "false"),
        rw!("and-false-2"; "(and ?a false)" => "false"),
        rw!("or-false"; "(or false ?a)" => "?a"),
        rw!("or-false-2"; "(or ?a false)" => "?a"),
        rw!("or-true"; "(or true ?a)" => "true"),
        rw!("or-true-2"; "(or ?a true)" => "true"),
        rw!("not-not"; "(not (not ?a))" => "?a"),
        rw!("if-true"; "(if true ?a ?b)" => "?a"),
        rw!("if-false"; "(if false ?a ?b)" => "?b"),
        rw!("if-same"; "(if ?c ?a ?a)" => "?a"),
        rw!("lt"; "(lt ?a ?b)" => { Order(true) }),
        rw!("le"; "(le ?a ?b)" => { Order(false) }),
        rw!("lin"; "?x" => Canonical),
    ]
}

/// Lengths of list shapes, reads of literal lists, and walkers over the empty list.
fn lists() -> Vec<Rule> {
    vec![
        rw!("append-nil"; "(append nil ?b)" => "?b"),
        rw!("append-nil-2"; "(append ?a nil)" => "?a"),
        rw!("append-cons"; "(append (cons ?h ?t) ?b)" => "(cons ?h (append ?t ?b))"),
        rw!("len-nil"; "(len nil)" => "0"),
        rw!("len-cons"; "(len (cons ?h ?t))" => { Sum(&["1", "?t"]) }),
        rw!("len-append"; "(len (append ?a ?b))" => { Sum(&["?a", "?b"]) }),
        rw!("len-map"; "(len (map ?f ?xs))" => "(len ?xs)"),
        rw!("read"; "(read ?xs ?k)" => "(if (has ?xs ?k) (at ?xs ?k) undefined)"),
        rw!("has"; "(has ?xs ?k)" => Range),
        rw!("at-head"; "(at (cons ?h ?t) 0)" => "?h"),
        rw!("map-nil"; "(map ?f nil)" => "nil"),
        rw!("filter-nil"; "(filter ?f nil)" => "nil"),
        rw!("filter-false"; "(filter (lam ?x ?i false) ?xs)" => "nil"),
        rw!("every-nil"; "(every ?f nil)" => "true"),
        rw!("some-nil"; "(some ?f nil)" => "false"),
        rw!("fold-nil"; "(fold ?f ?z nil)" => "?z"),
        rw!("join-nil"; "(join ?s nil)" => "utf16:"),
        rw!("flat-nil"; "(flat nil)" => "nil"),
    ]
}

/// List identities that reveal a witness: `[...a, z][0]` and `[z, ...xs][xs.length]`.
fn witnesses() -> Vec<Rule> {
    vec![
        rw!("append-default"; "(read (append ?a (cons ?z ?t)) 0)" => "(maybe default ?z (lam elem:@0 elem:@0) (read ?a 0) (has ?a 0))"),
        rw!("prefix-last"; "(read (cons ?z ?xs) (len ?xs))" => Last),
        rw!("maybe-absent"; "(maybe ?fam ?z ?f ?r ?h)" => "?z" if decided("?h", false)),
        rw!("maybe-present"; "(maybe ?fam ?z (lam ?e ?b) ?r ?h)" => "?b" if decided("?h", true) if constant("?b")),
        rw!("maybe-read"; "(maybe ?fam ?z (lam ?e ?e) ?r ?h)" => "?r" if decided("?h", true)),
        rw!("maybe-value"; "(maybe ?fam ?z ?f ?r ?h)" => "(elim ?z ?f ?r ?h)"),
        rw!("presence-absent"; "(maybe ?fam (if ?h ?a ?b) ?f ?r ?h)" => "(maybe ?fam ?b ?f ?r ?h)"),
        rw!("presence-present"; "(maybe ?fam ?z (lam ?e (if ?h ?a ?b)) ?r ?h)" => "(maybe ?fam ?z (lam ?e ?a) ?r ?h)"),
    ]
}

/// The canonical term of a form, atoms in class order.
pub fn add_form(g: &mut Graph, form: &Form) -> Id {
    if let Some(v) = form.known() {
        return g.add(Core::Int(v));
    }
    if let Some(atom) = form.single() {
        return atom;
    }
    let mut children = vec![g.add(Core::Int(form.constant))];
    let mut terms: Vec<_> = form.terms.iter().map(|(&a, &c)| (g.find(a), c)).collect();
    terms.sort_unstable();
    for (atom, c) in terms {
        children.push(g.add(Core::Int(c)));
        children.push(atom);
    }
    g.add(Core::Lin(children.into()))
}

fn unite(g: &mut Graph, id: Id, other: Id) -> Vec<Id> {
    if g.union(id, other) { vec![id] } else { vec![] }
}

/// `a < b` and `a <= b` as `0 <= b - a - 1` and `0 <= b - a`.
#[derive(Clone)]
struct Order(bool);
impl Applier<Core, Facts> for Order {
    fn apply_one(&self, g: &mut Graph, id: Id, s: &Subst, _: Option<&PatternAst<Core>>, _: Symbol) -> Vec<Id> {
        let (a, b) = (s[var("?a")], s[var("?b")]);
        if !self.0 && int(g, a) == Some(0) {
            return vec![];
        }
        let Some(gap) = class_form(g, b).plus(&class_form(g, a), -1).and_then(|f| f.plus(&Form::constant(i64::from(self.0)), -1)) else {
            return vec![];
        };
        let zero = g.add(Core::Int(0));
        let sum = add_form(g, &gap);
        let le = g.add(Core::Le([zero, sum]));
        unite(g, id, le)
    }
}

/// Every sum in canonical order, so equal sums share a class.
#[derive(Clone)]
struct Canonical;
impl Applier<Core, Facts> for Canonical {
    fn apply_one(&self, g: &mut Graph, id: Id, _: &Subst, _: Option<&PatternAst<Core>>, _: Symbol) -> Vec<Id> {
        let forms: Vec<Form> = g[id].nodes.iter().filter(|n| matches!(n, Core::Lin(_))).filter_map(|n| form_of(g, n)).collect();
        let mut changed = vec![];
        for form in forms {
            let canonical = add_form(g, &form);
            changed.extend(unite(g, id, canonical));
        }
        changed
    }
}

/// The length of a list shape as a sum of its parts' lengths (or constants).
#[derive(Clone)]
struct Sum(&'static [&'static str]);
impl Applier<Core, Facts> for Sum {
    fn apply_one(&self, g: &mut Graph, id: Id, s: &Subst, _: Option<&PatternAst<Core>>, _: Symbol) -> Vec<Id> {
        let mut total = Form::default();
        for part in self.0 {
            let piece = if let Ok(n) = part.parse::<i64>() {
                Form::constant(n)
            } else {
                let len = g.add(Core::Len(s[var(part)]));
                class_form(g, len)
            };
            let Some(sum) = total.plus(&piece, 1) else { return vec![] };
            total = sum;
        }
        let sum = add_form(g, &total);
        unite(g, id, sum)
    }
}

/// `has(xs, k)` is `0 <= k and 0 <= len(xs) - k - 1`.
#[derive(Clone)]
struct Range;
impl Applier<Core, Facts> for Range {
    fn apply_one(&self, g: &mut Graph, id: Id, s: &Subst, _: Option<&PatternAst<Core>>, _: Symbol) -> Vec<Id> {
        let (xs, k) = (s[var("?xs")], s[var("?k")]);
        let index = class_form(g, k);
        let len = g.add(Core::Len(xs));
        let Some(room) = class_form(g, len).plus(&index, -1).and_then(|f| f.plus(&Form::constant(1), -1)) else {
            return vec![];
        };
        let zero = g.add(Core::Int(0));
        let (k_form, room) = (add_form(g, &index), add_form(g, &room));
        let low = g.add(Core::Le([zero, k_form]));
        let high = g.add(Core::Le([zero, room]));
        let test = g.add(Core::And([low, high]));
        unite(g, id, test)
    }
}

/// `[z, ...xs][xs.length]` is the last element of `xs`, or `z` when `xs` is empty.
#[derive(Clone)]
struct Last;
impl Applier<Core, Facts> for Last {
    fn apply_one(&self, g: &mut Graph, id: Id, s: &Subst, _: Option<&PatternAst<Core>>, _: Symbol) -> Vec<Id> {
        let (z, xs) = (s[var("?z")], s[var("?xs")]);
        let len = g.add(Core::Len(xs));
        let Some(last) = class_form(g, len).plus(&Form::constant(1), -1) else { return vec![] };
        let last = add_form(g, &last);
        let read = g.add(Core::Read([xs, last]));
        let has = g.add(Core::Has([xs, last]));
        let identity = identity(g);
        let flow = g.add(Core::Flow(crate::core::Family::Default));
        let maybe = g.add(Core::Maybe([flow, z, identity, read, has]));
        unite(g, id, maybe)
    }
}

fn identity(g: &mut Graph) -> Id {
    let elem = g.add(Core::Var("elem:@0".parse().expect("a variable")));
    g.add(Core::Lam(vec![elem, elem].into()))
}

/// The presence test `h` is the constant `value`.
fn decided(h: &str, value: bool) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let h = var(h);
    move |g, _, s| g[s[h]].data.constant == Some(Const::Bool(value))
}

/// The class `b` has a known constant.
fn constant(b: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let b = var(b);
    move |g, _, s| g[s[b]].data.constant.is_some()
}
