use crate::affine::Form;
use egg::{rewrite as rw, *};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
pub type Graph = EGraph<SymbolLang, Facts>;
type Rule = Rewrite<SymbolLang, Facts>;

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct Data {
    pub free: BTreeSet<Id>,
    pub lo: Option<i64>,
    pub hi: Option<i64>,
    pub boolean: Option<bool>,
    pub text: Option<Symbol>,
    pub string: bool,
    pub integer: bool,
    pub clash: bool,
    /// The value is never undefined.
    pub defined: bool,
    /// A list whose in-bounds elements are all defined. Input lists are, by the model.
    pub elements: bool,
    /// A function whose result for a walker's (element, index) is defined.
    pub returns: bool,
    /// A function with a resolved body, which a walker can actually apply.
    pub callable: bool,
    /// Every representation contains unsupported syntax or an unresolved call.
    pub opaque: bool,
}
#[derive(Default)]
pub struct Facts;
fn op(n: &SymbolLang) -> &str {
    n.op.as_str()
}
fn has(g: &Graph, id: Id, name: &str) -> bool {
    g[id].nodes.iter().any(|n| op(n) == name)
}
fn num(g: &Graph, id: Id) -> Option<i64> {
    let d = &g[id].data;
    if d.lo == d.hi { d.lo } else { None }
}
fn max_bound(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (a, b) => a.or(b),
    }
}
fn min_bound(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}
impl Analysis<SymbolLang> for Facts {
    type Data = Data;
    fn make(g: &mut Graph, n: &SymbolLang, _id: Id) -> Data {
        let mut d = Data::default();
        let k = &n.children;
        for &id in k {
            d.free.extend(&g[id].data.free);
        }
        let iv = |i: usize| (g[k[i]].data.lo, g[k[i]].data.hi);
        let bounds = match op(n) {
            "Var" => {
                d.free.insert(k[0]);
                (None, None)
            }
            "Lam" => {
                d.free.remove(&k[0]);
                (None, None)
            }
            "Let" => {
                d.free = g[k[2]].data.free.clone();
                d.free.remove(&k[0]);
                d.free.extend(&g[k[1]].data.free);
                (None, None)
            }
            "Num" => {
                let v = g[k[0]].nodes[0].op.as_str().parse::<i64>().ok();
                (v, v)
            }
            "B" => {
                d.boolean = Some(has(g, k[0], "true"));
                (None, None)
            }
            "Str" => {
                d.text = Some(g[k[0]].nodes[0].op);
                d.string = true;
                (None, None)
            }
            "Concat" => {
                d.string = true;
                if let (Some(a), Some(b)) = (g[k[0]].data.text, g[k[1]].data.text) {
                    d.text = Some(format!("{}{}", a, &b.as_str()["utf16:".len()..]).into());
                }
                (None, None)
            }
            "Len" => (Some(0), None),
            "Rel" => (Some(0), iv(1).1),
            "Add" => (
                iv(0).0.zip(iv(1).0).and_then(|(a, b)| a.checked_add(b)),
                iv(0).1.zip(iv(1).1).and_then(|(a, b)| a.checked_add(b)),
            ),
            "Sub" => (
                iv(0).0.zip(iv(1).1).and_then(|(a, b)| a.checked_sub(b)),
                iv(0).1.zip(iv(1).0).and_then(|(a, b)| a.checked_sub(b)),
            ),
            "Neg" => (
                iv(0).1.and_then(i64::checked_neg),
                iv(0).0.and_then(i64::checked_neg),
            ),
            "Mul" => {
                let v = num(g, k[0])
                    .zip(num(g, k[1]))
                    .and_then(|(a, b)| a.checked_mul(b));
                (v, v)
            }
            "Min" => (
                iv(0).0.zip(iv(1).0).map(|(a, b)| a.min(b)),
                min_bound(iv(0).1, iv(1).1),
            ),
            "Max" => (
                max_bound(iv(0).0, iv(1).0),
                iv(0).1.zip(iv(1).1).map(|(a, b)| a.max(b)),
            ),
            "If" => (
                iv(1).0.zip(iv(2).0).map(|(a, b)| a.min(b)),
                iv(1).1.zip(iv(2).1).map(|(a, b)| a.max(b)),
            ),
            "Lt" | "Le" => {
                let strict = op(n) == "Lt";
                if iv(0)
                    .1
                    .zip(iv(1).0)
                    .is_some_and(|(a, b)| if strict { a < b } else { a <= b })
                {
                    d.boolean = Some(true);
                }
                if iv(0)
                    .0
                    .zip(iv(1).1)
                    .is_some_and(|(a, b)| if strict { a >= b } else { a > b })
                {
                    d.boolean = Some(false);
                }
                (None, None)
            }
            "StrictEq" | "EqI" => {
                if let (Some(a), Some(b)) = (num(g, k[0]), num(g, k[1])) {
                    d.boolean = Some(a == b);
                }
                if op(n) == "StrictEq" {
                    if let (Some(a), Some(b)) = (g[k[0]].data.text, g[k[1]].data.text) {
                        d.boolean = Some(a == b);
                    }
                    // Strict equality never coerces strings to numbers or booleans. Handle both
                    // orientations without a swap cycle; undefined is strict-eq-defined-undef.
                    for (a, b) in [(k[0], k[1]), (k[1], k[0])] {
                        if g[a].data.string && (g[b].data.integer || g[b].data.boolean.is_some()) {
                            d.boolean = Some(false);
                        }
                    }
                }
                (None, None)
            }
            _ => {
                if let Some(f) = Form::decode(n) {
                    let mut lo = Some(f.constant);
                    let mut hi = lo;
                    for (id, c) in f.terms {
                        let a = &g[id].data;
                        let (l, h) = if c >= 0 { (a.lo, a.hi) } else { (a.hi, a.lo) };
                        lo = lo
                            .zip(l)
                            .and_then(|(a, b)| a.checked_add(b.checked_mul(c)?));
                        hi = hi
                            .zip(h)
                            .and_then(|(a, b)| a.checked_add(b.checked_mul(c)?));
                    }
                    (lo, hi)
                } else {
                    (None, None)
                }
            }
        };
        (d.lo, d.hi) = bounds;
        d.integer = d.lo.is_some()
            || d.hi.is_some()
            || matches!(op(n), "Add" | "Sub" | "Neg")
            || op(n).starts_with("Lin:");
        let c = |i: usize| &g[k[i]].data;
        d.defined = d.integer
            || d.string
            || d.boolean.is_some()
            || match op(n) {
                "Num" | "B" | "Str" | "Concat" | "Len" | "Mul" | "Min" | "Max" => true,
                "StrictEq" | "EqI" | "Lt" | "Le" | "Not" | "And" | "Or" | "Truthy" => true,
                "Every" | "Some" | "Lam" => true,
                "Nil" | "Cons" | "Append" | "Sublist" | "Reverse" | "Select" | "Filteri" => true,
                "Map" => true,
                // An in-bounds read is exactly as defined as the list's elements.
                "At" => c(0).elements,
                "If" => c(1).defined && c(2).defined,
                "Maybe" => c(0).defined || c(1).defined,
                _ => false,
            };
        d.elements = match op(n) {
            "Var" | "Nil" => true,
            "Cons" => c(0).defined && c(1).elements,
            "Append" => c(0).elements && c(1).elements,
            "If" => c(1).elements && c(2).elements,
            "Sublist" | "Reverse" | "Select" => c(0).elements,
            "Filteri" => c(2).elements,
            // map's elements are f's results: defined only when f provably returns a value.
            "Map" => c(0).returns,
            _ => false,
        };
        if op(n) == "Lam" {
            let body = k[1];
            d.returns = if has(g, body, "Lam") {
                g[body].data.returns
            } else {
                g[body].data.defined
            };
            d.callable = !g[body].data.opaque;
        }
        d.opaque = SYNTAX.contains(&op(n))
            || (HIGHER_ORDER.contains(&op(n)) && !c(0).callable)
            || k.iter().any(|&id| g[id].data.opaque);
        d
    }
    fn merge(&mut self, a: &mut Data, b: Data) -> DidMerge {
        let old = a.clone();
        a.free = a.free.intersection(&b.free).copied().collect();
        a.lo = max_bound(a.lo, b.lo);
        a.hi = min_bound(a.hi, b.hi);
        a.clash |= b.clash
            || a.boolean.zip(b.boolean).is_some_and(|(a, b)| a != b)
            || a.text.zip(b.text).is_some_and(|(a, b)| a != b)
            || a.lo.zip(a.hi).is_some_and(|(l, h)| l > h);
        a.boolean = a.boolean.or(b.boolean);
        a.text = a.text.or(b.text);
        a.string |= b.string;
        a.integer |= b.integer;
        a.clash |= a.string && (a.integer || a.boolean.is_some());
        // Proofs: one representation suffices. Opacity: every representation must be opaque.
        a.defined |= b.defined;
        a.elements |= b.elements;
        a.returns |= b.returns;
        a.callable |= b.callable;
        a.opaque &= b.opaque;
        DidMerge(*a != old, *a != b)
    }
    fn modify(g: &mut Graph, id: Id) {
        if g[id].data.clash {
            return;
        }
        if let Some(n) = num(g, id) {
            let a = g.add(SymbolLang::leaf(n.to_string()));
            let b = g.add(SymbolLang::new("Num", vec![a]));
            g.union(id, b);
        }
        if let Some(v) = g[id].data.boolean {
            let a = g.add(SymbolLang::leaf(if v { "true" } else { "false" }));
            let b = g.add(SymbolLang::new("B", vec![a]));
            g.union(id, b);
        }
        if let Some(text) = g[id].data.text {
            let a = g.add(SymbolLang::leaf(text));
            let b = g.add(SymbolLang::new("Str", vec![a]));
            g.union(id, b);
        }
    }
}
fn v(s: &str) -> Var {
    const NAMES: [&str; 14] = [
        "?a", "?b", "?v", "?e", "?body", "?xs", "?k", "?f", "?z", "?c", "?acc", "?idx", "?j", "?x",
    ];
    static VARS: OnceLock<[Var; 14]> = OnceLock::new();
    let vars = VARS.get_or_init(|| NAMES.map(|s| s.parse().unwrap()));
    NAMES
        .iter()
        .position(|&name| name == s)
        .map(|i| vars[i])
        .unwrap_or_else(|| s.parse().unwrap())
}
fn independent(a: &str, b: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let (a, b) = (v(a), v(b));
    move |g, _, s| !g[s[b]].data.free.contains(&s[a])
}
fn different(a: &str, b: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let (a, b) = (v(a), v(b));
    move |g, _, s| g.find(s[a]) != g.find(s[b])
}

fn live(c: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let c = v(c);
    move |g, _, s| g[s[c]].data.boolean.is_none()
}
fn unbranched(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| {
        !g[s[a]]
            .nodes
            .iter()
            .any(|n| op(n) == "If" && g[n.children[0]].data.boolean.is_none())
    }
}
fn undecided() -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    |g, id, _| g[id].data.boolean.is_none()
}
fn unknown_length(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| {
        g.lookup(SymbolLang::new("Len", vec![s[a]]))
            .is_none_or(|len| num(g, len).is_none())
    }
}
fn defined(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| g[s[a]].data.defined
}
fn integer(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| g[s[a]].data.integer
}
fn form(g: &Graph, id: Id) -> Form {
    let original = g.find(id);
    if let Some(n) = num(g, id) {
        return Form::constant(n);
    }
    for node in &g[id].nodes {
        if let Some(f) = Form::decode(node) {
            let mut out = Form::constant(f.constant);
            for (id, c) in f.terms {
                let a = Form {
                    constant: 0,
                    terms: [(g.find(id), c)].into(),
                };
                if let Some(f) = out.plus(&a, 1) {
                    out = f;
                } else {
                    return Form::atom(original);
                }
            }
            return out;
        }
    }
    Form::atom(g.find(id))
}
fn add_form(g: &mut Graph, f: Form) -> Id {
    if f.terms.is_empty() {
        let n = g.add(SymbolLang::leaf(f.constant.to_string()));
        return g.add(SymbolLang::new("Num", vec![n]));
    }
    if f.constant == 0 && f.terms.len() == 1 && f.terms.values().next() == Some(&1) {
        return *f.terms.keys().next().unwrap();
    }
    g.add(f.node())
}
#[derive(Clone)]
struct Normalize(&'static str);
impl Applier<SymbolLang, Facts> for Normalize {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let a = form(g, s[v("?a")]);
        let f = if self.0 == "Neg" {
            Form::default().plus(&a, -1)
        } else {
            a.plus(&form(g, s[v("?b")]), if self.0 == "Sub" { -1 } else { 1 })
        };
        let Some(f) = f else { return vec![] };
        let b = add_form(g, f);
        if g.union(id, b) { vec![id] } else { vec![] }
    }
}
#[derive(Clone)]
struct Width;
impl Applier<SymbolLang, Facts> for Width {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let Some(f) = form(g, s[v("?b")]).plus(&form(g, s[v("?a")]), -1) else {
            return vec![];
        };
        if !f.terms.is_empty() || f.constant < 0 {
            return vec![];
        }
        let mut d = g[id].data.clone();
        let hi = min_bound(d.hi, Some(f.constant));
        if hi == d.hi {
            return vec![];
        }
        d.hi = hi;
        g.set_analysis_data(id, d);
        vec![id]
    }
}

include!("rules.rs");

fn rules() -> &'static [Rule] {
    static RULES: OnceLock<Vec<Rule>> = OnceLock::new();
    RULES.get_or_init(make_rules)
}
// Walkers that apply their first child as a callback.
const HIGHER_ORDER: &[&str] = &["Map", "Filteri", "Foldl", "Every", "Some"];
const SYNTAX: &[&str] = &[
    "Prop",
    "Elem",
    "MCall0",
    "MCall1",
    "MCall2",
    "App",
    "Call2",
    "Truthy",
    "Coalesce",
    "Default",
    "ArrCons",
    "ArrSpread",
    "Unknown",
    "Let",
];
// Unsupported syntax and unresolved calls, including a walker over a function it cannot
// apply, cost enough that extraction prefers any resolved representation.
#[derive(Clone)]
struct Cost<'a>(&'a Graph);
impl CostFunction<SymbolLang> for Cost<'_> {
    type Cost = usize;
    fn cost<C>(&mut self, n: &SymbolLang, mut costs: C) -> usize
    where
        C: FnMut(Id) -> usize,
    {
        let unresolved = SYNTAX.contains(&op(n))
            || (HIGHER_ORDER.contains(&op(n)) && !self.0[n.children[0]].data.callable);
        let own = if unresolved { 10000 } else { 1 };
        n.children
            .iter()
            .fold(own, |a, &id| a.saturating_add(costs(id)))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Cheat,
    NoCheat,
    Undecided,
}
impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Cheat => "CHEAT",
            Self::NoCheat => "no cheat",
            Self::Undecided => "UNDECIDED",
        })
    }
}
pub struct Evaluation {
    pub verdict: Verdict,
    pub saturated: bool,
    pub consistent: bool,
    pub iterations: usize,
    pub nodes: usize,
    pub classes: usize,
    pub parse_time: Duration,
    pub total_time: Duration,
    pub stop: String,
    pub canonical: RecExpr<SymbolLang>,
    pub graph: Graph,
    pub root: Id,
}
/// Initialize shared rules, the native parser, and egg's calibrated clock at harness startup.
/// Evaluation itself always uses a fresh e-graph; no expression results are cached.
pub fn initialize() {
    static READY: OnceLock<()> = OnceLock::new();
    READY.get_or_init(|| {
        let _ = rules();
        let expression = crate::frontend::parse("0").expect("valid bootstrap expression");
        // egg uses quanta: the first run calibrates its clock. Pay that once at startup.
        let _ = Runner::<SymbolLang, Facts, ()>::default()
            .with_expr(&expression)
            .run(&[] as &[Rule]);
    });
}
/// Parse, lower, saturate, check consistency, and extract a verdict in-process.
pub fn evaluate(src: &str) -> Result<Evaluation, String> {
    evaluate_with_limits(src, 60, 10000, Duration::from_millis(50))
}
pub fn evaluate_with_limits(
    src: &str,
    iterations: usize,
    nodes: usize,
    time: Duration,
) -> Result<Evaluation, String> {
    let start = Instant::now();
    let expr = crate::frontend::parse(src)?;
    let parse_time = start.elapsed();
    let r = Runner::<SymbolLang, Facts, ()>::default()
        .with_iter_limit(iterations)
        .with_node_limit(nodes)
        .with_time_limit(time)
        .with_scheduler(SimpleScheduler)
        .with_expr(&expr)
        .run(rules());
    if std::env::var_os("TRACE").is_some() {
        for (i, it) in r.iterations.iter().enumerate() {
            eprintln!(
                "{i}: {} nodes, search {:.0} us, apply {:.0} us, rebuild {:.0} us {:?}",
                it.egraph_nodes,
                it.search_time * 1e6,
                it.apply_time * 1e6,
                it.rebuild_time * 1e6,
                it.applied
            );
        }
    }
    let root = r.egraph.find(r.roots[0]);
    let saturated = matches!(r.stop_reason, Some(StopReason::Saturated));
    let canonical = Extractor::new(&r.egraph, Cost(&r.egraph)).find_best(root).1;
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    let mut hit = false;
    while let Some(id) = stack.pop() {
        let id = r.egraph.find(id);
        if !seen.insert(id) {
            continue;
        }
        for n in &r.egraph[id].nodes {
            stack.extend(&n.children);
            if op(n) == "Maybe" {
                let (z, m) = (n.children[0], n.children[1]);
                // An undetermined read: not proven present (At), absent, or defined.
                if has(&r.egraph, m, "IndexQ")
                    && !r.egraph[m].data.defined
                    && !["Undef", "At", "Oob"].iter().any(|o| has(&r.egraph, m, o))
                    && !["Undef", "Oob", "Throw"]
                        .iter()
                        .any(|o| has(&r.egraph, z, o))
                {
                    hit = true;
                }
            }
        }
    }
    let consistent = r.egraph.classes().all(|c| {
        !c.data.clash
            && !(has(&r.egraph, c.id, "Nil") && has(&r.egraph, c.id, "Cons"))
            && !(has(&r.egraph, c.id, "Undef") && c.data.defined)
    });
    let opaque = r.egraph[root].data.opaque;
    let verdict = if !consistent || !saturated {
        Verdict::Undecided
    } else if hit {
        Verdict::Cheat
    } else if opaque {
        Verdict::Undecided
    } else {
        Verdict::NoCheat
    };
    Ok(Evaluation {
        verdict,
        saturated,
        consistent,
        iterations: r.iterations.len(),
        nodes: r.egraph.total_size(),
        classes: r.egraph.number_of_classes(),
        parse_time,
        total_time: start.elapsed(),
        stop: format!("{:?}", r.stop_reason.unwrap()),
        canonical,
        graph: r.egraph,
        root,
    })
}
#[derive(Clone)]
struct Substitute;
impl Applier<SymbolLang, Facts> for Substitute {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let (var, e, body) = (s[v("?v")], s[v("?e")], s[v("?body")]);
        if !g[body].data.free.contains(&var) {
            return if g.union(id, body) { vec![id] } else { vec![] };
        }
        let mut changed = false;
        for n in g[body].nodes.clone() {
            let k = &n.children;
            let result = match op(&n) {
                "Var" => {
                    if k[0] == var {
                        e
                    } else {
                        body
                    }
                }
                "Lam" => {
                    if k[0] == var {
                        body
                    } else {
                        if g[e].data.free.contains(&k[0]) {
                            continue;
                        }
                        let b = g.add(SymbolLang::new("Let", vec![var, e, k[1]]));
                        g.add(SymbolLang::new("Lam", vec![k[0], b]))
                    }
                }
                "Let" => {
                    if g[e].data.free.contains(&k[0]) {
                        continue;
                    }
                    let a = g.add(SymbolLang::new("Let", vec![var, e, k[1]]));
                    let b = if k[0] == var {
                        k[2]
                    } else {
                        g.add(SymbolLang::new("Let", vec![var, e, k[2]]))
                    };
                    g.add(SymbolLang::new("Let", vec![k[0], a, b]))
                }
                // An affine sum stays canonical: substitute its atoms, never nest a Lin in one.
                _ if let Some(f) = Form::decode(&n)
                    && let Some(f) = substitute_form(g, f, &[(var, e)]) =>
                {
                    add_form(g, f)
                }
                _ => {
                    let mut n = n.clone();
                    for c in &mut n.children {
                        if g[*c].data.free.contains(&var) {
                            if g[*c]
                                .nodes
                                .iter()
                                .any(|n| op(n) == "Var" && n.children[0] == var)
                            {
                                *c = e;
                            } else {
                                *c = g.add(SymbolLang::new("Let", vec![var, e, *c]));
                            }
                        }
                    }
                    g.add(n)
                }
            };
            changed |= g.union(id, result);
        }
        if changed { vec![id] } else { vec![] }
    }
}
#[derive(Clone)]
struct NormalizeAffine;
impl Applier<SymbolLang, Facts> for NormalizeAffine {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        _: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        if !g[id].nodes.iter().any(|n| op(n).starts_with("Lin:")) {
            return vec![];
        }
        let mut changed = false;
        for n in g[id].nodes.clone() {
            if let Some(f) = Form::decode(&n) {
                let mut out = Some(Form::constant(f.constant));
                for (child, c) in f.terms {
                    // Never expand a class through itself. Only one level of canonical affine children.
                    if g.find(child) == g.find(id) {
                        out = None;
                        break;
                    }
                    let a = form(g, child);
                    let scaled = Form::default().plus(&a, c);
                    out = out.zip(scaled).and_then(|(a, b)| a.plus(&b, 1));
                }
                if let Some(f) = out {
                    let b = add_form(g, f);
                    changed |= g.union(id, b);
                }
            }
        }
        if changed { vec![id] } else { vec![] }
    }
}
#[derive(Clone)]
struct SeedLength;
impl Applier<SymbolLang, Facts> for SeedLength {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        _: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let n = SymbolLang::new("Len", vec![id]);
        if g.lookup(n.clone()).is_some() {
            return vec![];
        }
        vec![g.add(n)]
    }
}
#[derive(Clone)]
struct SeedIndex;
impl Applier<SymbolLang, Facts> for SeedIndex {
    fn apply_one(
        &self,
        g: &mut Graph,
        _: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let (xs, k) = (s[v("?xs")], s[v("?k")]);
        if num(g, k).is_some() && (has(g, xs, "Cons") || has(g, xs, "Nil")) {
            return vec![]; // Presence is decided: at-cons walks the literal.
        }
        let n = SymbolLang::new("IndexQ", vec![xs, k]);
        if g.lookup(n.clone()).is_some() {
            return vec![];
        }
        vec![g.add(n)]
    }
}
// M1: a branch on whether xs[k] exists, answering f(xs[k]) when it does and a written z
// when it does not, is maybe z f (xs !? k). It is built as Maybe z (IndexQ (Map f xs) k),
// fromMaybe over the mapped read; f = id is plain fromMaybe z (xs !? k). The partial read
// is found by its expansion If c (At xs k) Undef among the parents of the branch condition.
// Report only a changed union, so a successful match does not prevent saturation.
#[derive(Clone)]
struct MaybeFromRead;
impl Applier<SymbolLang, Facts> for MaybeFromRead {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let id = g.find(id);
        let (c, t, z) = (g.find(s[v("?c")]), g.find(s[v("?t")]), g.find(s[v("?z")]));
        // A branch that is its own present value (If c X z = X) says nothing about the read.
        // One witness per class is enough; rebuilding more would only grow the graph.
        if t == id
            || g[c].data.boolean.is_some()
            || ["Undef", "Oob", "Throw"].iter().any(|o| has(g, z, o))
            || g[id].nodes.iter().any(|n| {
                op(n) == "Maybe" && g.find(n.children[0]) == z && has(g, n.children[1], "IndexQ")
            })
        {
            return vec![];
        }
        let Some(undef) = g.lookup(SymbolLang::leaf("Undef")) else {
            return vec![];
        };
        let mut changed = false;
        if !g[t].data.defined {
            return vec![]; // Maybe z m equals If c t z only when t is never undefined.
        }
        for (m, at, xs, k) in reads_tested_by(g, c) {
            let maybe = if t == at {
                SymbolLang::new("Maybe", vec![z, m])
            } else {
                let Some(f) = element_function(g, t, &[at, m], c, z) else {
                    continue;
                };
                let map = g.add(SymbolLang::new("Map", vec![f, xs]));
                let read = g.add(SymbolLang::new("IndexQ", vec![map, k]));
                // The mapped read is f(xs[k]) where xs[k] exists: state its expansion
                // directly rather than re-deriving it through Len, At, and substitution.
                let expansion = g.add(SymbolLang::new("If", vec![c, t, undef]));
                changed |= g.union(read, expansion);
                SymbolLang::new("Maybe", vec![z, read])
            };
            let maybe = g.add(maybe);
            changed |= g.union(id, maybe);
        }
        if changed { vec![id] } else { vec![] }
    }
}
// Partial reads whose presence test is c, found by their expansion If c (At xs k) Undef
// among the parents of c: (read class, At class, xs, k).
fn reads_tested_by(g: &Graph, c: Id) -> Vec<(Id, Id, Id, Id)> {
    let c = g.find(c);
    let Some(undef) = g.lookup(SymbolLang::leaf("Undef")) else {
        return vec![];
    };
    let mut reads = vec![];
    for parent in g[c].parents().map(|p| g.find(p)).collect::<BTreeSet<_>>() {
        for n in &g[parent].nodes {
            let k = &n.children;
            if op(n) == "If"
                && g.find(k[0]) == c
                && g.find(k[2]) == undef
                && let Some(at) = g[k[1]].nodes.iter().find(|n| op(n) == "At")
            {
                reads.push((parent, g.find(k[1]), at.children[0], at.children[1]));
            }
        }
    }
    reads
}
fn presence(c: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let c = v(c);
    move |g, _, s| !reads_tested_by(g, s[c]).is_empty()
}
// The f of maybe z f (xs !? k), abstracted from the defined present branch t. None unless
// t varies with the element and can collide with z: a constant t only observes absence
// (isNothing), and a non-empty list never collides with the empty one.
fn element_function(g: &mut Graph, t: Id, read: &[Id], present: Id, z: Id) -> Option<Id> {
    let d = &g[t].data;
    if d.boolean.is_some() || d.text.is_some() || num(g, t).is_some() {
        return None;
    }
    if has(g, t, "Cons") && has(g, z, "Nil") {
        return None;
    }
    let binder = g.add(SymbolLang::leaf("@elem"));
    if g[t].data.free.contains(&binder) {
        return None;
    }
    let x = g.add(SymbolLang::new("Var", vec![binder]));
    // The presence test is true wherever f runs; it is not a use of the element.
    let body = abstract_read(g, t, read, x, &mut HashMap::from([(present, None)]))?;
    Some(g.add(SymbolLang::new("Lam", vec![binder, body])))
}
// Rebuild one term of `id` with the read replaced by x, reusing every class that does not
// mention it. Binders are never crossed, so x cannot be captured, and a class with a known
// constant value never varies with the element. None means no term mentions the read.
fn abstract_read(
    g: &mut Graph,
    id: Id,
    read: &[Id],
    x: Id,
    seen: &mut HashMap<Id, Option<Id>>,
) -> Option<Id> {
    let id = g.find(id);
    if read.contains(&id) {
        return Some(x);
    }
    if let Some(&done) = seen.get(&id) {
        return done; // Finished, or still open on this path: a cycle mentions nothing new.
    }
    let d = &g[id].data;
    if d.boolean.is_some() || d.text.is_some() || num(g, id).is_some() {
        return None;
    }
    seen.insert(id, None);
    for mut n in g[id].nodes.clone() {
        if matches!(op(&n), "Lam" | "Let") {
            continue;
        }
        let mut hit = false;
        for c in &mut n.children {
            if let Some(r) = abstract_read(g, *c, read, x, seen) {
                *c = r;
                hit = true;
            }
        }
        if hit {
            let out = Some(g.add(n));
            seen.insert(id, out);
            return out;
        }
    }
    None
}
// Apply a callback as JavaScript does: bind one parameter per argument and drop surplus
// arguments. An opaque callee keeps curried App nodes.
fn call(g: &mut Graph, f: Id, args: &[Id]) -> Id {
    let mut body = f;
    let mut binds = vec![];
    for &a in args {
        let Some(lam) = g[body].nodes.iter().find(|n| op(n) == "Lam").cloned() else {
            break;
        };
        binds.push((lam.children[0], a));
        body = lam.children[1];
    }
    if binds.is_empty() {
        return args
            .iter()
            .fold(f, |f, &a| g.add(SymbolLang::new("App", vec![f, a])));
    }
    for (var, a) in binds.into_iter().rev() {
        body = g.add(SymbolLang::new("Let", vec![var, a, body]));
    }
    body
}
// xs[k] on a cons: the head at 0, the tail at k - 1 above it, nothing below. A known index
// takes its one branch; building the dead ones seeded reads at -1, -2, ... down the list.
#[derive(Clone)]
struct AtCons;
impl Applier<SymbolLang, Facts> for AtCons {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let (h, t, k) = (s[v("?h")], s[v("?t")], s[v("?k")]);
        let tail = |g: &mut Graph| {
            let k = form(g, k).plus(&Form::constant(1), -1)?;
            let k = add_form(g, k);
            Some(g.add(SymbolLang::new("At", vec![t, k])))
        };
        let out = match num(g, k) {
            Some(0) => h,
            Some(n) if n > 0 => match tail(g) {
                Some(read) => read,
                None => return vec![],
            },
            Some(_) => g.add(SymbolLang::leaf("Oob")),
            None => {
                let Some(read) = tail(g) else { return vec![] };
                let zero = add_form(g, Form::constant(0));
                let oob = g.add(SymbolLang::leaf("Oob"));
                let at_head = g.add(SymbolLang::new("EqI", vec![k, zero]));
                let head = g.add(SymbolLang::new("If", vec![at_head, h, oob]));
                let above = g.add(SymbolLang::new("Lt", vec![zero, k]));
                g.add(SymbolLang::new("If", vec![above, read, head]))
            }
        };
        if g.union(id, out) { vec![id] } else { vec![] }
    }
}
// A rule's callback application, Call2 f a b, reduced by the one arity-aware helper.
#[derive(Clone)]
struct Call2;
impl Applier<SymbolLang, Facts> for Call2 {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let out = call(g, s[v("?f")], &[s[v("?a")], s[v("?b")]]);
        if g.union(id, out) { vec![id] } else { vec![] }
    }
}
// every, some, and a filter's length over a list of at most one element: the callback
// on xs[0] when it exists, and the empty-list answer when it does not.
#[derive(Clone, Copy)]
enum Walk {
    Every,
    Some,
    Count,
}
impl Applier<SymbolLang, Facts> for Walk {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let xs = s[v("?xs")];
        let len_node = SymbolLang::new("Len", vec![xs]);
        let existed = g.lookup(len_node.clone());
        let len = g.add(len_node);
        if g[len].data.hi.is_none_or(|hi| hi > 1) {
            return if existed.is_none() { vec![len] } else { vec![] };
        }
        let zero = add_form(g, Form::constant(0));
        let read = g.add(SymbolLang::new("At", vec![xs, zero]));
        let value = call(g, s[v("?f")], &[read, s[v("?k")]]);
        let pass = g.add(SymbolLang::new("Truthy", vec![value]));
        let present = g.add(SymbolLang::new("Lt", vec![zero, len]));
        let constant = |g: &mut Graph, b: bool| {
            let leaf = g.add(SymbolLang::leaf(if b { "true" } else { "false" }));
            g.add(SymbolLang::new("B", vec![leaf]))
        };
        let (yes, absent) = match self {
            Walk::Every => (pass, constant(g, true)),
            Walk::Some => (pass, constant(g, false)),
            Walk::Count => {
                let one = add_form(g, Form::constant(1));
                (g.add(SymbolLang::new("If", vec![pass, one, zero])), zero)
            }
        };
        let out = g.add(SymbolLang::new("If", vec![present, yes, absent]));
        if g.union(id, out) { vec![id] } else { vec![] }
    }
}
fn known(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| num(g, s[a]).is_some()
}
#[derive(Clone)]
struct Compare(bool);
impl Applier<SymbolLang, Facts> for Compare {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let Some(mut f) = form(g, s[v("?b")]).plus(&form(g, s[v("?a")]), -1) else {
            return vec![];
        };
        if self.0 {
            let Some(n) = f.constant.checked_sub(1) else {
                return vec![];
            };
            f.constant = n;
        }
        let b = add_form(g, f);
        let zero = add_form(g, Form::constant(0));
        let out = g.add(SymbolLang::new("Le", vec![zero, b]));
        if g.union(id, out) { vec![id] } else { vec![] }
    }
}
fn not_identity(a: &str, b: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let (a, b) = (v(a), v(b));
    move |g, _, s| {
        !g[s[b]]
            .nodes
            .iter()
            .any(|n| op(n) == "Var" && n.children[0] == s[a])
    }
}
fn not_literal(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| !has(g, s[a], "Cons") && !has(g, s[a], "Nil")
}
fn not_cons(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| !has(g, s[a], "Cons")
}
fn expand_read(a: &str, b: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let (a, b) = (v(a), v(b));
    move |g, id, s| {
        // Already expanded, e.g. by M1's mapped read.
        if g[id]
            .nodes
            .iter()
            .any(|n| op(n) == "If" && has(g, n.children[2], "Undef"))
        {
            return false;
        }
        let (xs, k) = (s[a], s[b]);
        for n in &g[xs].nodes {
            match op(n) {
                "Select" => return false,
                "Filteri" if index_predicate(g, n.children[0]) => return false,
                "Append" if num(g, k) == Some(0) && has(g, n.children[1], "Cons") => return false,
                "Cons" => {
                    if let Some(len) = g.lookup(SymbolLang::new("Len", vec![n.children[1]]))
                        && g.find(len) == g.find(k)
                    {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }
}
fn not_index_predicate(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| !index_predicate(g, s[a])
}
fn index_predicate(g: &Graph, id: Id) -> bool {
    for a in &g[id].nodes {
        if op(a) != "Lam" {
            continue;
        }
        for b in &g[a.children[1]].nodes {
            if op(b) != "Lam" || a.children[0] == b.children[0] {
                continue;
            }
            for eq in &g[b.children[1]].nodes {
                if op(eq) != "StrictEq" {
                    continue;
                }
                for (i, j) in [(0, 1), (1, 0)] {
                    if g[eq.children[i]]
                        .nodes
                        .iter()
                        .any(|n| op(n) == "Var" && n.children[0] == b.children[0])
                        && !g[eq.children[j]].data.free.contains(&a.children[0])
                        && !g[eq.children[j]].data.free.contains(&b.children[0])
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
}
#[derive(Clone)]
struct ShortFold;
impl Applier<SymbolLang, Facts> for ShortFold {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let xs = s[v("?xs")];
        for a in &g[s[v("?f")]].nodes {
            if op(a) == "Lam" {
                for b in &g[a.children[1]].nodes {
                    if op(b) == "Lam"
                        && a.children[0] != b.children[0]
                        && g[b.children[1]]
                            .nodes
                            .iter()
                            .any(|n| op(n) == "Var" && n.children[0] == b.children[0])
                    {
                        return vec![];
                    }
                }
            }
        }
        let len_node = SymbolLang::new("Len", vec![xs]);
        let existed = g.lookup(len_node.clone());
        let len = g.add(len_node);
        if g[len].data.hi.is_none_or(|hi| hi > 1) {
            return if existed.is_none() { vec![len] } else { vec![] };
        }
        let zero = add_form(g, Form::constant(0));
        let read = g.add(SymbolLang::new("At", vec![xs, zero]));
        let mut binders = None;
        for a in &g[s[v("?f")]].nodes {
            if op(a) == "Lam" {
                for b in &g[a.children[1]].nodes {
                    if op(b) == "Lam"
                        && a.children[0] != b.children[0]
                        && !g[s[v("?z")]].data.free.contains(&b.children[0])
                    {
                        binders = Some((a.children[0], b.children[0], b.children[1]));
                        break;
                    }
                }
            }
        }
        let affine = binders.and_then(|(acc, element, body)| {
            substitute_affine(g, body, &[(acc, s[v("?z")]), (element, read)])
        });
        let value = match affine {
            Some(f) => add_form(g, f),
            None => call(g, s[v("?f")], &[s[v("?z")], read]),
        };
        let c = g.add(SymbolLang::new("Lt", vec![zero, len]));
        let out = g.add(SymbolLang::new("If", vec![c, value, s[v("?z")]]));
        if g.union(id, out) { vec![id] } else { vec![] }
    }
}
#[derive(Clone)]
struct ShortRead;
impl Applier<SymbolLang, Facts> for ShortRead {
    fn apply_one(
        &self,
        g: &mut Graph,
        id: Id,
        s: &Subst,
        _: Option<&PatternAst<SymbolLang>>,
        _: Symbol,
    ) -> Vec<Id> {
        let xs = s[v("?xs")];
        if num(g, s[v("?k")]).is_some() {
            return vec![];
        }
        let Some(len) = g.lookup(SymbolLang::new("Len", vec![xs])) else {
            return vec![];
        };
        if g[len].data.hi.is_none_or(|hi| hi > 1) {
            return vec![];
        }
        let Some(diff) = form(g, len).plus(&form(g, s[v("?k")]), -1) else {
            return vec![];
        };
        if diff.constant != 1 || !diff.terms.is_empty() {
            return vec![];
        }
        let zero = add_form(g, Form::constant(0));
        let out = g.add(SymbolLang::new("IndexQ", vec![xs, zero]));
        if g.union(id, out) { vec![id] } else { vec![] }
    }
}
/// Saturate several roots together for inspecting algebraic equivalence.
pub struct JointEvaluation {
    pub roots: Vec<Id>,
    pub canonical: Vec<RecExpr<SymbolLang>>,
    pub saturated: bool,
    pub nodes: usize,
    pub iterations: usize,
}
pub fn evaluate_joint(sources: &[&str]) -> Result<JointEvaluation, String> {
    let mut runner = Runner::<SymbolLang, Facts, ()>::default()
        .with_iter_limit(60)
        .with_node_limit(10000)
        .with_time_limit(Duration::from_millis(50))
        .with_scheduler(SimpleScheduler);
    for source in sources {
        runner = runner.with_expr(&crate::frontend::parse(source)?);
    }
    let r = runner.run(rules());
    let roots: Vec<_> = r.roots.iter().map(|&id| r.egraph.find(id)).collect();
    let extractor = Extractor::new(&r.egraph, Cost(&r.egraph));
    let canonical = roots.iter().map(|&id| extractor.find_best(id).1).collect();
    Ok(JointEvaluation {
        roots,
        canonical,
        saturated: matches!(r.stop_reason, Some(StopReason::Saturated)),
        nodes: r.egraph.total_size(),
        iterations: r.iterations.len(),
    })
}
// Append(xs, Nil) merges with xs. Opening that cyclic representative again creates
// redundant bounds/absence branches; the identity rules already cover it completely.
fn non_nil(a: &str) -> impl Fn(&mut Graph, Id, &Subst) -> bool {
    let a = v(a);
    move |g, _, s| !has(g, s[a], "Nil")
}

// Substitution into an already canonical affine body does not need intermediate Lets.
// Atoms containing a binder anywhere but a Var must use capture-checked substitution.
fn substitute_affine(g: &Graph, body: Id, bindings: &[(Id, Id)]) -> Option<Form> {
    substitute_form(g, form(g, body), bindings)
}
fn substitute_form(g: &Graph, f: Form, bindings: &[(Id, Id)]) -> Option<Form> {
    let mut result = Form::constant(f.constant);
    for (atom, coefficient) in f.terms {
        let mut replacement = Form::atom(atom);
        for &(var, value) in bindings {
            if g[atom]
                .nodes
                .iter()
                .any(|n| op(n) == "Var" && n.children[0] == var)
            {
                replacement = form(g, value);
                break;
            }
            if g[atom].data.free.contains(&var) {
                return None;
            }
        }
        result = result.plus(&replacement, coefficient)?;
    }
    Some(result)
}
