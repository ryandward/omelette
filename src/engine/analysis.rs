//! The only facts egg tracks: known constants and integer bounds.
use crate::affine::Form;
use crate::core::{Core, Kind, Utf16};
use egg::{Analysis, DidMerge, EGraph, Id};

pub type Graph = EGraph<Core, Facts>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Const {
    Int(i64),
    Bool(bool),
    Str(Utf16),
    Undef,
    NaN,
    Nil,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Data {
    pub constant: Option<Const>,
    pub lo: Option<i64>,
    pub hi: Option<i64>,
    /// Two representations proven different: the graph is inconsistent.
    pub clash: bool,
}

#[derive(Default)]
pub struct Facts;

impl Analysis<Core> for Facts {
    type Data = Data;
    fn make(g: &mut Graph, n: &Core, _: Id) -> Data {
        let constant = constant(g, n);
        let (lo, hi) = match &constant {
            Some(Const::Int(v)) => (Some(*v), Some(*v)),
            _ => bounds(g, n),
        };
        Data { constant, lo, hi, clash: false }
    }
    fn merge(&mut self, a: &mut Data, b: Data) -> DidMerge {
        let old = a.clone();
        a.clash |= b.clash || a.constant.as_ref().zip(b.constant.as_ref()).is_some_and(|(x, y)| x != y);
        a.constant = a.constant.take().or(b.constant.clone());
        a.lo = max_opt(a.lo, b.lo);
        a.hi = min_opt(a.hi, b.hi);
        a.clash |= a.lo.zip(a.hi).is_some_and(|(l, h)| l > h);
        DidMerge(*a != old, *a != b)
    }
    fn modify(g: &mut Graph, id: Id) {
        if g[id].data.clash {
            return;
        }
        if let Some(c) = g[id].data.constant.clone() {
            let node = match c {
                Const::Int(v) => Core::Int(v),
                Const::Bool(true) => Core::True,
                Const::Bool(false) => Core::False,
                Const::Str(s) => Core::Str(s),
                Const::Undef => Core::Undef,
                Const::NaN => Core::NaN,
                Const::Nil => Core::Nil,
            };
            let c = g.add(node);
            g.union(id, c);
        }
    }
}

fn max_opt(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    a.max(b).or(a).or(b)
}
fn min_opt(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, y) => x.or(y),
    }
}

pub fn int(g: &Graph, id: Id) -> Option<i64> {
    match g[id].data.constant {
        Some(Const::Int(v)) => Some(v),
        _ => None,
    }
}
/// The in-range tests of a read: the `c` of each `If(c, At(..), Undef)` in its class.
pub fn range_tests(g: &Graph, read: Id) -> impl Iterator<Item = Id> + '_ {
    g[read].nodes.iter().filter_map(move |n| match n {
        Core::If([c, at, undef])
            if g[*at].nodes.iter().any(|n| matches!(n, Core::At(_))) && g[*undef].nodes.iter().any(|n| matches!(n, Core::Undef)) =>
        {
            Some(g.find(*c))
        }
        _ => None,
    })
}

/// Whether a read is proven in range (`true`) or out of range (`false`). A read whose
/// element is `undefined` is still present: only its range test decides.
pub fn in_range(g: &Graph, read: Id) -> Option<bool> {
    range_tests(g, read).find_map(|c| boolean(g, c))
}

fn boolean(g: &Graph, id: Id) -> Option<bool> {
    match g[id].data.constant {
        Some(Const::Bool(b)) => Some(b),
        _ => None,
    }
}

fn constant(g: &Graph, n: &Core) -> Option<Const> {
    match n {
        Core::Int(v) => Some(Const::Int(*v)),
        Core::True => Some(Const::Bool(true)),
        Core::False => Some(Const::Bool(false)),
        Core::Str(s) => Some(Const::Str(*s)),
        Core::Undef => Some(Const::Undef),
        Core::NaN => Some(Const::NaN),
        Core::Nil => Some(Const::Nil),
        Core::Lin(_) | Core::Mul(_) => form_of(g, n).and_then(|f| f.known()).map(Const::Int),
        Core::Le(_) | Core::Lt(_) | Core::Not(_) | Core::And(_) | Core::Or(_) | Core::Eq(_) => logic(g, n).map(Const::Bool),
        Core::If([test, yes, no]) => {
            boolean(g, *test).and_then(|t| g[if t { *yes } else { *no }].data.constant.clone())
        }
        Core::Concat([left, right]) => {
            text(g, *left).zip(text(g, *right)).map(|(l, r)| Const::Str(l.concat(r)))
        }
        Core::Text(item) => join_text(g, *item).map(Const::Str),
        _ => None,
    }
}

fn logic(g: &Graph, n: &Core) -> Option<bool> {
    match n {
        Core::Le([a, b]) => order(g, *a, *b, false),
        Core::Lt([a, b]) => order(g, *a, *b, true),
        Core::Not(a) => boolean(g, *a).map(|b| !b),
        Core::And([a, b]) => match (boolean(g, *a), boolean(g, *b)) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        Core::Or([a, b]) => match (boolean(g, *a), boolean(g, *b)) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        Core::Eq([a, b]) => Some(strict_eq(g[*a].data.constant.as_ref()?, g[*b].data.constant.as_ref()?)),
        _ => None,
    }
}

/// `a < b` or `a <= b` decided by bounds.
fn order(g: &Graph, a: Id, b: Id, strict: bool) -> Option<bool> {
    let (a, b) = (&g[a].data, &g[b].data);
    let holds = |hi: i64, lo: i64| if strict { hi < lo } else { hi <= lo };
    if a.hi.zip(b.lo).is_some_and(|(h, l)| holds(h, l)) {
        return Some(true);
    }
    let fails = |lo: i64, hi: i64| if strict { lo >= hi } else { lo > hi };
    a.lo.zip(b.hi).is_some_and(|(l, h)| fails(l, h)).then_some(false)
}

fn strict_eq(a: &Const, b: &Const) -> bool {
    !matches!((a, b), (Const::NaN, _) | (_, Const::NaN)) && a == b
}

fn text(g: &Graph, id: Id) -> Option<Utf16> {
    match &g[id].data.constant {
        Some(Const::Str(s)) => Some(*s),
        _ => None,
    }
}

/// The text join writes for a known element: nothing for undefined.
fn join_text(g: &Graph, id: Id) -> Option<Utf16> {
    let s = match g[id].data.constant.as_ref()? {
        Const::Str(s) => return Some(*s),
        Const::Int(v) => v.to_string(),
        Const::Bool(b) => b.to_string(),
        Const::Undef => String::new(),
        Const::NaN => "NaN".into(),
        Const::Nil => return None,
    };
    Some(Utf16::new(s.encode_utf16()))
}

fn bounds(g: &Graph, n: &Core) -> (Option<i64>, Option<i64>) {
    match n {
        Core::Len(list) => (Some(0), width(g, *list)),
        Core::Var(v) if v.kind == Kind::Index => (Some(0), None),
        Core::Lin(_) => form_of(g, n).map_or((None, None), |f| interval(g, &f)),
        Core::If([_, a, b]) => {
            let (a, b) = (&g[*a].data, &g[*b].data);
            (a.lo.zip(b.lo).map(|(x, y)| x.min(y)), a.hi.zip(b.hi).map(|(x, y)| x.max(y)))
        }
        _ => (None, None),
    }
}

/// The most elements a slice can hold. Bounds that differ by `d >= 0` keep at most `d`
/// elements whatever their signs; a negative difference, as in `slice(1, -1)`, bounds nothing.
fn width(g: &Graph, list: Id) -> Option<i64> {
    g[list].nodes.iter().find_map(|n| match n {
        Core::Slice([_, a, b]) => class_form(g, *b).plus(&class_form(g, *a), -1)?.known().filter(|&w| w >= 0),
        _ => None,
    })
}

fn interval(g: &Graph, form: &Form) -> (Option<i64>, Option<i64>) {
    let step = |total: Option<i64>, bound: Option<i64>, coefficient: i64| {
        total.zip(bound).and_then(|(sum, b)| sum.checked_add(b.checked_mul(coefficient)?))
    };
    let mut low = Some(form.constant);
    let mut high = Some(form.constant);
    for (&atom, &coefficient) in &form.terms {
        let data = &g[atom].data;
        let (down, up) = if coefficient >= 0 { (data.lo, data.hi) } else { (data.hi, data.lo) };
        low = step(low, down, coefficient);
        high = step(high, up, coefficient);
    }
    (low, high)
}

/// The affine form of a Lin or Mul node, with atoms canonical.
pub fn form_of(g: &Graph, n: &Core) -> Option<Form> {
    node_form(g, n, 4)
}

fn node_form(g: &Graph, n: &Core, depth: usize) -> Option<Form> {
    match n {
        Core::Lin(children) => {
            let mut form = Form::constant(int(g, children[0])?);
            for pair in children[1..].chunks(2) {
                let atom = nested_form(g, pair[1], depth).scale(int(g, pair[0])?)?;
                form = form.plus(&atom, 1)?;
            }
            Some(form)
        }
        Core::Mul([a, b]) => Some(Form::constant(int(g, *a)?.checked_mul(int(g, *b)?)?)),
        _ => None,
    }
}

/// The affine form of a class: its constant, the sum it holds, or the class as an atom.
pub fn class_form(g: &Graph, id: Id) -> Form {
    nested_form(g, id, 4)
}

fn nested_form(g: &Graph, id: Id, depth: usize) -> Form {
    let id = g.find(id);
    if let Some(v) = int(g, id) {
        return Form::constant(v);
    }
    let sum = depth.checked_sub(1).and_then(|d| {
        g[id].nodes.iter().find_map(|n| matches!(n, Core::Lin(_)).then(|| node_form(g, n, d)).flatten())
    });
    sum.unwrap_or_else(|| Form::atom(id))
}
