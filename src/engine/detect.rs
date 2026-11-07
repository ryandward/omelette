//! Witness detection: which flows swallow a read that may be missing.
use super::analysis::{Const, Graph, in_range};
use crate::core::{Core, Family, Kind};
use egg::{Id, Language};
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Default)]
pub struct Findings {
    /// Families of the cheats found.
    pub families: BTreeSet<Family>,
    /// A witness whose replacement or family leaves the answer to unknown inputs.
    pub possible: bool,
    /// Unsupported syntax or an unresolved call reaches the result, or lowering evaluated one.
    pub opaque: bool,
}

pub fn scan(g: &Graph, root: Id) -> Findings {
    let known = known(g);
    let mut found = Findings::default();
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        let id = g.find(id);
        if !seen.insert(id) {
            continue;
        }
        for n in &g[id].nodes {
            stack.extend(n.children());
            visit(g, n, &mut found);
        }
        for group in witnesses(g, id).values() {
            judge(g, &known, group, &mut found);
        }
    }
    found
}

fn visit(g: &Graph, n: &Core, found: &mut Findings) {
    match n {
        Core::Escape(v) if undetermined(g, *v) => {
            found.families.insert(Family::Drift);
        }
        Core::Unsupported(_) | Core::Call(_) => found.opaque = true,
        Core::Map([f, _]) | Core::Filter([f, _]) | Core::Every([f, _]) | Core::Some([f, _]) | Core::Fold([f, _, _]) => {
            found.opaque |= !g[*f].nodes.iter().any(|n| matches!(n, Core::Lam(_)));
        }
        _ => {}
    }
}

/// One class's witnesses, grouped by read.
fn witnesses(g: &Graph, id: Id) -> HashMap<Id, Vec<[Id; 4]>> {
    let mut groups: HashMap<Id, Vec<[Id; 4]>> = HashMap::new();
    for n in &g[id].nodes {
        if let Core::Maybe(parts) = n {
            groups.entry(g.find(parts[3])).or_default().push(*parts);
        }
    }
    groups
}

/// Witnesses in one class over one read denote one value, so their replacements agree
/// where the read is missing and their present branches agree on every element: one
/// representative's proof that the branch ignores the element, that it is free of unknowns,
/// or that the replacement is certainly a value, holds for all of them.
fn judge(g: &Graph, known: &HashSet<Id>, group: &[[Id; 4]], found: &mut Findings) {
    let read = group[0][3];
    if !undetermined(g, read) {
        return;
    }
    let families: BTreeSet<Family> = group.iter().filter_map(|&[flow, ..]| family(g, flow)).collect();
    if families.contains(&Family::Undecided) {
        found.possible = true;
    }
    let swallowing: Vec<Family> = families.into_iter().filter(|f| f.swallows()).collect();
    if swallowing.is_empty() {
        return;
    }
    let observed = group.iter().any(|&[_, _, lam, _]| constant_body(g, lam));
    let visible = group.iter().any(|&[_, z, ..]| empty(g, z)) && group.iter().any(|&[_, _, lam, _]| nonempty_body(g, lam));
    if observed || visible {
        return;
    }
    // An unknown function or value may make the branch ignore the element (`p = () => false`)
    // or test its presence (`p = () => true`, or `n === x` with `x` undefined).
    let resolved = group.iter().any(|&[_, _, lam, _]| bodies(g, lam).any(|body| known.contains(&g.find(body))));
    if resolved && group.iter().any(|&[_, z, ..]| certain(g, z)) {
        found.families.extend(swallowing);
    } else {
        found.possible = true;
    }
}

/// Classes with a representative free of unknowns: unresolved calls, unsupported syntax, and
/// free variables that may be any value or any function.
fn known(g: &Graph) -> HashSet<Id> {
    let mut known = HashSet::new();
    loop {
        let before = known.len();
        for class in g.classes() {
            let free = |n: &Core| {
                !matches!(n, Core::Call(_) | Core::Unsupported(_))
                    && !matches!(n, Core::Var(v) if matches!(v.kind, Kind::Any | Kind::Fun))
                    && n.children().iter().all(|&c| known.contains(&g.find(c)))
            };
            if !known.contains(&class.id) && class.nodes.iter().any(free) {
                known.insert(class.id);
            }
        }
        if known.len() == before {
            return known;
        }
    }
}

fn family(g: &Graph, flow: Id) -> Option<Family> {
    g[flow].nodes.iter().find_map(|n| match n {
        Core::Flow(f) => Some(*f),
        _ => None,
    })
}

/// A read not proven in or out of range.
fn undetermined(g: &Graph, id: Id) -> bool {
    g[id].nodes.iter().any(|n| matches!(n, Core::Read(_))) && in_range(g, id).is_none()
}

/// The lambda's body, for each lambda in its class.
fn bodies(g: &Graph, lam: Id) -> impl Iterator<Item = Id> + '_ {
    g[lam].nodes.iter().filter_map(|n| match n {
        Core::Lam(children) => children.last().copied(),
        _ => None,
    })
}

/// The present branch does not depend on the element: the absence is observed.
fn constant_body(g: &Graph, lam: Id) -> bool {
    bodies(g, lam).any(|body| g[body].data.constant.is_some())
}

/// The present branch is a non-empty list, so it never yields the empty replacement.
fn nonempty_body(g: &Graph, lam: Id) -> bool {
    bodies(g, lam).any(|body| g[body].nodes.iter().any(|n| matches!(n, Core::Cons(_))))
}

fn empty(g: &Graph, z: Id) -> bool {
    g[z].nodes.iter().any(|n| matches!(n, Core::Nil))
}

/// A replacement that is certainly a value, never undefined: a defined constant, or a node
/// whose every value is defined. Anything not listed here may be undefined.
fn certain(g: &Graph, z: Id) -> bool {
    let class = &g[z];
    if let Some(c) = &class.data.constant {
        return *c != Const::Undef;
    }
    class.nodes.iter().any(|n| match n {
        Core::Var(v) => !matches!(v.kind, Kind::Any | Kind::Acc | Kind::Item),
        n => matches!(
            n,
            Core::NaN | Core::True | Core::False | Core::Nil | Core::Int(_) | Core::Str(_)
                | Core::Lin(_) | Core::Mul(_) | Core::Le(_) | Core::Lt(_) | Core::Not(_) | Core::And(_) | Core::Or(_) | Core::Eq(_)
                | Core::Concat(_) | Core::Text(_) | Core::Dyn(_) | Core::Cons(_) | Core::Append(_) | Core::Slice(_) | Core::Len(_)
                | Core::Map(_) | Core::Filter(_) | Core::Every(_) | Core::Some(_) | Core::Join(_) | Core::Flat(_)
        ),
    })
}
