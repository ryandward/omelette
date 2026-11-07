//! Witness detection: which flows swallow a read that may be missing.
use super::analysis::{Const, Graph};
use crate::core::{Core, Family, Kind};
use egg::{Id, Language};
use std::collections::{BTreeSet, HashSet};

#[derive(Default)]
pub struct Findings {
    /// Families of the cheats found.
    pub families: BTreeSet<Family>,
    /// A witness whose replacement or family leaves the answer to unknown inputs.
    pub possible: bool,
    /// Unsupported syntax or an unresolved call reaches the result.
    pub opaque: bool,
}

pub fn scan(g: &Graph, root: Id) -> Findings {
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
    }
    found
}

fn visit(g: &Graph, n: &Core, found: &mut Findings) {
    match n {
        Core::Maybe([flow, z, lam, read]) => witness(g, *flow, *z, *lam, *read, found),
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

fn witness(g: &Graph, flow: Id, z: Id, lam: Id, read: Id, found: &mut Findings) {
    if !undetermined(g, read) {
        return;
    }
    let Some(family) = g[flow].nodes.iter().find_map(|n| match n {
        Core::Flow(f) => Some(*f),
        _ => None,
    }) else {
        return;
    };
    if family == Family::Undecided {
        found.possible = true;
    } else if family.swallows() && !constant_body(g, lam) {
        if certain(g, z) {
            found.families.insert(family);
        } else {
            found.possible = true;
        }
    }
}

/// A read not proven present or missing.
fn undetermined(g: &Graph, id: Id) -> bool {
    let class = &g[id];
    class.nodes.iter().any(|n| matches!(n, Core::Read(_)))
        && !class.nodes.iter().any(|n| matches!(n, Core::At(_) | Core::Undef))
}

/// The present branch does not depend on the element: the absence is observed.
fn constant_body(g: &Graph, lam: Id) -> bool {
    g[lam].nodes.iter().any(|n| match n {
        Core::Lam(children) => children.last().is_some_and(|&body| g[body].data.constant.is_some()),
        _ => false,
    })
}

/// A replacement that is certainly a value, never undefined.
fn certain(g: &Graph, z: Id) -> bool {
    let class = &g[z];
    if let Some(c) = &class.data.constant {
        return *c != Const::Undef;
    }
    class.nodes.iter().any(|n| match n {
        Core::Var(v) => !matches!(v.kind, Kind::Any | Kind::Acc),
        Core::Undef | Core::Throw | Core::Read(_) | Core::Maybe(_) | Core::If(_) | Core::Call(_) | Core::Unsupported(_) | Core::Fold(_) => false,
        _ => true,
    })
}
