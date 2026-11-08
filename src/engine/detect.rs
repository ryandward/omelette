//! Witness detection: which flows swallow a read that may be missing.
use super::analysis::{Const, Graph, decided};
use crate::affine::Form;
use crate::core::{Core, Family, Kind, Mutator, Shape};
use egg::{Id, Language, Symbol};
use std::cell::RefCell;
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

/// A witness `maybe(flow, z, lam, read, has)`.
type Witness = [Id; 5];

/// What the judgments share: the root, and the classes with a representative free of
/// unknowns, and of throws.
struct Context {
    root: Id,
    known: HashSet<Id>,
    throwless: HashSet<Id>,
}

/// Judge the classes the root's value depends on. A class with a known constant depends on
/// nothing, and neither does a conditional's dead arm, a witness's dead side, or a walker's
/// callback over an empty list, so detection does not descend into them. A witness or escape
/// counts only if the root has no representative that avoids its class.
pub fn scan(g: &Graph, root: Id) -> Findings {
    let unknown = |_: Id, n: &Core| {
        matches!(n, Core::Call(_) | Core::Unsupported(_)) || matches!(n, Core::Var(v) if matches!(v.kind, Kind::Any | Kind::Fun))
    };
    let ctx = Context {
        root: g.find(root),
        known: avoiding(g, unknown),
        throwless: avoiding(g, |_, n| matches!(n, Core::Throw)),
    };
    let mut found = Findings::default();
    let mut seen = HashSet::new();
    let mut stack = vec![ctx.root];
    while let Some(id) = stack.pop() {
        let id = g.find(id);
        if !seen.insert(id) || g[id].data.constant.is_some() {
            continue;
        }
        for n in &g[id].nodes {
            stack.extend(live(g, n));
            visit(g, &ctx, id, n, &mut found);
        }
        for group in witnesses(g, id).values() {
            if relevant(g, &ctx, id) {
                judge(g, &ctx, group, &mut found);
            }
        }
    }
    found
}

/// The children a node's value depends on.
fn live(g: &Graph, n: &Core) -> Vec<Id> {
    let empty = |xs: Id| g[xs].data.constant == Some(Const::Nil);
    match n {
        Core::If([c, yes, no]) => match decided(g, *c) {
            Some(b) => vec![if b { *yes } else { *no }],
            None => vec![*c, *yes, *no],
        },
        Core::Maybe([flow, z, lam, read, has]) => match decided(g, *has) {
            Some(true) => vec![*lam, *read],
            Some(false) => vec![*z],
            None => vec![*flow, *z, *lam, *read, *has],
        },
        Core::Elim([z, lam, read, has]) => match decided(g, *has) {
            Some(true) => vec![*lam, *read],
            Some(false) => vec![*z],
            None => vec![*z, *lam, *read, *has],
        },
        Core::Map([_, xs]) | Core::Filter([_, xs]) | Core::Every([_, xs]) | Core::Some([_, xs]) if empty(*xs) => vec![],
        Core::Fold([_, z, xs]) if empty(*xs) => vec![*z],
        n => n.children().to_vec(),
    }
}

fn visit(g: &Graph, ctx: &Context, id: Id, n: &Core, found: &mut Findings) {
    match n {
        // Lowering escapes only reads whose replacement is still undefined.
        Core::Escape([_, has]) if decided(g, *has).is_none() && relevant(g, ctx, id) => {
            found.families.insert(Family::Drift);
        }
        Core::Unsupported(_) | Core::Call(_) => found.opaque = true,
        Core::Map([f, _]) | Core::Filter([f, _]) | Core::Every([f, _]) | Core::Some([f, _]) | Core::Fold([f, _, _]) => {
            found.opaque |= !g[*f].nodes.iter().any(|n| matches!(n, Core::Lam(_)));
        }
        Core::Sort([f, _]) => found.opaque |= !g[*f].nodes.iter().any(|n| matches!(n, Core::Lam(_) | Core::Undef)),
        _ => {}
    }
}

/// Whether the root's value goes through class `id` in every representative.
fn relevant(g: &Graph, ctx: &Context, id: Id) -> bool {
    id == ctx.root || !avoiding(g, |class, _| class == id).contains(&ctx.root)
}

/// One class's witnesses, grouped by read and presence test.
fn witnesses(g: &Graph, id: Id) -> HashMap<(Id, Id), Vec<Witness>> {
    let mut groups: HashMap<(Id, Id), Vec<Witness>> = HashMap::new();
    for n in &g[id].nodes {
        if let Core::Maybe(parts) = n {
            groups.entry((g.find(parts[3]), g.find(parts[4]))).or_default().push(*parts);
        }
    }
    groups
}

/// Witnesses in one class over one read denote one value, so their replacements agree
/// where the read is missing and their present branches agree on every element: one
/// representative's proof that the branch ignores the element, that it is free of unknowns,
/// or that the replacement is certainly a value, holds for all of them.
fn judge(g: &Graph, ctx: &Context, group: &[Witness], found: &mut Findings) {
    if decided(g, group[0][4]).is_some() {
        return;
    }
    let families: BTreeSet<Family> = group.iter().filter_map(|&[flow, ..]| family(g, flow)).collect();
    if families.contains(&Family::Undecided) {
        found.possible = true;
    }
    if apart(g, group) {
        return;
    }
    // Passing the absence on as `undefined` is honest only where no present element yields
    // `undefined` too, which `apart` proves when it holds.
    if families.contains(&Family::Propagate) {
        found.possible = true;
    }
    let swallowing: Vec<Family> = families.into_iter().filter(|f| f.swallows()).collect();
    if swallowing.is_empty() {
        return;
    }
    match observation(g, group) {
        Some(true) => return,
        // The branch ignores this read's element but reads the same list another way, which
        // may be the same element.
        Some(false) => {
            found.possible = true;
            return;
        }
        None => {}
    }
    // An unknown function or value may make the branch ignore the element (`p = () => false`)
    // or test its presence (`p = () => true`, or `n === x` with `x` undefined).
    let resolved = group.iter().any(|&[_, _, lam, ..]| bodies(g, lam).any(|body| ctx.known.contains(&g.find(body))));
    // An element that may itself be undefined: a branch that varies only there conflates the
    // missing read with that element, not with an ordinary value, and detection cannot tell
    // the two apart.
    let ordinary = !group.iter().any(|&[_, _, lam, ..]| binds(g, lam, Kind::Item));
    // A replacement that may throw is a world where the read was not evaluated, or where it
    // throws: nothing is swallowed there.
    let certain = group.iter().any(|&[_, z, ..]| certain(g, z) && ctx.throwless.contains(&g.find(z)));
    if resolved && ordinary && certain {
        found.families.extend(swallowing);
    } else {
        found.possible = true;
    }
}

/// Classes with a representative that contains no node `bad` picks (given the node's class).
fn avoiding(g: &Graph, bad: impl Fn(Id, &Core) -> bool) -> HashSet<Id> {
    let mut free = HashSet::new();
    loop {
        let before = free.len();
        for class in g.classes() {
            let clean = |n: &Core| !bad(class.id, n) && n.children().iter().all(|&c| free.contains(&g.find(c)));
            if !free.contains(&class.id) && class.nodes.iter().any(clean) {
                free.insert(class.id);
            }
        }
        if free.len() == before {
            return free;
        }
    }
}

fn family(g: &Graph, flow: Id) -> Option<Family> {
    g[flow].nodes.iter().find_map(|n| match n {
        Core::Flow(f) => Some(*f),
        _ => None,
    })
}

/// The lambda's body, for each lambda in its class.
fn bodies(g: &Graph, lam: Id) -> impl Iterator<Item = Id> + '_ {
    g[lam].nodes.iter().filter_map(|n| match n {
        Core::Lam(children) => children.last().copied(),
        _ => None,
    })
}

/// Whether the lambda's binder is a variable of this kind.
fn binds(g: &Graph, lam: Id, kind: Kind) -> bool {
    g[lam].nodes.iter().any(|n| match n {
        Core::Lam(children) => children.first().is_some_and(|&b| g[b].nodes.iter().any(|n| matches!(n, Core::Var(v) if v.kind == kind))),
        _ => false,
    })
}

/// Whether the present branch observes the absence rather than replacing it: `Some(true)`
/// when a representative of its body mentions neither the element nor another read of a
/// list that shares one of the read's free lists, `Some(false)` when it avoids the element
/// only by such a read, and `None` when it depends on the element.
fn observation(g: &Graph, group: &[Witness]) -> Option<bool> {
    let mine: HashSet<Symbol> = group.iter().flat_map(|&[.., read, _]| read_lists(g, read)).collect();
    let mut loose = false;
    for &[_, _, lam, ..] in group {
        for n in &g[lam].nodes {
            let Core::Lam(children) = n else { continue };
            let (Some(&binder), Some(&body)) = (children.first(), children.last()) else { continue };
            let Some(var) = variable(g, binder) else { continue };
            let element = |n: &Core| matches!(n, Core::Var(v) if *v == var);
            let aliased = |n: &Core| match n {
                Core::Read([l, _]) | Core::At([l, _]) => !lists(g, *l).is_disjoint(&mine),
                _ => false,
            };
            let body = g.find(body);
            if avoiding(g, |_, n| element(n) || aliased(n)).contains(&body) {
                return Some(true);
            }
            loose |= avoiding(g, |_, n| element(n)).contains(&body);
        }
    }
    loose.then_some(false)
}

fn variable(g: &Graph, id: Id) -> Option<crate::core::Variable> {
    g[id].nodes.iter().find_map(|n| match n {
        Core::Var(v) => Some(*v),
        _ => None,
    })
}

/// The free lists a read's class reads from.
fn read_lists(g: &Graph, read: Id) -> HashSet<Symbol> {
    g[read]
        .nodes
        .iter()
        .filter_map(|n| match n {
            Core::Read([l, _]) => Some(lists(g, *l)),
            _ => None,
        })
        .flatten()
        .collect()
}

/// The free list variables a term mentions in any representative.
fn lists(g: &Graph, id: Id) -> HashSet<Symbol> {
    free(g, id, |v| v.kind == Kind::List)
}

/// The free variables `pick` accepts that a term mentions in any representative.
fn free(g: &Graph, id: Id, pick: impl Fn(&crate::core::Variable) -> bool) -> HashSet<Symbol> {
    let (mut out, mut seen, mut stack) = (HashSet::new(), HashSet::new(), vec![id]);
    while let Some(id) = stack.pop() {
        let id = g.find(id);
        if !seen.insert(id) {
            continue;
        }
        for n in &g[id].nodes {
            match n {
                Core::Var(v) => {
                    if pick(v) {
                        out.insert(v.name);
                    }
                }
                n => stack.extend(n.children()),
            }
        }
    }
    out
}

/// The replacement is a value the present branch never yields, so the missing read stays
/// visible in the result rather than erased into an ordinary one. Witnesses in a group denote
/// one value, so any replacement may face any branch.
fn apart(g: &Graph, group: &[Witness]) -> bool {
    let read = group.iter().flat_map(|&[.., read, has]| [read, has]).flat_map(|id| free(g, id, |_| true)).collect();
    let apart = Apart { g, read, known: RefCell::default(), fixed: RefCell::default() };
    group.iter().any(|&[_, z, ..]| group.iter().any(|&[_, _, lam, ..]| bodies(g, lam).any(|body| apart.distinct(z, body, true))))
}

/// Compares a replacement with a present branch, given the variables the read depends on.
/// Comparisons are remembered, so shared classes are compared once; one still under way when
/// it is reached again counts as not apart, which only makes the answer more cautious.
struct Apart<'g> {
    g: &'g Graph,
    read: HashSet<Symbol>,
    known: RefCell<HashMap<(Id, Id, bool), bool>>,
    fixed: RefCell<HashMap<Id, bool>>,
}

impl Apart<'_> {
    /// Whether `z` differs from every value `body` takes. Splitting either at a conditional
    /// compares each arm, whatever its test. A test that shares no variable with the read is
    /// fixed while the read varies, so where both split on it, each side is compared under
    /// it; there, a world where the whole replacement and the whole branch are one term never
    /// evaluates the read and erases nothing. A test on the read's variables may be its
    /// presence, which differs between the two sides, so it splits only one of them.
    fn distinct(&self, z: Id, body: Id, whole: bool) -> bool {
        let g = self.g;
        let (z, body) = (g.find(z), g.find(body));
        if z == body {
            return whole;
        }
        if let Some(&known) = self.known.borrow().get(&(z, body, whole)) {
            return known;
        }
        self.known.borrow_mut().insert((z, body, whole), false);
        let apart = self.compare(z, body, whole);
        self.known.borrow_mut().insert((z, body, whole), apart);
        apart
    }

    fn compare(&self, z: Id, body: Id, whole: bool) -> bool {
        let g = self.g;
        if self.direct(z, body) {
            return true;
        }
        if let Some(Const::Str(text)) = &g[z].data.constant
            && self.affixes(&text.units(), body, 6)
        {
            return true;
        }
        // Lists differ where their heads or their tails do.
        let cells = |id: Id| g[id].nodes.iter().filter_map(|n| if let Core::Cons(c) = n { Some(*c) } else { None });
        if cells(z).any(|[zh, zt]| cells(body).any(|[bh, bt]| self.distinct(zh, bh, false) || self.distinct(zt, bt, false))) {
            return true;
        }
        let arms = |id: Id| g[id].nodes.iter().filter_map(|n| if let Core::If([c, y, n]) = n { Some((g.find(*c), *y, *n)) } else { None });
        let joint = arms(z).any(|(c, zy, zn)| {
            self.fixed(c) && arms(body).any(|(d, by, bn)| d == c && self.distinct(zy, by, whole) && self.distinct(zn, bn, whole))
        });
        joint
            || arms(body).any(|(_, y, n)| self.distinct(z, y, false) && self.distinct(z, n, false))
            || arms(z).any(|(_, y, n)| self.distinct(y, body, false) && self.distinct(n, body, false))
    }

    /// Whether a test shares no variable with the read, so it stays fixed while the read varies.
    fn fixed(&self, test: Id) -> bool {
        if let Some(&fixed) = self.fixed.borrow().get(&test) {
            return fixed;
        }
        let fixed = free(self.g, test, |_| true).is_disjoint(&self.read);
        self.fixed.borrow_mut().insert(test, fixed);
        fixed
    }

    /// Whether the text `z` differs from every string `body` takes: `body` joins a constant
    /// prefix `z` does not start with, or a constant suffix it does not end with, or the rest
    /// of `z` differs from the rest of `body`.
    fn affixes(&self, z: &[u16], body: Id, depth: u8) -> bool {
        let text = |id: Id| match &self.g[id].data.constant {
            Some(Const::Str(units)) => Some(units.units()),
            _ => None,
        };
        let rest = |rest: &[u16], id: Id| depth > 0 && self.affixes(rest, id, depth - 1);
        self.g[body].nodes.iter().any(|node| {
            let Core::Concat([left, right]) = node else { return false };
            match (text(*left), text(*right)) {
                (Some(prefix), _) => z.strip_prefix(prefix.as_slice()).is_none_or(|tail| rest(tail, *right)),
                (_, Some(suffix)) => z.strip_suffix(suffix.as_slice()).is_none_or(|head| rest(head, *left)),
                _ => false,
            }
        }) || text(body).is_some_and(|whole| whole != z)
    }

    /// Whether `z` differs from every value `body` takes, by their facts alone: a type the
    /// body never has, another constant, a value outside the integers or the bounds the body
    /// keeps to, or a list whose length always differs from the body's.
    fn direct(&self, z: Id, body: Id) -> bool {
        let g = self.g;
        let (zd, bd) = (&g[z].data, &g[body].data);
        if !zd.shape.meets(bd.shape) {
            return true;
        }
        if zd.shape.within(Shape::LIST)
            && bd.shape.within(Shape::LIST)
            && let Some(gap) = length(g, body, 16).plus(&length(g, z, 16), -1)
        {
            // Every unknown length is at least zero, so a gap whose parts share a sign and
            // whose constant has it too is never zero.
            let longer = gap.constant > 0 && gap.terms.values().all(|&c| c >= 0);
            let shorter = gap.constant < 0 && gap.terms.values().all(|&c| c <= 0);
            if longer || shorter {
                return true;
            }
        }
        let Some(c) = &zd.constant else { return false };
        let outside = match c {
            Const::Int(v) => bd.lo.is_some_and(|l| *v < l) || bd.hi.is_some_and(|h| *v > h),
            // Only integers have bounds.
            _ => bd.lo.is_some() || bd.hi.is_some(),
        };
        outside || bd.constant.as_ref().is_some_and(|d| d != c)
    }
}

/// A list's length as a sum: one for each cell it spells out, and the length of each list
/// it does not, an unknown at least zero.
fn length(g: &Graph, id: Id, depth: u8) -> Form {
    let id = g.find(id);
    let Some(depth) = depth.checked_sub(1) else { return Form::atom(id) };
    for n in &g[id].nodes {
        let form = match n {
            Core::Nil => Some(Form::constant(0)),
            Core::Cons([_, tail]) => length(g, *tail, depth).plus(&Form::constant(1), 1),
            Core::Append([a, b]) => length(g, *a, depth).plus(&length(g, *b, depth), 1),
            _ => None,
        };
        if let Some(form) = form {
            return form;
        }
    }
    Form::atom(id)
}

/// A replacement that is certainly a value, never undefined.
fn certain(g: &Graph, z: Id) -> bool {
    !g[z].data.shape.meets(Shape::UNDEF)
}

/// The live mutations in an effect log: those of arrays someone outside the expression holds,
/// and whether any reaches an array of unknown holder.
#[derive(Default)]
pub struct Mutations {
    pub observable: BTreeSet<Mutator>,
    pub unknown: bool,
}

/// Walk the effect log as detection walks a value: decided conditionals and presence tests
/// prune what cannot happen. A conditional's test is known inside each arm, so a presence
/// test the enclosing branch decides prunes too.
pub fn mutations(g: &Graph, log: Id) -> Mutations {
    let mut found = Mutations::default();
    let mut seen = HashSet::new();
    let mut stack: Vec<(Id, Vec<(Id, bool)>)> = vec![(log, Vec::new())];
    while let Some((id, facts)) = stack.pop() {
        let id = g.find(id);
        if g[id].data.constant.is_some() || !seen.insert((id, facts.clone())) {
            continue;
        }
        let known = |c: Id| decided(g, c).or_else(|| facts.iter().find(|(k, _)| g.find(*k) == g.find(c)).map(|&(_, b)| b));
        for n in &g[id].nodes {
            match n {
                Core::Mutate([op, owner]) => {
                    let (external, unknown) = holders(g, *owner);
                    if external && let Some(m) = mutator(g, *op) {
                        found.observable.insert(m);
                    }
                    found.unknown |= unknown;
                }
                Core::If([c, yes, no]) => {
                    if let Some(b) = known(*c) {
                        stack.push((if b { *yes } else { *no }, facts.clone()));
                    } else {
                        let with = |b: bool| facts.iter().copied().chain(std::iter::once((*c, b))).collect::<Vec<_>>();
                        stack.push((*yes, with(true)));
                        stack.push((*no, with(false)));
                    }
                }
                Core::Maybe([_, z, lam, _, has]) | Core::Elim([z, lam, _, has]) => match known(*has) {
                    Some(true) => stack.push((*lam, facts.clone())),
                    Some(false) => stack.push((*z, facts.clone())),
                    None => {
                        let with = |b: bool| facts.iter().copied().chain(std::iter::once((*has, b))).collect::<Vec<_>>();
                        stack.push((*z, with(false)));
                        stack.push((*lam, with(true)));
                    }
                },
                n => stack.extend(live(g, n).into_iter().map(|c| (c, facts.clone()))),
            }
        }
    }
    found
}

/// Whether an owner term reaches someone outside, and whether it reaches an unknown holder.
fn holders(g: &Graph, owner: Id) -> (bool, bool) {
    let (mut external, mut unknown) = (false, false);
    let mut seen = HashSet::new();
    let mut stack = vec![owner];
    while let Some(id) = stack.pop() {
        let id = g.find(id);
        if !seen.insert(id) {
            continue;
        }
        let class = &g[id];
        external |= class.nodes.iter().any(|n| matches!(n, Core::External));
        unknown |= class.nodes.iter().any(|n| matches!(n, Core::Unowned));
        for n in &class.nodes {
            stack.extend(live(g, n));
        }
    }
    (external, unknown)
}

fn mutator(g: &Graph, op: Id) -> Option<Mutator> {
    g[op].nodes.iter().find_map(|n| match n {
        Core::Op(m) => Some(*m),
        _ => None,
    })
}
