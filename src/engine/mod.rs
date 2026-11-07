//! Equational saturation of lowered terms, and the verdict.
mod analysis;
mod detect;
mod rules;

pub use analysis::{Const, Data, Facts, Graph};
use crate::core::{Core, Family};
use egg::{CostFunction, Extractor, Id, Language, RecExpr, Runner, SimpleScheduler, StopReason};
use std::fmt;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Cheat,
    NoCheat,
    Undecided,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Cheat => "CHEAT",
            Self::NoCheat => "no cheat",
            Self::Undecided => "UNDECIDED",
        })
    }
}

pub struct Evaluation {
    pub verdict: Verdict,
    /// The flows by which a missing read is swallowed, when the verdict is CHEAT.
    pub families: Vec<Family>,
    pub saturated: bool,
    pub consistent: bool,
    pub iterations: usize,
    pub nodes: usize,
    pub classes: usize,
    /// Parsing, semantic analysis, and lowering.
    pub parse_time: Duration,
    pub total_time: Duration,
    pub stop: String,
    pub canonical: RecExpr<Core>,
    pub graph: Graph,
    pub root: Id,
}

/// Warm the shared rules, the parser, and egg's clock once at harness startup.
///
/// # Panics
/// Never: the bootstrap expression is valid.
pub fn initialize() {
    static READY: OnceLock<()> = OnceLock::new();
    READY.get_or_init(|| {
        let _ = rules::rules();
        let expr = crate::lower::lower("0").expect("a valid bootstrap expression");
        let _ = runner(Limits::default()).with_expr(&expr).run(&[]);
    });
}

/// Limits on saturation; they are cooperative, not a real-time deadline.
#[derive(Clone, Copy)]
pub struct Limits {
    pub iterations: usize,
    pub nodes: usize,
    pub time: Duration,
}

impl Default for Limits {
    fn default() -> Self {
        Self { iterations: 60, nodes: 10_000, time: Duration::from_millis(50) }
    }
}

fn runner(limits: Limits) -> Runner<Core, Facts, ()> {
    Runner::default()
        .with_iter_limit(limits.iterations)
        .with_node_limit(limits.nodes)
        .with_time_limit(limits.time)
        .with_scheduler(SimpleScheduler)
}

/// Lower, saturate, and judge one expression.
///
/// # Errors
/// A syntax error, or source that is not a single expression.
pub fn evaluate(source: &str) -> Result<Evaluation, String> {
    evaluate_with_limits(source, Limits::default())
}

/// [`evaluate`] with explicit limits.
///
/// # Errors
/// A syntax error, or source that is not a single expression.
pub fn evaluate_with_limits(source: &str, limits: Limits) -> Result<Evaluation, String> {
    let start = Instant::now();
    let expr = crate::lower::lower(source)?;
    let parse_time = start.elapsed();
    let run = runner(limits).with_expr(&expr).run(rules::rules());
    if std::env::var_os("TRACE").is_some() {
        trace(&run);
    }
    let root = run.egraph.find(run.roots[0]);
    let saturated = matches!(run.stop_reason, Some(StopReason::Saturated));
    let consistent = run.egraph.classes().all(|c| !c.data.clash);
    let found = detect::scan(&run.egraph, root);
    let verdict = judge(saturated && consistent, &found);
    let families = if verdict == Verdict::Cheat { found.families.into_iter().collect() } else { Vec::new() };
    let canonical = Extractor::new(&run.egraph, Cost).find_best(root).1;
    Ok(Evaluation {
        verdict,
        families,
        saturated,
        consistent,
        iterations: run.iterations.len(),
        nodes: run.egraph.total_size(),
        classes: run.egraph.number_of_classes(),
        parse_time,
        total_time: start.elapsed(),
        stop: run.stop_reason.as_ref().map_or_else(|| "none".into(), |r| format!("{r:?}")),
        canonical,
        graph: run.egraph,
        root,
    })
}

fn judge(sound: bool, found: &detect::Findings) -> Verdict {
    if !sound {
        Verdict::Undecided
    } else if !found.families.is_empty() {
        Verdict::Cheat
    } else if found.possible || found.opaque {
        Verdict::Undecided
    } else {
        Verdict::NoCheat
    }
}

fn trace(run: &Runner<Core, Facts, ()>) {
    for (i, it) in run.iterations.iter().enumerate() {
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

/// Several roots saturated in one graph, for proving equalities between spellings.
pub struct JointEvaluation {
    pub roots: Vec<Id>,
    pub canonical: Vec<RecExpr<Core>>,
    pub saturated: bool,
    /// An inconsistent graph proves any two roots equal, so its classes prove nothing.
    pub consistent: bool,
    pub nodes: usize,
    pub iterations: usize,
}

/// Saturate expressions that share their free variables in one graph. Each free variable
/// gets one precondition from its uses across all the expressions.
///
/// # Errors
/// A syntax error, or a source that is not a single expression.
pub fn evaluate_joint(sources: &[&str]) -> Result<JointEvaluation, String> {
    let mut runner = runner(Limits::default());
    for expr in crate::lower::lower_all(sources)? {
        runner = runner.with_expr(&expr);
    }
    let run = runner.run(rules::rules());
    let roots: Vec<_> = run.roots.iter().map(|&id| run.egraph.find(id)).collect();
    let extractor = Extractor::new(&run.egraph, Cost);
    Ok(JointEvaluation {
        canonical: roots.iter().map(|&id| extractor.find_best(id).1).collect(),
        roots,
        saturated: matches!(run.stop_reason, Some(StopReason::Saturated)),
        consistent: run.egraph.classes().all(|c| !c.data.clash),
        nodes: run.egraph.total_size(),
        iterations: run.iterations.len(),
    })
}

/// Smallest term, with unresolved constructs priced out when any alternative exists.
struct Cost;
impl CostFunction<Core> for Cost {
    type Cost = usize;
    fn cost<C: FnMut(Id) -> usize>(&mut self, n: &Core, mut costs: C) -> usize {
        let own = match n {
            Core::Unsupported(_) | Core::Call(_) => 10_000,
            // Show the tagged witness rather than its untagged value.
            Core::Elim(_) => 100,
            Core::Int(_) | Core::Str(_) | Core::True | Core::False | Core::Undef => 0,
            _ => 1,
        };
        n.children().iter().fold(own, |acc, &c| acc.saturating_add(costs(c)))
    }
}
