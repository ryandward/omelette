#![allow(dead_code)]
use omelette::core::Family;
use omelette::engine::{Evaluation, Verdict, evaluate};

/// Evaluate, and require saturation, consistency, a small graph, and the verdict.
pub fn checked(source: &str, verdict: Verdict) -> Evaluation {
    let r = evaluate(source).unwrap();
    assert!(r.saturated, "{source}: {}", r.stop);
    assert!(r.consistent, "{source}: inconsistent graph");
    assert!(r.nodes < 150, "{source}: {} nodes", r.nodes);
    assert_eq!(r.verdict, verdict, "{source}: {}", r.canonical);
    r
}

/// A cheat of exactly these families.
pub fn cheat(source: &str, families: &[Family]) -> Evaluation {
    let r = checked(source, Verdict::Cheat);
    assert_eq!(r.families, families, "{source}: {}", r.canonical);
    r
}

/// No cheat, and the canonical term.
pub fn value(source: &str, expected: &str) {
    let r = checked(source, Verdict::NoCheat);
    assert_eq!(r.canonical.to_string(), expected, "{source}");
}
