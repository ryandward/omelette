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
