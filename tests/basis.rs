use omelette::engine::{Verdict, evaluate, initialize};
#[test]
fn golden_basis_saturates_without_clashes() {
    initialize();
    for line in include_str!("cases.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        let (expected, source) = line.split_once('\t').unwrap();
        let r = evaluate(source).unwrap();
        assert!(r.consistent, "{source}: inconsistent graph");
        assert!(r.saturated, "{source}: {} ({} nodes)", r.stop, r.nodes);
        assert_eq!(r.verdict.to_string(), expected, "{source}: {}", r.canonical);
    }
}
#[test]
fn two_element_sum_stays_small() {
    let r = evaluate("widths.slice(i, i + 2).reduce((a, b) => a + b, 0)").unwrap();
    assert_eq!(r.verdict, Verdict::NoCheat);
    assert!(r.saturated && r.consistent);
    assert!(r.nodes < 150, "{} nodes", r.nodes);
}
#[test]
fn find_mirrors_and_length() {
    for src in [
        "widths.find((_, idx) => idx === i) ?? 0",
        "widths.find((_, idx) => i === idx) ?? 0",
    ] {
        let r = evaluate(src).unwrap();
        assert_eq!(r.verdict, Verdict::Cheat);
        assert!(r.saturated && r.consistent);
        assert!(
            r.graph[r.root]
                .nodes
                .iter()
                .any(|n| n.op.as_str() == "Maybe")
        );
    }
    let r = evaluate("widths.length ?? 0").unwrap();
    assert_eq!(r.verdict, Verdict::NoCheat);
    assert!(r.saturated && r.consistent);
}
#[test]
fn affine_lowering_is_canonical_before_egg() {
    let lower = |s| omelette::frontend::parse(s).unwrap().to_string();
    assert_eq!(lower("i + (j + 2) - i"), lower("2 + j"));
    assert_eq!(lower("2 * (i + 3) - i - 6"), lower("i"));
    assert_eq!(lower("i + 2 * j + 3"), lower("3 + j * 2 + i"));
    assert_eq!(lower("(acc - acc) + x"), lower("x"));
}
#[test]
fn substitution_preserves_free_variables_and_shadowing() {
    for (source, expected) in [
        ("((x) => (y) => x)(y)(0)", "(Var free:y)"),
        ("((x) => ((x) => x)(2))(1)", "(Num 2)"),
        ("((undefined) => undefined)(3)", "(Num 3)"),
        ("((x, y) => x - y)(i, i)", "(Num 0)"),
        ("((x, y) => x + y)(2, 2)", "(Num 4)"),
        (
            "((x) => { const y = x; return ((x) => y)(2); })(1)",
            "(Num 1)",
        ),
    ] {
        let r = evaluate(source).unwrap();
        assert!(r.saturated && r.consistent, "{source}");
        assert_eq!(r.canonical.to_string(), expected, "{source}");
    }
    // Predicates depending on the element or comparing the index to itself are not projections.
    for source in [
        "xs.find((x, i) => i === x) ?? 0",
        "xs.find((x, i) => i === i) ?? 0",
    ] {
        let r = evaluate(source).unwrap();
        assert!(
            !r.graph
                .classes()
                .any(|c| c.nodes.iter().any(|n| n.op.as_str() == "Select")),
            "{source}"
        );
    }
}
#[test]
fn malformed_unsupported_and_limits_fail_closed() {
    for src in ["widths[", "x; y", "x trailing"] {
        assert!(evaluate(src).is_err(), "{src}");
    }
    for src in ["xs?.foo(1)", "({x: 1})", "null ?? 0", "1.5"] {
        assert_eq!(evaluate(src).unwrap().verdict, Verdict::Undecided, "{src}");
    }
    let r = omelette::engine::evaluate_with_limits(
        "widths[i] ?? 0",
        1,
        100,
        std::time::Duration::from_secs(1),
    )
    .unwrap();
    assert!(!r.saturated);
    assert_eq!(r.verdict, Verdict::Undecided);
}
#[test]
fn joint_roots_prove_projection_and_affine_equivalence() {
    let r = omelette::engine::evaluate_joint(&[
        "widths.find((_, idx) => idx === i)",
        "widths[i]",
        "widths.length ?? 0",
        "widths.length",
        "widths[i] ?? 0",
        "i + 2 * j",
        "2 * j + i",
    ])
    .unwrap();
    assert!(r.saturated);
    assert_eq!(r.roots[0], r.roots[1]);
    assert_eq!(r.roots[2], r.roots[3]);
    assert_ne!(r.roots[1], r.roots[4]);
    assert_eq!(r.roots[5], r.roots[6]);
}
