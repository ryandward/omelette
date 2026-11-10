mod common;
use omelette::engine::{Limits, Verdict, evaluate, evaluate_joint, evaluate_with_limits, initialize};
use std::time::Duration;

#[test]
fn golden_cases_saturate_with_their_verdicts() {
    initialize();
    let cases = include_str!("cases.txt").lines().filter(|l| !l.starts_with('#') && !l.is_empty());
    for line in cases {
        let (expected, source) = line.split_once('\t').unwrap();
        let r = evaluate(source).unwrap();
        assert!(r.consistent && r.saturated, "{source}: {}", r.stop);
        assert!(r.nodes < 150, "{source}: {} nodes", r.nodes);
        assert_eq!(r.verdict.to_string(), expected, "{source}: {}", r.canonical);
    }
}

#[test]
fn malformed_input_is_an_error_and_limits_are_undecided() {
    for source in ["widths[", "x; y", "x trailing"] {
        assert!(evaluate(source).is_err(), "{source}");
    }
    // A declaration must give a type the model holds, to a variable that is not a global it
    // models, and only declarations may precede the expression.
    for source in [
        "declare const xs: null[]; xs[i]",
        "declare const n: bigint; n",
        "declare const String: string; 1",
        "declare const xs; xs",
        "declare const xs: string[]; let y = 1; y",
        "declare const xs: string[]; declare const xs: number[]; xs",
        "let y = 1; y",
        "const [a] = xs; a",
        "const f = (x) => x; f(1); 2",
    ] {
        assert!(evaluate(source).is_err(), "{source}");
    }
    for source in ["xs?.foo(1)", "({ ...o }).x", "null ?? 0", "1.5", "xs.foo(1)"] {
        assert_eq!(evaluate(source).unwrap().verdict, Verdict::Undecided, "{source}");
    }
    let tight = Limits { iterations: 1, nodes: 100, time: Duration::from_secs(1) };
    let r = evaluate_with_limits("xs.length ? xs[xs.length - 1] : 0", tight).unwrap();
    assert!(!r.saturated);
    assert_eq!(r.verdict, Verdict::Undecided);
}

#[test]
fn spellings_of_one_witness_share_a_class() {
    let groups: [&[&str]; 3] = [
        &["names[i] === undefined ? true : names[i] !== 'off'", "names[i] !== 'off'", "names[i] === undefined || names[i] !== 'off'"],
        &["names[i] === undefined ? false : names[i] === 'on'", "names[i] === 'on'", "names[i] !== undefined && names[i] === 'on'"],
        &["widths[i] ?? 0", "widths[i] === undefined ? 0 : widths[i]", "widths[i] !== undefined ? widths[i] : 0"],
    ];
    for sources in groups {
        let r = evaluate_joint(sources).unwrap();
        assert!(r.saturated, "{sources:?}");
        assert!(r.roots.iter().all(|&id| id == r.roots[0]), "{sources:?}: {:?}", r.canonical);
    }
}

#[test]
fn a_callback_that_forwards_is_not_the_function_it_calls() {
    // map passes (element, index, array); a wrapper that forwards fewer arguments differs.
    for (a, b) in [("xs.map(f)", "xs.map((x) => f(x))"), ("xs.map(f)", "xs.map((x, k) => f(x, k))")] {
        let r = evaluate_joint(&[a, b]).unwrap();
        assert_ne!(r.roots[0], r.roots[1], "{a} and {b}");
    }
}

#[test]
fn the_two_element_slice_sum_stays_a_fold() {
    let r = common::checked("widths.slice(i, i + 2).reduce((a, b) => a + b, 0)", Verdict::NoCheat);
    assert!(r.nodes < 30, "{} nodes", r.nodes);
}

#[test]
fn mutation_cases_saturate_with_their_verdicts() {
    initialize();
    let cases = include_str!("mutations.txt").lines().filter(|l| !l.starts_with('#') && !l.is_empty());
    for line in cases {
        let (expected, source) = line.split_once('\t').unwrap();
        let r = evaluate(source).unwrap();
        assert!(r.consistent && r.saturated, "{source}: {}", r.stop);
        assert!(r.nodes < 150, "{source}: {} nodes", r.nodes);
        assert_eq!(r.mutation.to_string(), expected, "{source}: {}", r.canonical);
    }
}
