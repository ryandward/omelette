use egg::{AstSize, Extractor};
mod common;
use common::checked;
use omelette::engine::{Evaluation, Verdict, evaluate_joint};

/// maybe true (!== 'off') (names !? i), as the engine spells it.
const EVERY: &str = "(Maybe (B true) (IndexQ (Map (Lam @elem (Not (StrictEq (Var @elem) (Str utf16:006f00660066)))) (Var free:names)) (Var free:i)))";
/// maybe false (=== 'on') (names !? i).
const SOME: &str = "(Maybe (B false) (IndexQ (Map (Lam @elem (StrictEq (Var @elem) (Str utf16:006f006e))) (Var free:names)) (Var free:i)))";

/// Every Maybe z (IndexQ xs k) witness in the root class.
fn witnesses(r: &Evaluation) -> Vec<String> {
    let ex = Extractor::new(&r.graph, AstSize);
    let best = |id| ex.find_best(id).1.to_string();
    let mut out = vec![];
    for n in &r.graph[r.root].nodes {
        if n.op.as_str() != "Maybe" {
            continue;
        }
        for q in &r.graph[n.children[1]].nodes {
            if q.op.as_str() == "IndexQ" {
                let [xs, k] = [q.children[0], q.children[1]].map(best);
                out.push(format!("(Maybe {} (IndexQ {xs} {k}))", best(n.children[0])));
            }
        }
    }
    out
}

/// Each direct-read spelling carries the canonical witness, and all share one class.
fn reduce_to(canonical: &str, sources: [&str; 3]) {
    for source in sources {
        let r = checked(source, Verdict::Cheat);
        assert!(
            witnesses(&r).iter().any(|w| w == canonical),
            "{source}: {:?}",
            witnesses(&r)
        );
    }
    let r = evaluate_joint(&sources).unwrap();
    assert!(r.saturated);
    assert_eq!(r.roots[0], r.roots[1]);
    assert_eq!(r.roots[0], r.roots[2]);
}

#[test]
fn direct_reads_reduce_to_the_canonical_maybe() {
    reduce_to(
        EVERY,
        [
            "names[i] === undefined ? true : names[i] !== 'off'",
            "names[i] !== 'off'",
            "names[i] === undefined || names[i] !== 'off'",
        ],
    );
    reduce_to(
        SOME,
        [
            "names[i] === undefined ? false : names[i] === 'on'",
            "names[i] === 'on'",
            "names[i] !== undefined && names[i] === 'on'",
        ],
    );
}

#[test]
fn walkers_over_a_short_slice_map_the_callback_over_the_read() {
    let ne = "(Lam @elem (Not (StrictEq (Var @elem) (Str utf16:006f00660066))))";
    for (source, z) in [
        ("names.slice(i, i + 1).every((n) => n !== 'off')", "true"),
        ("names.slice(i, i + 1).some((n) => n !== 'off')", "false"),
    ] {
        let r = checked(source, Verdict::Cheat);
        let w = witnesses(&r);
        assert!(
            w.iter().any(
                |w| w.starts_with(&format!("(Maybe (B {z}) (IndexQ (Map {ne} "))
                    && w.ends_with(" (Num 0)))")
            ),
            "{source}: {w:?}"
        );
    }
    // Truthiness is a boolean, and an unknown predicate cannot prove it is constant.
    for source in [
        "names.slice(i, i + 1).every((n) => n)",
        "names.slice(i, i + 1).every(f)",
        "!names.slice(i, i + 1).some((n) => n === 'off')",
        "names.slice(i, i + 1).filter((n) => n === 'off').length",
    ] {
        checked(source, Verdict::Cheat);
    }
}

#[test]
fn observing_absence_is_not_eliminating_it() {
    for source in [
        // isNothing and its negation: the absence answer is unique to absence.
        "names[i] === undefined",
        "names[i] !== undefined",
        "names[i] !== undefined ? true : false",
        "names.slice(i, i + 1).every(() => false)",
        // A present branch that ignores the element.
        "names[i] !== undefined ? y : 5",
        // maybeToList and a short filter stay lists; the empty list still means absent.
        "names[i] !== undefined ? [names[i]] : []",
        "names.slice(i, i + 1).filter((n) => n === 'off')",
        "names.slice(i, i + 1).map((n) => n !== 'off')",
        "names.every((n) => n !== 'off')",
    ] {
        checked(source, Verdict::NoCheat);
    }
}

#[test]
fn a_walker_index_reads_its_own_receiver_totally() {
    for source in [
        "widths.map((x, k) => widths[k] ?? 0)",
        "names.map((n, i) => names[i] !== 'off')",
        "names.filter((n, k) => names[k] !== 'off')",
        "names.some((n, k) => names[k] === 'off')",
    ] {
        checked(source, Verdict::NoCheat);
    }
    // Another list, or a shadowed index, is still a partial read.
    for source in [
        "widths.map((x, k) => other[k] ?? 0)",
        "widths.map((x, k) => ((k) => widths[k] ?? 0)(j))",
        "widths.map((x, k) => widths[k + 1] ?? 0)",
    ] {
        checked(source, Verdict::Cheat);
    }
}

#[test]
fn callbacks_bind_one_parameter_per_argument() {
    for (source, expected) in [
        ("['a'].every((n) => n !== 'off')", "(B true)"),
        ("['off'].every((n) => n !== 'off')", "(B false)"),
        ("[].every((n) => n !== 'off')", "(B true)"),
        ("['off'].some((n) => n === 'off')", "(B true)"),
        ("[].some((n) => n === 'off')", "(B false)"),
        ("names.slice(i, i + 1).every((n, k) => k === 0)", "(B true)"),
    ] {
        let r = checked(source, Verdict::NoCheat);
        assert_eq!(r.canonical.to_string(), expected, "{source}");
    }
}
