use omelette::engine::{Evaluation, Verdict, evaluate, evaluate_joint};

fn checked(source: &str, verdict: Verdict) -> Evaluation {
    let r = evaluate(source).unwrap();
    assert!(r.saturated, "{source}: {}", r.stop);
    assert!(r.consistent, "{source}: inconsistent graph");
    assert!(r.nodes < 150, "{source}: {} nodes", r.nodes);
    assert_eq!(r.verdict, verdict, "{source}: {}", r.canonical);
    r
}

/// Saturate the sources together and report which roots share a class.
fn same(sources: &[&str]) -> Vec<bool> {
    let r = evaluate_joint(sources).unwrap();
    assert!(r.saturated, "{sources:?}");
    r.roots[1..].iter().map(|&id| id == r.roots[0]).collect()
}

#[test]
fn filter_reduce_and_map_share_the_callback_application() {
    for (source, expected) in [
        ("[1, -1].filter((x) => x > 0).length", "(Num 1)"),
        ("[3, 1, 2].filter((x) => x > 1).length", "(Num 2)"),
        ("['a', 'off'].filter((n) => n !== 'off').length", "(Num 1)"),
        ("[1, -1].filter((x, k) => k === 1)[0]", "(Num -1)"),
        ("[1, 2].reduce((acc) => acc, 0)", "(Num 0)"),
        ("[1, 2].reduce((a, b) => a + b, 0)", "(Num 3)"),
        ("[1, 2].map((x) => x + 1)[0]", "(Num 2)"),
        ("[1, 2].map((x, k) => x + k)[1]", "(Num 3)"),
    ] {
        let r = checked(source, Verdict::NoCheat);
        assert_eq!(r.canonical.to_string(), expected, "{source}");
    }
}

#[test]
fn a_decided_branch_is_never_distributed_into() {
    // Nil's class holds If(false, [-1], Nil). Filtering through that dead If re-filtered
    // [-1] at every next index and never saturated.
    let r = checked("[1, -1].filter((x, k) => x > 0)", Verdict::NoCheat);
    assert_eq!(r.canonical.to_string(), "(Cons (Num 1) Nil)");
}

#[test]
fn point_free_and_full_arity_callbacks_are_one_class() {
    // map and filter pass (element, index), so (x, k) => f(x, k) is f, and its read is f(1, 0).
    assert_eq!(
        same(&[
            "[1, 2].map(f)[0] ?? 0",
            "[1, 2].map((x, k) => f(x, k))[0] ?? 0",
            "f(1, 0) ?? 0",
        ]),
        [true, true]
    );
    assert_eq!(same(&["xs.map(f)", "xs.map((x, k) => f(x, k))"]), [true]);
    assert_eq!(
        same(&["xs.filter(p)", "xs.filter((x, k) => p(x, k))"]),
        [true]
    );
    // The one-parameter wrapper drops the index: ['1', '2'].map(parseInt) is [1, NaN],
    // but ['1', '2'].map((x) => parseInt(x)) is [1, 2]. Merging them would be unsound.
    assert_eq!(
        same(&[
            "[1, 2].map((x) => f(x))[0] ?? 0",
            "f(1) ?? 0",
            "[1, 2].map(f)[0] ?? 0",
        ]),
        [true, false]
    );
    assert_eq!(same(&["xs.map(f)", "xs.map((x) => f(x))"]), [false]);
    assert_eq!(same(&["xs.filter(p)", "xs.filter((x) => p(x))"]), [false]);
    assert_eq!(same(&["xs.map(f)", "xs.map((x, k) => f(k, x))"]), [false]);
}

#[test]
fn a_mapped_read_is_only_as_defined_as_the_callback_result() {
    for (source, expected) in [
        ("[1, 2].map((x) => undefined)[0] ?? 0", "(Num 0)"),
        (
            "[1, 2].map((x) => x > 1 ? x : undefined)[0] ?? 0",
            "(Num 0)",
        ),
        ("[1, 2].map((x) => x + 1)[0] ?? 0", "(Num 2)"),
        ("[undefined][0] ?? 0", "(Num 0)"),
    ] {
        let r = checked(source, Verdict::NoCheat);
        assert_eq!(r.canonical.to_string(), expected, "{source}");
    }
    // The read is present, but f's result may be undefined, so ?? 0 survives.
    for source in [
        "[1, 2].map(f)[0] ?? 0",
        "[1, 2].map((x, k) => f(x, k))[0] ?? 0",
        "[1, 2].map((x) => f(x))[0] ?? 0",
    ] {
        let r = checked(source, Verdict::Undecided);
        assert!(
            r.canonical.to_string().starts_with("(Maybe (Num 0) "),
            "{source}"
        );
    }
}

#[test]
fn a_walker_over_an_unknown_function_is_an_unresolved_call() {
    for source in [
        "[1, 2].map(f)[0]",
        "xs.map(f)",
        "xs.filter(p)",
        "xs.reduce(f, 0)",
        "names.every(f)",
        "f(1, 0)",
    ] {
        checked(source, Verdict::Undecided);
    }
    // A possibly absent read laundered by a written default is a cheat whatever f is.
    for source in ["xs.map(f)[i] ?? 0", "names.slice(i, i + 1).every(f)"] {
        checked(source, Verdict::Cheat);
    }
}
