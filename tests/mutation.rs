//! Observable mutation: values of local construction, and how mutation meets absence.
mod common;
use common::{checked, value};
use omelette::core::{Family, Mutator};
use omelette::engine::{Mutation, Verdict, evaluate};

fn mutation(source: &str) -> Mutation {
    evaluate(source).unwrap().mutation
}

#[test]
fn local_construction_computes_its_value() {
    for (source, expected) in [
        ("(() => { const a = []; a.push(1); a.push(2); return a; })()", "(cons 1 (cons 2 nil))"),
        ("(() => { const a = [3, 1, 2]; a.sort(); return a; })()", "(cons 1 (cons 2 (cons 3 nil)))"),
        ("[10, 9, 1].sort()", "(cons 1 (cons 10 (cons 9 nil)))"),
        ("(() => { const a = [1]; const b = a; b.push(2); return a.length; })()", "2"),
        ("(() => { const a = [1, 2, 3]; return a.pop(); })()", "3"),
        ("(() => { const a = [1, 2, 3, 4]; a.splice(1, 2); return a; })()", "(cons 1 (cons 4 nil))"),
        ("(() => { const a = [1, 2]; a[2] = 9; return a; })()", "(cons 1 (cons 2 (cons 9 nil)))"),
        ("(() => { const a = [1]; const b = [a, a]; a.push(2); return b[1].length; })()", "2"),
        ("(() => { const a = [3, 1]; return a.sort() === a; })()", "true"),
    ] {
        value(source, expected);
        assert_eq!(mutation(source), Mutation::None, "{source}");
    }
}

#[test]
fn a_mutated_input_is_read_after_the_mutation() {
    value("(() => { const n = xs.length; xs.push(1); return xs.length - n; })()", "1");
    value("(xs.reverse(), xs.reverse(), xs)", "list:xs");
    checked("(xs.length = 0, xs[0] ?? 5)", Verdict::NoCheat);
}

#[test]
fn mutation_and_absence_are_separate_axes() {
    let r = checked("xs.pop() ?? 0", Verdict::Cheat);
    assert_eq!(r.families, [Family::Default]);
    assert_eq!(r.mutation, Mutation::Observable(vec![Mutator::Pop]));
    let r = checked("[...xs].sort()[i] ?? 0", Verdict::Cheat);
    assert_eq!(r.mutation, Mutation::None);
}

#[test]
fn a_mutation_in_a_branch_that_cannot_run_is_not_observable() {
    for source in ["xs.length >= 0 ? 0 : ys.push(1)", "xs.filter(() => false).map((x) => ys.push(x))", "[0, 1].every((x) => x > 0 && xs.push(1))"] {
        assert_eq!(mutation(source), Mutation::None, "{source}");
    }
    assert_eq!(mutation("xs[i] === undefined ? ys.push(1) : 0"), Mutation::Observable(vec![Mutator::Push]));
}

#[test]
fn a_local_array_handed_to_the_caller_is_theirs() {
    let source = "(() => { const a = []; xs.push(a); a.push(1); return 0; })()";
    assert_eq!(mutation(source), Mutation::Observable(vec![Mutator::Push]));
}

#[test]
fn code_lowering_cannot_see_leaves_mutation_undecided_and_values_unknown() {
    assert_eq!(mutation("f(xs)"), Mutation::Undecided);
    let r = evaluate("(() => { const a = [0]; for (const x of [1, 2]) a.push(x); return a; })()").unwrap();
    assert_eq!(r.mutation, Mutation::Undecided);
    assert_ne!(r.canonical.to_string(), "(cons 0 nil)");
    // `forEach` is modeled: it pushes onto an array only the expression holds.
    let r = evaluate("(() => { const a = [0]; [1, 2].forEach((x) => a.push(x)); return a; })()").unwrap();
    assert_eq!(r.mutation, Mutation::None);
    assert_eq!(r.canonical.to_string(), "(cons 0 (cons 1 (cons 2 nil)))");
}

#[test]
fn branches_that_grow_a_local_array_merge_without_losing_it() {
    for source in [
        "(() => { const b = [1]; if (n > 0) { b.push([2]); } return b.length; })()",
        "(() => { const b = []; (n > 0 && b.push([])); return 0; })()",
    ] {
        assert_eq!(mutation(source), Mutation::None, "{source}");
    }
}

#[test]
fn a_mapped_element_is_what_the_map_built() {
    assert_eq!(mutation("xs.map((x) => { const a = [x]; return a; })[0]"), Mutation::None);
    value("xs.map((x) => [[x]])[0][0]", "(maybe propagate throw (lam elem:@3 (cons elem:@3 nil)) (read list:xs 0) (has list:xs 0))");
    assert_eq!(mutation("xs.map((x, i, a) => a)[0].push(1)"), Mutation::Observable(vec![Mutator::Push]));
    assert_eq!(mutation("(() => { const a = [xs]; const m = zs.map((z) => a[0]); a[0] = []; m[0].push(1); return 0; })()"), Mutation::Observable(vec![Mutator::Push]));
}

#[test]
fn a_projection_with_effects_is_a_walker() {
    for source in ["xs.find((x, i) => i === ys.push(1))", "xs.filter((x, i) => i === ys.push(1))"] {
        assert_eq!(mutation(source), Mutation::Observable(vec![Mutator::Push]), "{source}");
    }
}

#[test]
fn a_literal_walker_sees_its_callbacks_change_the_receiver() {
    value("[1, 2].map((x, i, a) => (a.push(9), a.length))", "(cons 3 (cons 4 nil))");
    value("(() => { const a = [1, 2, 3, 4]; const b = []; a.every((x, i, arr) => (arr.pop(), b.push(x))); return b; })()", "(cons 1 (cons 2 nil))");
    assert_eq!(mutation("[[], []].map((x, i, arr) => (arr[1] = ys, x.push(0)))"), Mutation::Observable(vec![Mutator::Push]));
}

#[test]
fn a_choice_may_be_either_alternative() {
    let source = "(() => { const a = []; const b = n > 0 ? a : []; return b === a ? ys.push(1) : 0; })()";
    assert_eq!(mutation(source), Mutation::Observable(vec![Mutator::Push]));
}

#[test]
fn an_escape_that_cannot_happen_is_no_escape() {
    for source in [
        "(() => { const a = []; (xs.length < 0 ? ys.push(a) : 0); a.push(1); return 0; })()",
        "(() => { const a = []; xs.filter(() => false).map(() => ys.push(a)); a.push(1); return 0; })()",
    ] {
        assert_eq!(mutation(source), Mutation::None, "{source}");
    }
}

#[test]
fn nothing_after_a_throw_runs() {
    for source in [
        "(xs.concat([1])[xs.length + 1].length, ys.push(1))",
        "(() => { const s = [3, 1].sort((p, q) => p - q); (s.length > 1 ? s[5].length : 0); xs.push(1); return 0; })()",
        "(xs.length > 0 ? 0 : xs[0].push(1))",
    ] {
        assert_eq!(mutation(source), Mutation::None, "{source}");
    }
}

#[test]
fn a_callback_runs_only_as_often_as_its_list_allows() {
    for source in [
        "[1].sort((a, b) => (ys.push(1), 0))",
        "[3].sort((p, q) => p - q).reduce((a, b) => (ys.push(1), a))",
        "xs.slice(0, 1).filter(() => false).map(() => ys.push(1))",
        "xs.slice(-1, 0).map(() => ys.push(1))",
    ] {
        assert_eq!(mutation(source), Mutation::None, "{source}");
    }
}

#[test]
fn a_self_containing_array_has_no_term() {
    let r = evaluate("(() => { const a = [1]; a.push(a); return a; })()").unwrap();
    assert_eq!(r.mutation, Mutation::Undecided);
    assert_eq!(mutation("(() => { const a = []; a.push(a); xs.push(a); return 0; })()"), Mutation::Observable(vec![Mutator::Push]));
}

#[test]
fn a_length_must_be_a_length() {
    value("(() => { const a = [1]; a.length = -1; return a; })()", "throw");
}

const SETUP: &str = "const s = [3, 1].sort((p, q) => p - q); const a = [1, 2]; const b = [a, 3]; const c = [b, b];";

fn program(body: &str) -> String {
    format!("(() => {{ {SETUP} {body} }})()")
}

#[test]
fn a_branch_that_throws_stops_the_program() {
    // s has two elements, so the && runs a[0].push(1), and 1 has no push.
    value(&program("(s.length < 5 && a[0].push(1)); return a;"), "throw");
}

#[test]
fn a_cycle_through_a_merged_array_resolves() {
    let r = evaluate(&program("(s.length > 2 ? b[0].splice(-1, 0, b[0]) : b[0].push(undefined)); return b;")).unwrap();
    assert!(r.consistent && r.saturated);
}

#[test]
fn a_consumed_conditional_throw_leaves_the_value_unknown() {
    let r = evaluate(&program("[1, 2, 3].every((x) => x < 2 && (s.length > 3 ? b.shift() : a[0].shift())); return 0;")).unwrap();
    assert!(r.opaque);
    assert_eq!(r.mutation, Mutation::Undecided);
}

#[test]
fn an_array_shared_along_many_paths_lowers_once_per_array() {
    let body = "a.map((x, i, arr) => (arr.push([9]), x)); (s.length > 0 ? (s.length > 0 ? b.sort() : a[0].fill(2)) : (s.length > 2 ? c[1].push(a.length) : a.splice(1, 2, undefined))); (s[1] ?? c[1].sort()); return c;";
    let r = evaluate(&program(body)).unwrap();
    assert!(r.parse_time.as_millis() < 50, "{:?}", r.parse_time);
    assert!(r.consistent);
}

#[test]
fn storing_an_array_into_a_symbolic_list_keeps_no_snapshot() {
    let source = "(() => { const a = []; (xs.length < 0 ? ys.push(a) : 0); a.push(1); return 0; })()";
    assert_eq!(mutation(source), Mutation::None);
}
