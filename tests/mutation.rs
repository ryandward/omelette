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
    let r = evaluate("(() => { const a = [0]; [1, 2].forEach((x) => a.push(x)); return a; })()").unwrap();
    assert_eq!(r.mutation, Mutation::Undecided);
    assert_ne!(r.canonical.to_string(), "(cons 0 nil)");
}
