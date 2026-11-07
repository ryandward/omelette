//! Regressions from the soundness hunts and the documentation audit, by root cause.
mod common;
use common::{checked, cheat, value};
use omelette::core::Family;
use omelette::engine::Verdict;

#[test]
fn statements_after_a_branch_that_does_not_return_still_run() {
    value("(() => { if (true) {} return 5; })()", "5");
    cheat("(() => { if (names[i] !== undefined) {} else { return 'x'; } return names[i]; })()", &[Family::Default]);
}

#[test]
fn a_projection_through_filter_is_a_list_of_at_most_one_read() {
    cheat("names.filter((_, k) => k === i).every((n) => n !== 'off')", &[Family::Unit]);
    cheat("names.filter((_, k) => k === i).join('')", &[Family::Unit]);
    cheat("names.slice(-1).every((n) => n !== 'off')", &[Family::Unit]);
}

#[test]
fn joining_one_possibly_missing_read_is_a_cheat() {
    cheat("[names[i]].join('')", &[Family::Unit]);
}

#[test]
fn logical_operators_return_their_operands() {
    value("[1, 2].length || 7", "2");
    value("0 && false", "0");
    checked("names[i] && names[i] !== 'off'", Verdict::NoCheat);
}

#[test]
fn list_operations_apply_only_to_lists() {
    value("[].concat(5) === 5", "false");
    value("[...'ab'] === 'ab'", "false");
    checked("'ab'[0] ?? 'z'", Verdict::NoCheat);
}

#[test]
fn a_witness_in_an_unused_branch_does_not_count() {
    for source in ["true ? 5 : names[i] ?? 'x'", "[].length ? names[i] ?? 'x' : 5", "[names[i] ?? 'x'].length", "((y) => 5)(names[i] ?? 'x')"] {
        checked(source, Verdict::NoCheat);
    }
}

#[test]
fn present_but_undefined_elements_are_not_absent() {
    value("[...[1].map((x) => undefined), 0][0]", "undefined");
    value("((ys) => ys.every((y, k) => ys[k] !== undefined))([1].map((x) => undefined))", "false");
}

#[test]
fn an_index_that_is_not_an_integer_selects_nothing() {
    value("[1, 2].find((_, idx) => idx === '0')", "undefined");
}

#[test]
fn integers_beyond_exact_range_are_not_folded() {
    let r = checked("9007199254740991 + 1 === 9007199254740991 + 2", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "false");
}

#[test]
fn coalescing_an_unknown_with_an_unknown_may_be_undefined() {
    checked("names[i] === undefined ? (x ?? y) : names[i]", Verdict::Undecided);
    cheat("names[i] === undefined ? (x ?? 0) : names[i]", &[Family::Default]);
}

#[test]
fn an_undecided_step_leaves_the_whole_flow_undecided() {
    // With `x` undefined, the first is `names[i] !== undefined` and the second is `false`.
    checked("!(names[i] === x)", Verdict::Undecided);
    checked("(names[i] + 1) === x", Verdict::Undecided);
}

#[test]
fn passing_a_replacement_through_keeps_its_flow() {
    cheat("[...groups.slice(i, i + 1).flat()]", &[Family::Container]);
    cheat("groups.slice(i, i + 1).flat().length", &[Family::Container]);
    cheat("[...groups.slice(i, i + 1).flat(), 1]", &[Family::Container]);
}

#[test]
fn witnesses_of_one_value_over_one_read_share_their_present_branch() {
    // Where the read is present the length is nonzero, so the element is never used.
    checked("xs.length ? 5 : (xs[xs.length - 1] ?? 0)", Verdict::NoCheat);
}

#[test]
fn reduce_without_an_initial_value_returns_a_lone_element_uncalled() {
    value("[3].reduce((_, x) => 7)", "3");
    value("[3, 4].reduce((_, x) => 7)", "7");
    let r = checked("xs.reduce((_, x) => 7)", Verdict::NoCheat);
    assert!(r.canonical.to_string().starts_with("(fold "), "{}", r.canonical);
    value("xs.reduce((_, x) => x)", "(read list:xs (lin -1 1 (len list:xs)))");
}

#[test]
fn an_index_inside_parentheses_or_a_type_assertion_is_still_an_index() {
    for source in ["names[(i)] !== 'off'", "names[i as number] !== 'off'", "names[(i)!] !== 'off'"] {
        cheat(source, &[Family::Sink]);
    }
}

#[test]
fn an_unknown_in_the_present_branch_leaves_the_witness_undecided() {
    // `p = () => false` ignores the element; `p = () => true` and `x = undefined` test presence.
    for source in [
        "xs.slice(i, i + 1).some(p)",
        "xs.slice(i, i + 1).every((n) => n === x)",
        "xs.slice(i, i + 1).reduce(f, 0)",
        "xs.slice(i, i + 1).flatMap(f)",
    ] {
        checked(source, Verdict::Undecided);
    }
    // A one-element join never writes its separator.
    cheat("xs.slice(i, i + 1).join(s)", &[Family::Unit]);
    cheat("xs.slice(i, i + 1).every((n) => n > k)", &[Family::Unit]);
}

#[test]
fn a_present_element_that_is_undefined_is_not_missing() {
    // The read is in range; its element's value is `undefined`, which egg also proves.
    value("[undefined, ...ys].map((x) => 5)[0]", "5");
}
