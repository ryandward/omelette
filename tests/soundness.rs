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
    // An empty list throws.
    value("xs.reduce((_, x) => x)", "(maybe propagate throw (lam elem:@1 elem:@1) (read list:xs (lin -1 1 (len list:xs))))");
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

#[test]
fn a_list_built_with_undefined_elements_does_not_claim_they_are_defined() {
    // The element is `undefined`, so `x !== undefined` may be false.
    let r = checked("[undefined, ...ys].every((x) => x !== undefined)", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "true");
    let r = checked("xs.map(() => undefined).every((x) => x !== undefined)", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "true");
}

#[test]
fn a_projection_of_a_mapped_list_holds_the_mapped_value() {
    cheat("users.map((u, k) => roles[k] ?? 'none').filter((_, k) => k === i)[0]", &[Family::Default]);
    value("users.map((u) => 'on').filter((_, k) => k === i).every((n) => n === 'on')", "true");
}

#[test]
fn a_slice_whose_bounds_differ_by_a_negative_amount_can_hold_anything() {
    value("[1, 2, 3].slice(1, -1).length", "1");
    cheat("xs.slice(1, -1)[0] ?? 0", &[Family::Default]);
    let r = checked("xs.slice(0, -1)", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "nil");
}

#[test]
fn length_is_undefined_on_numbers_and_unknown_on_unknown_values() {
    value("(5).length === undefined", "true");
    value("true.length === undefined", "true");
    let r = checked("((a) => a.length === undefined)(y)", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "false");
}

#[test]
fn spreading_iterates_code_points_and_an_unknown_value_is_opaque() {
    value("[...'\u{1F600}'].length", "1");
    checked("((a) => [...a])(y)", Verdict::Undecided);
    cheat("groups.map((g) => [...g, names[i] ?? 'x'])", &[Family::Default]);
    cheat("users.reduce((acc, u, i) => [...acc, roles[i] ?? 'none'], [])", &[Family::Default]);
}

#[test]
fn concat_spreads_every_argument() {
    value("[1].concat(2, 3).length", "3");
    value("[1].concat().length", "1");
}

#[test]
fn a_throw_is_an_effect_not_a_value() {
    // Each throws where the read is missing: no value is swallowed.
    for source in ["xs[i].length + 1", "xs[i].length < 3", "(() => { const n = xs[i].length; return xs[i] ?? 0; })()"] {
        checked(source, Verdict::NoCheat);
    }
    value("[undefined.length, 1][1]", "throw");
    value("((y) => 5)(undefined.length)", "throw");
    value("[1, 2].map((x) => undefined.length)", "throw");
}

#[test]
fn evaluating_what_is_not_modeled_leaves_the_value_unknown() {
    for source in ["[null.x, 1][1]", "[(() => { throw 1 })(), 1][1]", "[f(1), 2][1]"] {
        checked(source, Verdict::Undecided);
    }
}

#[test]
fn plus_concatenates_undefined_next_to_a_possible_string() {
    cheat("names[i] + undefined", &[Family::Sink]);
    cheat("((pre) => pre + names[i])()", &[Family::Sink]);
    value("undefined + []", "utf16:0075006e0064006500660069006e00650064");
    let r = checked("undefined + y", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "nan");
}

#[test]
fn arguments_is_not_a_free_list() {
    checked("(function (a) { return arguments[0]; })(xs[i] ?? 0)", Verdict::Undecided);
    checked("xs.map(function () { return arguments[1] ?? 0; })", Verdict::Undecided);
}

#[test]
fn integer_overflow_is_never_a_constant() {
    for source in ["i * 9007199254740991 * 1024 < 1 - i * 9007199254740991 * 1024", "i * 9007199254740991 * 1024 === 1 - i * 9007199254740991 * 1024"] {
        let r = checked(source, Verdict::NoCheat);
        assert!(!matches!(r.canonical.to_string().as_str(), "true" | "false"), "{source}: {}", r.canonical);
    }
}

#[test]
fn lists_compare_by_identity() {
    value("[] === []", "false");
    value("((a) => a === a)([])", "true");
    cheat("[] === [] ? 0 : xs[i] ?? 0", &[Family::Default]);
}

#[test]
fn list_methods_check_their_arguments() {
    value("[[1]].flat(0).length", "1");
    checked("[[[1]]].flat(2)", Verdict::Undecided);
    checked("groups.slice(i, i + 1).flat(0)", Verdict::NoCheat);
    for source in ["[].map()", "[].some(1)", "[1, 2].reduce()", "[].filter()"] {
        value(source, "throw");
    }
}

#[test]
fn a_closure_called_in_a_world_sees_its_read_decided() {
    checked("(xs[i] === undefined ? () => xs[i] ?? 0 : () => 1)()", Verdict::NoCheat);
    cheat("(xs[i] === undefined ? (() => 0) : (() => xs[i]))()", &[Family::Default]);
}

#[test]
fn a_literal_filter_does_not_hide_a_possibly_missing_element() {
    cheat("[names[i]].filter((n) => n === 'off').length === 0", &[Family::Sink]);
}

#[test]
fn drift_survives_short_lists_projections_and_present_branches() {
    for source in [
        "users.map((_, i) => roles.slice(i, i + 1)[0])",
        "users.map((_, i) => roles.filter((_, k) => k === i)[0])",
        "users.map((_, i) => roles.map((r) => r + 1)[i])",
        "users.map((_, i) => roles[i] && roles[i] + '!')",
    ] {
        cheat(source, &[Family::Drift]);
    }
    // A missing read that throws leaves no hole.
    checked("users.map((_, i) => roles[i].length)", Verdict::NoCheat);
}

#[test]
fn what_the_value_does_not_depend_on_is_not_judged() {
    for source in ["xs.length >= 0 ? 1 : [names[i] ?? 'x']", "xs.length < 0 && [names[i] ?? 'x']", "xs.filter(() => false).map(() => ys[j] ?? 0)"] {
        checked(source, Verdict::NoCheat);
    }
}

#[test]
fn a_present_branch_that_ignores_the_element_observes() {
    for source in ["names[i] ? ys.length : ys.length", "names[i] ? n * 2 : n * 2"] {
        checked(source, Verdict::NoCheat);
    }
}

#[test]
fn reads_a_walker_keeps_in_range_are_present() {
    for source in [
        "((m) => m.map((y, k) => m[k] !== 'off'))(names.map((n) => n))",
        "xs.filter((x) => x !== 'off').map((x, i) => xs[i] !== 'off')",
        "xs.map((x, i) => [...xs, 0][i])",
        "xs.map((x, i) => xs.slice(0)[i])",
        "xs.map((x) => xs[0] ?? 0)",
        "xs.map((x, i) => xs.at(-1) ?? 0)",
        "xs.map((x, i) => xs.slice(i, i + 1).every((y) => y > 0))",
    ] {
        checked(source, Verdict::NoCheat);
    }
    cheat("ys.map((y) => xs[0] ?? 0)", &[Family::Default]);
}

#[test]
fn destructuring_iterates_code_points() {
    value("(([a]) => a)('\u{1F600}').length", "2");
    value("(([a, b]) => b)('ab')", "utf16:0062");
    value("(([a]) => a)(undefined)", "throw");
}

#[test]
fn a_witness_over_an_element_that_may_be_undefined_is_undecided() {
    // Every defined element gives 1 and a missing read gives 2: presence is observed. Only the
    // present `undefined` element also gives 2, which detection cannot separate from a cheat.
    for source in ["[undefined, ...ys][k] === undefined", "((v) => v !== undefined ? 1 : 2)([undefined, ...ys][k])"] {
        checked(source, Verdict::Undecided);
    }
}
