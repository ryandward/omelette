mod common;
use common::value;

#[test]
fn literals_evaluate_as_javascript_does() {
    for (source, expected) in [
        ("[1, 2][0]", "1"),
        ("[1, 2][2] ?? 0", "0"),
        ("[1, 2].map((x, k) => x + k)", "(cons 1 (cons 3 nil))"),
        ("[3, 1, 2].filter((x) => x > 1).length", "2"),
        ("[1, 2].reduce((a, b) => a + b, 0)", "3"),
        ("[10, 20].reduce((a, b, k) => k, 0)", "1"),
        ("[1, 2].find((x) => x > 1)", "2"),
        ("[0, 1, 2].slice(1).length", "2"),
        ("[1, 2].at(-1)", "2"),
        ("[].concat(5).length", "1"),
        ("[...'ab'].length", "2"),
        ("['a', 'b'].join('-')", "utf16:0061002d0062"),
        ("[1, [2, 3]].join(';')", "utf16:0031003b0032002c0033"),
        ("[true, undefined].join('|')", "utf16:0074007200750065007c"),
        ("[[1, 2], 3].flat().length", "3"),
        ("[[1], [2]].flatMap((g) => g)[0] ?? 0", "1"),
        ("'ab'[1]", "utf16:0062"),
        ("[].length && 7", "0"),
        ("'a' || true", "utf16:0061"),
    ] {
        value(source, expected);
    }
}

#[test]
fn functions_inline_with_javascript_arity_and_blocks() {
    for (source, expected) in [
        ("((a, b, k) => k)(1, 2)", "undefined"),
        ("((x, y = 3) => y)(1)", "3"),
        ("(([x = 0]) => x)([])", "0"),
        ("(() => { if (true) {} return 5; })()", "5"),
        ("(() => { { const a = 1; } return 5; })()", "5"),
        ("(() => { if (false) return 1; else if (false) return 2; return 3; })()", "3"),
        ("((x) => (y) => x)(1)(2)", "1"),
    ] {
        value(source, expected);
    }
}

#[test]
fn strings_compare_by_code_units_without_coercion() {
    for (source, expected) in [
        ("'a' === 'a'", "true"),
        ("'1' === 1", "false"),
        ("undefined === 'a'", "false"),
        (r"'😀' === '😀'", "true"),
        (r"'\ud800' === '\ud801'", "false"),
        ("'a' + 'b' === 'ab'", "true"),
        ("'a' + 'b' === 'b' + 'a'", "false"),
        ("1 + '2'", "utf16:00310032"),
    ] {
        value(source, expected);
    }
}
