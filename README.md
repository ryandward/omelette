# omelette

An in-process Rust probe for absence laundering in JavaScript/TypeScript expressions. `names[i] ?? 'unknown'` replaces a possibly absent read with a written value; so does `names.slice(i, i + 1).every((n) => n !== 'off')`, which answers `true` when the element is missing. Both have the form `maybe z f (xs !? k)`: a constant `z` for the missing element, and `f` of the element otherwise. omelette proves the form by finding a witness `Maybe(z, IndexQ(xs, k))`, or `Maybe(z, IndexQ(Map(f, 0, xs), k))` when `f` is not the identity (`Map(f, 0, xs)` maps `f` over `xs` with indexes counted from 0). For `names[i] !== 'off'` the witness reads `names` at `i`; for the slice spelling it reads the one-element slice at `0`.

The runtime is [`egg`](https://github.com/egraphs-good/egg) with `oxc_parser` for native parsing, all in-process: no Node.js, TypeScript compiler, or subprocess. The 73 golden cases in [tests/cases.txt](tests/cases.txt) all reach saturation with their expected verdicts.

## Run and embed

`Cargo.toml` declares `rust-version = "1.97"`; development and the recorded benchmark use rustc 1.99.1.

```sh
cargo build --release
./target/release/omelette "names[i] ?? 'unknown'"
./target/release/omelette "names.slice(i, i + 1).every((n) => n !== 'off')"
./target/release/omelette 'widths.length ?? 0' --all
./target/release/omelette --joint 'widths.find((_, idx) => idx === i)' 'widths[i]'
./scripts/check.sh
cargo test --release
cargo run --release --example latency -- 500 --check
```

`--all` dumps every e-class; `--joint` saturates several expressions in one graph and prints each one's class, so a shared class number means a proven equality. `scripts/check.sh` runs every golden case and fails on a verdict mismatch, a non-saturated run (including expected `UNDECIDED` cases), or an inconsistent graph.

Use the library inside the harness loop:

```rust
use omelette::engine::{evaluate, initialize, Verdict};

initialize(); // Once at harness startup: rules, parser bootstrap, egg's clock calibration.
let result = evaluate("widths[i] ?? 0").expect("valid expression");
assert_eq!(result.verdict, Verdict::Cheat);
assert!(result.saturated && result.consistent);
```

`evaluate` parses, lowers, builds a fresh graph, saturates, checks consistency, and extracts a canonical term; nothing is cached between expressions. It runs with a limit of 60 iterations, 10,000 e-nodes, and 50 ms; `evaluate_with_limits` takes those three limits as arguments. They are cooperative bounds, not a real-time deadline. `parse_time` covers parsing and lowering; `total_time` ends before the returned graph is dropped. `TRACE=1` prints, for each iteration, the graph size, search, apply, and rebuild time, and the rules applied. Syntax errors return `Err`.

## Verdicts

Checked in this order:

1. `UNDECIDED` if the run did not saturate or the graph is inconsistent: a class with conflicting constants, an empty interval, a string merged with a number or boolean, both `Nil` and `Cons`, or `Undef` beside a value proven defined.
2. `CHEAT` if a class reachable from the root holds `Maybe(z, m)` where `m` is an `IndexQ` not proven present, absent, or defined, and `z` is not `undefined`, out of bounds, or a throw. In a class that also has a reduced form, the walk does not descend through unsupported syntax such as an unreduced binding or application, so `((xs) => xs[2] ?? 0)([1, 2])` is judged by its value, `0`.
3. `UNDECIDED` if the root is opaque: every representation of it holds unsupported syntax or an unresolved call.
4. `no cheat` otherwise.

A witness outranks opacity: `xs.map(f)[i] ?? 0` launders a possibly absent read whatever `f` is, while `xs.map(f)` alone is `UNDECIDED`.

## What counts as a cheat

Each spelling below answers with a constant when the element at `i` is missing. For the list operations over `slice(i, i + 1)`, that constant is the operation's empty-list value, the unit of its monoid.

| Spelling | Form |
| --- | --- |
| `xs[i] ?? z`, `xs.slice(i, i + 1).reduce((_, x) => x, z)` | `maybe z id` |
| `names[i] !== 'off'`, `names.slice(i, i + 1).every((n) => n !== 'off')` | `maybe true (!== 'off')` |
| `names[i] === 'on'`, `names.slice(i, i + 1).some((n) => n === 'on')` | `maybe false (=== 'on')` |
| `names.slice(i, i + 1).filter((n) => n === 'on').length` | `maybe 0 (x -> x === 'on' ? 1 : 0)` |
| `names.slice(i, i + 1).join(', ')` | `maybe '' text` |
| `groups.slice(i, i + 1).flat()`, `.flatMap((g) => g)` | `maybe [] spread` |

Bindings change nothing: `((y) => y ?? 0)(names[i])` and `(() => { const y = names[i]; return y ?? 0; })()` are cheats too. These are not:

- No partial read: `names.every((n) => n !== 'off')` and `names.join(', ')` speak for the whole list.
- No elimination: `names.slice(i, i + 1).map((n) => n === 'on')` and `.filter((n) => n === 'on')` stay lists, with `[]` as the absence answer; so does `names[i] !== undefined ? [names[i]] : []`.
- Absence observed rather than replaced: `names[i] === undefined`, or a present branch that ignores the element (`names[i] !== undefined ? y : 5`).
- The index is determined: inside `names.map((n, i) => names[i] === 'on')`, `names[i]` always exists.

## How it works

- **Frontend** ([frontend.rs](src/frontend.rs)) lowers the Oxc AST and normalizes at the boundary. Addition, subtraction, negation, and constant multiplication become canonical integer affine sums. String literals become `Str` keyed by their decoded UTF-16 code units. Binders are globally fresh. A non-negative integer literal index into an array literal folds to that element, or to `undefined` past its end, when no spread or hole precedes it. Inside a `map`, `filter`, `find`, `every`, `some`, or `flatMap` callback, the receiver indexed by the callback's own index parameter becomes the total read `At`. A two-parameter function that only forwards, `(x, k) => f(x, k)` with `f` mentioning neither, becomes `f`, so `map(f)` and `map((x, k) => f(x, k))` are one term.
- **Analysis** ([engine.rs](src/engine.rs)) gives every class interval bounds, free variables, known booleans and strings, and six facts. `defined`: the value is never `undefined`. A list's `elements` are defined for input lists, for literals of defined values, and for `Map(f, k, xs)` only when `f` provably `returns` a defined value; an in-bounds read is as defined as its list's elements. `params`: a function's parameter count. `callable`: a function of at most two parameters with a resolved body. `opaque`: every representation holds unsupported syntax or an unresolved call, where a `Map`, `Filteri`, `Foldl`, `Every`, or `Some` over a function that is not callable counts as a call. The `??` and `=== undefined` rules and M1 read `defined`; extraction and the verdict read `callable` and `opaque`.
- **M1** recognizes `If(c, t, z)` where `c` is the presence test of a partial read `xs[k]`, found among the parents of `c` as the read's expansion `If(c, At(xs, k), Undef)`, and `t` is defined. When `t` is the read it builds `Maybe(z, IndexQ(xs, k))`. Otherwise it abstracts `f = fun x -> t[xs[k] := x]`, builds `Maybe(z, IndexQ(Map(f, 0, xs), k))`, and unions the mapped read with `If(c, t, Undef)`. It skips a constant `t` and a non-empty list `t` against an empty `z`, and fires once per class.
- **Short lists.** Over a list of length at most one, a fold, `every`, `some`, a filter's `length`, `join`, and `flat` become the operation on `xs[0]` when it exists and the empty-list value otherwise; M1 then finds the witness. Slice lengths come from constant slice widths, so the two-element slice sum (length `[0, 2]`) stays a fold and is `no cheat`.
- **Literal lists** are decided structurally. `at-cons` and `at-append` take the one branch a known index selects; `foldl-cons`, `filteri-cons`, `map-cons`, `join-cons`, and `flat-cons` unfold them. `every` and `some` have no structural rules, so their short-list form also covers literals of at most one element. The other short-list forms and the relational read lemmas (`prefix-last`, `short-last`) leave literals alone, and no partial read is seeded at a known position of a literal.
- **Projection.** Index predicates such as `(_, idx) => idx === i` rewrite a filter to `Select`, the list holding at most the selected element, so `find` becomes an indexed read.
- **Callbacks** that rules apply go through one helper, which binds one parameter per argument and drops surplus arguments; rules spell it `Call2(f, a, b)`, and short folds try direct affine substitution first. An unknown free function is applied as the direct call `f(a, b)`. A parameter is applied once substitution supplies its value. A callback with a parameter left unbound stays an unresolved `Call2`. Substitution into an affine sum yields a canonical sum.
- **Rules** ([rules.rs](src/rules.rs)) are directed `egg::rewrite!` rules. `===` has explicit mirror rules; there is no general commutation or association. Distribution over a conditional never enters an `If` whose condition is decided, since the class already holds the live branch and the dead one can unfold without end. Comparison and negation rewrites stop once a class's boolean is known; integer equality on a live conditional is decided by distributing `===` into its branches only; `!` is pushed into a conditional only when that conditional tests a read's presence; `a && b` and `a || b` become `If(a, b, false)` and `If(a, true, b)`. Structural rules skip cyclic representatives such as `Append(xs, Nil)` once it has merged with `xs`.

## Model boundaries

The verdicts concern this algebraic model, not general JavaScript safety. Several boundaries give a wrong value or verdict rather than `UNDECIDED`; they are marked.

- Arithmetic is over integers, not IEEE-754 (`NaN`, infinities, rounding, signed zero). `+` is integer addition unless an operand is syntactically a string (a literal or a concatenation), which makes it ordered `Concat`. Wrong value: `names[i] + names[j] === 'ab'` folds to `false`. String-to-number coercion and string ordering are outside the model.
- Strict (in)equality against anything but `undefined` is in the cheat form; ordering comparisons are not. Wrong verdict: `widths[i] < 3` reads `no cheat` although `undefined < 3` is `false`, because the model does not coerce `undefined` to `NaN`.
- `z` is not required to be proven defined, so `names[i] ?? y` and `widths[i] === j` with unknown `y` and `j` are `CHEAT` even though `y` or `j` may be `undefined`.
- Input lists are dense and their elements defined; sparse arrays and stored `undefined` are outside the model.
- A walker passes a callback (element, index) and `reduce` passes (accumulator, element). A callback that declares more parameters reads what the model does not supply (the array, `reduce`'s index), so its application stays unresolved and the verdict is `UNDECIDED`, whether the callback is written in place or bound first.
- Direct calls are curried: `f(a, b)` applies `f` to `a`, then to `b`. So `(a, b) => e` and `(a) => (b) => e` are not distinguished. Wrong value: calling a function with fewer arguments than parameters yields a partial application instead of binding `undefined`; `((a, b, k) => k)(1, 2)` reads `no cheat` with a function as its value. Under currying, `(x, k) => f(x, k)` and `f` agree; in JavaScript they differ only when `f` reads further arguments. The one-parameter `(x) => f(x)` is kept distinct from `f`: `['1', '2'].map(parseInt)` is `[1, NaN]`, but `['1', '2'].map((x) => parseInt(x))` is `[1, 2]`.
- `flat()` spreads one level: a known list element is spread and a known number, string, or boolean is kept; an element of unknown type leaves `Spread` unresolved (`[x].flat()`). `flat(depth)` is unsupported. `join()` uses `','`, and an `undefined` element writes `''`.
- `every` and `some` over a literal list longer than one element stay `Every` and `Some` terms.
- Records, `Map.get`, object destructuring, mutation, side effects, and general control flow are not modeled: on their own they are `UNDECIDED`, but a witness elsewhere still makes the expression `CHEAT` (`names[i] ?? ({ x: 1 })`). Blocks support straight-line `const` bindings and returning branches. Logical operators are boolean. Symbolic slice bounds stay `Rel` terms until concrete bounds justify expansion.

## Latency

[benchmarks/latency.txt](benchmarks/latency.txt) records a release run with 500 samples per case on an Intel Core i7-8700K, and [benchmarks/environment.txt](benchmarks/environment.txt) records the toolchain and command. Each case gets five warmups; samples interleave all 73 cases, and each reparses the source and builds a new graph. Totals include dropping the graph.

| Measurement | Result |
| --- | ---: |
| Worst per-case parser p95 | 3.8 us |
| Worst per-case parser + lowering p95 | 19.0 us |
| Worst per-case total p95 / p99 | 804.7 / 926.3 us |
| Largest total among 36,500 samples | 1,471.1 us |
| Worst total p95: original / string / every / some cases | 516.9 / 513.4 / 633.2 / 804.7 us |
| Worst total p95: unknown-callback / join and flat cases | 313.9 / 368.1 us |
| Two-element slice sum total p50 / p95 | 153.0 / 170.2 us |
| Two-element slice sum graph / iterations | 28 / 5 |
| All-case graph sizes / iterations | 5-99 / 1-12 |
| One-time runtime initialization | 1,323.1 us |
| First evaluation after initialization | 302.6 us |

The worst case is `names.slice(i, i + 1).filter((n) => n === 'on').length !== 0` (99 e-nodes, 12 iterations); across runs its p99 lands on either side of 1 ms, and its largest sample exceeds it, while its p95 stays under the threshold. These are measured samples on this host, not scheduling guarantees. `--check` requires every case's parser and parser-plus-lowering p95 below 50 us, total p95 below 1 ms, and fewer than 150 e-nodes; the tests assert correctness and graph bounds without wall-clock thresholds.
