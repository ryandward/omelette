# omelette

An in-process Rust probe for absence laundering in JavaScript/TypeScript expressions. For example, `widths.slice(i, i + 1).reduce((_, x) => x, 0)` replaces a potentially absent read with a written default. omelette proves this by finding a `Maybe(default, IndexQ(array, index))` representation. A function of the read launders it the same way: `names.slice(i, i + 1).every((n) => n !== 'off')` answers `true` when the element is missing, which is `maybe true (!== 'off') (names !? i)`, found as `Maybe(true, IndexQ(Map(f, names), i))`.

The runtime uses **`egg`**, with **`oxc_parser` / `oxc_allocator`** for native parsing. There are no Node.js, TypeScript compiler, or parser subprocesses. All 66 golden cases pass and reach saturation: the original 29 cases, 11 string regressions, the `every` and `some` spellings with their non-cheats (9 and 10), and 7 unknown-callback cases, including both index-equality `find` predicates. `widths.length ?? 0` resolves to `no cheat`. String defaults such as `'MODE'`, `'measures'`, `'none'`, and `''` use the same absence-elimination rules as numeric defaults.

## Run and embed

Requires Rust 1.97 or newer.

```sh
cargo build --release
./target/release/omelette 'widths.find((_, idx) => idx === i) ?? 0'
./target/release/omelette "names[i] ?? 'unknown'"
./target/release/omelette "names.slice(i, i + 1).every((n) => n !== 'off')"
./target/release/omelette 'widths.length ?? 0' --all
./target/release/omelette --joint 'widths.find((_, idx) => idx === i)' 'widths[i]'
./scripts/check.sh
cargo test --release
cargo run --release --example latency -- 500 --check
```

Use the library inside the harness loop:

```rust
use omelette::engine::{evaluate, initialize, Verdict};

initialize(); // Once at harness startup: rules, parser bootstrap, egg's clock calibration.
let result = evaluate("widths[i] ?? 0").expect("valid expression");
assert_eq!(result.verdict, Verdict::Cheat);
assert!(result.saturated && result.consistent);
```

`evaluate` includes parsing, lowering, graph construction, saturation, consistency checking, and extraction. It creates a fresh graph for every input; expression results are not cached. The shared rules are initialized once. `parse_time` includes both parsing and lowering; `total_time` ends before disposal of the returned graph. The benchmark additionally includes that disposal. `TRACE=1` prints graph size, search, apply, and rebuild time, and rule applications for each iteration.

`evaluate_with_limits` exposes iteration, node, and saturation-time limits. Defaults are 60 iterations, 10,000 nodes, and 50 ms. Limits are cooperative engine bounds, not a hard real-time deadline; a limit or inconsistent graph returns `UNDECIDED`. Syntax errors return `Err`.

## Why egg

The basis needs directed algebraic rules plus small interval and free-variable analyses. It does not require a general Datalog runtime. `egglog` made those analyses concise, but the supplied baseline was 10–53 ms of saturation alone. The native implementation removes the subprocess frontend and the per-expression Datalog setup and joins. It meets the sub-millisecond steady-state target for this basis on the measured host; this is not a worst-case guarantee for arbitrary JavaScript or operating-system scheduling.

- [frontend.rs](src/frontend.rs) lowers the Oxc AST directly into terms. Addition, subtraction, negation, and constant multiplication become canonical affine forms **before entering egg**. Terms use integer coefficients instead of expanding constants into repeated units. Nonlinear multiplication stays opaque arithmetic.
- Inside a `map`, `filter`, `find`, `every`, or `some` callback, `receiver[index]` with the callback's own index parameter lowers to the total read `At`: the walker only passes positions that exist. A different list, a shifted index, or a shadowed name stays a partial read.
- A two-parameter callback that only forwards to a function, `(x, k) => f(x, k)`, lowers to `f` itself, because walkers pass (element, index). `map(f)` and `map((x, k) => f(x, k))` are therefore one term before they enter egg. The one-parameter `(x) => f(x)` stays distinct: `['1', '2'].map(parseInt)` is `[1, NaN]`, but `['1', '2'].map((x) => parseInt(x))` is `[1, 2]`. Doing this in the e-graph instead put `f` in a class with its own expansion, so every application of `f` beta-reduced back into itself (200 e-nodes for a two-element read).
- String literals use `Str` with exact decoded UTF-16 values, including escape sequences and lone surrogates. Strict equality compares values without coercion. Addition with a known string operand uses ordered `Concat`, outside affine arithmetic; literal concatenations fold to strings. Consistency checks reject distinct string constants merging with each other or with numeric/boolean/undefined values.
- [rules.rs](src/rules.rs) contains the directed `egg::rewrite!` rules. Explicit mirror rules handle `===`; there is no general equality commutation, association, or inverse arithmetic expansion. The former [rules.egg](src/rules.egg) remains as a historical specification, outside the runtime.
- [engine.rs](src/engine.rs) tracks interval bounds and free variables. Globally fresh frontend binders and free-variable guards prevent capture during beta reduction. Arithmetic introduced by semantic rewrites uses the same affine representation, with checked integer operations and coefficient merging after e-class unions.
- Index predicates lower to `Select`, a list containing at most the selected element. Projection then becomes an indexed read without distributing conditionals through the entire list. Short-list bounds are consumed directly by folds and reads. Structural rules skip cyclic identity representatives such as `Append(xs, Nil)` after it merges with `xs`.
- M1 recognizes `If(c, t, z)` where `c` is the presence test of a partial read `xs[k]`, found among the parents of `c` as the read's expansion `If(c, At(xs, k), Undef)`. When `t` is the read, it builds `Maybe(z, IndexQ(xs, k))`. When `t` is a defined value of the element, it abstracts `f = λx. t[xs[k] := x]` and builds `Maybe(z, IndexQ(Map(f, xs), k))`, stating the mapped read's expansion `If(c, t, Undef)` directly. It skips a constant `t` (that only observes absence, like `isNothing`) and a non-empty list against an empty `z` (`maybeToList`). The applier fires once per class and reports only changed unions.
- `every`, `some`, and a filter's `length` over a list of at most one element become the callback on `xs[0]` when it exists and the empty-list answer (`true`, `false`, `0`) when it does not. Callbacks bind one parameter per argument and drop surplus arguments, as JavaScript does.
- Definedness and resolution are analysis facts, not node shapes. A value is `defined` when it can never be `undefined` (numbers, booleans, strings, lists, comparisons). A list's `elements` are defined for input lists and literals of defined values, and for `Map(f, xs)` only when `f` provably `returns` a defined value; an in-bounds read `At` is exactly as defined as its list's elements. One rule drops `??` over a defined value, one rule folds `=== undefined` on a defined value to `false`, and M1, the cheat detector, and the consistency check read the same fact. A class is `opaque` when every representation holds unsupported syntax or an unresolved call, and a walker (`Map`, `Filteri`, `Foldl`, `Every`, `Some`) over a function it cannot apply is such a call. The verdict reads the root's opacity, and extraction prices those walkers like syntax.
- Every callback a rule applies (`filter`, `reduce`, `map`, and the short `every`, `some`, and filter `length`) goes through one arity-aware helper, written `Call2(f, a, b)` in the rules. Concrete lists therefore evaluate with one-parameter callbacks too, and `map` passes the index. An unresolved callee stays `Call2`, which counts as unsupported syntax.
- Distribution over a conditional (`at-if`, `filteri-if`, `strict-eq-if`, and the rest) never enters an `If` whose condition is decided. Its class already holds the live branch, and the dead branch could unfold forever: `[1, -1].filter((x, k) => x > 0)` re-filtered the list it had been proven empty against at every next index and hit the node limit. Comparison and negation rewrites also stop once a class's boolean value is known, integer equality on a live conditional is decided by distributing `===` into its branches instead of also expanding into `EqI`, and `!` is pushed into a conditional only when that conditional tests a read's presence, which is where a written absence answer becomes visible. `a && b` and `a || b` become `If(a, b, false)` and `If(a, true, b)` so both spellings of a presence test meet the same rules.

The two-element slice sum is deliberately left as a fold: its length bound is `[0, 2]`, so the singleton-fold lemma cannot fire. Its regression test requires `no cheat`, saturation, consistency, and fewer than 150 e-nodes.

## Reproducible latency measurements

[benchmarks/latency.txt](benchmarks/latency.txt) records a release-mode run with 500 samples per case on an Intel Core i7-8700K. [benchmarks/environment.txt](benchmarks/environment.txt) records the toolchain and command. Each case gets five warmups; samples interleave all 66 inputs. Each timed evaluation reparses the source and constructs a new graph. The benchmark reports runtime startup and the first evaluation separately, then p50/p95/p99/max latency for the steady-state loop.

Recorded results (microseconds; total includes graph disposal):

| Measurement | Result |
| --- | ---: |
| Worst per-case parser p95 | 4.0 µs |
| Worst per-case parser + lowering p95 | 27.2 µs |
| Worst per-case total p95 / p99 | 811.7 / 1,135.7 µs |
| Largest total among 33,000 samples | 1,824.5 µs |
| Worst string-case total p95 | 553.2 µs |
| Worst `every`-case / `some`-case total p95 | 657.7 / 811.7 µs |
| Worst unknown-callback-case total p95 | 534.0 µs |
| Two-element sum total p50 / p95 | 145.4 / 191.6 µs |
| Two-element sum graph / iterations | 28 / 5 |
| All-case graph sizes / iterations | 5–100 / 1–12 |
| One-time runtime initialization | 1,226.1 µs |
| First evaluation after initialization | 288.1 µs |

These are measured samples on this host, not scheduling guarantees. The worst case is `names.slice(i, i + 1).filter((n) => n === 'on').length !== 0` (99 e-nodes, 12 iterations); the worst p99 and the largest sample exceed 1 ms, while the p95 threshold holds. Reads of concrete literal lists are comparatively heavy: `[1, 2][0]` alone takes 76 e-nodes.

The `--check` option requires every case's parser and parser-plus-lowering p95 to be below 50 µs, total p95 below 1 ms, and graph size below 150 e-nodes. Ordinary tests assert correctness and graph bounds without wall-clock thresholds. `scripts/check.sh` also rejects non-saturated runs, including cases whose expected verdict is `UNDECIDED`.

## Verdicts and model boundaries

- `CHEAT`: a reachable class contains `Maybe(z, m)`, where `m` is an `IndexQ` (the read itself, or the read mapped through a function of the element) that is not proven present, absent, or defined, and `z` is a written value. It takes precedence over `UNDECIDED`: `xs.map(f)[i] ?? 0` launders a possibly absent read whatever `f` is.
- `no cheat`: saturation completed, the extracted expression has no unsupported syntax, and no such pattern was found.
- `UNDECIDED`: the root is opaque (unsupported syntax or an unresolved call, including `xs.map(f)` over an unknown `f`), the engine reached a limit, or consistency checks failed.

Comparing a possibly absent read against a defined value is therefore a cheat: `names[i] !== 'off'` is `true` for a missing element, and `widths[i] === 0` is `false`. Comparing it against `undefined` observes absence and is not. List results such as `map` or `filter` over `slice(i, i + 1)` keep the empty list as the absence answer and are not eliminations, but a filter's `length` is.

These verdicts concern the existing algebraic model, not general JavaScript safety. Numeric arithmetic models integers, not IEEE-754 behavior (`NaN`, infinities, rounding, and signed zero). String-to-number coercion and string ordering are outside the model. Input lists are dense and their in-bounds reads are assumed defined; a mapped list's reads are defined only when the callback provably returns a defined value; sparse arrays and stored `undefined` values are outside the model. Records, mutation, side effects, and general control flow are not modeled. Blocks support straight-line `const` bindings and returning branches; logical operators retain the basis's boolean interpretation. Callbacks model the element and index, not the array argument. `every`, `some`, and filter lengths expand only over lists of at most one element; longer lists stay `Every`, `Some`, and `Filteri` terms. Unknown callees remain unresolved. Symbolic slice bounds remain semantic `Rel` terms until concrete bounds justify expansion.
