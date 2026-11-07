# omelette

An in-process Rust probe for absence laundering in JavaScript/TypeScript expressions: information flows by which a read that may be missing is quietly swallowed or conflated with an ordinary value. `names[i] ?? 'unknown'` writes a default; `names[i] !== 'off'` answers `true` when the element is missing; `names.slice(i, i + 1).every((n) => n !== 'off')` answers `true` for the empty list. Each has the form `maybe z f (xs !? k)`: `z` where the read is missing, and `f` of the element where it is present. omelette proves it by finding a witness `maybe(family, z, x. f, read, has)` in an e-graph, where the family names the flow and `has` is the read's presence test.

The runtime is [`egg`](https://github.com/egraphs-good/egg) with `oxc_parser` and `oxc_semantic`, all in-process. The 73 golden cases in [tests/cases.txt](tests/cases.txt) reach saturation with their expected verdicts, and [tests/soundness.rs](tests/soundness.rs) holds the regressions from two soundness hunts. [docs/architecture.md](docs/architecture.md) describes the pipeline.

## Run and embed

`Cargo.toml` declares `rust-version = "1.97"`; development and the recorded benchmark use rustc 1.99.1.

```sh
cargo build --release
./target/release/omelette "names[i] ?? 'unknown'"
./target/release/omelette "names.slice(i, i + 1).every((n) => n !== 'off')"
./target/release/omelette 'users.map((_, i) => roles[i])' --all
./target/release/omelette --joint "names[i] !== 'off'" "names[i] === undefined || names[i] !== 'off'"
./scripts/check.sh
node scripts/differential.js FILE
cargo test --release
cargo run --release --example latency -- 500 --check
```

The command prints the verdict with its families, as in `verdict: CHEAT (sink)`. `--all` dumps every e-class. `--joint` saturates several expressions in one graph and prints the graph's consistency and each expression's class. Each free variable gets one precondition from its uses across all the expressions. In a consistent graph, a shared class proves the expressions equal. `scripts/check.sh` runs the golden cases and fails on a verdict mismatch, a run that did not saturate, or an inconsistent graph. `scripts/differential.js` evaluates closed expressions (one per line) in both omelette and Node. It fails on an inconsistent graph, or where omelette claims a value Node does not produce.

```rust
use omelette::core::Family;
use omelette::engine::{evaluate, initialize, Verdict};

initialize(); // Once at startup: rules, parser bootstrap, egg's clock calibration.
let result = evaluate("names[i] ?? 'unknown'").expect("valid expression");
assert_eq!(result.verdict, Verdict::Cheat);
assert_eq!(result.families, [Family::Default]);
```

`evaluate` parses, resolves symbols, lowers, saturates a new graph, checks consistency, and extracts a canonical term. Only the rewrite rules are shared between calls; egg's global symbol table also keeps every variable name and string it interns for the life of the process. It runs with a limit of 60 iterations, 10,000 e-nodes, and 50 ms; `evaluate_with_limits` takes a `Limits` value instead. These are cooperative bounds, not a real-time deadline. `parse_time` covers parsing, semantic analysis, and lowering. Setting `TRACE` to any value prints each iteration's graph size, search, apply, and rebuild time, and the rules applied. A syntax error, or source that is not a single expression, returns `Err`.

## Verdicts

Checked in this order:

1. `UNDECIDED` if the run did not saturate, or the graph is inconsistent: a class proven to hold two different constants, or an empty integer interval.
2. `CHEAT` if a witness or an escape shows a swallowed read. The families are reported. A witness counts when the root has no representative that avoids its class, its read is not proven in or out of range, and all of these hold:
   - its family swallows;
   - some witness of that class over that read has a replacement that is certainly a value, with no throw in it;
   - every representative of its present branch mentions the element, and some representative is free of unknown functions, unknown values, and unsupported syntax;
   - its present branch is not a non-empty list against an empty replacement;
   - the element it reads cannot itself be `undefined`.

   An escape of such a read whose replacement is still `undefined` is drift.
3. `UNDECIDED` if the answer depends on unknown inputs, or on something lowering does not model:
   - a witness's family is undecided, its replacement may itself be `undefined` or throw, its present branch holds an unknown, or the element it reads may itself be `undefined`;
   - a witness's present branch avoids the element only by reading the same free list another way, as in `xs[i] === undefined ? 0 : xs.slice(i, i + 1)[0]`, which may read that element;
   - lowering evaluated unsupported syntax, an unresolved call, a walker over an unknown callback, or a spread of a value of unknown type, anywhere in the expression;
   - such a construct reaches the result.
4. `no cheat` otherwise.

## What counts as a cheat

| Family | The missing read becomes | Examples |
| --- | --- | --- |
| `default` | a value the program wrote | `xs[i] ?? 0`, `xs[i] === undefined ? 0 : xs[i]`, `xs.length ? xs[xs.length - 1] : 0`, `[...a, 0][0]` |
| `unit` | the unit of a fold's monoid | `xs.slice(i, i + 1).every((x) => x > 0)` (`true`), `.some((x) => x > 0)` (`false`), `.join('')` (`''`), `.filter((x) => x > 0).length` (`0`), `xs.slice(i, j).reduce((_, x) => x, 0)` |
| `container` | an empty collection | `groups.slice(i, i + 1).flat()`, `.flatMap((g) => g)` |
| `sink` | what an operator makes of `undefined` | `names[i] === 'on'`, `names[i] !== 'off'`, `widths[i] < 3`, `widths[i] + 1`, `names[i] + '!'`, `` `${names[i]}` ``, `!names[i]` |
| `drift` | a hole in a collection shaped like another | `users.map((_, i) => roles[i])`, `names.map((n, i) => names[i + 1])` |

These are not cheats:

- the read reaches the result unchanged: `names[i]`, `names[i] && names[i] !== 'off'`;
- it stays visible in a container: `names.slice(i, i + 1).map((n) => n.length)`, `names[i] !== undefined ? [names[i]] : []`;
- its absence is observed rather than replaced: `names[i] === undefined`, `names.filter((_, k) => k === i).length === 0`, or a present branch that ignores the element;
- it throws when missing: `names[i].length`;
- the index is proven in range: `names.map((n, i) => names[i])`, `xs.map((x) => xs[0] ?? 0)`;
- the operation speaks for a whole list: `names.every((n) => n !== 'off')`, `names.join(', ')`.

Where an unknown decides the flow, the verdict is `UNDECIDED`. `names[i] === x` only tests presence when `x` is `undefined`. `xs.slice(i, i + 1).some(p)` does too when `p` always returns `true`, and it is constant when `p` always returns `false`.

## Model

The verdicts concern this model, not general JavaScript safety.

- **Free variables** get a precondition from how the expression uses them, looking through parentheses and type assertions.
  - A variable used as an index, a `slice` or `at` bound, an operand of `-`, `*`, unary `-`, or an ordering comparison, or compared with a walker callback's own index parameter, is an integer.
  - One used as a receiver or spread is a dense list whose elements are defined.
  - One that is called is a function.
  - Any other may be anything, including `undefined`.
- **Numbers** are integers. Symbolic integer arithmetic is assumed exact, so every intermediate value stays within 2^53 - 1 in magnitude. A value or term whose constant or coefficient lies beyond that is not folded, and non-integer literals are not modeled.
  - `+` concatenates when an operand is a string or a list, and otherwise adds integers and booleans.
  - An `undefined` or `NaN` operand makes arithmetic `NaN`.
  - Any other `+` is an uninterpreted operation that is never `undefined`.
- **Strings** compare by UTF-16 code units, and string ordering compares code units. Spread and array destructuring iterate code points.
- **Lists** compare by identity. A list built with `undefined` elements, such as `[undefined, ...ys]` or a map whose callback may return `undefined`, does not inherit the precondition's defined elements. A witness over such an element is `UNDECIDED`: a branch that varies only at the `undefined` element observes presence, and detection cannot separate that from a cheat. On a symbolic list, `map`, `filter`, `every`, `some`, `join`, `flat`, and `reduce` stay walker terms, except where lowering knows more:
  - a slice whose bounds differ by one, `slice(-1)`, or a filter that keeps exactly `list[j]` holds at most one element;
  - a `reduce` whose callback ignores its accumulator yields its value on the last element;
  - inside a walker's callback, reads at the walker's index of lists at least as long as the walked one, and at their first and last elements, are present.

  `flat` spreads an element of unknown type as if it may be a list.
- **Calls** to known functions inline with JavaScript's arity. Missing arguments are `undefined`, walkers pass (element, index, array), and `reduce` passes (accumulator, element, index, array). Calling a value that is not a function, passing one as a callback, or reading a property of `undefined` throws. A call to an unknown function, or a walker over one, is unresolved, and a fold whose seed may be missing is undecided.
- **Effects**: a throw is an effect, not a value. An array element, call operand, `const` initializer, or operator operand that throws makes the expression throw in that world, so a read that throws when missing is never swallowed. A walker's callback that throws on some element is the exception: the walker term stands for the list it would build.
- **Not modeled**, and `UNDECIDED` unless a witness elsewhere makes the expression a cheat:
  - records and property reads other than `length`, `Map`, optional chaining, and `null`;
  - loose equality, `typeof`, `in`, `instanceof`, `/`, `%`, `**`, bitwise operators, and unary `+`;
  - mutation, loops, `throw`, `let` and `var`, and statements other than `const`, `if`, blocks, and `return`;
  - named, async, and generator functions; rest parameters and rest elements; and `arguments`;
  - `flat` beyond depth one, `at` with an index of unknown sign, and `slice` of a literal list with symbolic bounds.

## Latency

[benchmarks/latency.txt](benchmarks/latency.txt) records each case's parser, parser-plus-lowering, and total quantiles from a release run with 500 samples per case. [benchmarks/environment.txt](benchmarks/environment.txt) records the host (an Intel Core i7-8700K), the toolchain, the protocol, and the command. Each case gets five warmups; samples interleave all 73 cases, and each reparses the source and builds a new graph. Totals include dropping the graph.

| Measurement | Result |
| --- | ---: |
| Worst per-case parser p95 | 4.0 us |
| Worst per-case parser + semantic analysis + lowering p95 | 32.1 us |
| Worst per-case total p95 / p99 | 489.3 / 663.9 us |
| Largest total among 36,500 samples | 787.8 us |
| Worst total p95: original / string / every / some cases | 489.3 / 349.4 / 161.5 / 178.7 us |
| Worst total p95: unknown-callback / join and flat cases | 44.1 / 150.3 us |
| Two-element slice sum total p50 / p95 | 40.5 / 66.1 us |
| All-case graph sizes / iterations | 1-76 / 1-8 |
| One-time runtime initialization | 818.1 us |
| First evaluation after initialization | 142.0 us |

The worst case is `[0, ...widths.slice(i, i + 1)].filter((_, k) => k === widths.slice(i, i + 1).length)[0]`. These are measured samples on this host, not scheduling guarantees. `--check` requires every case's parser and parser-plus-lowering p95 below 50 us, total p95 below 1 ms, and fewer than 150 e-nodes; the tests assert correctness and graph bounds without wall-clock thresholds.
