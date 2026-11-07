# omelette

This is an equality-saturation probe for absence laundering in TypeScript. Laundering is a total-typed expression that quietly turns a missing value into a default, such as `widths.slice(i, i + 1).reduce((_, x) => x, 0)`. The type checker sees `number` and has nothing to say. omelette tries to prove that the reader decomposes into `maybe(default, index?(xs, k))`, an absent read eliminated with a value the program wrote.

The pipeline has two parts:

- `frontend/dump.ts` lowers one TS expression to an S-expression. It works on syntax only and gives no node a meaning.
- `src/main.rs` saturates that S-expression with [egg](https://github.com/egraphs-good/egg) and runs the cheat query.

The rewrites carry the ECMAScript meaning of `slice`, `reduce`, `filter`, `??`, destructuring defaults and the rest. One e-class analysis tracks four things for each class: free variables, constants, integer intervals and an affine normal form for arithmetic. Because of that analysis, there are no commutativity or associativity rewrites.

## Run

```
cargo build --release
./target/release/egg-gate                                # the default cases
./target/release/egg-gate '<expr>' ['<expr>' ...]        # one run per expression
./target/release/egg-gate '<expr>' --all                 # print every e-class reachable from the root
./target/release/egg-gate --joint '<expr>' '<expr>' ...  # one e-graph; shows which roots share a class
```

The binary needs `node` on your PATH. The dumper loads TypeScript from `~/Git/GenomeHub/node_modules/typescript`, and you can set `TS_PATH` to point it somewhere else.

## Verdicts

- `CHEAT`: some class under the root holds `(maybe z m)`. `m` is an undetermined `index?` read, and `z` is a value the program wrote.
- `no cheat`: the run saturated, every node under the root has a meaning, and there was no finding.
- `UNDECIDED`: the run hit a limit, or some form under the root has no rule (an unknown method, an unresolved callee, unsupported syntax).

## Known limits

- Arithmetic is integer arithmetic, so `-0`, `NaN` and `Infinity` aren't modelled.
- Arrays are dense, records aren't modelled, and only straight-line blocks lower.
- A `filter` callback gets (element, index), not the array.
- Callees aren't resolved yet, so `somefn() ?? 0` is UNDECIDED until the dumper inlines the body of `somefn`.
