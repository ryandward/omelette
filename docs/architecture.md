# Architecture

## The question

A cheat is an information flow in which a read that may be missing is quietly swallowed or conflated with an ordinary value. The README lists the families: `default`, `unit`, `container`, `sink`, and `drift`. The first four leave a witness of the form `maybe z f (xs !? k)`: `z` where the read is missing, and `f` of the element where it is present. Drift leaves an `escape`: a read whose index came from another collection's walker, left as a possible hole in a mapped result.

## Pipeline

```
source --oxc_parser--> AST --oxc_semantic--> symbols, references, AST nodes
       --lower (partial evaluation)--> core IR
       --egg (equational saturation)--> classes --> witnesses --> verdict
```

Lowering decides every question of JavaScript's operational semantics: coercion, arity, method dispatch, statement control flow, and which operations are even modeled. The core IR is a small language with its own meaning, and egg proves equalities in that language only. Some of that meaning mirrors JavaScript where lowering needs it to: `eq` is strict equality, so `NaN` is unequal to itself; `text` is the text `join` writes for an element; and a `read` outside a list's bounds is `undefined`.

## Lowering: src/lower

A partial evaluator over a static value domain (`value.rs`):

- **Known values**: integers (affine forms with no atoms), `NaN`, strings as UTF-16 code units, booleans, `undefined`, a thrown error, lists of known length, and functions (parameters, body, and the bindings they closed over).
- **Symbolic values**: a core term with a static type: integer (an affine form over atoms), boolean, string, list, defined, or possibly undefined.
- **Splits**: a value that depends on whether one read is present. A read of a symbolic list at an index not proven in range lowers to a split whose absent side is `undefined` and whose present side is the read's element binder. Every split on one read shares one binder.
- **Short lists**: a symbolic list of at most one element, from a slice whose bounds differ by one, `slice(-1)`, or a filter whose predicate is `index === j` (a projection), with its element slot, the element's value, and whether a filter keeps it.

Operations are typed (`ops.rs`). Integer arithmetic stays affine. `+` concatenates when an operand is a string, coerces booleans, and gives `NaN` for an `undefined` or `NaN` operand. Ordering against `undefined` is `false`. An operation on values of unknown type becomes an uninterpreted `dyn` term that is never `undefined`. The one exception is `x ?? y` of an unknown `x` with a fallback that may itself be `undefined`, which becomes `dyn?`.

Every operation lifts over splits: it applies on both sides. A split's family is the last operation that wrote its absent side, with two qualifications. An operation that only passes values through (a read, `length`, a spread) keeps the family it was given. An undecided step, `===` against or `??` toward an unknown, leaves the whole chain undecided, since for some value of the unknown the chain only tests presence. Branches (`expr.rs`) lower each arm in every world of the splits in their test, with the split's read narrowed to missing or to its element. Presence tests, `&&`, `||`, and `??` all narrow this way.

Calls (`calls.rs`) inline known functions with JavaScript's arity, and run statement lists to their first `return`, so a branch that does not return continues with the statements after it. Methods dispatch on what lowering knows about the receiver:

- a literal list unrolls `map`, `find`, `every`, `some`, `reduce`, `join`, `flat`, `flatMap`, `slice`, `at`, and `concat`, and unrolls `filter` when every element's keep is known;
- a short list yields a split whose absent side is the method's unit: `true` for `every`, `false` for `some`, `''` for `join`, `[]` for `flat` and `flatMap`, the initial value for `reduce` (a throw without one), and `0` for a filtered count;
- a symbolic list yields a term: `map`, `filter`, `every`, `some`, and `reduce` (as `fold`) carry their callback, lowered once with fresh element and index binders, and `join` and `flat` take the list alone.

Before falling back to a term, lowering recognizes a filter or find whose predicate is `index === j` with `j` an integer, and a `reduce` whose callback ignores its accumulator. A callback that ignores its accumulator yields its value on the last element. Without an initial value, a one-element list returns that element without calling the callback, so the law then also requires the callback to return its element. Reading a mapped list applies its callback to the underlying read.

`oxc_semantic` provides symbol identity for inlining and for recognizing a projection's index parameter, and `usage.rs` uses its node tree to give each free variable its precondition, looking through parentheses and type assertions. A walker's index binder records the list it ranges over: reading that list at that binder is proven in range, and reading anything else at a coordinate derived from it is marked as drift. When a drift read reaches a map's result unreplaced, it is emitted as `escape`.

A split leaves lowering as `maybe(family, z, x. f, read)`, or as the read itself when nothing happened to it. When the family swallows but the present side does not mention the element, the family becomes `observe`.

## Core IR: src/core.rs

A typed `egg::define_language!` enum:

- constants, including `throw` and the tagged `unsupported`;
- canonical affine sums (`lin`), products of atoms (`mul`), integer order (`le`, `lt`), and booleans;
- strict equality (`eq`), strings (`concat`, and `text`);
- lists (`nil`, `cons`, `append`, `slice`, `len`);
- walkers over symbolic lists (`map`, `filter`, `every`, `some`, `fold` with bound callbacks; `join` and `flat`);
- reads that may be missing (`read`) and reads proven in range (`at`);
- witnesses (`maybe`), their untagged values (`elim`), and drift escapes (`escape`);
- `dyn`, `dyn?`, and `call`.

egg never substitutes into a lambda.

## egg: src/engine

The analysis (`analysis.rs`) tracks known constants and integer bounds: lengths are non-negative, a walker index is non-negative, a slice holds at most its bound difference, and a conditional lies between its branches. A class proven to hold two constants, or an empty interval, marks the graph inconsistent. The rules (`rules.rs`) are:

- boolean and conditional identities, and the normal forms `a < b` as `0 <= b - a - 1` and `a <= b` as `0 <= b - a`, with sums kept in canonical order;
- `read(xs, k)` expands to `if(0 <= k and k < len(xs), at(xs, k), undefined)`, and `at(cons(h, t), 0)` is `h`;
- list identities: lengths of `nil`, `cons`, `append`, and `map`, and appends of `nil` and `cons`;
- `[...a, z][0]` is `maybe(default, z, id, a[0])`, and `[z, ...xs][xs.length]` is `maybe(default, z, id, xs[len - 1])`;
- presence context: in `maybe(family, z, x. f, r)` where `z`, or the body of `f`, is a conditional whose test is `r`'s presence test, that conditional is its else branch in `z` and its then branch in `f`; a witness over a read proven missing is its `z`;
- every `maybe` implies the untagged `elim` of the same value, so spellings that reach one value through different flows share a class.

Detection (`detect.rs`) walks the classes reachable from the root and judges each class's witnesses together, one group per read. Witnesses in one class over one read denote one value: their replacements agree where the read is missing, and their present branches agree on every element. A proof from one representative therefore holds for the whole group: that the branch ignores the element, that it is free of unknowns, or that the replacement is certainly a value. The README's verdict section states the conditions.

## Code shape

`Cargo.toml` and `clippy.toml` deny pedantic Clippy findings and dead code, and cap functions at 60 lines, cognitive complexity at 15, and arguments at 5.
