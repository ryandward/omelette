# Architecture

## The question

A cheat is an information flow in which a read that may be missing is quietly swallowed or conflated with an ordinary value. The families are listed in the README: `default`, `unit`, `container`, `sink`, and `drift`. Every one is a witness of the form `maybe z f (xs !? k)`: `z` where the read is missing, and `f` of the element where it is present.

## Pipeline

```
source --oxc_parser--> AST --oxc_semantic--> symbols, references, AST nodes
       --lower (partial evaluation, all JavaScript semantics)--> core IR
       --egg (equational saturation, no JavaScript semantics)--> classes --> witnesses --> verdict
```

The boundary is hard: lowering decides every question of JavaScript's operational semantics, and egg only proves equalities between core terms.

## Lowering: src/lower

A partial evaluator over a static value domain (`value.rs`):

- **Known values**: integers (affine forms with no atoms), `NaN`, strings as UTF-16 code units, booleans, `undefined`, lists of known length, and functions (parameters, body, and the bindings they closed over).
- **Symbolic values**: a core term with a static type: integer (an affine form over atoms), boolean, string, list, defined, or possibly undefined.
- **Splits**: a value that depends on whether one read is present. A read of a symbolic list at an index not proven in range lowers to a split whose absent side is `undefined` and whose present side is the read's element binder. Every split on one read shares one binder.
- **Short lists**: a symbolic list of at most one element (a slice whose bounds differ by one, or a filter that keeps exactly `list[j]`), with its element slot, the element's value, and whether a filter keeps it.

Operations are typed (`ops.rs`): integer arithmetic stays affine, string `+` concatenates, ordering on `undefined` is `false`, and anything of unknown type becomes an uninterpreted `dyn` term that is never `undefined`. Every operation lifts over splits: it applies on both sides, and a split records as its family the last operation that changed its absent side. Branches (`expr.rs`) lower each arm in every world of the splits in their test, with the split's read narrowed to missing or to its element. Presence tests, `&&`, `||`, and `??` all narrow this way.

Calls (`calls.rs`) inline known functions with JavaScript's arity, and run statement lists to their first `return`, so a branch that does not return continues with the statements after it. Methods dispatch on what lowering knows about the receiver:

- a literal list unrolls (`map`, `filter`, `find`, `every`, `some`, `reduce`, `join`, `flat`, `flatMap`, `slice`, `at`, `concat`);
- a short list yields a split whose absent side is the method's unit: `true` for `every`, `false` for `some`, `''` for `join`, `[]` for `flat`, the initial value for `reduce`, and `0` for a filtered count;
- a symbolic list yields a walker term whose callback is lowered once with fresh element and index binders.

Before falling back to a walker term, lowering recognizes a filter or find whose predicate is `index === j` with `j` an integer (a projection), and a `reduce` whose callback ignores its accumulator (the last element). Reading a mapped list applies its callback to the underlying read.

`oxc_semantic` provides symbol identity for inlining and for recognizing a projection's index parameter, and `usage.rs` uses its node tree to give each free variable its precondition. A walker's index binder records the list it ranges over: reading that list at that binder is proven in range, and reading anything else at a coordinate derived from it is marked as drift. When a drift read reaches a map's result unreplaced, it is emitted as `escape`.

A split leaves lowering as `maybe(family, z, x. f, read)`, or as the read itself when nothing happened to it. When the present side does not mention the element, the family becomes `observe`.

## Core IR: src/core.rs

A typed `egg::define_language!` enum:

- constants;
- canonical affine sums (`lin`), integer order (`le`, `lt`), and booleans;
- strings (`concat`, and `text`, the text `join` writes for an element);
- lists (`nil`, `cons`, `append`, `slice`, `len`);
- walkers over symbolic lists with bound callbacks (`map`, `filter`, `every`, `some`, `fold`, `join`, `flat`);
- reads that may be missing (`read`) and reads proven in range (`at`);
- witnesses (`maybe`), their untagged values (`elim`), and drift escapes (`escape`);
- `dyn`, `call`, and `unsupported`.

egg never substitutes.

## egg: src/engine

The analysis tracks only known constants and integer bounds (lengths are non-negative, a walker index is non-negative, and a slice holds at most its bound difference). The rules (`rules.rs`) are:

- boolean and conditional identities, and the normal forms `a < b` as `0 <= b - a - 1` and `a <= b` as `0 <= b - a`, with sums kept in canonical order;
- `read(xs, k)` expands to `if(0 <= k and k < len(xs), at(xs, k), undefined)`;
- list identities: lengths of `nil`, `cons`, `append`, and `map`, and appends of `nil` and `cons`;
- `[...a, z][0]` is `maybe(default, z, id, a[0])`, and `[z, ...xs][xs.length]` is `maybe(default, z, id, xs[len - 1])`;
- presence context: inside `maybe(family, z, x. f, r)`, a condition that is `r`'s presence test is `true` in `f` and `false` in `z`; a witness over a read proven missing is its `z`;
- every `maybe` implies the untagged `elim` of the same value, so spellings that reach one value through different flows share a class.

Detection (`detect.rs`) walks the classes reachable from the root, as the README's verdict section states.

## Code shape

`Cargo.toml` and `clippy.toml` deny pedantic Clippy findings and dead code, and cap functions at 60 lines, cognitive complexity at 15, and arguments at 5.
