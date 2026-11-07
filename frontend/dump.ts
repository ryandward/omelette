// AST -> S-expression. Syntax only: every node becomes the S-expression of its own shape, and
// no node is given a meaning here. Bindings (parameters, destructuring, const) become `let`, the
// one desugaring a binder needs; what `slice`, `reduce`, `??` or a default mean is left to the
// rewrite rules in the engine.
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const ts = require(process.env.TS_PATH ?? `${process.env.HOME}/Git/GenomeHub/node_modules/typescript`);
const S = ts.SyntaxKind;

let fresh = 0;
const atom = (s: string) => (/^[A-Za-z_$][\w$]*$/.test(s) ? s : `"${s.replace(/"/g, "'")}"`);
const unknown = (n: any) => `(unknown ${atom(S[n.kind])})`;

// A binding pattern bound to `src`, wrapped around `body`.
function bind(pat: any, src: string, body: string): string {
  if (pat.kind === S.Identifier) return `(let ${atom(pat.text)} ${src} ${body})`;
  if (pat.kind === S.ArrayBindingPattern) {
    let out = body;
    pat.elements.forEach((el: any, k: number) => {
      if (el.kind === S.OmittedExpression) return;
      if (el.dotDotDotToken) { out = bind(el.name, `(mcall slice ${src} ${k})`, out); return; }
      const read = `(elem ${src} ${k})`;
      out = bind(el.name, el.initializer ? `(default ${read} ${expr(el.initializer)})` : read, out);
    });
    return out;
  }
  if (pat.kind === S.ObjectBindingPattern) {
    let out = body;
    for (const el of pat.elements) {
      const key = el.propertyName ? el.propertyName.text : el.name.text;
      const read = `(prop ${src} ${atom(key)})`;
      out = bind(el.name, el.initializer ? `(default ${read} ${expr(el.initializer)})` : read, out);
    }
    return out;
  }
  return unknown(pat);
}

function fn(n: any): string {
  let body = n.body.kind === S.Block ? block(n.body.statements, 0) : expr(n.body);
  for (const p of [...n.parameters].reverse()) {
    if (p.dotDotDotToken) return unknown(p);
    if (p.name.kind === S.Identifier && !p.initializer) { body = `(lam ${atom(p.name.text)} ${body})`; continue; }
    const v = `$p${fresh++}`;
    const src = p.initializer ? `(default (var ${v}) ${expr(p.initializer)})` : `(var ${v})`;
    body = `(lam ${v} ${bind(p.name, src, body)})`;
  }
  return n.parameters.length ? body : `(lam $unit ${body})`;
}

// Straight-line blocks: const declarations, if/return, return.
function block(sts: any[], i: number): string {
  const st = sts[i];
  if (!st) return 'undef';
  if (st.kind === S.ReturnStatement) return st.expression ? expr(st.expression) : 'undef';
  if (st.kind === S.VariableStatement && st.declarationList.flags & ts.NodeFlags.Const) {
    let rest = block(sts, i + 1);
    for (const d of [...st.declarationList.declarations].reverse()) rest = bind(d.name, expr(d.initializer), rest);
    return rest;
  }
  if (st.kind === S.IfStatement) {
    const then = st.thenStatement.kind === S.Block ? block(st.thenStatement.statements, 0) : block([st.thenStatement], 0);
    const els = st.elseStatement ? (st.elseStatement.kind === S.Block ? block(st.elseStatement.statements, 0) : block([st.elseStatement], 0)) : block(sts, i + 1);
    return `(if (truthy ${expr(st.expression)}) ${then} ${els})`;
  }
  return unknown(st);
}

function expr(n: any): string {
  switch (n.kind) {
    case S.ParenthesizedExpression: case S.AsExpression: case S.SatisfiesExpression: case S.NonNullExpression:
      return expr(n.expression);
    case S.NumericLiteral: return n.text;
    case S.TrueKeyword: return 'true';
    case S.FalseKeyword: return 'false';
    case S.Identifier: return n.text === 'undefined' ? 'undef' : `(var ${atom(n.text)})`;
    case S.PrefixUnaryExpression:
      if (n.operator === S.MinusToken) return n.operand.kind === S.NumericLiteral ? `-${n.operand.text}` : `(neg ${expr(n.operand)})`;
      if (n.operator === S.ExclamationToken) return `(! (truthy ${expr(n.operand)}))`;
      return unknown(n);
    case S.BinaryExpression: {
      const l = expr(n.left), r = expr(n.right);
      switch (n.operatorToken.kind) {
        case S.PlusToken: return `(+ ${l} ${r})`;
        case S.MinusToken: return `(- ${l} ${r})`;
        case S.AsteriskToken: return `(* ${l} ${r})`;
        case S.LessThanToken: return `(< ${l} ${r})`;
        case S.GreaterThanToken: return `(< ${r} ${l})`;
        case S.LessThanEqualsToken: return `(<= ${l} ${r})`;
        case S.GreaterThanEqualsToken: return `(<= ${r} ${l})`;
        case S.EqualsEqualsEqualsToken: return `(=== ${l} ${r})`;
        case S.ExclamationEqualsEqualsToken: return `(! (=== ${l} ${r}))`;
        case S.AmpersandAmpersandToken: return `(&& (truthy ${l}) (truthy ${r}))`;
        case S.BarBarToken: return `(|| (truthy ${l}) (truthy ${r}))`;
        case S.QuestionQuestionToken: return `(coalesce ${l} ${r})`;
      }
      return unknown(n);
    }
    case S.ConditionalExpression: return `(if (truthy ${expr(n.condition)}) ${expr(n.whenTrue)} ${expr(n.whenFalse)})`;
    case S.PropertyAccessExpression: return `(prop ${expr(n.expression)} ${atom(n.name.text)})`;
    case S.ElementAccessExpression: return `(elem ${expr(n.expression)} ${expr(n.argumentExpression)})`;
    case S.ArrayLiteralExpression: {
      let acc = 'nil';
      for (const e of [...n.elements].reverse()) acc = e.kind === S.SpreadElement ? `(arr-spread ${expr(e.expression)} ${acc})` : `(arr-cons ${expr(e)} ${acc})`;
      return acc;
    }
    case S.ArrowFunction: case S.FunctionExpression: return fn(n);
    case S.CallExpression: {
      const args = n.arguments.map(expr);
      if (n.expression.kind === S.PropertyAccessExpression) {
        return `(mcall ${atom(n.expression.name.text)} ${expr(n.expression.expression)}${args.map((a: string) => ' ' + a).join('')})`;
      }
      let f = expr(n.expression);
      if (args.length === 0) return `(app ${f} undef)`;
      for (const a of args) f = `(app ${f} ${a})`;
      return f;
    }
  }
  return unknown(n);
}

const src = process.argv[2];
const sf = ts.createSourceFile('x.ts', `const __r = (${src});`, ts.ScriptTarget.ES2022, true);
const init = (sf.statements[0] as any).declarationList.declarations[0].initializer;
console.log(expr(init));
