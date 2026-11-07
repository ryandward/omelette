//! Native lowering with affine arithmetic normalization and fresh binding names.
use egg::{Id, Language, RecExpr, SymbolLang};
use oxc_allocator::Allocator;
use oxc_ast::ast::*;
use oxc_parser::Parser;
use oxc_span::SourceType;
use oxc_syntax::operator::{BinaryOperator as B, LogicalOperator as L, UnaryOperator as U};
use std::fmt::Write;

pub fn parse(source: &str) -> Result<RecExpr<SymbolLang>, String> {
    let arena = Allocator::default();
    let ast = Parser::new(&arena, source, SourceType::ts())
        .parse_expression()
        .map_err(|errors| format!("{errors:?}"))?;
    let mut lower = Lower::default();
    let root = lower.expr(&ast);
    Ok(lower.out[root].build_recexpr(|id| lower.out[id].clone()))
}

#[derive(Default)]
struct Lower {
    out: RecExpr<SymbolLang>,
    scope: Vec<(String, Id)>,
    fresh: usize,
    intern: std::collections::HashMap<SymbolLang, Id>,
}
impl Lower {
    fn node(&mut self, op: &str, children: impl Into<Vec<Id>>) -> Id {
        let children = children.into();
        if matches!(op, "Add" | "Sub" | "Neg" | "Mul" | "Lt" | "Le")
            && children.iter().any(|&id| self.is_string(id))
        {
            // JavaScript + concatenates when either operand is a string. It cannot
            // share the commutative affine representation used for integer indices.
            return if op == "Add" {
                self.intern_node(SymbolLang::new("Concat", children))
            } else {
                self.unknown() // String-to-number coercions/order are outside this model.
            };
        }
        if matches!(op, "Add" | "Sub" | "Neg" | "Mul") {
            let a = self.form(children[0]);
            let form = if op == "Mul" {
                let b = self.form(children[1]);
                if a.terms.is_empty() {
                    crate::affine::Form::default().plus(&b, a.constant)
                } else if b.terms.is_empty() {
                    crate::affine::Form::default().plus(&a, b.constant)
                } else {
                    None
                }
            } else if op == "Neg" {
                crate::affine::Form::default().plus(&a, -1)
            } else {
                a.plus(&self.form(children[1]), if op == "Sub" { -1 } else { 1 })
            };
            if let Some(f) = form {
                if f.terms.is_empty() {
                    return self.num(f.constant);
                }
                if f.constant == 0 && f.terms.len() == 1 && f.terms.values().next() == Some(&1) {
                    return *f.terms.keys().next().unwrap();
                }
                // Stable structural ordering also makes separately lowered permutations identical.
                let mut terms: Vec<_> = f
                    .terms
                    .into_iter()
                    .map(|(id, c)| {
                        let key = self.out[id]
                            .build_recexpr(|id| self.out[id].clone())
                            .to_string();
                        (key, id, c)
                    })
                    .collect();
                terms.sort_by(|a, b| a.0.cmp(&b.0));
                let mut op = format!("Lin:{}", f.constant);
                let mut children = Vec::with_capacity(terms.len());
                for (_, id, c) in terms {
                    op.push_str(&format!(":{c}"));
                    children.push(id);
                }
                return self.intern_node(SymbolLang::new(op, children));
            }
        }
        self.intern_node(SymbolLang::new(op, children))
    }
    fn is_string(&self, id: Id) -> bool {
        let n = &self.out[id];
        match n.op.as_str() {
            "Str" | "Concat" => true,
            "Coalesce" | "Default" => n.children.iter().all(|&id| self.is_string(id)),
            "If" => n.children[1..].iter().all(|&id| self.is_string(id)),
            "Let" => self.is_string(n.children[2]),
            _ => false,
        }
    }
    fn intern_node(&mut self, n: SymbolLang) -> Id {
        if let Some(&id) = self.intern.get(&n) {
            return id;
        }
        let id = self.out.add(n.clone());
        self.intern.insert(n, id);
        id
    }
    fn form(&self, id: Id) -> crate::affine::Form {
        let n = &self.out[id];
        if n.op.as_str() == "Num" {
            return crate::affine::Form::constant(
                self.out[n.children[0]].op.as_str().parse().unwrap(),
            );
        }
        crate::affine::Form::decode(n).unwrap_or_else(|| crate::affine::Form::atom(id))
    }
    fn leaf(&mut self, op: &str) -> Id {
        self.node(op, vec![])
    }
    fn unknown(&mut self) -> Id {
        self.leaf("Unknown")
    }
    fn num(&mut self, n: i64) -> Id {
        let n = self.leaf(&n.to_string());
        self.node("Num", vec![n])
    }
    fn name(&mut self) -> Id {
        let name = format!("@{}", self.fresh);
        self.fresh += 1;
        self.leaf(&name)
    }
    fn declare(&mut self, p: &BindingPattern<'_>) {
        match p {
            BindingPattern::BindingIdentifier(p) => {
                let n = self.name();
                self.scope.push((p.name.to_string(), n));
            }
            BindingPattern::AssignmentPattern(p) => self.declare(&p.left),
            BindingPattern::ArrayPattern(p) => {
                for p in p.elements.iter().flatten() {
                    self.declare(p);
                }
                if let Some(p) = &p.rest {
                    self.declare(&p.argument);
                }
            }
            BindingPattern::ObjectPattern(p) => {
                for p in &p.properties {
                    self.declare(&p.value);
                }
            }
        }
    }
    fn bind(&mut self, p: &BindingPattern<'_>, src: Id, body: Id) -> Id {
        match p {
            BindingPattern::BindingIdentifier(p) => {
                let n = self
                    .scope
                    .iter()
                    .rev()
                    .find(|(n, _)| n == p.name.as_str())
                    .unwrap()
                    .1;
                self.node("Let", vec![n, src, body])
            }
            BindingPattern::AssignmentPattern(p) => {
                let d = self.expr(&p.right);
                let src = self.node("Default", vec![src, d]);
                self.bind(&p.left, src, body)
            }
            BindingPattern::ArrayPattern(p) => {
                let mut body = body;
                if let Some(rest) = &p.rest {
                    let k = self.num(p.elements.len() as i64);
                    let m = self.leaf("slice");
                    let r = self.node("MCall1", vec![m, src, k]);
                    body = self.bind(&rest.argument, r, body);
                }
                for (i, p) in p.elements.iter().enumerate().rev() {
                    if let Some(p) = p {
                        let k = self.num(i as i64);
                        let r = self.node("Elem", vec![src, k]);
                        body = self.bind(p, r, body);
                    }
                }
                body
            }
            BindingPattern::ObjectPattern(p) => {
                if p.rest.is_some() {
                    return self.unknown();
                }
                let mut body = body;
                for p in p.properties.iter().rev() {
                    if p.computed {
                        return self.unknown();
                    }
                    let Some(key) = p.key.static_name() else {
                        return self.unknown();
                    };
                    let key = self.leaf(key.as_str().unwrap_or("unsupported-property"));
                    let r = self.node("Prop", vec![src, key]);
                    body = self.bind(&p.value, r, body);
                }
                body
            }
        }
    }
    fn function(
        &mut self,
        params: &FormalParameters<'_>,
        body: Option<&FunctionBody<'_>>,
        expression: Option<&Expression<'_>>,
    ) -> Id {
        if params.rest.is_some() {
            return self.unknown();
        }
        let mark = self.scope.len();
        for p in &params.items {
            self.declare(&p.pattern);
        }
        let mut result = if let Some(e) = expression {
            self.expr(e)
        } else {
            self.block(&body.unwrap().statements)
        };
        if params.items.is_empty() {
            let n = self.name();
            result = self.node("Lam", vec![n, result]);
        }
        for p in params.items.iter().rev() {
            if p.initializer.is_none()
                && let BindingPattern::BindingIdentifier(id) = &p.pattern
            {
                let n = self
                    .scope
                    .iter()
                    .rev()
                    .find(|(n, _)| n == id.name.as_str())
                    .unwrap()
                    .1;
                result = self.node("Lam", vec![n, result]);
                continue;
            }
            let n = self.name();
            let mut arg = self.node("Var", vec![n]);
            if let Some(init) = &p.initializer {
                let d = self.expr(init);
                arg = self.node("Default", vec![arg, d]);
            }
            result = self.bind(&p.pattern, arg, result);
            result = self.node("Lam", vec![n, result]);
        }
        self.scope.truncate(mark);
        result
    }
    fn block(&mut self, stmts: &[Statement<'_>]) -> Id {
        let Some((first, rest)) = stmts.split_first() else {
            return self.leaf("Undef");
        };
        match first {
            Statement::ReturnStatement(s) => match &s.argument {
                Some(e) => self.expr(e),
                None => self.leaf("Undef"),
            },
            Statement::VariableDeclaration(s) if s.kind == VariableDeclarationKind::Const => {
                let mark = self.scope.len();
                let mut binds = vec![];
                for d in &s.declarations {
                    let Some(init) = &d.init else {
                        return self.unknown();
                    };
                    let value = self.expr(init);
                    self.declare(&d.id);
                    binds.push((&d.id, value));
                }
                let mut out = self.block(rest);
                for (p, v) in binds.into_iter().rev() {
                    out = self.bind(p, v, out);
                }
                self.scope.truncate(mark);
                out
            }
            Statement::IfStatement(s) => {
                let c = self.expr(&s.test);
                let c = self.node("Truthy", vec![c]);
                let a = self.block(std::slice::from_ref(&s.consequent));
                let b = if let Some(b) = &s.alternate {
                    self.block(std::slice::from_ref(b))
                } else {
                    self.block(rest)
                };
                self.node("If", vec![c, a, b])
            }
            Statement::BlockStatement(s) => self.block(&s.body),
            _ => self.unknown(),
        }
    }
    fn expr(&mut self, e: &Expression<'_>) -> Id {
        match e {
            Expression::ParenthesizedExpression(e) => self.expr(&e.expression),
            Expression::TSAsExpression(e) => self.expr(&e.expression),
            Expression::TSSatisfiesExpression(e) => self.expr(&e.expression),
            Expression::TSNonNullExpression(e) => self.expr(&e.expression),
            Expression::NumericLiteral(n)
                if n.value.is_finite()
                    && n.value.fract() == 0.0
                    && n.value.abs() <= 9_007_199_254_740_991.0 =>
            {
                self.num(n.value as i64)
            }
            Expression::BooleanLiteral(n) => {
                let b = self.leaf(if n.value { "true" } else { "false" });
                self.node("B", vec![b])
            }
            Expression::StringLiteral(n) => {
                // Key by decoded UTF-16 code units, including lone surrogates.
                // Raw spelling and lossy Unicode display are not string identity.
                let mut value = String::from("utf16:");
                for unit in n.value.encode_utf16() {
                    write!(&mut value, "{unit:04x}").unwrap();
                }
                let value = self.leaf(&value);
                self.node("Str", vec![value])
            }
            Expression::Identifier(n) => {
                if let Some((_, id)) = self.scope.iter().rev().find(|(s, _)| s == n.name.as_str()) {
                    let id = *id;
                    return self.node("Var", vec![id]);
                }
                if n.name == "undefined" {
                    return self.leaf("Undef");
                }
                let n = self.leaf(&format!("free:{}", n.name));
                self.node("Var", vec![n])
            }
            Expression::UnaryExpression(e) => {
                let a = self.expr(&e.argument);
                match e.operator {
                    U::UnaryNegation => self.node("Neg", vec![a]),
                    U::LogicalNot => {
                        let a = self.node("Truthy", vec![a]);
                        self.node("Not", vec![a])
                    }
                    _ => self.unknown(),
                }
            }
            Expression::BinaryExpression(e) => {
                let a = self.expr(&e.left);
                let b = self.expr(&e.right);
                let (op, args) = match e.operator {
                    B::Addition => ("Add", vec![a, b]),
                    B::Subtraction => ("Sub", vec![a, b]),
                    B::Multiplication => ("Mul", vec![a, b]),
                    B::LessThan => ("Lt", vec![a, b]),
                    B::LessEqualThan => ("Le", vec![a, b]),
                    B::GreaterThan => ("Lt", vec![b, a]),
                    B::GreaterEqualThan => ("Le", vec![b, a]),
                    B::StrictEquality | B::StrictInequality => ("StrictEq", vec![a, b]),
                    _ => return self.unknown(),
                };
                let result = self.node(op, args);
                if e.operator == B::StrictInequality {
                    self.node("Not", vec![result])
                } else {
                    result
                }
            }
            Expression::LogicalExpression(e) => {
                let mut a = self.expr(&e.left);
                let mut b = self.expr(&e.right);
                if e.operator != L::Coalesce {
                    a = self.node("Truthy", vec![a]);
                    b = self.node("Truthy", vec![b]);
                }
                self.node(
                    match e.operator {
                        L::And => "And",
                        L::Or => "Or",
                        L::Coalesce => "Coalesce",
                    },
                    vec![a, b],
                )
            }
            Expression::ConditionalExpression(e) => {
                let c = self.expr(&e.test);
                let c = self.node("Truthy", vec![c]);
                let a = self.expr(&e.consequent);
                let b = self.expr(&e.alternate);
                self.node("If", vec![c, a, b])
            }
            Expression::StaticMemberExpression(e) if !e.optional => {
                let a = self.expr(&e.object);
                let p = self.leaf(e.property.name.as_str());
                self.node("Prop", vec![a, p])
            }
            Expression::ComputedMemberExpression(e) if !e.optional => {
                let a = self.expr(&e.object);
                let b = self.expr(&e.expression);
                self.node("Elem", vec![a, b])
            }
            Expression::ArrayExpression(e) => {
                let mut out = self.leaf("Nil");
                for e in e.elements.iter().rev() {
                    let (op, a) = match e {
                        ArrayExpressionElement::SpreadElement(e) => {
                            ("ArrSpread", self.expr(&e.argument))
                        }
                        _ => match e.as_expression() {
                            Some(e) => ("ArrCons", self.expr(e)),
                            None => return self.unknown(),
                        },
                    };
                    out = self.node(op, vec![a, out]);
                }
                out
            }
            Expression::ArrowFunctionExpression(e) if !e.r#async => match &e.body {
                ArrowFunctionBody::FunctionBody(b) => self.function(&e.params, Some(b), None),
                b => self.function(&e.params, None, b.as_expression()),
            },
            Expression::FunctionExpression(e) if !e.r#async && !e.generator && e.id.is_none() => {
                match &e.body {
                    Some(b) => self.function(&e.params, Some(b), None),
                    None => self.unknown(),
                }
            }
            Expression::CallExpression(e) if !e.optional => {
                let mut args = vec![];
                for a in &e.arguments {
                    if let Some(a) = a.as_expression() {
                        args.push(self.expr(a));
                    } else {
                        return self.unknown();
                    }
                }
                if let Expression::StaticMemberExpression(m) = &e.callee {
                    if m.optional || args.len() > 2 {
                        return self.unknown();
                    }
                    let name = self.leaf(m.property.name.as_str());
                    let obj = self.expr(&m.object);
                    let op = format!("MCall{}", args.len());
                    let mut all = vec![name, obj];
                    all.extend(args);
                    self.node(&op, all)
                } else {
                    let mut f = self.expr(&e.callee);
                    if args.is_empty() {
                        args.push(self.leaf("Undef"));
                    }
                    for a in args {
                        f = self.node("App", vec![f, a]);
                    }
                    f
                }
            }
            _ => self.unknown(),
        }
    }
}
