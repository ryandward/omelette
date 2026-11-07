//! Expressions: symbols, operators, branches, and literals.
use super::Lowerer;
use super::ops::Bin;
use super::value::{Body, Fun, RefKey, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Kind, Utf16};
use egg::Id;
use oxc_ast::ast::{
    ArrayExpression, ArrayExpressionElement, BinaryExpression, ConditionalExpression, Expression,
    IdentifierReference, LogicalExpression, Statement, TemplateLiteral, UnaryExpression,
};
use oxc_syntax::operator::{BinaryOperator, LogicalOperator, UnaryOperator};
use std::rc::Rc;

/// A branch to lower once per world: an expression, the statements left to run, or a
/// lowered value.
#[derive(Clone, Copy)]
pub enum Arm<'a, 'v> {
    Expr(&'a Expression<'a>),
    Run(&'v [&'a Statement<'a>]),
    Val(&'v Val<'a>),
}

impl<'a> Lowerer<'a, '_> {
    pub fn expr(&mut self, e: &'a Expression<'a>) -> Val<'a> {
        match e {
            Expression::ParenthesizedExpression(p) => self.expr(&p.expression),
            Expression::TSAsExpression(t) => self.expr(&t.expression),
            Expression::TSSatisfiesExpression(t) => self.expr(&t.expression),
            Expression::TSNonNullExpression(t) => self.expr(&t.expression),
            Expression::NumericLiteral(n) => integer(n.value).map_or_else(|| self.unsupported(), Val::int),
            Expression::StringLiteral(s) => Val::Str(Utf16::new(s.value.encode_utf16())),
            Expression::BooleanLiteral(b) => Val::Bool(b.value),
            Expression::TemplateLiteral(t) => self.template(t),
            Expression::Identifier(id) => self.ident(id),
            Expression::UnaryExpression(u) => self.unary(u),
            Expression::BinaryExpression(b) => self.binop(b),
            Expression::LogicalExpression(l) => self.logical(l),
            Expression::ConditionalExpression(c) => self.conditional(c),
            Expression::ArrayExpression(a) => self.array(a),
            Expression::StaticMemberExpression(m) if !m.optional => {
                let object = self.expr(&m.object);
                self.property(object, m.property.name.as_str())
            }
            Expression::ComputedMemberExpression(m) if !m.optional => {
                let (object, index) = (self.expr(&m.object), self.expr(&m.expression));
                self.read(object, index)
            }
            Expression::ArrowFunctionExpression(f) if !f.r#async => match arrow_body(f) {
                Some(body) => self.closure(&f.params, body),
                None => self.unsupported(),
            },
            Expression::FunctionExpression(f) if !f.r#async && !f.generator && f.id.is_none() => match &f.body {
                Some(b) => self.closure(&f.params, Body::Block(b)),
                None => self.unsupported(),
            },
            Expression::CallExpression(c) if !c.optional => self.call(c),
            Expression::AssignmentExpression(a) => self.assignment(a),
            Expression::UpdateExpression(u) => self.increment(u),
            Expression::SequenceExpression(s) => self.sequence(&s.expressions),
            _ => self.unsupported(),
        }
    }
    /// `a, b, c`: each in turn, so one that throws stops the rest; the last one's value.
    fn sequence(&mut self, exprs: &'a [Expression<'a>]) -> Val<'a> {
        let Some((first, rest)) = exprs.split_first() else { return Val::Undef };
        let v = self.expr(first);
        if rest.is_empty() {
            return v;
        }
        self.strict(vec![v], &mut |l, _| l.sequence(rest))
    }
    pub fn unsupported(&mut self) -> Val<'a> {
        self.clobber();
        Val::Term(self.b.unsupported(), Ty::Any)
    }
    fn closure(&mut self, params: &'a oxc_ast::ast::FormalParameters<'a>, body: Body<'a>) -> Val<'a> {
        let env = self.env.clone();
        Val::Fun(Rc::new(Fun { params, body, env }))
    }
    fn ident(&mut self, id: &IdentifierReference<'_>) -> Val<'a> {
        match self.scoping.get_reference(id.reference_id()).symbol_id() {
            Some(symbol) => match self.env.get(&symbol).cloned() {
                Some(v) => self.settle(v),
                None => self.unsupported(),
            },
            None => self.free(id.name.as_str()),
        }
    }
    fn free(&mut self, name: &str) -> Val<'a> {
        match name {
            "undefined" => return Val::Undef,
            "NaN" => return Val::NaN,
            // A function's own arguments object, which lowering does not model.
            "arguments" => return self.unsupported(),
            _ => {}
        }
        let kind = self.kinds.get(name).copied().unwrap_or(Kind::Any);
        let var = self.b.var(kind, name);
        match kind {
            Kind::Int => Val::Num(Form::atom(var)),
            Kind::List => Val::Ref(RefKey::Input(egg::Symbol::from(name))),
            Kind::Fun => Val::Term(var, Ty::Defined),
            _ => Val::Term(var, Ty::Any),
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    fn unary(&mut self, u: &'a UnaryExpression<'a>) -> Val<'a> {
        if u.operator == UnaryOperator::Delete {
            return self.delete(&u.argument);
        }
        let v = self.expr(&u.argument);
        match u.operator {
            UnaryOperator::LogicalNot => self.not(v),
            UnaryOperator::UnaryNegation => self.binary(Bin::Sub, Val::int(0), v),
            _ => self.unsupported(),
        }
    }
    fn binop(&mut self, b: &'a BinaryExpression<'a>) -> Val<'a> {
        use BinaryOperator as B;
        let (left, right) = (self.expr(&b.left), self.expr(&b.right));
        match b.operator {
            B::Addition => self.binary(Bin::Add, left, right),
            B::Subtraction => self.binary(Bin::Sub, left, right),
            B::Multiplication => self.binary(Bin::Mul, left, right),
            B::LessThan => self.binary(Bin::Lt, left, right),
            B::LessEqualThan => self.binary(Bin::Le, left, right),
            B::GreaterThan => self.binary(Bin::Lt, right, left),
            B::GreaterEqualThan => self.binary(Bin::Le, right, left),
            B::StrictEquality => self.binary(Bin::Eq, left, right),
            B::StrictInequality => {
                let eq = self.binary(Bin::Eq, left, right);
                self.not(eq)
            }
            _ => self.unsupported(),
        }
    }
    fn template(&mut self, t: &'a TemplateLiteral<'a>) -> Val<'a> {
        let mut out = Val::Str(Utf16::new([]));
        for (i, quasi) in t.quasis.iter().enumerate() {
            let Some(cooked) = &quasi.value.cooked else { return self.unsupported() };
            out = self.binary(Bin::Add, out, Val::Str(Utf16::new(cooked.encode_utf16())));
            if let Some(e) = t.expressions.get(i) {
                let v = self.expr(e);
                out = self.binary(Bin::Add, out, v);
            }
        }
        out
    }
    /// An array literal: every element is evaluated, so one that throws makes it throw.
    fn array(&mut self, a: &'a ArrayExpression<'a>) -> Val<'a> {
        let mut values = Vec::with_capacity(a.elements.len());
        let mut spread = Vec::with_capacity(a.elements.len());
        for element in &a.elements {
            let (v, s) = match element {
                ArrayExpressionElement::SpreadElement(s) => (self.expr(&s.argument), true),
                ArrayExpressionElement::Elision(_) => return self.unsupported(),
                e => {
                    // An array inside an array keeps its identity.
                    let v = self.expr(e.to_expression());
                    (self.own(v), false)
                }
            };
            values.push(v);
            spread.push(s);
        }
        self.strict(values, &mut |l, values| {
            values.into_iter().zip(&spread).fold(Val::empty(), |out, (v, &s)| {
                let segment = if s { v } else { Val::List(Rc::new(vec![v])) };
                l.append(out, segment)
            })
        })
    }
}

impl<'a> Lowerer<'a, '_> {
    fn logical(&mut self, l: &'a LogicalExpression<'a>) -> Val<'a> {
        let left = self.expr(&l.left);
        let right = Arm::Expr(&l.right);
        match l.operator {
            LogicalOperator::Coalesce => self.coalesce(left, right),
            LogicalOperator::Or => self.short_circuit(left, right, true),
            LogicalOperator::And => self.short_circuit(left, right, false),
        }
    }
    /// `left ?? right`: right where left is undefined.
    pub fn coalesce(&mut self, left: Val<'a>, right: Arm<'a, '_>) -> Val<'a> {
        // The probe only types the fallback; lowering it evaluates nothing.
        let probe = self.speculate(|l| l.arm(right));
        let family = if matches!(probe, Val::Term(_, Ty::Any)) { Family::Undecided } else { Family::Default };
        self.worlds(left, family, &mut |l, v| match v {
            Val::Undef => l.arm(right),
            Val::Term(_, Ty::Any) => {
                // The fallback runs only where `v` is nullish, which lowering cannot decide.
                let taken = l.dynamic("nullish", &[&v], Ty::Bool);
                let join = super::refs::Join::Test { test: taken, first_if: false };
                let (_, fallback) = l.fork(&mut |l, second| if second { l.arm(right) } else { Val::Undef }, &join);
                let ty = if fallback.defined() { Ty::Defined } else { Ty::Any };
                l.dynamic("??", &[&v, &fallback], ty)
            }
            v => v,
        })
    }
    /// `left || right` (or) and `left && right`.
    pub fn short_circuit(&mut self, left: Val<'a>, right: Arm<'a, '_>, or: bool) -> Val<'a> {
        self.worlds(left, Family::Default, &mut |l, v| match l.truthy(v.clone()) {
            Val::Bool(b) if b == or => v,
            Val::Bool(_) => l.arm(right),
            Val::Throw => Val::Throw,
            test => {
                // The right operand runs only where the left does not decide.
                let join = super::refs::Join::Test { test: test.clone(), first_if: or };
                let (_, other) = l.fork(&mut |l, second| if second { l.arm(right) } else { Val::Undef }, &join);
                if or { l.select(&test, v, other) } else { l.select(&test, other, v) }
            }
        })
    }
    fn conditional(&mut self, c: &'a ConditionalExpression<'a>) -> Val<'a> {
        let test = self.expr(&c.test);
        self.branch(test, Arm::Expr(&c.consequent), Arm::Expr(&c.alternate))
    }
    /// `test ? yes : no`, lowering each arm in every world of the splits in `test`.
    pub fn branch(&mut self, test: Val<'a>, yes: Arm<'a, '_>, no: Arm<'a, '_>) -> Val<'a> {
        self.worlds(test, Family::Default, &mut |l, t| match l.truthy(t) {
            Val::Bool(true) => l.arm(yes),
            Val::Bool(false) => l.arm(no),
            Val::Throw => Val::Throw,
            test => {
                let join = super::refs::Join::Test { test: test.clone(), first_if: true };
                let (y, n) = l.fork(&mut |l, second| l.arm(if second { no } else { yes }), &join);
                l.select(&test, y, n)
            }
        })
    }
    pub fn arm(&mut self, arm: Arm<'a, '_>) -> Val<'a> {
        match arm {
            Arm::Expr(e) => self.expr(e),
            Arm::Run(s) => self.run(s),
            Arm::Val(v) => v.clone(),
        }
    }
}

impl<'a, 'l> Lowerer<'a, 'l> {
    /// Run `then` in each world of every split in `v`, with that split's read narrowed.
    pub fn worlds(&mut self, v: Val<'a>, family: Family, then: &mut super::ops::Op1<'a, 'l, '_>) -> Val<'a> {
        let Val::Split(s) = v else { return then(self, v) };
        let (absent, present) = self.fork(
            &mut |l, present| {
                let (world, side) = if present { (Val::Term(s.elem, s.items.ty()), s.present.clone()) } else { (Val::Undef, s.absent.clone()) };
                l.within(s.read, world, |l| l.worlds(side, family, then))
            },
            &super::refs::Join::Read(s.clone()),
        );
        self.resplit(&s, absent, present, family)
    }
    pub fn within(&mut self, read: Id, value: Val<'a>, f: impl FnOnce(&mut Self) -> Val<'a>) -> Val<'a> {
        let old = self.narrow.insert(read, value);
        let out = f(self);
        match old {
            Some(old) => self.narrow.insert(read, old),
            None => self.narrow.remove(&read),
        };
        out
    }
    /// `test ? yes : no` for a boolean test, pushed inside any splits when it is symbolic.
    pub fn select(&mut self, test: &Val<'a>, yes: Val<'a>, no: Val<'a>) -> Val<'a> {
        if let Val::Bool(b) = test {
            return if *b { yes } else { no };
        }
        // Choosing between arms swallows nothing: a split in an arm keeps its own flow.
        self.lift2(yes, no, Family::Propagate, &mut |l, y, n| l.choose(test, &y, &n, true))
    }
    /// [`Self::select`] as a term, without keeping identity: the contents of a choice.
    pub fn select_contents(&mut self, test: &Val<'a>, yes: Val<'a>, no: Val<'a>) -> Val<'a> {
        if let Val::Bool(b) = test {
            return if *b { yes } else { no };
        }
        self.lift2(yes, no, Family::Propagate, &mut |l, y, n| l.choose(test, &y, &n, false))
    }
    fn choose(&mut self, test: &Val<'a>, yes: &Val<'a>, no: &Val<'a>, identity: bool) -> Val<'a> {
        if yes.identical(no) || (yes.is_known() && super::ops::same(yes, no) == Some(true)) {
            return yes.clone();
        }
        // Choosing an array with identity keeps its identity.
        if identity && (super::refs::holds_ref(yes) || super::refs::holds_ref(no)) {
            return self.choice(test.clone(), yes.clone(), no.clone());
        }
        let ty = join(yes, no);
        let (c, y, n) = (self.emit(test), self.emit(yes), self.emit(no));
        let id = self.b.add(Core::If([c, y, n]));
        match ty {
            None => Val::Num(Form::atom(id)),
            Some(ty) => Val::Term(id, ty),
        }
    }
}

/// The type of a value that is one of two; None for an integer.
fn join(a: &Val<'_>, b: &Val<'_>) -> Option<Ty> {
    let ty = |v: &Val<'_>| match v {
        Val::Num(_) => None,
        Val::Bool(_) | Val::Term(_, Ty::Bool) => Some(Ty::Bool),
        Val::Str(_) | Val::Term(_, Ty::Str) => Some(Ty::Str),
        Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => v.items().map(Ty::List),
        Val::Undef | Val::Term(_, Ty::Any) | Val::Split(_) => Some(Ty::Any),
        _ => Some(Ty::Defined),
    };
    match (ty(a), ty(b)) {
        (x, y) if x == y => x,
        (Some(Ty::List(x)), Some(Ty::List(y))) => Some(Ty::List(x.both(y))),
        (Some(Ty::Any), _) | (_, Some(Ty::Any)) => Some(Ty::Any),
        _ => Some(Ty::Defined),
    }
}

fn integer(value: f64) -> Option<i64> {
    let whole = value.is_finite() && value.fract() == 0.0 && value.abs() <= 9_007_199_254_740_991.0;
    #[allow(clippy::cast_possible_truncation)]
    whole.then_some(value as i64)
}

fn arrow_body<'a>(f: &'a oxc_ast::ast::ArrowFunctionExpression<'a>) -> Option<Body<'a>> {
    match &f.body {
        oxc_ast::ast::ArrowFunctionBody::FunctionBody(b) => Some(Body::Block(b)),
        b => b.as_expression().map(Body::Expr),
    }
}
