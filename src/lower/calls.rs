//! Calls: inlining known functions with JavaScript arity, and list methods.
use super::Lowerer;
use super::expr::Arm;
use super::ops::Bin;
use super::value::{Body, Fun, Short, Ty, Val};
use crate::affine::Form;
use crate::core::{Core, Family, Kind};
use egg::Id;
use oxc_ast::ast::{BindingPattern, CallExpression, Expression, Statement, VariableDeclarationKind};
use std::rc::Rc;

const INLINE_DEPTH: usize = 64;

impl<'a> Lowerer<'a, '_> {
    pub fn call(&mut self, c: &'a CallExpression<'a>) -> Val<'a> {
        let mut args = Vec::with_capacity(c.arguments.len());
        for a in &c.arguments {
            let Some(e) = a.as_expression() else { return self.unsupported() };
            args.push(self.expr(e));
        }
        if let Expression::StaticMemberExpression(m) = &c.callee {
            if m.optional {
                return self.unsupported();
            }
            let receiver = self.expr(&m.object);
            return self.method(receiver, m.property.name.as_str(), args);
        }
        let callee = self.expr(&c.callee);
        self.apply(callee, args)
    }
    /// Call a value: inline a known function, or leave an opaque call.
    pub fn apply(&mut self, callee: Val<'a>, args: Vec<Val<'a>>) -> Val<'a> {
        match callee {
            Val::Fun(f) if self.depth < INLINE_DEPTH => self.inline(&f, args),
            Val::Split(_) => self.lift(callee, Family::Propagate, &mut |l, f| match f {
                Val::Undef => Val::Throw,
                f => l.apply(f, args.clone()),
            }),
            callee => {
                let mut children = vec![self.b.emit(&callee)];
                children.extend(args.iter().map(|a| self.b.emit(a)));
                Val::Term(self.b.add(Core::Call(children.into())), Ty::Any)
            }
        }
    }
    fn inline(&mut self, f: &Fun<'a>, args: Vec<Val<'a>>) -> Val<'a> {
        let saved = std::mem::replace(&mut self.env, f.env.clone());
        self.depth += 1;
        let out = if self.bind_params(f, args) { self.body(f.body) } else { self.unsupported() };
        self.depth -= 1;
        self.env = saved;
        out
    }
    /// Bind each parameter to its argument; a missing argument is undefined.
    fn bind_params(&mut self, f: &Fun<'a>, args: Vec<Val<'a>>) -> bool {
        if f.params.rest.is_some() {
            return false;
        }
        let mut args = args.into_iter();
        for p in &f.params.items {
            let mut value = args.next().unwrap_or(Val::Undef);
            if let Some(init) = &p.initializer {
                value = self.coalesce(value, Arm::Expr(init));
            }
            if !self.bind(&p.pattern, value) {
                return false;
            }
        }
        true
    }
    fn bind(&mut self, pattern: &'a BindingPattern<'a>, value: Val<'a>) -> bool {
        match pattern {
            BindingPattern::BindingIdentifier(id) => {
                self.env.insert(id.symbol_id(), value);
                true
            }
            BindingPattern::AssignmentPattern(p) => {
                let value = self.coalesce(value, Arm::Expr(&p.right));
                self.bind(&p.left, value)
            }
            BindingPattern::ArrayPattern(p) if p.rest.is_none() => p.elements.iter().enumerate().all(|(k, e)| {
                let index = Val::int(i64::try_from(k).unwrap_or(i64::MAX));
                let item = self.read(value.clone(), index);
                e.as_ref().is_none_or(|e| self.bind(e, item))
            }),
            _ => false,
        }
    }
    fn body(&mut self, body: Body<'a>) -> Val<'a> {
        match body {
            Body::Expr(e) => self.expr(e),
            Body::Block(b) => {
                let stmts: Vec<_> = b.statements.iter().collect();
                self.run(&stmts)
            }
        }
    }
    /// Run statements to the first return; falling off the end returns undefined. A branch
    /// that does not return continues with the statements after it.
    pub fn run(&mut self, stmts: &[&'a Statement<'a>]) -> Val<'a> {
        let Some((&first, rest)) = stmts.split_first() else { return Val::Undef };
        match first {
            Statement::ReturnStatement(r) => r.argument.as_ref().map_or(Val::Undef, |e| self.expr(e)),
            Statement::VariableDeclaration(d) if d.kind == VariableDeclarationKind::Const => {
                for declarator in &d.declarations {
                    let Some(init) = &declarator.init else { return self.unsupported() };
                    let value = self.expr(init);
                    if !self.bind(&declarator.id, value) {
                        return self.unsupported();
                    }
                }
                self.run(rest)
            }
            Statement::IfStatement(s) => {
                let test = self.expr(&s.test);
                let yes: Vec<_> = std::iter::once(&s.consequent).chain(rest.iter().copied()).collect();
                let no: Vec<_> = s.alternate.iter().chain(rest.iter().copied()).collect();
                self.branch(test, Arm::Run(&yes), Arm::Run(&no))
            }
            Statement::BlockStatement(b) => {
                let inner: Vec<_> = b.body.iter().chain(rest.iter().copied()).collect();
                self.run(&inner)
            }
            Statement::EmptyStatement(_) => self.run(rest),
            _ => self.unsupported(),
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    fn method(&mut self, receiver: Val<'a>, name: &str, args: Vec<Val<'a>>) -> Val<'a> {
        match receiver {
            Val::List(items) => self.literal_method(&items, name, args),
            Val::Short(s) => self.short_method(&s, name, args),
            Val::Term(id, Ty::List) => self.term_method(id, name, args),
            Val::Split(_) => self.lift(receiver, Family::Propagate, &mut |l, r| match r {
                Val::Undef => Val::Throw,
                r => l.method(r, name, args.clone()),
            }),
            _ => self.unsupported(),
        }
    }
    /// Unroll a method over a list of known length.
    fn literal_method(&mut self, items: &Rc<Vec<Val<'a>>>, name: &str, args: Vec<Val<'a>>) -> Val<'a> {
        let f = args.first().cloned().unwrap_or(Val::Undef);
        match name {
            "map" => Val::List(Rc::new(self.each(items, &f))),
            "every" | "some" => self.quantify(items, &f, name == "every"),
            "reduce" => self.fold_items(items, &f, args.get(1).cloned()),
            "join" => self.join_items(items, args.first().cloned()),
            "flat" => self.flat_items(items),
            "flatMap" => {
                let mapped = self.each(items, &f);
                self.flat_items(&Rc::new(mapped))
            }
            "concat" => self.concat_list(Val::List(items.clone()), f),
            _ => {
                let id = self.b.emit(&Val::List(items.clone()));
                self.term_method(id, name, args)
            }
        }
    }
    /// The callback applied to every (element, index, list).
    fn each(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>) -> Vec<Val<'a>> {
        let list = Val::List(items.clone());
        let indexed = items.iter().cloned().zip(0_i64..);
        indexed.map(|(x, k)| self.apply(f.clone(), vec![x, Val::int(k), list.clone()])).collect()
    }
    fn quantify(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>, every: bool) -> Val<'a> {
        let results = self.each(items, f);
        results.into_iter().rev().fold(Val::Bool(every), |rest, v| {
            let rest = Arm::Val(&rest);
            let truth = self.truthy_split(v);
            if every { self.branch(truth, rest, Arm::Val(&Val::Bool(false))) } else { self.branch(truth, Arm::Val(&Val::Bool(true)), rest) }
        })
    }
    fn truthy_split(&mut self, v: Val<'a>) -> Val<'a> {
        self.lift(v, Family::Sink, &mut |l, v| l.truthy(v))
    }
    fn fold_items(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        let list = Val::List(items.clone());
        let mut rest = items.iter().cloned().zip(0_i64..);
        let Some(mut acc) = init.or_else(|| rest.next().map(|(x, _)| x)) else { return Val::Throw };
        for (x, k) in rest {
            acc = self.apply(f.clone(), vec![acc, x, Val::int(k), list.clone()]);
        }
        acc
    }
}

impl<'a> Lowerer<'a, '_> {
    /// The text join writes for an element: nothing for undefined.
    fn join_text(&mut self, v: Val<'a>) -> Val<'a> {
        self.lift(v, Family::Unit, &mut |l, v| match v {
            Val::Undef => Val::Str(crate::core::Utf16::new([])),
            Val::Term(id, Ty::Defined | Ty::Any) => Val::Term(l.b.add(Core::Text(id)), Ty::Str),
            v => l.to_text(v),
        })
    }
    fn separator(&mut self, sep: Option<Val<'a>>) -> Val<'a> {
        match sep {
            None | Some(Val::Undef) => Val::Str(crate::core::Utf16::new(",".encode_utf16())),
            Some(v) => self.to_text(v),
        }
    }
    fn join_items(&mut self, items: &Rc<Vec<Val<'a>>>, sep: Option<Val<'a>>) -> Val<'a> {
        let sep = self.separator(sep);
        let mut out: Option<Val<'a>> = None;
        for item in items.iter() {
            let text = self.join_text(item.clone());
            out = Some(match out {
                None => text,
                Some(prefix) => {
                    let prefix = self.binary(Bin::Add, prefix, sep.clone());
                    self.binary(Bin::Add, prefix, text)
                }
            });
        }
        out.unwrap_or_else(|| Val::Str(crate::core::Utf16::new([])))
    }
    /// flat spreads a list element one level and keeps any other element.
    fn spread(&mut self, v: Val<'a>) -> Val<'a> {
        self.lift(v, Family::Container, &mut |l, v| match v {
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List) | Val::Throw => v,
            v if v.is_known() || matches!(v, Val::Term(_, Ty::Bool | Ty::Str) | Val::Num(_)) => Val::List(Rc::new(vec![v])),
            v => l.dynamic("spread", &[&v], Ty::List),
        })
    }
    fn flat_items(&mut self, items: &Rc<Vec<Val<'a>>>) -> Val<'a> {
        items.iter().cloned().fold(Val::empty(), |acc, item| {
            let part = self.spread(item);
            self.append(acc, part)
        })
    }
}

impl<'a, 'l> Lowerer<'a, 'l> {
    /// Methods over a list of at most one element: the unit where the slot is absent.
    fn short_method(&mut self, s: &Rc<Short<'a>>, name: &str, args: Vec<Val<'a>>) -> Val<'a> {
        let f = args.first().cloned().unwrap_or(Val::Undef);
        match name {
            "every" | "some" => {
                let every = name == "every";
                let unit = Val::Bool(every);
                self.over_slot(s, Family::Unit, &unit, &mut |l, x| {
                    let v = l.apply(f.clone(), vec![x, Val::int(0), Val::Short(s.clone())]);
                    l.truthy_split(v)
                })
            }
            "reduce" => {
                let init = args.get(1).cloned();
                let unit = init.clone().unwrap_or(Val::Throw);
                self.over_slot(s, Family::Unit, &unit, &mut |l, x| match &init {
                    Some(z) => l.apply(f.clone(), vec![z.clone(), x, Val::int(0), Val::Short(s.clone())]),
                    None => x,
                })
            }
            "join" => {
                let unit = Val::Str(crate::core::Utf16::new([]));
                self.over_slot(s, Family::Unit, &unit, &mut |l, x| l.join_text(x))
            }
            "flat" => self.over_slot(s, Family::Container, &Val::empty(), &mut |l, x| l.spread(x)),
            "map" | "filter" | "flatMap" => self.short_walk(s, name, &f),
            _ => self.term_method(s.list, name, args),
        }
    }
    /// The slot's value under `present`, or `unit` where it is absent or filtered out.
    fn over_slot(&mut self, s: &Short<'a>, family: Family, unit: &Val<'a>, present: &mut super::ops::Op1<'a, 'l, '_>) -> Val<'a> {
        let slot = self.split_read(s.read, false);
        let (elem, keep) = (s.elem.clone(), s.keep.clone());
        self.worlds(slot, family, &mut |l, v| match v {
            Val::Undef => unit.clone(),
            _ => {
                let value = present(l, elem.clone());
                l.select(&keep, value, unit.clone())
            }
        })
    }
    fn short_walk(&mut self, s: &Rc<Short<'a>>, name: &str, f: &Val<'a>) -> Val<'a> {
        let applied = self.apply(f.clone(), vec![s.elem.clone(), Val::int(0), Val::Short(s.clone())]);
        let kind = if name == "filter" { Walker::Filter } else { Walker::Map };
        let list = self.walker(kind, f, s.list);
        let mut next = Short { list, ..(**s).clone() };
        if name == "filter" {
            let pass = self.truthy_split(applied);
            next.keep = self.and_split(s.keep.clone(), pass);
        } else {
            next.elem = applied;
        }
        let next = Val::Short(Rc::new(next));
        if name == "flatMap" { self.method(next, "flat", Vec::new()) } else { next }
    }
    fn and_split(&mut self, a: Val<'a>, b: Val<'a>) -> Val<'a> {
        self.lift2(a, b, Family::Default, &mut |l, a, b| l.and(a, b))
    }
}

/// Walkers emitted over a symbolic list.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Walker {
    Map,
    Filter,
    Every,
    Some,
}

impl<'a> Lowerer<'a, '_> {
    fn term_method(&mut self, list: Id, name: &str, args: Vec<Val<'a>>) -> Val<'a> {
        let f = args.first().cloned().unwrap_or(Val::Undef);
        match name {
            "map" => Val::Term(self.walker(Walker::Map, &f, list), Ty::List),
            "every" => Val::Term(self.walker(Walker::Every, &f, list), Ty::Bool),
            "some" => Val::Term(self.walker(Walker::Some, &f, list), Ty::Bool),
            "filter" => self.filter(list, &f),
            "find" => self.find(list, &f),
            "reduce" => self.reduce(list, &f, args.get(1).cloned()),
            "join" => {
                let sep = self.separator(args.first().cloned());
                let sep = self.b.emit(&sep);
                Val::Term(self.b.add(Core::Join([sep, list])), Ty::Str)
            }
            "flat" => Val::Term(self.b.add(Core::Flat(list)), Ty::List),
            "flatMap" => {
                let mapped = self.walker(Walker::Map, &f, list);
                Val::Term(self.b.add(Core::Flat(mapped)), Ty::List)
            }
            "slice" => self.slice(list, args.first().cloned(), args.get(1).cloned()),
            "at" => self.at(list, f),
            "concat" => self.concat_list(Val::Term(list, Ty::List), f),
            _ => self.unsupported(),
        }
    }
    /// A walker node over `list` whose callback is lowered with fresh element and index
    /// binders. An unknown callback stays opaque.
    pub fn walker(&mut self, kind: Walker, f: &Val<'a>, list: Id) -> Id {
        let lam = match f {
            Val::Fun(_) => self.callback(kind, f, list),
            other => self.b.emit(other),
        };
        self.b.add(match kind {
            Walker::Map => Core::Map([lam, list]),
            Walker::Filter => Core::Filter([lam, list]),
            Walker::Every => Core::Every([lam, list]),
            Walker::Some => Core::Some([lam, list]),
        })
    }
    fn callback(&mut self, kind: Walker, f: &Val<'a>, list: Id) -> Id {
        let (x, i) = (self.b.fresh(Kind::Elem), self.b.fresh(Kind::Index));
        self.coords.insert(i, list);
        let args = vec![Val::Term(x, Ty::Defined), Val::Num(Form::atom(i)), Val::Term(list, Ty::List)];
        let result = self.apply(f.clone(), args);
        let body = match kind {
            Walker::Map => self.escape(result),
            _ => {
                let truth = self.truthy_split(result);
                self.b.emit(&truth)
            }
        };
        self.b.add(Core::Lam(vec![x, i, body].into()))
    }
    /// A possibly missing read at another collection's coordinate, left as a hole in a
    /// collection shaped like the walked one.
    fn escape(&mut self, v: Val<'a>) -> Id {
        let id = self.b.emit(&v);
        match &v {
            Val::Split(s) if s.drift && s.family == Family::Propagate => self.b.add(Core::Escape(id)),
            _ => id,
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    fn filter(&mut self, list: Id, f: &Val<'a>) -> Val<'a> {
        let walked = self.walker(Walker::Filter, f, list);
        match self.projection(f, list) {
            Some(index) => {
                let read = self.element(list, &index);
                self.projected(walked, read)
            }
            None => Val::Term(walked, Ty::List),
        }
    }
    /// A filtered list holding at most the element read by `slot`.
    fn projected(&mut self, list: Id, slot: Val<'a>) -> Val<'a> {
        let Val::Split(s) = &slot else { return Val::Term(list, Ty::List) };
        let short = Short { list, read: s.read, var: s.elem, elem: Val::Term(s.elem, Ty::Defined), keep: Val::Bool(true) };
        Val::Short(Rc::new(short))
    }
    fn find(&mut self, list: Id, f: &Val<'a>) -> Val<'a> {
        if let Some(index) = self.projection(f, list) {
            return self.element(list, &index);
        }
        let walked = self.walker(Walker::Filter, f, list);
        self.element(walked, &Form::constant(0))
    }
    /// The index `j` when the callback is `(_, idx) => idx === j` (either side) with `j` an
    /// integer that mentions neither parameter: the filter keeps at most `list[j]`.
    fn projection(&mut self, f: &Val<'a>, list: Id) -> Option<Form> {
        let Val::Fun(fun) = f else { return None };
        let (Body::Expr(body), Some(index)) = (fun.body, fun.params.items.get(1)) else { return None };
        let BindingPattern::BindingIdentifier(idx) = &index.pattern else { return None };
        let Expression::BinaryExpression(eq) = body.without_parentheses() else { return None };
        if eq.operator != oxc_syntax::operator::BinaryOperator::StrictEquality {
            return None;
        }
        let is_idx = |e: &Expression<'_>| match e.without_parentheses() {
            Expression::Identifier(r) => self.scoping.get_reference(r.reference_id()).symbol_id() == Some(idx.symbol_id()),
            _ => false,
        };
        let other = if is_idx(&eq.left) { &eq.right } else if is_idx(&eq.right) { &eq.left } else { return None };
        self.projected_index(fun, list, other)
    }
    fn projected_index(&mut self, fun: &Fun<'a>, list: Id, target: &'a Expression<'a>) -> Option<Form> {
        let (x, i) = (self.b.fresh(Kind::Elem), self.b.fresh(Kind::Index));
        let saved = std::mem::replace(&mut self.env, fun.env.clone());
        let args = vec![Val::Term(x, Ty::Defined), Val::Num(Form::atom(i)), Val::Term(list, Ty::List)];
        let bound = self.bind_params(fun, args);
        let value = bound.then(|| self.expr(target));
        self.env = saved;
        let Some(Val::Num(form)) = value else { return None };
        let free = !form.terms.keys().any(|&a| self.b.mentions(a, x) || self.b.mentions(a, i));
        free.then_some(form)
    }
}

impl<'a> Lowerer<'a, '_> {
    /// `list.reduce(f, init)`. A callback that ignores its accumulator yields its value on the
    /// last element, or the initial value for an empty list.
    fn reduce(&mut self, list: Id, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        let len = Form::atom(self.b.add(Core::Len(list)));
        let last = len.plus(&Form::constant(1), -1).unwrap_or_default();
        let slot = self.element(list, &last);
        let acc = self.b.fresh(Kind::Acc);
        let unit = init.clone().unwrap_or(Val::Throw);
        let f = f.clone();
        let body = self.worlds(slot.clone(), Family::Unit, &mut |l, x| match x {
            Val::Undef => unit.clone(),
            x => l.apply(f.clone(), vec![Val::Term(acc, Ty::Any), x, Val::Num(last.clone()), Val::Term(list, Ty::List)]),
        });
        let id = self.b.emit(&body);
        if !self.b.mentions(id, acc) {
            return body;
        }
        self.fold(list, &f, init)
    }
    fn fold(&mut self, list: Id, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        let (acc, x, i) = (self.b.fresh(Kind::Acc), self.b.fresh(Kind::Elem), self.b.fresh(Kind::Index));
        self.coords.insert(i, list);
        let args = vec![Val::Term(acc, Ty::Any), Val::Term(x, Ty::Defined), Val::Num(Form::atom(i)), Val::Term(list, Ty::List)];
        let body = self.apply(f.clone(), args);
        let body = self.b.emit(&body);
        let lam = self.b.add(Core::Lam(vec![acc, x, i, body].into()));
        let init = match init {
            Some(z) => self.b.emit(&z),
            None => self.b.add(Core::Throw),
        };
        Val::Term(self.b.add(Core::Fold([lam, init, list])), Ty::Any)
    }
    /// `list.slice(start, end)`: a list of at most one element when the bounds differ by
    /// one, since slicing never widens past `end - start`.
    fn slice(&mut self, list: Id, start: Option<Val<'a>>, end: Option<Val<'a>>) -> Val<'a> {
        let len = Form::atom(self.b.add(Core::Len(list)));
        let start = match start {
            None | Some(Val::Undef) => Form::constant(0),
            Some(Val::Num(f)) => f,
            Some(_) => return self.unsupported(),
        };
        let end = match end {
            None | Some(Val::Undef) => len,
            Some(Val::Num(f)) => f,
            Some(_) => return self.unsupported(),
        };
        let (a, z) = (self.b.form(&start), self.b.form(&end));
        let sliced = self.b.add(Core::Slice([list, a, z]));
        match end.plus(&start, -1).and_then(|w| w.known()) {
            Some(w) if w <= 0 => Val::empty(),
            Some(1) => self.short(sliced),
            _ => Val::Term(sliced, Ty::List),
        }
    }
    fn at(&mut self, list: Id, index: Val<'a>) -> Val<'a> {
        let Val::Num(k) = index else { return self.unsupported() };
        match k.known() {
            Some(n) if n < 0 => {
                let len = Form::atom(self.b.add(Core::Len(list)));
                let from_end = len.plus(&k, 1).unwrap_or_default();
                self.element(list, &from_end)
            }
            Some(_) => self.element(list, &k),
            None => self.unsupported(),
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    /// `list.concat(item)`: a list argument is spread, any other value appended.
    fn concat_list(&mut self, list: Val<'a>, item: Val<'a>) -> Val<'a> {
        let item = match item {
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List) => item,
            v if v.is_known() || matches!(v, Val::Term(_, Ty::Bool | Ty::Str) | Val::Num(_)) => Val::List(Rc::new(vec![v])),
            _ => return self.unsupported(),
        };
        self.append(list, item)
    }
}
