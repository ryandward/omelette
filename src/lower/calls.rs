//! Calls: inlining known functions with JavaScript arity, and list methods.
use super::Lowerer;
use super::expr::Arm;
use super::ops::Bin;
use super::value::{Body, Fun, Items, Seq, Short, Ty, Val};
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
            let name = m.property.name.as_str();
            let values = std::iter::once(receiver).chain(args).collect();
            return self.strict(values, &mut |l, mut values| {
                let receiver = values.remove(0);
                l.method(receiver, name, &values)
            });
        }
        let callee = self.expr(&c.callee);
        self.apply(callee, args)
    }
    /// Call a value once it and its arguments are evaluated: inline a known function, or
    /// leave an opaque call.
    pub fn apply(&mut self, callee: Val<'a>, args: Vec<Val<'a>>) -> Val<'a> {
        if callee.may_throw() || args.iter().any(Val::may_throw) {
            let values = std::iter::once(callee).chain(args).collect();
            return self.strict(values, &mut |l, mut values| {
                let callee = values.remove(0);
                l.apply(callee, values)
            });
        }
        match callee {
            Val::Fun(f) if self.depth < INLINE_DEPTH => self.inline(&f, args),
            Val::Split(_) => self.lift(callee, Family::Propagate, &mut |l, f| match f {
                Val::Undef => Val::Throw,
                f => l.apply(f, args.clone()),
            }),
            callee => {
                self.opaque = true;
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
            // Destructuring iterates, so a string yields its code points.
            BindingPattern::ArrayPattern(p) if p.rest.is_none() => {
                let items = self.lift(value, Family::Propagate, &mut |l, v| l.iterate(v));
                p.elements.iter().enumerate().all(|(k, e)| {
                    let index = Val::int(i64::try_from(k).unwrap_or(i64::MAX));
                    let item = self.read(items.clone(), index);
                    e.as_ref().is_none_or(|e| self.bind(e, item))
                })
            }
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
                self.declare(&d.declarations, rest)
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
    /// What a list method does before it runs, when that decides it: a callback that is not
    /// a function throws, and `flat` is modeled at depth one, or zero, which copies.
    fn precheck(&mut self, receiver: &Val<'a>, name: &str, args: &[Val<'a>]) -> Option<Val<'a>> {
        let first = args.first();
        if matches!(name, "map" | "filter" | "find" | "every" | "some" | "reduce" | "flatMap") && first.is_none_or(not_callable) {
            return Some(Val::Throw);
        }
        if name != "flat" {
            return None;
        }
        match first.map(|d| match d {
            Val::Undef => Some(1),
            Val::Num(f) => f.known(),
            _ => None,
        }) {
            None | Some(Some(1)) => None,
            Some(Some(0)) => Some(match receiver {
                Val::List(items) => Val::List(Rc::new(items.to_vec())),
                other => other.clone(),
            }),
            Some(_) => Some(self.unsupported()),
        }
    }
    /// Bind each `const` declarator once its initializer is evaluated, then run the rest.
    fn declare(&mut self, declarators: &'a [oxc_ast::ast::VariableDeclarator<'a>], rest: &[&'a Statement<'a>]) -> Val<'a> {
        let Some((first, others)) = declarators.split_first() else { return self.run(rest) };
        let Some(init) = &first.init else { return self.unsupported() };
        let value = self.expr(init);
        self.strict(vec![value], &mut |l, mut value| {
            if l.bind(&first.id, value.remove(0)) { l.declare(others, rest) } else { l.unsupported() }
        })
    }
    fn method(&mut self, receiver: Val<'a>, name: &str, args: &[Val<'a>]) -> Val<'a> {
        if receiver.items().is_some()
            && let Some(early) = self.precheck(&receiver, name, args)
        {
            return early;
        }
        match receiver {
            Val::List(items) => self.literal_method(&items, name, args),
            Val::Short(s) => self.short_method(&s, name, args),
            Val::Term(id, Ty::List(items)) => self.term_method(Seq { id, items }, name, args),
            Val::Split(_) => self.lift(receiver, Family::Propagate, &mut |l, r| match r {
                Val::Undef => Val::Throw,
                r => l.method(r, name, args),
            }),
            Val::Undef | Val::Throw => Val::Throw,
            _ => self.unsupported(),
        }
    }
    /// Unroll a method over a list of known length.
    fn literal_method(&mut self, items: &Rc<Vec<Val<'a>>>, name: &str, args: &[Val<'a>]) -> Val<'a> {
        let f = args.first().cloned().unwrap_or(Val::Undef);
        match name {
            "map" => {
                let mapped = self.each(items, &f);
                self.strict(mapped, &mut |_, mapped| Val::List(Rc::new(mapped)))
            }
            // A walker over the list would hide a possibly missing element from detection,
            // so the filter runs in every world of the reads among its elements.
            "filter" => self.decide(items.to_vec(), |v| matches!(v, Val::Split(_)), &mut |l, items| {
                let items = Rc::new(items);
                l.filter_items(&items, &f).unwrap_or_else(|| {
                    let list = l.seq(&items);
                    l.term_method(list, name, args)
                })
            }),
            "find" => self.find_items(items, &f),
            "slice" => slice_items(items, args.first(), args.get(1)).unwrap_or_else(|| self.unsupported()),
            "at" => self.at_items(items, &f),
            "every" | "some" => self.quantify(items, &f, name == "every"),
            "reduce" => self.fold_items(items, &f, args.get(1).cloned()),
            "join" => self.join_items(items, args.first().cloned()),
            "flat" => self.flat_items(items),
            "flatMap" => {
                let mapped = self.each(items, &f);
                self.flat_items(&Rc::new(mapped))
            }
            "concat" => self.concat_list(Val::List(items.clone()), args),
            _ => {
                let list = self.seq(items);
                self.term_method(list, name, args)
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
    pub fn join_items(&mut self, items: &Rc<Vec<Val<'a>>>, sep: Option<Val<'a>>) -> Val<'a> {
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
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) | Val::Throw => v,
            v if v.is_known() || matches!(v, Val::Term(_, Ty::Bool | Ty::Str) | Val::Num(_)) => Val::List(Rc::new(vec![v])),
            v => l.dynamic("spread", &[&v], Ty::List(Items::Any)),
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
    fn short_method(&mut self, s: &Rc<Short<'a>>, name: &str, args: &[Val<'a>]) -> Val<'a> {
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
        let slot = self.split_read(s.read, s.drift, s.items);
        let (elem, keep) = (s.elem.clone(), s.keep.clone());
        self.worlds(slot, family, &mut |l, v| {
            if matches!(v, Val::Undef) {
                return unit.clone();
            }
            let value = present(l, elem.clone());
            l.select(&keep, value, unit.clone())
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
        if name == "flatMap" { self.method(next, "flat", &[]) } else { next }
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
    fn term_method(&mut self, list: Seq, name: &str, args: &[Val<'a>]) -> Val<'a> {
        let f = args.first().cloned().unwrap_or(Val::Undef);
        match name {
            "map" => self.walker(Walker::Map, &f, list).val(),
            "every" => Val::Term(self.walker(Walker::Every, &f, list).id, Ty::Bool),
            "some" => Val::Term(self.walker(Walker::Some, &f, list).id, Ty::Bool),
            "filter" => self.filter(list, &f),
            "find" => self.find(list, &f),
            "reduce" => self.reduce(list, &f, args.get(1).cloned()),
            "join" => {
                let sep = self.separator(args.first().cloned());
                let sep = self.b.emit(&sep);
                Val::Term(self.b.add(Core::Join([sep, list.id])), Ty::Str)
            }
            // A nested element's own elements are not covered by the precondition.
            "flat" => Seq { id: self.b.add(Core::Flat(list.id)), items: Items::Any }.val(),
            "flatMap" => {
                let mapped = self.walker(Walker::Map, &f, list);
                Seq { id: self.b.add(Core::Flat(mapped.id)), items: Items::Any }.val()
            }
            "slice" => self.slice(list, args.first().cloned(), args.get(1).cloned()),
            "at" => self.at(list, f),
            "concat" => self.concat_list(list.val(), args),
            _ => self.unsupported(),
        }
    }
    /// A walker node over `list` whose callback is lowered with fresh element and index
    /// binders. An unknown callback stays opaque. The result's elements are the callback's
    /// values for a map, and the list's own otherwise.
    pub fn walker(&mut self, kind: Walker, f: &Val<'a>, list: Seq) -> Seq {
        let (lam, items) = match f {
            Val::Fun(_) => self.callback(kind, f, list),
            other => {
                self.opaque = true;
                (self.b.emit(other), Items::Any)
            }
        };
        let node = self.b.add(match kind {
            Walker::Map => Core::Map([lam, list.id]),
            Walker::Filter => Core::Filter([lam, list.id]),
            Walker::Every => Core::Every([lam, list.id]),
            Walker::Some => Core::Some([lam, list.id]),
        });
        if kind == Walker::Map && matches!(f, Val::Fun(_)) {
            self.maps.insert(node, (f.clone(), list));
        }
        Seq { id: node, items: if kind == Walker::Map { items } else { list.items } }
    }
    /// The callback's lambda, and whether every value it returns is defined.
    fn callback(&mut self, kind: Walker, f: &Val<'a>, list: Seq) -> (Id, Items) {
        let (x, i) = (self.b.fresh(list.items.kind()), self.b.fresh(Kind::Index));
        self.coords.insert(i, list.id);
        let args = vec![Val::Term(x, list.items.ty()), Val::Num(Form::atom(i)), list.val()];
        self.walking.push(list.id);
        let result = self.apply(f.clone(), args);
        self.walking.pop();
        let items = Items::of(result.defined());
        let body = if kind == Walker::Map {
            self.escape(&result)
        } else {
            let truth = self.truthy_split(result);
            self.b.emit(&truth)
        };
        (self.b.add(Core::Lam(vec![x, i, body].into())), items)
    }
    /// A possibly missing read at another collection's coordinate, left as a hole in a
    /// collection shaped like the walked one.
    fn escape(&mut self, v: &Val<'a>) -> Id {
        let id = self.b.emit(v);
        match v {
            Val::Split(s) if s.drift && matches!(s.absent, Val::Undef) => {
                let has = self.b.has(s.read);
                self.b.add(Core::Escape([id, has]))
            }
            _ => id,
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    fn filter(&mut self, list: Seq, f: &Val<'a>) -> Val<'a> {
        if let Some((index, lam)) = self.projection(f, list) {
            let walked = Seq { id: self.b.add(Core::Filter([lam, list.id])), items: list.items };
            let read = self.element(list, &index);
            return projected(walked, &read);
        }
        self.walker(Walker::Filter, f, list).val()
    }
    fn find(&mut self, list: Seq, f: &Val<'a>) -> Val<'a> {
        if let Some((index, _)) = self.projection(f, list) {
            return self.element(list, &index);
        }
        let walked = self.walker(Walker::Filter, f, list);
        self.element(walked, &Form::constant(0))
    }
    /// The index `j` when the callback is `(_, idx) => idx === j` (either side) with `j` an
    /// integer that mentions neither parameter: the filter keeps at most `list[j]`. Also the
    /// predicate's term, lowered once.
    fn projection(&mut self, f: &Val<'a>, list: Seq) -> Option<(Form, Id)> {
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
    fn projected_index(&mut self, fun: &Fun<'a>, list: Seq, target: &'a Expression<'a>) -> Option<(Form, Id)> {
        let (x, i) = (self.b.fresh(list.items.kind()), self.b.fresh(Kind::Index));
        let (saved, opaque) = (std::mem::replace(&mut self.env, fun.env.clone()), self.opaque);
        let args = vec![Val::Term(x, list.items.ty()), Val::Num(Form::atom(i)), list.val()];
        let bound = self.bind_params(fun, args);
        let value = bound.then(|| self.expr(target));
        // Recognizing a projection evaluates nothing; the walker that replaces it does.
        (self.env, self.opaque) = (saved, opaque);
        let Some(Val::Num(form)) = value else { return None };
        if form.terms.keys().any(|&a| self.b.mentions(a, x) || self.b.mentions(a, i)) {
            return None;
        }
        self.coords.insert(i, list.id);
        let test = self.strict_eq(&Val::Num(Form::atom(i)), &Val::Num(form.clone()));
        let body = self.b.emit(&test);
        Some((form, self.b.add(Core::Lam(vec![x, i, body].into()))))
    }
}

impl<'a> Lowerer<'a, '_> {
    /// `list.reduce(f, init)`. A callback that ignores its accumulator yields its value on the
    /// last element, or the initial value for an empty list.
    fn reduce(&mut self, list: Seq, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        let len = Form::atom(self.b.add(Core::Len(list.id)));
        let final_index = len.plus(&Form::constant(1), -1).unwrap_or_default();
        let slot = self.element(list, &final_index);
        let acc = self.b.fresh(Kind::Acc);
        let unit = init.clone().unwrap_or(Val::Throw);
        let f = f.clone();
        // Without an initial value, a one-element list returns its element uncalled, so the
        // law also needs the callback to return its element.
        let mut returns_element = true;
        let body = self.worlds(slot.clone(), Family::Unit, &mut |l, x| match x {
            Val::Undef => unit.clone(),
            x => {
                let out = l.apply(f.clone(), vec![Val::Term(acc, Ty::Any), x.clone(), Val::Num(final_index.clone()), list.val()]);
                returns_element &= out.identical(&x);
                out
            }
        });
        let id = self.b.emit(&body);
        if self.b.mentions(id, acc) || (init.is_none() && !returns_element) {
            return self.fold(list, &f, init);
        }
        body
    }
    fn fold(&mut self, list: Seq, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        let (acc, x, i) = (self.b.fresh(Kind::Acc), self.b.fresh(list.items.kind()), self.b.fresh(Kind::Index));
        self.coords.insert(i, list.id);
        let args = vec![Val::Term(acc, Ty::Any), Val::Term(x, list.items.ty()), Val::Num(Form::atom(i)), list.val()];
        self.walking.push(list.id);
        let body = self.apply(f.clone(), args);
        self.walking.pop();
        let body = self.b.emit(&body);
        let lam = self.b.add(Core::Lam(vec![acc, x, i, body].into()));
        let init = match init {
            Some(z) => self.b.emit(&z),
            None => self.b.add(Core::Throw),
        };
        Val::Term(self.b.add(Core::Fold([lam, init, list.id])), Ty::Any)
    }
    /// `list.slice(start, end)`, whose bounds count from the end when negative. Bounds that
    /// differ by `d >= 0` keep at most `d` elements whatever their signs, so a difference of
    /// one is a list of at most one element; a negative difference can keep any number.
    fn slice(&mut self, list: Seq, start: Option<Val<'a>>, end: Option<Val<'a>>) -> Val<'a> {
        let len = Form::atom(self.b.add(Core::Len(list.id)));
        let start = match start {
            None | Some(Val::Undef) => Form::constant(0),
            Some(Val::Num(f)) => f,
            Some(_) => return self.unsupported(),
        };
        let open = matches!(end, None | Some(Val::Undef));
        let end = match end {
            None | Some(Val::Undef) => len,
            Some(Val::Num(f)) => f,
            Some(_) => return self.unsupported(),
        };
        // slice(-k) keeps at most the last k elements.
        let tail = start.known().filter(|&k| open && k < 0).map(|k| -k);
        let drift = start.terms.keys().chain(end.terms.keys()).any(|a| self.coords.contains_key(a));
        let (a, z) = (self.b.form(&start), self.b.form(&end));
        let sliced = Seq { id: self.b.add(Core::Slice([list.id, a, z])), items: list.items };
        match tail.or_else(|| end.plus(&start, -1).and_then(|w| w.known())) {
            Some(0) => Val::empty(),
            // A walker's own index is in range, so the slice holds exactly that element.
            Some(1) if start.single().is_some() && self.in_range(list.id, &start) => {
                let element = self.element(list, &start);
                Val::List(Rc::new(vec![element]))
            }
            Some(1) => self.short(sliced, drift),
            _ => sliced.val(),
        }
    }
    fn at(&mut self, list: Seq, index: Val<'a>) -> Val<'a> {
        let Val::Num(k) = index else { return self.unsupported() };
        match k.known() {
            Some(n) if n < 0 => {
                let len = Form::atom(self.b.add(Core::Len(list.id)));
                let from_end = len.plus(&k, 1).unwrap_or_default();
                self.element(list, &from_end)
            }
            Some(_) => self.element(list, &k),
            None => self.unsupported(),
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    /// `list.concat(...items)`: each list argument is spread, and any other value appended.
    fn concat_list(&mut self, list: Val<'a>, items: &[Val<'a>]) -> Val<'a> {
        let mut out = self.append(list, Val::empty());
        for item in items {
            let item = match item {
                Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => item.clone(),
                v if v.is_known() || matches!(v, Val::Term(_, Ty::Bool | Ty::Str) | Val::Num(_)) => Val::List(Rc::new(vec![v.clone()])),
                _ => return self.unsupported(),
            };
            out = self.append(out, item);
        }
        out
    }
}

/// A value calling which certainly throws.
fn not_callable(v: &Val<'_>) -> bool {
    matches!(v, Val::Undef | Val::NaN | Val::Bool(_) | Val::Num(_) | Val::Str(_) | Val::List(_) | Val::Short(_))
        || matches!(v, Val::Term(_, Ty::Bool | Ty::Str | Ty::List(_)))
}

/// A filtered list holding at most the element read by `slot`, with that element's value
/// where present (a mapped list's mapped value), and the slot's drift.
fn projected<'a>(list: Seq, slot: &Val<'a>) -> Val<'a> {
    let Val::Split(s) = slot else { return list.val() };
    let short = Short {
        list,
        read: s.read,
        var: s.elem,
        items: s.items,
        elem: s.present.clone(),
        keep: Val::Bool(true),
        drift: s.drift,
    };
    Val::Short(Rc::new(short))
}

impl<'a> Lowerer<'a, '_> {
    /// The kept elements, when every keep decision is known.
    fn filter_items(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>) -> Option<Val<'a>> {
        let decisions = self.each(items, f);
        let mut kept = Vec::new();
        for (item, decision) in items.iter().zip(decisions) {
            match self.truthy_split(decision) {
                Val::Bool(true) => kept.push(item.clone()),
                Val::Bool(false) => {}
                Val::Throw => return Some(Val::Throw),
                _ => return None,
            }
        }
        Some(Val::List(Rc::new(kept)))
    }
    /// The first element the callback accepts, or undefined.
    fn find_items(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>) -> Val<'a> {
        let decisions = self.each(items, f);
        items.iter().zip(decisions).rev().fold(Val::Undef, |rest, (item, decision)| {
            let truth = self.truthy_split(decision);
            self.branch(truth, Arm::Val(item), Arm::Val(&rest))
        })
    }
    fn at_items(&mut self, items: &Rc<Vec<Val<'a>>>, index: &Val<'a>) -> Val<'a> {
        let Val::Num(k) = index else { return self.unsupported() };
        let Some(k) = k.known() else { return self.unsupported() };
        let len = i64::try_from(items.len()).unwrap_or(i64::MAX);
        let k = if k < 0 { len + k } else { k };
        usize::try_from(k).ok().and_then(|k| items.get(k).cloned()).unwrap_or(Val::Undef)
    }
}

/// `items.slice(start, end)` with JavaScript's relative, clamped bounds.
fn slice_items<'a>(items: &Rc<Vec<Val<'a>>>, start: Option<&Val<'a>>, end: Option<&Val<'a>>) -> Option<Val<'a>> {
    let len = i64::try_from(items.len()).ok()?;
    let bound = |v: Option<&Val<'a>>, default: i64| match v {
        None | Some(Val::Undef) => Some(default),
        Some(Val::Num(f)) => f.known().map(|k| if k < 0 { (len + k).max(0) } else { k.min(len) }),
        Some(_) => None,
    };
    let (from, to) = (usize::try_from(bound(start, 0)?).ok()?, usize::try_from(bound(end, len)?).ok()?);
    Some(Val::List(Rc::new(items.get(from..to.max(from)).unwrap_or(&[]).to_vec())))
}
