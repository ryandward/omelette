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
        if let Some(b) = self.builtin_member(&c.callee) {
            return self.apply(Val::Builtin(b), args);
        }
        if let Expression::StaticMemberExpression(m) = &c.callee {
            if m.optional {
                return self.unsupported();
            }
            let receiver = self.expr(&m.object);
            let name = m.property.name.as_str();
            let mutator = crate::core::Mutator::method(name);
            let values = std::iter::once(receiver).chain(args).collect();
            return self.strict(values, &mut |l, mut values| {
                let receiver = values.remove(0);
                match mutator {
                    Some(m) => l.mutate(receiver, m, &values),
                    None => l.method(receiver, name, &values),
                }
            });
        }
        let callee = self.expr(&c.callee);
        self.apply(callee, args)
    }
    /// Call a value once it and its arguments are evaluated.
    pub fn apply(&mut self, callee: Val<'a>, args: Vec<Val<'a>>) -> Val<'a> {
        if callee.may_throw() || args.iter().any(Val::may_throw) {
            let values = std::iter::once(callee).chain(args).collect();
            return self.strict(values, &mut |l, mut values| {
                let callee = values.remove(0);
                l.invoke(callee, values)
            });
        }
        self.invoke(callee, args)
    }
    /// Inline a known function, throw for a value that is not one, or leave an opaque call.
    fn invoke(&mut self, callee: Val<'a>, args: Vec<Val<'a>>) -> Val<'a> {
        if not_callable(&callee) || matches!(callee, Val::Throw) {
            return Val::Throw;
        }
        match callee {
            Val::Fun(f) if self.depth < INLINE_DEPTH => self.inline(&f, args),
            Val::Builtin(b) => self.builtin(b, &args),
            Val::Split(_) => self.lift(callee, Family::Propagate, &mut |l, f| l.invoke(f, args.clone())),
            callee => {
                let mut children = vec![self.emit(&callee)];
                children.extend(args.iter().map(|a| self.emit(a)));
                self.clobber();
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
                // A bound array has an identity its aliases share.
                let value = self.own(value);
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
            Statement::ExpressionStatement(e) => {
                let v = self.expr(&e.expression);
                self.strict(vec![v], &mut |l, _| l.run(rest))
            }
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
    /// A method on a receiver: its contents decide the dispatch, and its callbacks receive the
    /// receiver itself.
    fn method(&mut self, receiver: Val<'a>, name: &str, args: &[Val<'a>]) -> Val<'a> {
        // The callbacks can reach and change the receiver, so it has an identity.
        let this = match receiver {
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => self.own(receiver),
            receiver => receiver,
        };
        let receiver = self.deref(this.clone());
        let saved = self.this.replace(this);
        let out = self.dispatch(receiver, name, args);
        self.this = saved;
        out
    }
    fn dispatch(&mut self, receiver: Val<'a>, name: &str, args: &[Val<'a>]) -> Val<'a> {
        if receiver.items().is_some()
            && let Some(early) = self.precheck(&receiver, name, args)
        {
            return early;
        }
        match receiver {
            Val::List(items) => self.literal_method(&items, name, args),
            Val::Short(s) => self.short_method(&s, name, args),
            Val::Term(id, Ty::List(items)) => self.term_method(Seq { id, items }, name, args),
            // Each world's contents, with the receiver the callbacks see unchanged.
            Val::Split(_) => self.lift(receiver, Family::Propagate, &mut |l, r| match r {
                Val::Undef => Val::Throw,
                r => l.dispatch(r, name, args),
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
                // Each result is held in the new list, so an array among them gets an identity.
                let mapped = self.each(items, &f);
                self.strict(mapped, &mut |l, mapped| Val::List(Rc::new(mapped.into_iter().map(|v| l.own(v)).collect())))
            }
            "filter" => self.filter_items(items, &f),
            "find" => self.find_items(items, &f, 0),
            "slice" => slice_items(items, args.first(), args.get(1)).unwrap_or_else(|| self.unsupported()),
            "at" => self.at_items(items, &f),
            "every" | "some" => self.quantify(items, &f, name == "every", 0),
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
    /// The callback on every element: `map` keeps the receiver's length at the start and
    /// reads each element as it is when its turn comes.
    fn each(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>) -> Vec<Val<'a>> {
        let list = self.this_or(Val::List(items.clone()));
        (0..items.len())
            .map(|k| {
                // A removed element leaves a hole, which lowering does not model.
                let x = self.item_at(items, k).unwrap_or_else(|| self.unsupported());
                self.apply(f.clone(), vec![x, index(k), list.clone()])
            })
            .collect()
    }
    /// Element `k` of the list a literal walker runs over, as it is now, since a callback may
    /// have changed the receiver; `None` where it is gone.
    fn item_at(&mut self, items: &Rc<Vec<Val<'a>>>, k: usize) -> Option<Val<'a>> {
        let Some(this @ Val::Ref(_)) = self.this.clone() else { return items.get(k).cloned() };
        let now = self.deref(this);
        if let Val::List(now) = self.settle(now) {
            now.get(k).cloned()
        } else {
            self.clobber();
            items.get(k).cloned()
        }
    }
    /// `every` or `some` over a literal list, from element `k`: each callback runs only while
    /// the answer is still open.
    fn quantify(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>, every: bool, k: usize) -> Val<'a> {
        if k >= items.len() {
            return Val::Bool(every);
        }
        let Some(item) = self.item_at(items, k) else { return self.quantify(items, f, every, k + 1) };
        let list = self.this_or(Val::List(items.clone()));
        let v = self.apply(f.clone(), vec![item, Val::int(i64::try_from(k).unwrap_or(i64::MAX)), list]);
        let truth = self.truthy_split(v);
        self.worlds(truth, Family::Default, &mut |l, t| match l.truthy(t) {
            Val::Bool(b) if b == every => l.quantify(items, f, every, k + 1),
            Val::Bool(_) => Val::Bool(!every),
            Val::Throw => Val::Throw,
            t => {
                let join = super::refs::Join::Test { test: t.clone(), first_if: every };
                let (more, stop) = l.fork(&mut |l, second| if second { Val::Bool(!every) } else { l.quantify(items, f, every, k + 1) }, &join);
                if every { l.select(&t, more, stop) } else { l.select(&t, stop, more) }
            }
        })
    }
    fn truthy_split(&mut self, v: Val<'a>) -> Val<'a> {
        self.lift(v, Family::Sink, &mut |l, v| l.truthy(v))
    }
    fn fold_items(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        let list = self.this_or(Val::List(items.clone()));
        let mut ks = 0..items.len();
        let mut acc = init;
        while acc.is_none() {
            let Some(k) = ks.next() else { return Val::Throw };
            acc = self.item_at(items, k);
        }
        let mut acc = acc.unwrap_or(Val::Throw);
        for k in ks {
            if let Some(x) = self.item_at(items, k) {
                acc = self.apply(f.clone(), vec![acc, x, index(k), list.clone()]);
            }
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
    /// The separator `join` writes: a comma where the argument is undefined, which writes a
    /// default for a separator that may be missing.
    fn separator(&mut self, sep: Option<Val<'a>>) -> Val<'a> {
        let comma = Val::Str(crate::core::Utf16::new(",".encode_utf16()));
        match sep {
            None => comma,
            Some(v) => self.lift(v, Family::Default, &mut |l, v| match v {
                Val::Undef => comma.clone(),
                v => l.to_text(v),
            }),
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
            Val::Ref(_) => l.deref(v),
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
    pub fn short_method(&mut self, s: &Rc<Short<'a>>, name: &str, args: &[Val<'a>]) -> Val<'a> {
        let f = args.first().cloned().unwrap_or(Val::Undef);
        match name {
            "every" | "some" => {
                let every = name == "every";
                let unit = Val::Bool(every);
                self.over_slot(s, Family::Unit, &unit, &mut |l, x| {
                    let array = l.this_or(Val::Short(s.clone()));
                    let v = l.apply(f.clone(), vec![x, Val::int(0), array]);
                    l.truthy_split(v)
                })
            }
            "reduce" => {
                let init = args.get(1).cloned();
                let unit = init.clone().unwrap_or(Val::Throw);
                self.over_slot(s, Family::Unit, &unit, &mut |l, x| match &init {
                    Some(z) => {
                        let array = l.this_or(Val::Short(s.clone()));
                        l.apply(f.clone(), vec![z.clone(), x, Val::int(0), array])
                    }
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
        let read_list = self.slot_list(s);
        self.worlds(slot, family, &mut |l, v| {
            if matches!(v, Val::Undef) {
                return unit.clone();
            }
            // The callback runs only on an element the filters kept.
            let mut run = |l: &mut Self| {
                l.walking.push(read_list);
                let value = present(l, elem.clone());
                l.walking.pop();
                value
            };
            match &keep {
                Val::Bool(false) => unit.clone(),
                Val::Bool(true) => run(l),
                keep => {
                    let join = super::refs::Join::Test { test: keep.clone(), first_if: true };
                    let (value, _) = l.fork(&mut |l, second| if second { unit.clone() } else { run(l) }, &join);
                    l.select(keep, value, unit.clone())
                }
            }
        })
    }
    /// The list the slot reads, which is non-empty where the slot is present.
    fn slot_list(&self, s: &Short<'a>) -> Id {
        match self.b.node(s.read) {
            Core::Read([list, _]) => *list,
            _ => s.list.id,
        }
    }
    /// A walker over the short list: its callback runs only where the slot is present.
    fn short_walk(&mut self, s: &Rc<Short<'a>>, name: &str, f: &Val<'a>) -> Val<'a> {
        // The walker below runs the callback with its effects, guarded by the list being
        // non-empty; the element's value comes from running it once more, as the walker would.
        let (world, read_list) = (Val::Term(s.var, s.items.ty()), self.slot_list(s));
        let (outer, choices) = (self.state.cells.clone(), self.choices.len());
        let applied = if matches!(s.keep, Val::Bool(false)) {
            Val::Undef
        } else {
            self.speculate(|l| {
                l.within(s.read, world, |l| {
                    l.walking.push(read_list);
                    let array = l.this_or(Val::Short(s.clone()));
                    let out = l.apply(f.clone(), vec![s.elem.clone(), Val::int(0), array]);
                    l.walking.pop();
                    l.detach(out, &outer, choices)
                })
            })
        };
        let kind = if name == "filter" { Walker::Filter } else { Walker::Map };
        let list = self.walker(kind, f, s.list);
        let mut next = Short { list, ..(**s).clone() };
        if name == "filter" {
            let pass = self.truthy_split(applied);
            next.keep = self.and_split(s.keep.clone(), pass);
        } else {
            next.elem = self.own(applied);
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
                let sep = self.emit(&sep);
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
        let (state, this) = (self.state.clone(), self.this_or(list.val()));
        let (lam, items) = match f {
            Val::Fun(_) | Val::Builtin(_) => self.callback(kind, f, list),
            other => {
                let lam = self.emit(other);
                self.clobber();
                (lam, Items::Any)
            }
        };
        let node = self.b.add(match kind {
            Walker::Map => Core::Map([lam, list.id]),
            Walker::Filter => Core::Filter([lam, list.id]),
            Walker::Every => Core::Every([lam, list.id]),
            Walker::Some => Core::Some([lam, list.id]),
        });
        if kind == Walker::Map && matches!(f, Val::Fun(_) | Val::Builtin(_)) {
            // Arrays the callback built do not count; arrays that outlive it do.
            let writes = self.state.cells.iter().any(|(k, v)| match state.cells.get(k) {
                Some(old) => !old.identical(v),
                None => matches!(k, super::value::RefKey::Input(_)),
            });
            self.maps.insert(node, super::value::Mapping { f: f.clone(), base: list, this, state, writes });
            if std::mem::take(&mut self.built) {
                self.fresh.insert(node);
            }
            if std::mem::take(&mut self.passed) {
                self.passes.insert(node);
            }
        }
        Seq { id: node, items: if kind == Walker::Map { items } else { list.items } }
    }
    /// The callback's lambda, and whether every value it returns is defined.
    fn callback(&mut self, kind: Walker, f: &Val<'a>, list: Seq) -> (Id, Items) {
        let (x, i) = (self.b.fresh(list.items.kind()), self.b.fresh(Kind::Index));
        self.coords.insert(i, list.id);
        self.members.insert(x, list.id);
        let args = vec![Val::Term(x, list.items.ty()), Val::Num(Form::atom(i)), self.this_or(list.val())];
        self.walking.push(list.id);
        let before = self.next_ref;
        let result = self.repeat(list.id, 1, |l| l.apply(f.clone(), args));
        self.walking.pop();
        // A callback that returns an array it just built builds a new one for every element;
        // one that returns its element passes the list's elements through.
        self.built = matches!(result, Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)))
            || matches!(result, Val::Ref(super::value::RefKey::Local(k)) if k > before);
        self.passed = matches!(result, Val::Term(id, _) if id == x);
        let items = Items::of(result.defined());
        let body = if kind == Walker::Map {
            self.escape(&result)
        } else {
            let truth = self.truthy_split(result);
            self.emit(&truth)
        };
        (self.b.add(Core::Lam(vec![x, i, body].into())), items)
    }
    /// A possibly missing read at another collection's coordinate, left as a hole in a
    /// collection shaped like the walked one.
    fn escape(&mut self, v: &Val<'a>) -> Id {
        let id = self.emit(v);
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
            let base = self.base_of(list);
            // A present element is all the filter keeps.
            if self.in_range(base.id, &index) {
                let element = self.element(list, &index);
                return Val::List(Rc::new(vec![element]));
            }
            let idx = self.b.form(&index);
            let slot = self.b.add(Core::Read([base.id, idx]));
            let read = self.element(list, &index);
            return projected(walked, slot, &read);
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
        let saved = std::mem::replace(&mut self.env, fun.env.clone());
        let args = vec![Val::Term(x, list.items.ty()), Val::Num(Form::atom(i)), self.this_or(list.val())];
        // Recognizing a projection evaluates nothing; the walker that replaces it does. The
        // compared expression runs once per element, so one with effects is no projection.
        let (value, pure) = self.probe(|l| l.bind_params(fun, args).then(|| l.expr(target)));
        self.env = saved;
        let (Some(Val::Num(form)), true) = (value, pure) else { return None };
        if form.terms.keys().any(|&a| self.b.mentions(a, x) || self.b.mentions(a, i)) {
            return None;
        }
        self.coords.insert(i, list.id);
        let test = self.strict_eq(&Val::Num(Form::atom(i)), &Val::Num(form.clone()));
        let body = self.emit(&test);
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
        // law also needs the callback to return its element. A callback with effects runs on
        // every element, not only the last.
        let before = self.state.clone();
        let mut returns_element = true;
        let body = self.worlds(slot.clone(), Family::Unit, &mut |l, x| match x {
            Val::Undef => unit.clone(),
            x => {
                let array = l.this_or(list.val());
                let out = l.apply(f.clone(), vec![Val::Term(acc, Ty::Any), x.clone(), Val::Num(final_index.clone()), array]);
                returns_element &= out.identical(&x);
                out
            }
        });
        let id = self.emit(&body);
        if self.b.mentions(id, acc) || (init.is_none() && !returns_element) || !self.state.same(&before) {
            self.state = before;
            return self.fold(list, &f, init);
        }
        body
    }
    /// A fold over a symbolic list. A seed that may be missing flows into the accumulator,
    /// where the callback may swallow it or not, so its flow is undecided.
    fn fold(&mut self, list: Seq, f: &Val<'a>, init: Option<Val<'a>>) -> Val<'a> {
        if let Some(seed @ Val::Split(_)) = init {
            return self.lift(seed, Family::Undecided, &mut |l, z| l.fold(list, f, Some(z)));
        }
        let (acc, x, i) = (self.b.fresh(Kind::Acc), self.b.fresh(list.items.kind()), self.b.fresh(Kind::Index));
        self.coords.insert(i, list.id);
        self.members.insert(x, list.id);
        let args = vec![Val::Term(acc, Ty::Any), Val::Term(x, list.items.ty()), Val::Num(Form::atom(i)), self.this_or(list.val())];
        self.walking.push(list.id);
        // Without a seed, the callback first runs on the second element.
        let least = if init.is_some() { 1 } else { 2 };
        let body = self.repeat(list.id, least, |l| l.apply(f.clone(), args));
        self.walking.pop();
        let body = self.emit(&body);
        let lam = self.b.add(Core::Lam(vec![acc, x, i, body].into()));
        let init = match init {
            Some(z) => self.emit(&z),
            None => self.b.add(Core::Throw),
        };
        Val::Term(self.b.add(Core::Fold([lam, init, list.id])), Ty::Any)
    }
    /// `list.slice(start, end)`, whose bounds count from the end when negative. Bounds that
    /// differ by `d >= 0` keep at most `d` elements whatever their signs, so a difference of
    /// one is a list of at most one element; a negative difference can keep any number.
    pub fn slice(&mut self, list: Seq, start: Option<Val<'a>>, end: Option<Val<'a>>) -> Val<'a> {
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
        // Known bounds that select nothing: an end at or before a non-negative start, or an end
        // of zero after a start counted from the end.
        let known_end = if open { None } else { end.known() };
        if let (Some(a), Some(z)) = (start.known(), known_end)
            && ((a >= 0 && z >= 0 && z <= a) || (a < 0 && z == 0))
        {
            return Val::empty();
        }
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
            let item = match self.deref(item.clone()) {
                item @ (Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_))) => item,
                v if v.is_known() || matches!(v, Val::Term(_, Ty::Bool | Ty::Str) | Val::Num(_)) => Val::List(Rc::new(vec![v])),
                _ => return self.unsupported(),
            };
            out = self.append(out, item);
        }
        out
    }
}

/// A value calling which certainly throws.
fn not_callable(v: &Val<'_>) -> bool {
    matches!(v, Val::Undef | Val::NaN | Val::Bool(_) | Val::Num(_) | Val::Str(_) | Val::List(_) | Val::Short(_) | Val::Ref(_))
        || matches!(v, Val::Term(_, Ty::Bool | Ty::Str | Ty::List(_)))
}

/// A filtered list holding at most the element `slot` reads, with that element's value where
/// present (a mapped list's mapped value) and the read's drift. When the value is not a split
/// on that read, its presence is not tracked, and the filter stays a term.
fn projected<'a>(list: Seq, slot: Id, value: &Val<'a>) -> Val<'a> {
    let Val::Split(s) = value else { return list.val() };
    if s.read != slot {
        return list.val();
    }
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
    /// The kept elements: each element's keep decides, in every world of its splits,
    /// whether the element is appended, and a symbolic keep appends it conditionally.
    fn filter_items(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>) -> Val<'a> {
        let list = self.this_or(Val::List(items.clone()));
        (0..items.len()).fold(Val::empty(), |acc, k| {
            let Some(item) = self.item_at(items, k) else { return acc };
            let keep = self.apply(f.clone(), vec![item.clone(), index(k), list.clone()]);
            let keep = self.truthy_split(keep);
            self.lift2(acc, keep, Family::Propagate, &mut |l, acc, keep| match keep {
                Val::Bool(false) => acc,
                Val::Throw => Val::Throw,
                keep => {
                    let item = l.settle(item.clone());
                    let kept = l.append(acc.clone(), Val::List(Rc::new(vec![item])));
                    l.select(&keep, kept, acc)
                }
            })
        })
    }
    /// The first element the callback accepts, or undefined.
    fn find_items(&mut self, items: &Rc<Vec<Val<'a>>>, f: &Val<'a>, k: usize) -> Val<'a> {
        if k >= items.len() {
            return Val::Undef;
        }
        // find reads every index up to the starting length, present or not.
        let item = self.item_at(items, k).unwrap_or(Val::Undef);
        let list = self.this_or(Val::List(items.clone()));
        let v = self.apply(f.clone(), vec![item.clone(), Val::int(i64::try_from(k).unwrap_or(i64::MAX)), list]);
        let truth = self.truthy_split(v);
        self.worlds(truth, Family::Default, &mut |l, t| match l.truthy(t) {
            Val::Bool(true) => l.settle(item.clone()),
            Val::Bool(false) => l.find_items(items, f, k + 1),
            Val::Throw => Val::Throw,
            t => {
                let join = super::refs::Join::Test { test: t.clone(), first_if: true };
                let (found, rest) = l.fork(&mut |l, second| if second { l.find_items(items, f, k + 1) } else { l.settle(item.clone()) }, &join);
                l.select(&t, found, rest)
            }
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

fn index<'a>(k: usize) -> Val<'a> {
    Val::int(i64::try_from(k).unwrap_or(i64::MAX))
}
