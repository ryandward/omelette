//! Lowering: a partial evaluator that owns JavaScript's operational semantics and emits core
//! terms for egg. See docs/architecture.md.
mod build;
mod builtins;
mod calls;
mod expr;
mod lists;
mod mutate;
mod ops;
mod refs;
mod usage;
mod value;

use crate::core::{Core, Kind};
use build::Builder;
use egg::{Id, RecExpr};
use oxc_allocator::Allocator;
use oxc_ast::ast::{Expression, Program, Statement};
use oxc_parser::Parser;
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use std::collections::HashMap;
use value::{Env, Val};

/// A lowered expression.
pub struct Lowered {
    pub expr: RecExpr<Core>,
    /// The mutations someone outside the expression may observe, as a list of `mutate`
    /// terms; `None` when there are none.
    pub effects: Option<RecExpr<Core>>,
    /// Lowering evaluated a construct it does not model, a call it could not resolve, or a
    /// walker over an unknown callback. Any of them may throw, so the expression's value is
    /// unknown even where its term does not mention them.
    pub opaque: bool,
}

/// Lower one expression.
///
/// # Errors
/// A syntax error, or source that is not a single expression.
pub fn lower(source: &str) -> Result<Lowered, String> {
    Ok(lower_all(&[source])?.remove(0))
}

/// Lower expressions that share their free variables: one used as a number in any of them
/// is an integer in all of them.
///
/// # Errors
/// A syntax error, or a source that is not a single expression.
pub fn lower_all(sources: &[&str]) -> Result<Vec<Lowered>, String> {
    let arena = Allocator::default();
    let wrapped: Vec<String> = sources.iter().map(|s| format!("(\n{s}\n);")).collect();
    let programs = wrapped
        .iter()
        .map(|s| parse(&arena, s))
        .collect::<Result<Vec<_>, _>>()?;
    let semantics: Vec<_> = programs
        .iter()
        .map(|p| SemanticBuilder::new().with_build_nodes(true).build(p).semantic)
        .collect();
    let mut kinds = HashMap::new();
    for semantic in &semantics {
        usage::classify(semantic, &mut kinds);
    }
    Ok(programs
        .iter()
        .zip(&semantics)
        .map(|(program, semantic)| {
            let mut lowerer = Lowerer::new(semantic.scoping(), &kinds);
            let value = lowerer.expr(expression(program));
            let root = lowerer.emit(&value);
            let log = lowerer.state.log.clone();
            let effects = match &log {
                Val::List(entries) if entries.is_empty() => None,
                log => {
                    let id = lowerer.emit(log);
                    Some(lowerer.b.finish(id))
                }
            };
            Lowered { expr: lowerer.b.finish(root), effects, opaque: lowerer.opaque }
        })
        .collect())
}

fn parse<'a>(arena: &'a Allocator, source: &'a str) -> Result<Program<'a>, String> {
    let parsed = Parser::new(arena, source, SourceType::ts()).parse();
    if !parsed.diagnostics.is_empty() {
        return Err(format!("{:?}", parsed.diagnostics));
    }
    let program = parsed.program;
    match program.body.as_slice() {
        [Statement::ExpressionStatement(_)] => Ok(program),
        _ => Err("expected a single expression".into()),
    }
}

fn expression<'p, 'a>(program: &'p Program<'a>) -> &'p Expression<'a> {
    let Statement::ExpressionStatement(s) = &program.body[0] else {
        unreachable!("parse admits only one expression statement")
    };
    &s.expression
}

/// The partial evaluator's state while lowering one expression.
pub struct Lowerer<'a, 'l> {
    b: Builder,
    scoping: &'l Scoping,
    kinds: &'l HashMap<String, Kind>,
    env: Env<'a>,
    /// Reads whose presence a branch has decided: absent, or the element.
    narrow: HashMap<Id, Val<'a>>,
    /// The element binder of every read, so all splits on one read agree.
    elems: HashMap<Id, Id>,
    /// Each walker index binder, with the list it ranges over.
    coords: HashMap<Id, Id>,
    /// Each element binder, with the list it is an element of.
    members: HashMap<Id, Id>,
    /// Mapped lists whose callback builds a new array for every element.
    fresh: std::collections::HashSet<Id>,
    /// Mapped lists whose callback returns its element.
    passes: std::collections::HashSet<Id>,
    /// Whether the last walker callback lowered returned an array it built.
    built: bool,
    /// Whether the last walker callback lowered returned its element.
    passed: bool,
    /// The lists whose walkers' callbacks are being lowered: each is non-empty there.
    walking: Vec<Id>,
    /// Each mapped list, with what reading its elements needs.
    maps: HashMap<Id, value::Mapping<'a>>,
    depth: usize,
    /// See [`Lowered::opaque`].
    opaque: bool,
    /// The store and effect log along the path being lowered.
    state: refs::State<'a>,
    /// Each choice reference's test and alternatives.
    choices: Vec<(Val<'a>, Val<'a>, Val<'a>)>,
    /// The last local reference allocated.
    next_ref: u32,
    /// The receiver of the list method being lowered, which its callbacks receive.
    this: Option<Val<'a>>,
    /// The references being resolved into a term, innermost last.
    resolving: Vec<value::RefKey>,
    /// The references whose contents some term holds.
    embedded: std::collections::HashSet<value::RefKey>,
    /// Each reference's contents, resolved, during one emission.
    resolved: HashMap<value::RefKey, Val<'a>>,
}

impl<'l> Lowerer<'_, 'l> {
    fn new(scoping: &'l Scoping, kinds: &'l HashMap<String, Kind>) -> Self {
        Self {
            b: Builder::default(),
            scoping,
            kinds,
            env: Env::new(),
            narrow: HashMap::new(),
            elems: HashMap::new(),
            coords: HashMap::new(),
            members: HashMap::new(),
            fresh: std::collections::HashSet::new(),
            passes: std::collections::HashSet::new(),
            built: false,
            passed: false,
            walking: Vec::new(),
            maps: HashMap::new(),
            depth: 0,
            opaque: false,
            state: refs::State::new(),
            choices: Vec::new(),
            next_ref: 0,
            this: None,
            resolving: Vec::new(),
            embedded: std::collections::HashSet::new(),
            resolved: HashMap::new(),
        }
    }
}
