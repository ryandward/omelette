//! Lowering: a partial evaluator that owns JavaScript's operational semantics and emits core
//! terms for egg. See docs/architecture.md.
mod build;
mod calls;
mod expr;
mod lists;
mod ops;
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

/// Lower one expression.
///
/// # Errors
/// A syntax error, or source that is not a single expression.
pub fn lower(source: &str) -> Result<RecExpr<Core>, String> {
    Ok(lower_all(&[source])?.remove(0))
}

/// Lower expressions that share their free variables: one used as a number in any of them
/// is an integer in all of them.
///
/// # Errors
/// A syntax error, or a source that is not a single expression.
pub fn lower_all(sources: &[&str]) -> Result<Vec<RecExpr<Core>>, String> {
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
            let root = lowerer.b.emit(&value);
            lowerer.b.finish(root)
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
    /// Each mapped list, with its callback and the list it maps.
    maps: HashMap<Id, (Val<'a>, Id)>,
    depth: usize,
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
            maps: HashMap::new(),
            depth: 0,
        }
    }
}
