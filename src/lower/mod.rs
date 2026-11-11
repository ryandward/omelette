//! Lowering: a partial evaluator that owns JavaScript's operational semantics and emits core
//! terms for egg. See docs/architecture.md.
mod build;
mod builtins;
mod calls;
mod declare;
mod expr;
mod lists;
mod mutate;
mod ops;
mod refs;
mod usage;
mod value;

use crate::core::{Core, Kind, Utf16};
use build::Builder;
use egg::{Id, RecExpr};
use oxc_allocator::Allocator;
use oxc_ast::ast::{Program, Statement};
use oxc_parser::Parser;
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashMap;
use declare::Declared;
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

/// Lower one expression, optionally after `declare const` statements that give free
/// variables TypeScript types.
///
/// # Errors
/// A syntax error, source that is not a single expression after its declarations, or a
/// declaration lowering does not accept.
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
    // A source with a prelude is a program; any other is one expression, parenthesized so an
    // object literal is not a block.
    let texts: Vec<String> = sources.iter().map(|s| if has_prelude(s) { (*s).to_string() } else { format!("(\n{s}\n);") }).collect();
    let programs = texts.iter().map(|s| parse(&arena, s)).collect::<Result<Vec<_>, _>>()?;
    let mut declared: HashMap<String, Declared> = HashMap::new();
    for program in &programs {
        for (name, ty) in declare::prelude(program)? {
            if declared.insert(name.clone(), ty).is_some_and(|old| old != ty) {
                return Err(format!("`{name}` is declared twice"));
            }
        }
    }
    let semantics: Vec<_> = programs
        .iter()
        .map(|p| SemanticBuilder::new().with_build_nodes(true).build(p).semantic)
        .collect();
    let ambient: Vec<_> = programs.iter().map(|p| declare::ambient(p)).collect();
    let types: Vec<_> = programs.iter().map(declare::Types::of).collect();
    let mut kinds = HashMap::new();
    for (semantic, ambient) in semantics.iter().zip(&ambient) {
        usage::classify(semantic, ambient, &mut kinds);
    }
    for (name, ty) in &declared {
        kinds.insert(name.clone(), declare::kind(*ty, kinds.get(name).copied()));
    }
    Ok(programs
        .iter()
        .zip(&semantics)
        .zip(&ambient)
        .zip(&types)
        .map(|(((program, semantic), ambient), types)| {
            let mut lowerer = Lowerer::new(semantic.scoping(), &kinds, &declared, types);
            lowerer.ambient = ambient.iter().map(|(_, symbol)| *symbol).collect();
            let value = lowerer.module(&program.body);
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

/// Whether a source starts with a prelude: declarations or definitions before its
/// expression.
fn has_prelude(source: &str) -> bool {
    let first = source.trim_start().split(|c: char| !c.is_ascii_alphabetic()).next().unwrap_or("");
    matches!(first, "declare" | "const" | "function" | "let" | "var" | "type" | "interface")
}

fn parse<'a>(arena: &'a Allocator, source: &'a str) -> Result<Program<'a>, String> {
    let parsed = Parser::new(arena, source, SourceType::ts()).parse();
    if !parsed.diagnostics.is_empty() {
        return Err(format!("{:?}", parsed.diagnostics));
    }
    let program = parsed.program;
    match program.body.as_slice() {
        [.., Statement::ExpressionStatement(_)] => Ok(program),
        _ => Err("expected a single expression".into()),
    }
}

/// The partial evaluator's state while lowering one expression.
pub struct Lowerer<'a, 'l> {
    b: Builder,
    scoping: &'l Scoping,
    kinds: &'l HashMap<String, Kind>,
    /// What declarations say the free variables hold.
    declared: &'l HashMap<String, Declared>,
    /// The variables `declare const` names: inputs, though the program binds them.
    ambient: FxHashSet<oxc_semantic::SymbolId>,
    /// Each stand-in for a declared or widened answer, with the exact answer, which control
    /// flow still follows.
    exact: FxHashMap<Id, Val<'a>>,
    /// Each string the source spells, as text.
    texts: FxHashMap<&'a str, Utf16>,
    /// Each declared return type's form, by the type's address in the program.
    forms: FxHashMap<usize, std::rc::Rc<declare::Form>>,
    /// The types the program names, through which a declared return type resolves.
    types: &'l declare::Types<'l, 'a>,
    /// The helpers the program defines before its expression, which any code may call.
    defined: FxHashMap<oxc_semantic::SymbolId, Val<'a>>,
    env: Env<'a>,
    /// Reads whose presence a branch has decided: absent, or the element.
    narrow: FxHashMap<Id, Val<'a>>,
    /// The element binder of every read, so all splits on one read agree.
    elems: FxHashMap<Id, Id>,
    /// Each walker index binder, with the list it ranges over.
    coords: FxHashMap<Id, Id>,
    /// Each element binder, with the list it is an element of.
    members: FxHashMap<Id, Id>,
    /// Mapped lists whose callback builds a new array for every element.
    fresh: FxHashSet<Id>,
    /// Mapped lists whose callback returns its element.
    passes: FxHashSet<Id>,
    /// Whether the last walker callback lowered returned an array it built.
    built: bool,
    /// Whether the last walker callback lowered returned its element.
    passed: bool,
    /// The lists whose walkers' callbacks are being lowered: each is non-empty there.
    walking: Vec<Id>,
    /// Each mapped list, with what reading its elements needs.
    maps: FxHashMap<Id, value::Mapping<'a>>,
    depth: usize,
    /// See [`Lowered::opaque`].
    opaque: bool,
    /// The store and effect log along the path being lowered.
    state: refs::State<'a>,
    /// Each choice reference's test and alternatives.
    choices: Vec<(Val<'a>, Val<'a>, Val<'a>)>,
    /// The last local reference allocated.
    next_ref: u32,
    /// The arrays whose text is being written, innermost last.
    joining: Vec<value::RefKey>,
    /// The receiver of the list method being lowered, which its callbacks receive.
    this: Option<Val<'a>>,
    /// The references being resolved into a term, innermost last.
    resolving: Vec<value::RefKey>,
    /// The references whose contents some term holds.
    embedded: FxHashSet<value::RefKey>,
    /// Each reference's contents, resolved, during one emission.
    resolved: FxHashMap<value::RefKey, Val<'a>>,
}

impl<'a, 'l> Lowerer<'a, 'l> {
    fn new(scoping: &'l Scoping, kinds: &'l HashMap<String, Kind>, declared: &'l HashMap<String, Declared>, types: &'l declare::Types<'l, 'a>) -> Self {
        Self {
            b: Builder::default(),
            scoping,
            kinds,
            declared,
            ambient: FxHashSet::default(),
            types,
            exact: FxHashMap::default(),
            forms: FxHashMap::default(),
            texts: FxHashMap::default(),
            defined: FxHashMap::default(),
            env: Env::default(),
            narrow: FxHashMap::default(),
            elems: FxHashMap::default(),
            coords: FxHashMap::default(),
            members: FxHashMap::default(),
            fresh: FxHashSet::default(),
            passes: FxHashSet::default(),
            built: false,
            passed: false,
            walking: Vec::new(),
            maps: FxHashMap::default(),
            depth: 0,
            opaque: false,
            state: refs::State::new(),
            choices: Vec::new(),
            next_ref: 0,
            this: None,
            joining: Vec::new(),
            resolving: Vec::new(),
            embedded: FxHashSet::default(),
            resolved: FxHashMap::default(),
        }
    }
    /// A string the source spells, as text, encoded once however often lowering visits it.
    fn spelled(&mut self, s: &'a str) -> Utf16 {
        *self.texts.entry(s).or_insert_with(|| Utf16::new(s.encode_utf16()))
    }
}
