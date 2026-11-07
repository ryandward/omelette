//! The model's preconditions on free variables, from how the expression uses them.
use crate::core::Kind;
use oxc_ast::AstKind;
use oxc_ast::ast::{BinaryExpression, CallExpression, Expression};
use oxc_semantic::{NodeId, Semantic};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};
use std::collections::HashMap;

/// Record each free variable's kind: an integer where used as an index, a bound, or an
/// arithmetic operand; a list where used as a receiver; a function where called. A name
/// used in conflicting ways keeps no precondition.
pub fn classify(semantic: &Semantic<'_>, kinds: &mut HashMap<String, Kind>) {
    let scoping = semantic.scoping();
    for (name, references) in scoping.root_unresolved_references() {
        for &reference in references {
            let node = scoping.get_reference(reference).node_id();
            if let Some(kind) = role(semantic, node) {
                let entry = kinds.entry(name.as_str().to_string()).or_insert(kind);
                if *entry != kind {
                    *entry = Kind::Any;
                }
            }
        }
    }
}

fn role(semantic: &Semantic<'_>, node: NodeId) -> Option<Kind> {
    let nodes = semantic.nodes();
    let me = nodes.get_node(node).span();
    match nodes.parent_kind(node) {
        AstKind::ComputedMemberExpression(m) => {
            Some(if m.expression.span() == me { Kind::Int } else { Kind::List })
        }
        AstKind::StaticMemberExpression(_) | AstKind::SpreadElement(_) => Some(Kind::List),
        AstKind::BinaryExpression(b) if numeric_operator(b) => Some(Kind::Int),
        AstKind::BinaryExpression(b) => compares_walker_index(semantic, b, me).then_some(Kind::Int),
        AstKind::UnaryExpression(u) => (u.operator == UnaryOperator::UnaryNegation).then_some(Kind::Int),
        AstKind::CallExpression(c) => call_role(c, me),
        _ => None,
    }
}

fn numeric_operator(b: &BinaryExpression<'_>) -> bool {
    use BinaryOperator as B;
    matches!(
        b.operator,
        B::Subtraction | B::Multiplication | B::LessThan | B::LessEqualThan | B::GreaterThan | B::GreaterEqualThan
    )
}

fn call_role(call: &CallExpression<'_>, me: Span) -> Option<Kind> {
    if call.callee.span() == me {
        return Some(Kind::Fun);
    }
    let Expression::StaticMemberExpression(m) = &call.callee else {
        return None;
    };
    matches!(m.property.name.as_str(), "slice" | "at").then_some(Kind::Int)
}

/// `j === idx` (either side) where `idx` is a walker callback's index parameter: `j` is
/// used as an index.
fn compares_walker_index(semantic: &Semantic<'_>, b: &BinaryExpression<'_>, me: Span) -> bool {
    use BinaryOperator as B;
    if !matches!(b.operator, B::StrictEquality | B::StrictInequality) {
        return false;
    }
    let other = if b.left.span() == me { &b.right } else { &b.left };
    let Expression::Identifier(r) = other.without_parentheses() else { return false };
    let scoping = semantic.scoping();
    scoping
        .get_reference(r.reference_id())
        .symbol_id()
        .is_some_and(|symbol| walker_index(semantic, scoping.symbol_declaration(symbol)))
}

/// A declaration that is the second parameter of a function passed to a walker.
fn walker_index(semantic: &Semantic<'_>, declaration: NodeId) -> bool {
    let nodes = semantic.nodes();
    // The declaration is the node holding the binding: for a parameter, the parameter.
    let mut ancestors = std::iter::once(declaration).chain(nodes.ancestor_ids(declaration)).map(|id| nodes.kind(id));
    let Some(AstKind::FormalParameter(param)) = ancestors.find(|k| matches!(k, AstKind::FormalParameter(_))) else {
        return false;
    };
    let Some(AstKind::FormalParameters(params)) = ancestors.next() else { return false };
    if params.items.get(1).is_none_or(|second| second.span != param.span) {
        return false;
    }
    let Some(function) = ancestors.next() else { return false };
    let Some(AstKind::CallExpression(call)) = ancestors.next() else { return false };
    let passed = call.arguments.first().is_some_and(|a| a.span() == function.span());
    let walker = matches!(&call.callee, Expression::StaticMemberExpression(m)
        if matches!(m.property.name.as_str(), "map" | "filter" | "find" | "every" | "some" | "flatMap"));
    passed && walker
}
