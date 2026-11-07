//! The model's preconditions on free variables, from how the expression uses them.
use crate::core::Kind;
use oxc_ast::AstKind;
use oxc_ast::ast::{BinaryExpression, CallExpression, Expression};
use oxc_semantic::{AstNodes, NodeId, Semantic};
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
            if let Some(kind) = role(semantic.nodes(), node) {
                let entry = kinds.entry(name.as_str().to_string()).or_insert(kind);
                if *entry != kind {
                    *entry = Kind::Any;
                }
            }
        }
    }
}

fn role(nodes: &AstNodes<'_>, node: NodeId) -> Option<Kind> {
    let me = nodes.get_node(node).span();
    match nodes.parent_kind(node) {
        AstKind::ComputedMemberExpression(m) => {
            Some(if m.expression.span() == me { Kind::Int } else { Kind::List })
        }
        AstKind::StaticMemberExpression(_) | AstKind::SpreadElement(_) => Some(Kind::List),
        AstKind::BinaryExpression(b) => numeric_operator(b).then_some(Kind::Int),
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
