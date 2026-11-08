//! Declared types: `declare const xs: string[];` before the expression says what a free
//! variable holds, which narrows the model's preconditions. TypeScript is structural, so an
//! object type admits arrays and functions too; a type lowering cannot name holds anything.
use super::value::Builtin;
use crate::core::{Kind, Shape};
use oxc_ast::ast::{
    BindingPattern, Program, Statement, TSLiteral, TSSignature, TSTupleElement, TSType, TSTypeLiteral, TSTypeName,
    TSTypeOperatorOperator,
};
use oxc_span::GetSpan;
use std::collections::HashMap;

/// What a declaration says a free variable holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Declared {
    /// A list whose elements have this shape.
    List(Shape),
    /// A value of this shape.
    Value(Shape),
}

/// A source's declarations, and the span of the expression after them, when it has any.
///
/// # Errors
/// A statement other than a declaration before the expression, a declaration without a
/// type, or a type that holds what the model does not (`null`, `bigint`, `symbol`).
pub fn prelude<'s>(program: &Program<'_>, source: &'s str) -> Result<(HashMap<String, Declared>, &'s str), String> {
    let mut declared = HashMap::new();
    let Some((last, declarations)) = program.body.split_last() else { return Err("expected an expression".into()) };
    for statement in declarations {
        let Statement::VariableDeclaration(d) = statement else { return Err("only `declare const` may precede the expression".into()) };
        if !d.declare {
            return Err("only `declare const` may precede the expression".into());
        }
        for v in &d.declarations {
            let BindingPattern::BindingIdentifier(name) = &v.id else { return Err("a declaration names one variable".into()) };
            let Some(annotation) = &v.type_annotation else { return Err(format!("`{}` has no type", name.name)) };
            if Builtin::is_global(name.name.as_str()) {
                return Err(format!("`{}` is a global omelette models", name.name));
            }
            let ty = declaration(&annotation.type_annotation)?;
            if declared.insert(name.name.to_string(), ty).is_some_and(|old| old != ty) {
                return Err(format!("`{}` is declared twice", name.name));
            }
        }
    }
    let Statement::ExpressionStatement(e) = last else { return Err("expected an expression after the declarations".into()) };
    let span = e.expression.span();
    Ok((declared, &source[span.start as usize..span.end as usize]))
}

/// The kind a declared variable takes: a declared list is a list, and otherwise the kind its
/// uses give it stands where the declaration agrees with it (an integer is a number, a
/// function a function), and is overridden where it does not.
pub fn kind(ty: Declared, used: Option<Kind>) -> Kind {
    match (ty, used) {
        (Declared::List(_), _) => Kind::List,
        (Declared::Value(s), Some(Kind::Int)) if s == Shape::NUM => Kind::Int,
        (Declared::Value(s), _) if s.within(Shape::FUN) => Kind::Fun,
        (Declared::Value(_), _) => Kind::Any,
    }
}

fn declaration(t: &TSType<'_>) -> Result<Declared, String> {
    Ok(match elements(t)? {
        Some(items) => Declared::List(items),
        None => Declared::Value(shape(t)?),
    })
}

/// The elements of an array type, or `None` for any other type.
fn elements(t: &TSType<'_>) -> Result<Option<Shape>, String> {
    Ok(Some(match t {
        TSType::TSArrayType(a) => shape(&a.element_type)?,
        TSType::TSTupleType(t) => {
            let mut items = Shape::NONE;
            for e in &t.element_types {
                items = items.or(element(e)?);
            }
            items
        }
        TSType::TSTypeOperatorType(o) if o.operator == TSTypeOperatorOperator::Readonly => return elements(&o.type_annotation),
        TSType::TSParenthesizedType(p) => return elements(&p.type_annotation),
        TSType::TSTypeReference(r) if matches!(name(&r.type_name), Some("Array" | "ReadonlyArray")) => {
            match r.type_arguments.as_ref().and_then(|a| a.params.first()) {
                Some(t) => shape(t)?,
                None => Shape::ALL,
            }
        }
        _ => return Ok(None),
    }))
}

/// What one element of a tuple can be.
fn element(e: &TSTupleElement<'_>) -> Result<Shape, String> {
    match e {
        // A missing optional element reads as undefined.
        TSTupleElement::TSOptionalType(o) => Ok(shape(&o.type_annotation)?.or(Shape::UNDEF)),
        TSTupleElement::TSRestType(r) => Ok(elements(&r.type_annotation)?.unwrap_or(Shape::ALL)),
        other => other.as_ts_type().map_or(Ok(Shape::ALL), shape),
    }
}

fn name<'a>(n: &'a TSTypeName<'_>) -> Option<&'a str> {
    match n {
        TSTypeName::IdentifierReference(id) => Some(id.name.as_str()),
        _ => None,
    }
}

/// The JavaScript types a value of TypeScript type `t` can have.
fn shape(t: &TSType<'_>) -> Result<Shape, String> {
    let object = Shape::OBJ.or(Shape::LIST).or(Shape::FUN);
    Ok(match t {
        TSType::TSStringKeyword(_) | TSType::TSTemplateLiteralType(_) => Shape::STR,
        TSType::TSNumberKeyword(_) => Shape::NUM,
        TSType::TSBooleanKeyword(_) => Shape::BOOL,
        TSType::TSUndefinedKeyword(_) | TSType::TSVoidKeyword(_) => Shape::UNDEF,
        TSType::TSNeverKeyword(_) => Shape::NONE,
        TSType::TSObjectKeyword(_) => object,
        TSType::TSTypeLiteral(l) => literal(l),
        TSType::TSFunctionType(_) | TSType::TSConstructorType(_) => Shape::FUN,
        TSType::TSArrayType(_) | TSType::TSTupleType(_) => Shape::LIST,
        TSType::TSLiteralType(l) => match &l.literal {
            TSLiteral::BooleanLiteral(_) => Shape::BOOL,
            TSLiteral::NumericLiteral(_) | TSLiteral::UnaryExpression(_) => Shape::NUM,
            TSLiteral::StringLiteral(_) | TSLiteral::TemplateLiteral(_) => Shape::STR,
            TSLiteral::BigIntLiteral(_) => return Err("bigint is not modeled".into()),
        },
        TSType::TSUnionType(u) => {
            let mut out = Shape::NONE;
            for t in &u.types {
                out = out.or(shape(t)?);
            }
            out
        }
        TSType::TSIntersectionType(i) => {
            let mut out = Shape::ALL;
            for t in &i.types {
                out = out.and(shape(t)?);
            }
            out
        }
        TSType::TSParenthesizedType(p) => shape(&p.type_annotation)?,
        TSType::TSTypeOperatorType(o) if o.operator == TSTypeOperatorOperator::Readonly => shape(&o.type_annotation)?,
        TSType::TSNamedTupleMember(m) => {
            let e = element(&m.element_type)?;
            if m.optional { e.or(Shape::UNDEF) } else { e }
        }
        TSType::TSNullKeyword(_) | TSType::JSDocNullableType(_) => return Err("null is not modeled".into()),
        TSType::TSBigIntKeyword(_) => return Err("bigint is not modeled".into()),
        TSType::TSSymbolKeyword(_) => return Err("symbol is not modeled".into()),
        TSType::TSTypeReference(r) => match name(&r.type_name) {
            Some("Array" | "ReadonlyArray") => Shape::LIST,
            Some("Function") => Shape::FUN,
            // The wrappers' types also admit their primitives.
            Some("String") => Shape::STR.or(object),
            Some("Number") => Shape::NUM.or(object),
            Some("Boolean") => Shape::BOOL.or(object),
            // Any value but `undefined` has `Object`'s members, and a record's keys may be ones
            // a primitive has.
            Some("Object" | "Record") => Shape::DEFINED,
            Some("Map" | "Set" | "WeakMap" | "WeakSet" | "Date" | "RegExp" | "Promise" | "Error") => object,
            // An interface or an alias lowering does not resolve may be anything.
            _ => Shape::ALL,
        },
        // `any`, `unknown`, `keyof`, queries, and computed types.
        _ => Shape::ALL,
    })
}

/// Members a string, a number, or a boolean has, so a type requiring only these (or
/// numeric keys, which a string's indices meet) may hold a primitive.
const PRIMITIVE_MEMBERS: &[&str] = &[
    "length", "constructor", "toString", "valueOf", "toLocaleString", "hasOwnProperty", "isPrototypeOf",
    "propertyIsEnumerable", "__proto__", "__defineGetter__", "__defineSetter__", "__lookupGetter__",
    "__lookupSetter__", "at", "charAt", "charCodeAt", "codePointAt", "concat", "endsWith", "includes", "indexOf",
    "lastIndexOf", "localeCompare", "match", "matchAll", "normalize", "padEnd", "padStart", "repeat", "replace",
    "replaceAll", "search", "slice", "split", "startsWith", "substring", "substr", "toLowerCase", "toUpperCase",
    "toLocaleLowerCase", "toLocaleUpperCase", "trim", "trimStart", "trimEnd", "trimLeft", "trimRight", "isWellFormed",
    "toWellFormed", "anchor", "big", "blink", "bold", "fixed", "fontcolor", "fontsize", "italics", "link", "small",
    "strike", "sub", "sup", "toFixed", "toExponential", "toPrecision",
];

/// What a type literal admits. TypeScript checks structure, so `{ length: number }` holds a
/// string; only a required member no primitive has rules primitives out, and a call
/// signature admits only functions.
fn literal(l: &TSTypeLiteral<'_>) -> Shape {
    let object = Shape::OBJ.or(Shape::LIST).or(Shape::FUN);
    let required = |key: &oxc_ast::ast::PropertyKey<'_>, computed: bool, optional: bool| {
        let name = key.static_name();
        let name = name.as_ref().and_then(|n| n.as_str());
        !computed && !optional && name.is_some_and(|n| n.parse::<f64>().is_err() && !PRIMITIVE_MEMBERS.contains(&n))
    };
    let mut shape = Shape::DEFINED;
    for member in &l.members {
        match member {
            TSSignature::TSCallSignatureDeclaration(_) | TSSignature::TSConstructSignatureDeclaration(_) => shape = shape.and(Shape::FUN),
            TSSignature::TSPropertySignature(p) if required(&p.key, p.computed, p.optional) => shape = shape.and(object),
            TSSignature::TSMethodSignature(m) if required(&m.key, m.computed, m.optional) => shape = shape.and(object),
            _ => {}
        }
    }
    shape
}
