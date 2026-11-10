//! Declared types: `declare const xs: string[];` before the expression says what a free
//! variable holds, which narrows the model's preconditions. TypeScript is structural, so an
//! object type admits arrays and functions too; a type lowering cannot name holds anything.
use super::value::Builtin;
use crate::core::{Kind, Shape};
use oxc_ast::ast::{
    BindingPattern, Program, Statement, TSLiteral, TSSignature, TSTupleElement, TSType, TSTypeName,
    TSTypeOperatorOperator,
};
use std::collections::HashMap;

/// What a declaration says a free variable holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Declared {
    /// A list whose elements have this shape.
    List(Shape),
    /// A value of this shape.
    Value(Shape),
}

/// A program's declared types. Before its one expression, a program may declare free
/// variables (`declare const xs: string[];`) and define helpers (`const f = ...;` or
/// `function f() {}`), which the expression may call.
///
/// # Errors
/// Another kind of statement before the expression, a definition that is not a named
/// `const` with a value or a named function, a declaration without a type, or a type that
/// holds what the model does not (`null`, `bigint`, `symbol`).
pub fn prelude(program: &Program<'_>) -> Result<HashMap<String, Declared>, String> {
    let types = Types::of(program);
    let mut declared = HashMap::new();
    let Some((last, declarations)) = program.body.split_last() else { return Err("expected an expression".into()) };
    for statement in declarations {
        let d = match statement {
            Statement::FunctionDeclaration(f) if f.id.is_some() && !f.declare => continue,
            Statement::TSTypeAliasDeclaration(_) | Statement::TSInterfaceDeclaration(_) => continue,
            Statement::VariableDeclaration(d) if !d.declare => {
                let named = d.declarations.iter().all(|v| matches!(v.id, BindingPattern::BindingIdentifier(_)) && v.init.is_some());
                if d.kind != oxc_ast::ast::VariableDeclarationKind::Const || !named {
                    return Err("a definition is a named `const` with a value".into());
                }
                continue;
            }
            Statement::VariableDeclaration(d) => d,
            _ => return Err("only declarations and definitions may precede the expression".into()),
        };
        for v in &d.declarations {
            let BindingPattern::BindingIdentifier(name) = &v.id else { return Err("a declaration names one variable".into()) };
            let Some(annotation) = &v.type_annotation else { return Err(format!("`{}` has no type", name.name)) };
            if Builtin::is_global(name.name.as_str()) {
                return Err(format!("`{}` is a global omelette models", name.name));
            }
            let ty = types.declaration(&annotation.type_annotation)?;
            if declared.insert(name.name.to_string(), ty).is_some_and(|old| old != ty) {
                return Err(format!("`{}` is declared twice", name.name));
            }
        }
    }
    if !matches!(last, Statement::ExpressionStatement(_)) {
        return Err("expected an expression after the declarations".into());
    }
    Ok(declared)
}

/// The variables a program declares with `declare const`: inputs, named in the program.
pub fn ambient(program: &Program<'_>) -> Vec<(String, oxc_semantic::SymbolId)> {
    program
        .body
        .iter()
        .filter_map(|s| match s {
            Statement::VariableDeclaration(d) if d.declare => Some(d),
            _ => None,
        })
        .flat_map(|d| d.declarations.iter())
        .filter_map(|v| match &v.id {
            BindingPattern::BindingIdentifier(id) => Some((id.name.to_string(), id.symbol_id())),
            _ => None,
        })
        .collect()
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

/// The types a program names: its aliases and interfaces, which a reference resolves to.
pub struct Types<'t, 'a> {
    named: HashMap<&'t str, Named<'t, 'a>>,
    /// The names being resolved, so an alias that refers to itself admits anything.
    open: std::cell::RefCell<Vec<&'t str>>,
}

#[derive(Clone, Copy)]
enum Named<'t, 'a> {
    Alias(&'t TSType<'a>),
    Interface(&'t [TSSignature<'a>]),
}

impl<'t, 'a> Types<'t, 'a> {
    /// The aliases and interfaces a program declares without type parameters; a generic one
    /// is not resolved.
    pub fn of(program: &'t Program<'a>) -> Self {
        let mut named = HashMap::new();
        for statement in &program.body {
            match statement {
                Statement::TSTypeAliasDeclaration(d) if d.type_parameters.is_none() => {
                    named.insert(d.id.name.as_str(), Named::Alias(&d.type_annotation));
                }
                Statement::TSInterfaceDeclaration(d) if d.type_parameters.is_none() => {
                    named.insert(d.id.name.as_str(), Named::Interface(&d.body.body));
                }
                _ => {}
            }
        }
        Self { named, open: std::cell::RefCell::default() }
    }
    /// What a named type admits, through its alias or interface: `None` for a name the
    /// program does not declare.
    fn resolve(&self, name: &str) -> Option<Result<Shape, String>> {
        let (&key, named) = self.named.get_key_value(name)?;
        if self.open.borrow().contains(&key) {
            return Some(Ok(Shape::ALL));
        }
        self.open.borrow_mut().push(key);
        let shape = match *named {
            Named::Alias(t) => self.shape(t),
            Named::Interface(signatures) => Ok(members(signatures)),
        };
        self.open.borrow_mut().pop();
        Some(shape)
    }
    /// The elements of a named type that is an array, through its alias.
    fn resolve_elements(&self, name: &str) -> Option<Result<Option<Shape>, String>> {
        let (&key, Named::Alias(t)) = self.named.get_key_value(name)? else { return None };
        if self.open.borrow().contains(&key) {
            return None;
        }
        self.open.borrow_mut().push(key);
        let items = self.elements(t);
        self.open.borrow_mut().pop();
        Some(items)
    }
    fn declaration(&self, t: &TSType<'_>) -> Result<Declared, String> {
        Ok(match self.elements(t)? {
            Some(items) => Declared::List(items),
            None => Declared::Value(self.shape(t)?),
        })
    }

    /// The elements of an array type, or `None` for any other type.
    fn elements(&self, t: &TSType<'_>) -> Result<Option<Shape>, String> {
        Ok(Some(match t {
            TSType::TSArrayType(a) => self.shape(&a.element_type)?,
            TSType::TSTupleType(t) => {
                let mut items = Shape::NONE;
                for e in &t.element_types {
                    items = items.or(self.element(e)?);
                }
                items
            }
            TSType::TSTypeOperatorType(o) if o.operator == TSTypeOperatorOperator::Readonly => return self.elements(&o.type_annotation),
            TSType::TSParenthesizedType(p) => return self.elements(&p.type_annotation),
            TSType::TSTypeReference(r) if matches!(name(&r.type_name), Some("Readonly")) => match r.type_arguments.as_ref().and_then(|a| a.params.first()) {
                Some(t) => return self.elements(t),
                None => return Ok(None),
            },
            TSType::TSTypeReference(r) if r.type_arguments.is_none() && name(&r.type_name).and_then(|n| self.resolve_elements(n)).is_some() => {
                return name(&r.type_name).and_then(|n| self.resolve_elements(n)).unwrap_or(Ok(None));
            }
            TSType::TSTypeReference(r) if matches!(name(&r.type_name), Some("Array" | "ReadonlyArray")) => {
                match r.type_arguments.as_ref().and_then(|a| a.params.first()) {
                    Some(t) => self.shape(t)?,
                    None => Shape::ALL,
                }
            }
            _ => return Ok(None),
        }))
    }

    /// What one element of a tuple can be.
    fn element(&self, e: &TSTupleElement<'_>) -> Result<Shape, String> {
        match e {
            // A missing optional element reads as undefined.
            TSTupleElement::TSOptionalType(o) => Ok(self.shape(&o.type_annotation)?.or(Shape::UNDEF)),
            TSTupleElement::TSRestType(r) => Ok(self.elements(&r.type_annotation)?.unwrap_or(Shape::ALL)),
            other => other.as_ts_type().map_or(Ok(Shape::ALL), |t| self.shape(t)),
        }
    }

    /// The JavaScript types a value of TypeScript type `t` can have.
    fn shape(&self, t: &TSType<'_>) -> Result<Shape, String> {
        let object = Shape::OBJ.or(Shape::LIST).or(Shape::FUN);
        Ok(match t {
            TSType::TSStringKeyword(_) | TSType::TSTemplateLiteralType(_) => Shape::STR,
            TSType::TSNumberKeyword(_) => Shape::NUM,
            TSType::TSBooleanKeyword(_) => Shape::BOOL,
            TSType::TSUndefinedKeyword(_) | TSType::TSVoidKeyword(_) => Shape::UNDEF,
            TSType::TSNeverKeyword(_) => Shape::NONE,
            TSType::TSObjectKeyword(_) => object,
            TSType::TSTypeLiteral(l) => members(&l.members),
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
                    out = out.or(self.shape(t)?);
                }
                out
            }
            TSType::TSIntersectionType(i) => {
                let mut out = Shape::ALL;
                for t in &i.types {
                    out = out.and(self.shape(t)?);
                }
                out
            }
            TSType::TSParenthesizedType(p) => self.shape(&p.type_annotation)?,
            TSType::TSTypeOperatorType(o) if o.operator == TSTypeOperatorOperator::Readonly => self.shape(&o.type_annotation)?,
            TSType::TSNamedTupleMember(m) => {
                let e = self.element(&m.element_type)?;
                if m.optional { e.or(Shape::UNDEF) } else { e }
            }
            TSType::TSNullKeyword(_) | TSType::JSDocNullableType(_) => return Err("null is not modeled".into()),
            TSType::TSBigIntKeyword(_) => return Err("bigint is not modeled".into()),
            TSType::TSSymbolKeyword(_) => return Err("symbol is not modeled".into()),
            // A name the program declares admits what its alias or interface does.
            TSType::TSTypeReference(r) if r.type_arguments.is_none() && name(&r.type_name).is_some_and(|n| self.named.contains_key(n)) => {
                name(&r.type_name).and_then(|n| self.resolve(n)).unwrap_or(Ok(Shape::ALL))?
            }
            TSType::TSTypeReference(r) if matches!(name(&r.type_name), Some("Readonly" | "NonNullable")) => {
                let inner = r.type_arguments.as_ref().and_then(|a| a.params.first());
                let shape = inner.map_or(Ok(Shape::ALL), |t| self.shape(t))?;
                if name(&r.type_name) == Some("NonNullable") { shape.without(Shape::UNDEF) } else { shape }
            }
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
}

fn name<'a>(n: &'a TSTypeName<'_>) -> Option<&'a str> {
    match n {
        TSTypeName::IdentifierReference(id) => Some(id.name.as_str()),
        _ => None,
    }
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
fn members(members: &[TSSignature<'_>]) -> Shape {
    let object = Shape::OBJ.or(Shape::LIST).or(Shape::FUN);
    let required = |key: &oxc_ast::ast::PropertyKey<'_>, computed: bool, optional: bool| {
        let name = key.static_name();
        let name = name.as_ref().and_then(|n| n.as_str());
        !computed && !optional && name.is_some_and(|n| n.parse::<f64>().is_err() && !PRIMITIVE_MEMBERS.contains(&n))
    };
    let mut shape = Shape::DEFINED;
    for member in members {
        match member {
            TSSignature::TSCallSignatureDeclaration(_) | TSSignature::TSConstructSignatureDeclaration(_) => shape = shape.and(Shape::FUN),
            TSSignature::TSPropertySignature(p) if required(&p.key, p.computed, p.optional) => shape = shape.and(object),
            TSSignature::TSMethodSignature(m) if required(&m.key, m.computed, m.optional) => shape = shape.and(object),
            _ => {}
        }
    }
    shape
}
