//! The global conversion functions: `Number`, `String`, `Boolean`, `parseInt`, `parseFloat`,
//! and `JSON.stringify`, as values and as calls. Known arguments fold exactly as JavaScript
//! computes them; others become `dyn` terms of the shape the function returns.
use super::Lowerer;
use super::expr::integer;
use super::ops::Bin;
use super::value::{Builtin, RefKey, Ty, Val};
use crate::core::{Core, Family, Shape, Utf16};

/// The largest integer a double holds exactly.
const SAFE: i64 = 9_007_199_254_740_991;

impl Builtin {
    /// The global a free name refers to, when it is one lowering models.
    pub fn global(name: &str) -> Option<Self> {
        Some(match name {
            "Number" => Self::Number,
            "String" => Self::String,
            "Boolean" => Self::Boolean,
            "parseInt" => Self::ParseInt,
            "parseFloat" => Self::ParseFloat,
            _ => return None,
        })
    }
    /// The function `object.property` names, for a free `object`.
    pub fn member(object: &str, property: &str) -> Option<Self> {
        (object == "JSON" && property == "stringify").then_some(Self::Stringify)
    }
    /// Whether a free name is a global lowering models rather than an input.
    pub fn is_global(name: &str) -> bool {
        Self::global(name).is_some() || name == "JSON"
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::Number => "Number",
            Self::String => "String",
            Self::Boolean => "Boolean",
            Self::ParseInt => "parseInt",
            Self::ParseFloat => "parseFloat",
            Self::Stringify => "JSON.stringify",
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    /// Call a builtin on evaluated arguments.
    pub fn builtin(&mut self, b: Builtin, args: &[Val<'a>]) -> Val<'a> {
        let first = args.first().cloned();
        match (b, first) {
            (Builtin::Number, None) => Val::int(0),
            (Builtin::String, None) => Val::Str(Utf16::new([])),
            (Builtin::Boolean, None) => Val::Bool(false),
            (Builtin::Number, Some(v)) => self.lift(v, Family::Sink, &mut |l, v| l.to_number(v)),
            (Builtin::String, Some(v)) => self.lift(v, Family::Sink, &mut |l, v| l.to_text(v)),
            (Builtin::Boolean, Some(v)) => self.lift(v, Family::Sink, &mut |l, v| l.truthy(v)),
            (Builtin::ParseInt, v) => {
                let radix = args.get(1).cloned().unwrap_or(Val::Undef);
                let text = self.lift(v.unwrap_or(Val::Undef), Family::Sink, &mut |l, v| l.to_text(v));
                self.lift2(text, radix, Family::Sink, &mut |l, text, radix| l.parse_int(&text, &radix))
            }
            (Builtin::ParseFloat, v) => {
                let text = self.lift(v.unwrap_or(Val::Undef), Family::Sink, &mut |l, v| l.to_text(v));
                self.lift(text, Family::Sink, &mut |l, text| l.parse_float(&text))
            }
            (Builtin::Stringify, v) => {
                // A replacer that is not a function or an array, and a space that is not a
                // number or a string, change nothing: `xs.map(JSON.stringify)` passes an
                // index and the array there.
                let replacer = args.get(1).is_none_or(|r| matches!(r, Val::Undef | Val::Num(_)));
                let space = args.get(2).is_none_or(|s| matches!(s, Val::Undef | Val::Ref(_) | Val::List(_) | Val::Term(_, Ty::List(_))));
                if !(replacer && space) {
                    return self.unsupported();
                }
                self.lift(v.unwrap_or(Val::Undef), Family::Sink, &mut |l, v| l.json(v, &[], false))
            }
        }
    }

    /// `ToNumber`: what `Number(v)`, unary `+`, and arithmetic make of a value. Only integers
    /// are values here, so a fraction or an infinity is a number lowering does not know.
    pub fn to_number(&mut self, v: Val<'a>) -> Val<'a> {
        self.consume(&v);
        // An array keeps its identity into its text, so a cycle in it is written once.
        if matches!(v, Val::Ref(_)) && self.deref(v.clone()).items().is_some() {
            let text = self.to_text(v);
            return self.lift(text, Family::Sink, &mut |l, text| l.to_number(text));
        }
        let v = self.deref(v);
        match v {
            Val::Throw | Val::NaN | Val::Num(_) => v,
            Val::Undef | Val::Fun(_) | Val::Builtin(_) => Val::NaN,
            // A record's text is `[object Object]`, which is no number.
            Val::Record(fields) => {
                let own = ["toString", "valueOf"].iter().any(|n| fields.iter().any(|(k, _)| *k == Utf16::new(n.encode_utf16())));
                if own { self.unsupported() } else { Val::NaN }
            }
            Val::Bool(b) => Val::int(i64::from(b)),
            Val::Str(s) => match string_number(&s.units()) {
                Parsed::Int(n) => Val::int(n),
                Parsed::NaN => Val::NaN,
                Parsed::Other => self.shaped("number", &[&v], Ty::Defined, Shape::NUM),
            },
            // A list is the number its text spells; an element's text may depend on a read.
            Val::List(_) | Val::Short(_) | Val::Term(_, Ty::List(_)) => {
                let text = self.to_text(v);
                self.lift(text, Family::Sink, &mut |l, text| l.to_number(text))
            }
            Val::Term(_, Ty::Bool) => {
                let test = v.clone();
                self.select(&test, Val::int(1), Val::int(0))
            }
            v => self.shaped("number", &[&v], Ty::Defined, Shape::NUM),
        }
    }

    fn parse_int(&mut self, text: &Val<'a>, radix: &Val<'a>) -> Val<'a> {
        // The radix is read as a 32-bit integer.
        let radix = match radix {
            Val::Undef => Some(0),
            Val::Num(f) => f.known().map(|r| {
                let r = r.rem_euclid(1 << 32);
                if r >= 1 << 31 { r - (1 << 32) } else { r }
            }),
            _ => None,
        };
        match (text, radix) {
            (Val::Throw, _) => Val::Throw,
            (Val::Str(s), Some(radix)) => match leading_int(&s.units(), radix) {
                Some(Parsed::Int(n)) => Val::int(n),
                Some(Parsed::NaN) => Val::NaN,
                Some(Parsed::Other) | None => self.shaped("parseInt", &[text], Ty::Defined, Shape::NUM),
            },
            _ => {
                let radix = radix.map_or(Val::Undef, Val::int);
                self.shaped("parseInt", &[text, &radix], Ty::Defined, Shape::NUM)
            }
        }
    }

    fn parse_float(&mut self, text: &Val<'a>) -> Val<'a> {
        match text {
            Val::Throw => Val::Throw,
            Val::Str(s) => match leading_float(&s.units()) {
                Parsed::Int(n) => Val::int(n),
                Parsed::NaN => Val::NaN,
                Parsed::Other => self.shaped("parseFloat", &[text], Ty::Defined, Shape::NUM),
            },
            _ => self.shaped("parseFloat", &[text], Ty::Defined, Shape::NUM),
        }
    }

    /// `JSON.stringify(v)`: `undefined` for `undefined` and functions, and a string
    /// otherwise; as an array's element (`nested`), `null` instead of `undefined`. An array
    /// that contains itself throws; `open` holds the arrays being written.
    fn json(&mut self, v: Val<'a>, open: &[RefKey], nested: bool) -> Val<'a> {
        self.consume(&v);
        let key = if let Val::Ref(k) = v { Some(k) } else { None };
        if key.is_some_and(|k| open.contains(&k)) {
            return Val::Throw;
        }
        let text = |s: &str| Val::Str(Utf16::new(s.encode_utf16()));
        match self.deref(v) {
            Val::Throw => Val::Throw,
            Val::Undef | Val::Fun(_) | Val::Builtin(_) if nested => text("null"),
            Val::Undef | Val::Fun(_) | Val::Builtin(_) => Val::Undef,
            Val::NaN => text("null"),
            Val::Bool(b) => text(if b { "true" } else { "false" }),
            n @ Val::Num(_) => self.to_text(n),
            Val::Str(s) => Val::Str(Utf16::new(quote(&s.units()))),
            Val::List(items) => {
                let open: Vec<RefKey> = open.iter().copied().chain(key).collect();
                let mut out = text("[");
                for (k, item) in items.iter().enumerate() {
                    // Each element is written in its own worlds, so a read in it is lifted.
                    let part = self.lift(item.clone(), Family::Sink, &mut |l, item| l.json(item, &open, true));
                    if matches!(part, Val::Throw) {
                        return Val::Throw;
                    }
                    if k > 0 {
                        out = self.binary(Bin::Add, out, text(","));
                    }
                    out = self.binary(Bin::Add, out, part);
                }
                self.binary(Bin::Add, out, text("]"))
            }
            b @ Val::Term(_, Ty::Bool) => self.select(&b, text("true"), text("false")),
            // A record whose every field always writes: its fields, in order. A field that may
            // write nothing (undefined, a function, an object with `toJSON`) is not modeled.
            Val::Record(fields) => {
                let always = |l: &Self, v: &Val<'a>| matches!(v, Val::Record(_) | Val::List(_)) || l.shape(v).within(Shape::BOOL.or(Shape::NUM).or(Shape::STR).or(Shape::LIST));
                if !fields.iter().all(|(_, v)| always(self, v)) {
                    return self.unsupported();
                }
                let mut out = text("{");
                for (k, (name, value)) in fields.iter().enumerate() {
                    let part = self.lift(value.clone(), Family::Sink, &mut |l, v| l.json(v, open, false));
                    if matches!(part, Val::Throw) {
                        return Val::Throw;
                    }
                    let key = Val::Str(Utf16::new(quote(&name.units()).into_iter().chain(":".encode_utf16())));
                    let head = if k > 0 { self.binary(Bin::Add, out, text(",")) } else { out };
                    let head = self.binary(Bin::Add, head, key);
                    out = self.binary(Bin::Add, head, part);
                }
                self.binary(Bin::Add, out, text("}"))
            }
            // A list's text is always a string: its elements that have none write `null`.
            v @ (Val::Term(_, Ty::Str | Ty::List(_)) | Val::Short(_)) => self.shaped("json", &[&v], Ty::Str, Shape::STR),
            // As an element, anything writes some text, and so does a primitive or a list.
            v if nested || self.shape(&v).within(Shape::BOOL.or(Shape::NUM).or(Shape::STR).or(Shape::LIST)) => self.shaped("json", &[&v], Ty::Str, Shape::STR),
            // A function, or an object whose `toJSON` returns `undefined`, writes nothing.
            v => self.shaped("json", &[&v], Ty::Any, Shape::STR.or(Shape::UNDEF)),
        }
    }
}

impl<'a> Lowerer<'a, '_> {
    /// A function's answer judged by the type it declares: in each world, a stand-in that is
    /// one of the type's literals, a record of its tags, or a primitive of its type, and that
    /// depends on the answer, so a branch that answers still depends on what it read. An
    /// answer of an array, object, or function type, or one holding an array with identity,
    /// stays as it is: those are no tags, and their identity matters.
    pub fn declared(&mut self, answer: Val<'a>, form: &super::declare::Form) -> Val<'a> {
        self.lift(answer, Family::Propagate, &mut |l, v| match v {
            Val::Throw => Val::Throw,
            v if super::refs::holds_ref(&v) || matches!(v, Val::Fun(_) | Val::Builtin(_)) => v,
            v => l.stand_in(&v, form, 0),
        })
    }
    fn stand_in(&mut self, answer: &Val<'a>, form: &super::declare::Form, tag: i64) -> Val<'a> {
        use super::declare::Form;
        match form {
            Form::Str(s) => Val::Str(*s),
            Form::Num(n) => Val::int(*n),
            Form::Bool(b) => Val::Bool(*b),
            Form::Undef => Val::Undef,
            // An array, an object, or a function is no tag, and someone else may hold it: the
            // answer stays itself.
            Form::Any(shape) if shape.meets(Shape::LIST.or(Shape::OBJ).or(Shape::FUN)) => answer.clone(),
            Form::Any(shape) => {
                let stand_in = self.shaped("declared", &[answer], Ty::of(*shape), *shape);
                self.remember(&stand_in, answer);
                stand_in
            }
            // One of the forms, chosen by tests on the answer that lowering does not decide.
            Form::Union(forms) => {
                let Some((last, rest)) = forms.split_last() else { return Val::Throw };
                let mut out = self.stand_in(answer, last, tag * 8 + 7);
                for (k, f) in rest.iter().enumerate().rev() {
                    let which = Val::int(tag * 8 + i64::try_from(k).unwrap_or(0));
                    let test = self.shaped("is", &[answer, &which], Ty::Bool, Shape::BOOL);
                    let arm = self.stand_in(answer, f, tag * 8 + i64::try_from(k).unwrap_or(0) + 1);
                    out = self.select(&test, arm, out);
                }
                self.remember(&out, answer);
                out
            }
            // The type's named fields, each a stand-in for the answer's field.
            Form::Record(fields) => {
                let mut children = Vec::with_capacity(fields.len() * 2);
                for (name, f) in fields {
                    let key = Val::Str(*name);
                    let field = self.shaped("field", &[answer, &key], Ty::Any, Shape::ALL);
                    let value = self.stand_in(&field, f, tag);
                    children.push(self.b.add(Core::Str(*name)));
                    children.push(self.emit(&value));
                }
                let stand_in = Val::Term(self.b.add(Core::Obj(children.into())), Ty::Defined);
                self.remember(&stand_in, answer);
                stand_in
            }
        }
    }
    /// A stand-in's exact answer, which decides control flow: the type judges what the
    /// answer can be, but the program still does what the value says.
    fn remember(&mut self, stand_in: &Val<'a>, answer: &Val<'a>) {
        if let Val::Term(id, _) = stand_in {
            self.exact.insert(*id, answer.clone());
        }
    }
}

/// A string read as a number: an integer double, `NaN`, or some other number.
enum Parsed {
    Int(i64),
    NaN,
    Other,
}

impl Parsed {
    fn of(x: f64) -> Self {
        if x.is_nan() { Self::NaN } else { integer(x).map_or(Self::Other, Self::Int) }
    }
}

/// JavaScript's white space and line terminators, which number parsing skips.
fn space(u: u16) -> bool {
    matches!(u, 0x09..=0x0d | 0x20 | 0xa0 | 0x1680 | 0x2000..=0x200a | 0x2028 | 0x2029 | 0x202f | 0x205f | 0x3000 | 0xfeff)
}

fn trim_start(units: &[u16]) -> &[u16] {
    let start = units.iter().position(|&u| !space(u)).unwrap_or(units.len());
    &units[start..]
}

/// ASCII text, or `None` if any unit is not ASCII (and so no part of a number).
fn ascii(units: &[u16]) -> Option<String> {
    units.iter().map(|&u| u8::try_from(u).ok().filter(u8::is_ascii).map(char::from)).collect()
}

/// `StringToNumber`: the whole string, trimmed, as a decimal literal, a prefixed integer,
/// `Infinity`, or empty (zero).
fn string_number(units: &[u16]) -> Parsed {
    let units = trim_start(units);
    let end = units.iter().rposition(|&u| !space(u)).map_or(0, |k| k + 1);
    let Some(text) = ascii(&units[..end]) else { return Parsed::NaN };
    if text.is_empty() {
        return Parsed::Int(0);
    }
    let prefixed = [("0x", 16), ("0X", 16), ("0o", 8), ("0O", 8), ("0b", 2), ("0B", 2)];
    if let Some((digits, radix)) = prefixed.iter().find_map(|(p, r)| text.strip_prefix(p).map(|d| (d, *r))) {
        if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
            return Parsed::NaN;
        }
        return i64::from_str_radix(digits, radix).ok().filter(|n| *n <= SAFE).map_or(Parsed::Other, Parsed::Int);
    }
    let unsigned = text.strip_prefix(['+', '-']).unwrap_or(&text);
    if unsigned == "Infinity" {
        return Parsed::Other;
    }
    // Rust's float syntax accepts words JavaScript does not ("inf", "nan"); these
    // characters rule them out.
    if !text.chars().all(|c| c.is_ascii_digit() || matches!(c, '+' | '-' | '.' | 'e' | 'E')) {
        return Parsed::NaN;
    }
    text.parse::<f64>().map_or(Parsed::NaN, Parsed::of)
}

/// `parseInt`: the longest run of digits in `radix` after white space, a sign, and (for
/// radix 0 or 16) a `0x` prefix.
fn leading_int(units: &[u16], radix: i64) -> Option<Parsed> {
    let units = trim_start(units);
    let (negative, units) = match units.first() {
        Some(&u) if u == u16::from(b'-') => (true, &units[1..]),
        Some(&u) if u == u16::from(b'+') => (false, &units[1..]),
        _ => (false, units),
    };
    let hex = units.len() >= 2 && units[0] == u16::from(b'0') && (units[1] | 0x20) == u16::from(b'x');
    let (radix, units) = match radix {
        0 | 16 if hex => (16, &units[2..]),
        0 => (10, units),
        r @ 2..=36 => (u32::try_from(r).ok()?, units),
        _ => return Some(Parsed::NaN),
    };
    let digits: Vec<u32> = units.iter().map_while(|&u| char::from_u32(u32::from(u)).and_then(|c| c.to_digit(radix))).collect();
    if digits.is_empty() {
        return Some(Parsed::NaN);
    }
    let mut value: i64 = 0;
    for d in digits {
        value = value.checked_mul(i64::from(radix))?.checked_add(i64::from(d))?;
        if value > SAFE {
            return Some(Parsed::Other);
        }
    }
    Some(Parsed::Int(if negative { -value } else { value }))
}

/// `parseFloat`: the longest decimal literal after white space, or `Infinity`.
fn leading_float(units: &[u16]) -> Parsed {
    let units = trim_start(units);
    let text: String = units.iter().map_while(|&u| u8::try_from(u).ok().filter(u8::is_ascii).map(char::from)).collect();
    let unsigned = text.strip_prefix(['+', '-']).unwrap_or(&text);
    if unsigned.starts_with("Infinity") {
        return Parsed::Other;
    }
    let sign = text.len() - unsigned.len();
    let bytes = unsigned.as_bytes();
    let digits = |from: usize| bytes[from..].iter().take_while(|b| b.is_ascii_digit()).count();
    let whole = digits(0);
    let mut end = whole;
    let mut fraction = 0;
    if bytes.get(end) == Some(&b'.') {
        fraction = digits(end + 1);
        if whole + fraction > 0 {
            end += 1 + fraction;
        }
    }
    if whole + fraction == 0 {
        return Parsed::NaN;
    }
    if matches!(bytes.get(end), Some(b'e' | b'E')) {
        let signed = usize::from(matches!(bytes.get(end + 1), Some(b'+' | b'-')));
        let exponent = digits(end + 1 + signed);
        if exponent > 0 {
            end += 1 + signed + exponent;
        }
    }
    text[..sign + end].parse::<f64>().map_or(Parsed::NaN, Parsed::of)
}

/// A string as JSON writes it: quoted, with quotes, backslashes, control characters, and
/// lone surrogates escaped.
fn quote(units: &[u16]) -> Vec<u16> {
    let mut out = vec![u16::from(b'"')];
    let mut k = 0;
    while k < units.len() {
        let unit = units[k];
        let pair = (0xd800..0xdc00).contains(&unit) && units.get(k + 1).is_some_and(|next| (0xdc00..0xe000).contains(next));
        let escape = match unit {
            0x22 => Some("\\\"".to_string()),
            0x5c => Some("\\\\".to_string()),
            0x08 => Some("\\b".to_string()),
            0x0c => Some("\\f".to_string()),
            0x0a => Some("\\n".to_string()),
            0x0d => Some("\\r".to_string()),
            0x09 => Some("\\t".to_string()),
            _ if pair => None,
            0x00..=0x1f | 0xd800..=0xdfff => Some(format!("\\u{unit:04x}")),
            _ => None,
        };
        match escape {
            Some(text) => out.extend(text.encode_utf16()),
            None if pair => {
                out.extend([unit, units[k + 1]]);
                k += 1;
            }
            None => out.push(unit),
        }
        k += 1;
    }
    out.push(u16::from(b'"'));
    out
}
