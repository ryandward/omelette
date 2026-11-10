//! The core IR saturated by egg: typed nodes with no operational JavaScript left in them.
use egg::{Id, Symbol, define_language};
use std::fmt::{self, Display};
use std::str::FromStr;

define_language! {
    /// Lowering decides every JavaScript semantic question before building these terms.
    pub enum Core {
        "undefined" = Undef,
        "nan" = NaN,
        "true" = True,
        "false" = False,
        "nil" = Nil,
        "throw" = Throw,
        // A construct lowering does not model; its tag keeps distinct ones distinct.
        "unsupported" = Unsupported(Id),
        // Affine integer sum: [constant, coefficient, atom, coefficient, atom, ...].
        "lin" = Lin(Box<[Id]>),
        "mul" = Mul([Id; 2]),
        // Integer order, canonically Le(0, sum).
        "le" = Le([Id; 2]),
        "lt" = Lt([Id; 2]),
        "not" = Not(Id),
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "if" = If([Id; 3]),
        // Strict equality of two values whose types lowering could not separate.
        "eq" = Eq([Id; 2]),
        "concat" = Concat([Id; 2]),
        // The text join writes for an element.
        "text" = Text(Id),
        // An operation lowering resolved to no known value: its name, the shape of what it
        // can produce, then its operands. `dyn` never produces undefined; `dyn?` may.
        "dyn" = Dyn(Box<[Id]>),
        "dyn?" = DynUndef(Box<[Id]>),
        "cons" = Cons([Id; 2]),
        "append" = Append([Id; 2]),
        "slice" = Slice([Id; 3]),
        // The length of a list or a string: an integer, never negative.
        "len" = Len(Id),
        // Binders, then the body.
        "lam" = Lam(Box<[Id]>),
        "map" = Map([Id; 2]),
        "filter" = Filter([Id; 2]),
        "every" = Every([Id; 2]),
        "some" = Some([Id; 2]),
        "fold" = Fold([Id; 3]),
        "join" = Join([Id; 2]),
        "flat" = Flat(Id),
        // A read that may be missing, one proven in range, and whether `xs[k]` is in range.
        "read" = Read([Id; 2]),
        "at" = At([Id; 2]),
        "has" = Has([Id; 2]),
        // maybe z (x. f) read, tagged with the flow that produced it: the evidence. Its last
        // child is the read's `has`: a read's class also holds its value, which a present
        // `undefined` element shares with every missing read.
        "maybe" = Maybe([Id; 5]),
        // The same value without the tag, where spellings of one value meet.
        "elim" = Elim([Id; 4]),
        // A possibly missing read (its value, then its `has`) left as a hole in a collection
        // shaped like another.
        "escape" = Escape([Id; 2]),
        // An object the expression built: each field's name, then its value.
        "obj" = Obj(Box<[Id]>),
        // A call of a function lowering could not resolve: callee, then arguments.
        "call" = Call(Box<[Id]>),
        // A list's elements in the order a comparator (or `undefined`) sorts them, and in
        // reverse: the values in-place `sort` and `reverse` leave behind.
        "sort" = Sort([Id; 2]),
        "reverse" = Reverse(Id),
        // An in-place mutation and the owner of the array it reaches: someone outside the
        // expression, the expression itself, or unknown. A choice between arrays is an `if`
        // over their owners.
        "mutate" = Mutate([Id; 2]),
        "external" = External,
        "internal" = Internal,
        "unowned" = Unowned,
        Int(i64),
        Str(Utf16),
        Flow(Family),
        Op(Mutator),
        Kinds(Shape),
        Var(Variable),
    }
}

/// A string's identity: its UTF-16 code units, lone surrogates included.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Utf16(Symbol);

impl Utf16 {
    pub fn new(units: impl IntoIterator<Item = u16>) -> Self {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut key = String::from("utf16:");
        for u in units {
            for shift in [12, 8, 4, 0] {
                key.push(char::from(HEX[usize::from((u >> shift) & 0xf)]));
            }
        }
        Self(Symbol::from(key))
    }
    pub fn units(self) -> Vec<u16> {
        let hex = &self.0.as_str()["utf16:".len()..];
        (0..hex.len())
            .step_by(4)
            .filter_map(|i| u16::from_str_radix(&hex[i..i + 4], 16).ok())
            .collect()
    }
    #[must_use]
    pub fn concat(self, other: Self) -> Self {
        Self::new(self.units().into_iter().chain(other.units()))
    }
}

impl Display for Utf16 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl FromStr for Utf16 {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        let hex = s.strip_prefix("utf16:").ok_or("not a string")?;
        let whole = hex.len() % 4 == 0 && hex.bytes().all(|b| b.is_ascii_hexdigit());
        if whole { Ok(Self(Symbol::from(s))) } else { Err(s.into()) }
    }
}

/// The information flow by which a witness swallows or keeps the absent value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// A value the program wrote: `??`, `||`, a branch on presence.
    Default,
    /// The unit of a fold's monoid: every, some, join, reduce, a filter's length.
    Unit,
    /// An empty collection: flat, flatMap.
    Container,
    /// What an operator makes of undefined: ===, <, +, !.
    Sink,
    /// The absence passes through: the absent side is still undefined.
    Propagate,
    /// The absent side depends on an unknown that may itself be undefined.
    Undecided,
    /// A possibly missing read left as a hole in a collection shaped like another.
    Drift,
}

impl Family {
    pub const ALL: [Self; 7] = [
        Self::Default,
        Self::Unit,
        Self::Container,
        Self::Sink,
        Self::Propagate,
        Self::Undecided,
        Self::Drift,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Self::Default => "default",
            Self::Unit => "unit",
            Self::Container => "container",
            Self::Sink => "sink",
            Self::Propagate => "propagate",
            Self::Undecided => "undecided",
            Self::Drift => "drift",
        }
    }
    /// Whether this flow swallows or conflates the absent value.
    pub fn swallows(self) -> bool {
        matches!(self, Self::Default | Self::Unit | Self::Container | Self::Sink | Self::Drift)
    }
    /// The flow after `next` changes an absent side this flow produced. The last operation
    /// that wrote the replacement names it; an operation that only passes values through
    /// (`propagate`: a read, `length`, a spread) keeps the flow it was given; and one
    /// undecided step leaves the whole chain undecided, since its unknown operand may make
    /// the chain an observation.
    #[must_use]
    pub fn then(self, next: Self) -> Self {
        match (self, next) {
            (Self::Undecided, _) | (_, Self::Undecided) => Self::Undecided,
            (flow, Self::Propagate) => flow,
            (_, next) => next,
        }
    }
}

impl Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl FromStr for Family {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        Self::ALL
            .into_iter()
            .find(|f| f.name() == s)
            .ok_or_else(|| s.into())
    }
}

/// An operation that changes an array or object in place.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mutator {
    Push,
    Pop,
    Shift,
    Unshift,
    Splice,
    Sort,
    Reverse,
    Fill,
    CopyWithin,
    /// An assignment to an element or property, including `length`.
    Assign,
    Delete,
}

impl Mutator {
    pub const ALL: [Self; 11] = [
        Self::Push,
        Self::Pop,
        Self::Shift,
        Self::Unshift,
        Self::Splice,
        Self::Sort,
        Self::Reverse,
        Self::Fill,
        Self::CopyWithin,
        Self::Assign,
        Self::Delete,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Self::Push => "push",
            Self::Pop => "pop",
            Self::Shift => "shift",
            Self::Unshift => "unshift",
            Self::Splice => "splice",
            Self::Sort => "sort",
            Self::Reverse => "reverse",
            Self::Fill => "fill",
            Self::CopyWithin => "copyWithin",
            Self::Assign => "assign",
            Self::Delete => "delete",
        }
    }
    /// The array method of this name that mutates its receiver.
    pub fn method(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|m| m.name() == name && !matches!(m, Self::Assign | Self::Delete))
    }
}

impl Display for Mutator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "mut:{}", self.name())
    }
}

impl FromStr for Mutator {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        let name = s.strip_prefix("mut:").ok_or_else(|| s.to_string())?;
        Self::ALL.into_iter().find(|m| m.name() == name).ok_or_else(|| s.into())
    }
}

/// The JavaScript types a value can have: a set over undefined, boolean, number (`NaN`
/// included), string, list, other object, and function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Shape(u8);

impl Shape {
    pub const NONE: Self = Self(0);
    pub const UNDEF: Self = Self(1);
    pub const BOOL: Self = Self(2);
    pub const NUM: Self = Self(4);
    pub const STR: Self = Self(8);
    pub const LIST: Self = Self(16);
    pub const OBJ: Self = Self(32);
    pub const FUN: Self = Self(64);
    pub const ALL: Self = Self(127);
    pub const DEFINED: Self = Self(126);
    const LETTERS: [(char, Self); 7] =
        [('u', Self::UNDEF), ('b', Self::BOOL), ('n', Self::NUM), ('s', Self::STR), ('l', Self::LIST), ('o', Self::OBJ), ('f', Self::FUN)];
    #[must_use]
    pub fn or(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    #[must_use]
    pub fn and(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
    #[must_use]
    pub fn without(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }
    pub fn meets(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
    /// Some value, and every value, of this shape is also of `other`.
    pub fn within(self, other: Self) -> bool {
        self != Self::NONE && self.0 & !other.0 == 0
    }
    pub fn letters(self) -> String {
        Self::LETTERS.iter().filter(|(_, s)| self.meets(*s)).map(|(c, _)| *c).collect()
    }
    pub fn parse(letters: &str) -> Option<Self> {
        letters.chars().try_fold(Self::NONE, |shape, c| Self::LETTERS.iter().find(|(l, _)| *l == c).map(|(_, s)| shape.or(*s)))
    }
}

/// What a shape computation knows of a node's children.
pub trait Known {
    /// What the term can be.
    fn shape(&self, id: Id) -> Shape;
    /// When the term is a list, what its elements can be.
    fn items(&self, id: Id) -> Shape;
    /// What a lambda's body can be, and its elements.
    fn returns(&self, lam: Id) -> (Shape, Shape);
    /// The shape a `kinds` leaf declares.
    fn declared(&self, id: Id) -> Option<Shape>;
}

/// The types a node's value can have, from its operation and what is known of its children.
pub fn shape_of(n: &Core, known: &impl Known) -> Shape {
    let of = |id: &Id| known.shape(*id);
    let items = |id: &Id| known.items(*id);
    match n {
        Core::At([xs, _]) => items(xs),
        Core::Read([xs, _]) => items(xs).or(Shape::UNDEF),
        Core::Undef => Shape::UNDEF,
        Core::NaN | Core::Int(_) | Core::Lin(_) | Core::Mul(_) | Core::Len(_) => Shape::NUM,
        Core::True
        | Core::False
        | Core::Le(_)
        | Core::Lt(_)
        | Core::Not(_)
        | Core::And(_)
        | Core::Or(_)
        | Core::Eq(_)
        | Core::Every(_)
        | Core::Some(_)
        | Core::Has(_) => Shape::BOOL,
        Core::Str(_) | Core::Concat(_) | Core::Text(_) | Core::Join(_) => Shape::STR,
        Core::Nil
        | Core::Cons(_)
        | Core::Append(_)
        | Core::Slice(_)
        | Core::Map(_)
        | Core::Filter(_)
        | Core::Flat(_)
        | Core::Sort(_)
        | Core::Reverse(_) => Shape::LIST,
        Core::Lam(_) => Shape::FUN,
        Core::Obj(_) => Shape::OBJ,
        Core::Throw => Shape::NONE,
        Core::If([_, yes, no]) => of(yes).or(of(no)),
        Core::Maybe([_, z, lam, ..]) | Core::Elim([z, lam, ..]) => of(z).or(known.returns(*lam).0),
        Core::Escape([v, _]) => of(v).or(Shape::UNDEF),
        Core::Dyn(children) | Core::DynUndef(children) => children.get(1).and_then(|k| known.declared(*k)).unwrap_or(Shape::ALL),
        Core::Var(v) => v.values(),
        _ => Shape::ALL,
    }
}

/// When a node is a list, the types its elements can have.
pub fn items_of(n: &Core, known: &impl Known) -> Shape {
    let items = |id: &Id| known.items(*id);
    match n {
        Core::Nil => Shape::NONE,
        Core::Cons([head, tail]) => known.shape(*head).or(items(tail)),
        Core::Append([a, b]) | Core::If([_, a, b]) => items(a).or(items(b)),
        Core::Slice([xs, ..]) | Core::Filter([_, xs]) | Core::Sort([_, xs]) | Core::Reverse(xs) => items(xs),
        Core::Map([f, _]) => known.returns(*f).0,
        // Flattening keeps the elements that are not lists and spreads the ones that are.
        Core::Flat(xs) if !items(xs).meets(Shape::LIST) => items(xs),
        Core::Maybe([_, z, lam, ..]) | Core::Elim([z, lam, ..]) => items(z).or(known.returns(*lam).1),
        Core::Var(v) => v.items(),
        _ => Shape::ALL,
    }
}

impl Default for Shape {
    fn default() -> Self {
        Self::ALL
    }
}

impl Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "shape:{}", self.letters())
    }
}

impl FromStr for Shape {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        s.strip_prefix("shape:").and_then(Self::parse).ok_or_else(|| s.to_string())
    }
}

/// What lowering knows about a variable: the model's precondition for a free one, or a
/// binder introduced for a walker's callback.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// Used as an index, a bound, or an arithmetic operand: an integer.
    Int,
    /// Used as a list: dense, with defined elements.
    List,
    /// Used as a function.
    Fun,
    /// Nothing known; possibly undefined.
    Any,
    /// A walker's element, which the model's dense lists make defined.
    Elem,
    /// An element of a list that may hold undefined, such as `[undefined, ...ys]`.
    Item,
    /// A walker's index, an integer in range of its receiver.
    Index,
    /// A fold's accumulator.
    Acc,
}

impl Kind {
    /// What a variable of this kind can be, or for a list what its elements can be, before
    /// any declared type narrows it. An input list's elements are never undefined.
    pub fn shape(self) -> Shape {
        match self {
            Self::Int | Self::Index => Shape::NUM,
            Self::List | Self::Elem => Shape::DEFINED,
            Self::Fun => Shape::FUN,
            Self::Any | Self::Item | Self::Acc => Shape::ALL,
        }
    }
    const ALL: [Self; 8] = [
        Self::Int,
        Self::List,
        Self::Fun,
        Self::Any,
        Self::Elem,
        Self::Item,
        Self::Index,
        Self::Acc,
    ];
    fn prefix(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::List => "list",
            Self::Fun => "fn",
            Self::Any => "any",
            Self::Elem => "elem",
            Self::Item => "item",
            Self::Index => "index",
            Self::Acc => "acc",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable {
    pub kind: Kind,
    pub name: Symbol,
    /// What the variable's values can be, or for a list what its elements can be.
    pub shape: Shape,
}

impl Variable {
    /// What the variable's values can be.
    pub fn values(self) -> Shape {
        if self.kind == Kind::List { Shape::LIST } else { self.shape }
    }
    /// What its elements can be, when it is a list.
    pub fn items(self) -> Shape {
        if self.kind == Kind::List { self.shape } else { Shape::ALL }
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.shape == self.kind.shape() {
            write!(f, "{}:{}", self.kind.prefix(), self.name)
        } else {
            write!(f, "{}.{}:{}", self.kind.prefix(), self.shape.letters(), self.name)
        }
    }
}

impl FromStr for Variable {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        let (prefix, name) = s.split_once(':').ok_or("not a variable")?;
        let (prefix, letters) = prefix.split_once('.').map_or((prefix, None), |(p, l)| (p, Some(l)));
        let kind = Kind::ALL
            .into_iter()
            .find(|k| k.prefix() == prefix)
            .ok_or("unknown kind")?;
        let shape = match letters {
            Some(letters) => Shape::parse(letters).ok_or("unknown shape")?,
            None => kind.shape(),
        };
        Ok(Self { kind, name: Symbol::from(name), shape })
    }
}
