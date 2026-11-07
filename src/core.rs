//! The core IR saturated by egg: typed nodes with no operational JavaScript left in them.
use egg::{Id, Symbol, define_language};
use std::fmt::{self, Display, Write};
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
        // An operation lowering resolved to no known type; never undefined.
        "dyn" = Dyn(Box<[Id]>),
        "cons" = Cons([Id; 2]),
        "append" = Append([Id; 2]),
        "slice" = Slice([Id; 3]),
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
        // A read that may be missing, and one proven in range.
        "read" = Read([Id; 2]),
        "at" = At([Id; 2]),
        // maybe z (x i. f) read, tagged with the flow that produced it.
        "maybe" = Maybe([Id; 4]),
        // A possibly missing read left as a hole in a collection shaped like another.
        "escape" = Escape(Id),
        // A call of a function lowering could not resolve: callee, then arguments.
        "call" = Call(Box<[Id]>),
        Int(i64),
        Str(Utf16),
        Flow(Family),
        Var(Variable),
    }
}

/// A string's identity: its UTF-16 code units, lone surrogates included.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Utf16(Symbol);

impl Utf16 {
    pub fn new(units: impl IntoIterator<Item = u16>) -> Self {
        let key = units.into_iter().fold(String::from("utf16:"), |mut key, u| {
            let _ = write!(key, "{u:04x}");
            key
        });
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
    /// The absence is observed, not replaced: `=== undefined`.
    Observe,
    /// The absence passes through: the absent side is still undefined.
    Propagate,
    /// The absent side depends on an unknown that may itself be undefined.
    Undecided,
    /// A possibly missing read left as a hole in a collection shaped like another.
    Drift,
}

impl Family {
    pub const ALL: [Self; 8] = [
        Self::Default,
        Self::Unit,
        Self::Container,
        Self::Sink,
        Self::Observe,
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
            Self::Observe => "observe",
            Self::Propagate => "propagate",
            Self::Undecided => "undecided",
            Self::Drift => "drift",
        }
    }
    /// Whether this flow swallows or conflates the absent value.
    pub fn swallows(self) -> bool {
        matches!(self, Self::Default | Self::Unit | Self::Container | Self::Sink | Self::Drift)
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
    /// A walker's index, an integer in range of its receiver.
    Index,
    /// A fold's accumulator.
    Acc,
}

impl Kind {
    const ALL: [Self; 7] = [
        Self::Int,
        Self::List,
        Self::Fun,
        Self::Any,
        Self::Elem,
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
            Self::Index => "index",
            Self::Acc => "acc",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable {
    pub kind: Kind,
    pub name: Symbol,
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.kind.prefix(), self.name)
    }
}

impl FromStr for Variable {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        let (prefix, name) = s.split_once(':').ok_or("not a variable")?;
        let kind = Kind::ALL
            .into_iter()
            .find(|k| k.prefix() == prefix)
            .ok_or("unknown kind")?;
        Ok(Self {
            kind,
            name: Symbol::from(name),
        })
    }
}
