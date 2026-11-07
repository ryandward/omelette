//! Integer affine sums: a constant plus integer multiples of atoms, with checked arithmetic.
use egg::Id;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Form {
    pub constant: i64,
    pub terms: BTreeMap<Id, i64>,
}

impl Form {
    pub fn constant(constant: i64) -> Self {
        Self {
            constant,
            terms: BTreeMap::new(),
        }
    }
    pub fn atom(id: Id) -> Self {
        Self {
            constant: 0,
            terms: BTreeMap::from([(id, 1)]),
        }
    }
    /// The value, when the form has no atoms.
    pub fn known(&self) -> Option<i64> {
        self.terms.is_empty().then_some(self.constant)
    }
    /// The atom itself, when the form is exactly one atom.
    pub fn single(&self) -> Option<Id> {
        let mut terms = self.terms.iter();
        match (self.constant, terms.next(), terms.next()) {
            (0, Some((&id, 1)), None) => Some(id),
            _ => None,
        }
    }
    /// `self + sign * other`, or None on overflow.
    pub fn plus(&self, other: &Self, sign: i64) -> Option<Self> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(other.constant.checked_mul(sign)?)?;
        for (&id, &c) in &other.terms {
            let sum = out.terms.get(&id).copied().unwrap_or(0).checked_add(c.checked_mul(sign)?)?;
            if sum == 0 {
                out.terms.remove(&id);
            } else {
                out.terms.insert(id, sum);
            }
        }
        Some(out)
    }
    pub fn scale(&self, k: i64) -> Option<Self> {
        Self::default().plus(self, k)
    }
}
