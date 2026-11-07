//! Canonical integer affine terms. No associativity or commutativity rewrites.
use egg::{Id, SymbolLang};
use std::collections::BTreeMap;
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Form {
    pub constant: i64,
    pub terms: BTreeMap<Id, i64>,
}
impl Form {
    pub fn atom(id: Id) -> Self {
        Self {
            constant: 0,
            terms: [(id, 1)].into(),
        }
    }
    pub fn constant(n: i64) -> Self {
        Self {
            constant: n,
            terms: BTreeMap::new(),
        }
    }
    pub fn plus(&self, b: &Self, sign: i64) -> Option<Self> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(b.constant.checked_mul(sign)?)?;
        for (&id, &n) in &b.terms {
            let n = out
                .terms
                .get(&id)
                .copied()
                .unwrap_or(0)
                .checked_add(n.checked_mul(sign)?)?;
            if n == 0 {
                out.terms.remove(&id);
            } else {
                out.terms.insert(id, n);
            }
        }
        Some(out)
    }
    pub fn decode(n: &SymbolLang) -> Option<Self> {
        let mut parts = n.op.as_str().strip_prefix("Lin:")?.split(':');
        let constant = parts.next()?.parse().ok()?;
        let mut out = Self::constant(constant);
        for &id in &n.children {
            let coefficient = parts.next()?.parse().ok()?;
            // Rebuild can merge distinct atoms; sum their coefficients, never overwrite them.
            out = out.plus(
                &Self {
                    constant: 0,
                    terms: [(id, coefficient)].into(),
                },
                1,
            )?;
        }
        if parts.next().is_some() {
            return None;
        }
        Some(out)
    }
    pub fn node(&self) -> SymbolLang {
        let mut op = format!("Lin:{}", self.constant);
        for n in self.terms.values() {
            op.push_str(&format!(":{n}"));
        }
        SymbolLang::new(op, self.terms.keys().copied().collect::<Vec<_>>())
    }
}
