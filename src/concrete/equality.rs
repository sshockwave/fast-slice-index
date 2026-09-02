//! [`Axiomize`]'s equality, packaged as a structure.
//!
//! Nothing is proved here, and that is the point. `=` in this development is
//! *defined* — `x = y ≡ ∀z. z ∈ x ↔ z ∈ y` — and every property it has as an
//! equivalence relation follows from that definition alone, for any membership
//! relation whatsoever. So the mathematics is in [`crate::rel::ext`], the
//! bridge to [`poset`](crate::rel::poset)'s guarded shape is in
//! [`crate::rel::eq`], and both are generic over the logic. All this module
//! does is say which relation [`Axiomize`] means by `∈`.
//!
//! Keeping those generic is not tidiness. Their proof terms mention
//! `M::In<'z, 'x>` at a type parameter, which rustc cannot expand; written
//! here against the defined [`Eq`] they would mention a 116 KB type at every
//! occurrence, and `mir_borrowck` cost scales with that. See
//! [`crate::rel::set`].
#![forbid(unsafe_code)]

use super::Axiomize;
use super::lang::{Eq, In, IsSet};
use crate::logic::function::EqualityDef;
use crate::logic::prop::Cert;
use crate::rel::eq::Closed;
use crate::rel::ext::{Ext, ExtEq, Membership};

/// `∈` on the universe of sets.
pub struct SetIn;

impl Membership<Axiomize> for SetIn {
    /// In ZFC every object is a set, so the domain is everything.
    type El<'a> = IsSet<'a>;
    type In<'a, 'b> = In<'a, 'b>;
}

/// `=` on the universe of sets: the equality [`SetIn`] induces.
pub type SetEq = Ext<Axiomize, SetIn>;

/// [`SetEq`] presented on its domain, so it is an
/// [`Equivalence`](crate::rel::poset::Equivalence).
pub type SetEqRel = Closed<Axiomize, SetEq>;

impl EqualityDef for Axiomize {
    type EqRel = SetEqRel;
}

/// [`lang::Eq`](Eq) and the induced [`ExtEq`] are the same proposition — the
/// alias is what the axioms are stated against, the projection is what the
/// generic proofs produce, and the delegation above is only sound if a
/// certificate for one is a certificate for the other.
#[expect(dead_code, reason = "typecheck-only proof assertion")]
fn eq_is_extensional<'x, 'y>(
    c: Cert<Axiomize, Eq<'x, 'y>>,
) -> Cert<Axiomize, ExtEq<'x, 'y, Axiomize, SetIn>> {
    c
}
