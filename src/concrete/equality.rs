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
//! [`crate::rel::func`].
#![forbid(unsafe_code)]

use super::Axiomize;
use super::axioms::ext;
use super::lang::{Eq, ExtCongrView, ExtView, ExtView1, In, IsSet};
use crate::logic::function::EqualityDef;
use crate::logic::prop::{And, Cert, FirstOrder, Imply, syllogism};
use crate::rel::eq::Closed;
use crate::rel::ext::{Ext, ExtEq, Extensional, Membership};

/// `∈` on the universe of sets.
///
/// The ambient logic is its own membership vocabulary. Keeping this as an
/// associated implementation avoids a separate concrete wrapper type at every
/// generic proof boundary.
impl Membership<Axiomize> for Axiomize {
    /// In ZFC every object is a set, so the domain is everything.
    type El<'a> = IsSet<'a>;
    type In<'a, 'b> = In<'a, 'b>;
}

/// `=` on the universe of sets: the equality induced by [`Axiomize`]'s
/// membership vocabulary.
/// Extensionality, discharged by [the axiom](super::axioms::ext).
///
/// The only place a ZFC assumption enters the equality machinery. Everything
/// [`Ext`] proves without this — that equality is an equivalence, and that
/// equals may be substituted on the right of `∈` — holds of any membership
/// relation whatever.
impl Extensional<Axiomize> for Axiomize {
    fn in_left_at<'x, 'y, 'w>() -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<Eq<'x, 'y>, <Axiomize as Imply>::Imply<In<'x, 'w>, In<'y, 'w>>>,
    > {
        let congr = ext()
            .pipe(<Axiomize as FirstOrder>::forall_elim::<'x, ExtView>())
            .pipe(<Axiomize as FirstOrder>::forall_elim::<'y, ExtView1<'x>>());
        syllogism().mp(congr).mp(syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<
                'w,
                ExtCongrView<'x, 'y>,
            >())
            .mp(<Axiomize as And>::and_left()))
    }
}

impl EqualityDef for Axiomize {
    type EqRel = Closed<Axiomize, Ext<Axiomize, Axiomize>>;
}

/// [`lang::Eq`](Eq) and the induced [`ExtEq`] are the same proposition — the
/// alias is what the axioms are stated against, the projection is what the
/// generic proofs produce, and the delegation above is only sound if a
/// certificate for one is a certificate for the other.
#[expect(dead_code, reason = "typecheck-only proof assertion")]
fn eq_is_extensional<'x, 'y>(
    c: Cert<Axiomize, Eq<'x, 'y>>,
) -> Cert<Axiomize, ExtEq<'x, 'y, Axiomize, Axiomize>> {
    c
}
