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
use super::axioms::In;
use crate::logic::function::EqualityDef;
use crate::logic::prop::{Cert, FirstOrder, Imply};
use crate::rel::eq::Closed;
use crate::rel::ext::{Ext, ExtEq, Extensional, InLeftView2, Membership};
use crate::rel::zfc::Zfc;

/// `∈` on the universe of sets.
///
/// The ambient logic is its own membership vocabulary. Keeping this as an
/// associated implementation avoids a separate concrete wrapper type at every
/// generic proof boundary.
impl Membership<Axiomize> for Axiomize {
    /// In ZFC every object is a set, so the domain is everything.
    type El<'a> = <Axiomize as Imply>::Imply<In<'a, 'a>, In<'a, 'a>>;
    type In<'a, 'b> = In<'a, 'b>;
}

/// `=` on the universe of sets: the equality induced by [`Axiomize`]'s
/// membership vocabulary.
/// Extensionality, discharged by [`Zfc::extensionality`].
///
/// The only place a ZFC assumption enters the equality machinery. Everything
/// [`Ext`] proves without this — that equality is an equivalence, and that
/// equals may be substituted on the right of `∈` — holds of any membership
/// relation whatever.
impl Extensional<Axiomize> for Axiomize {
    fn in_left_at<'x, 'y, 'w>() -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<ExtEq<'x, 'y, Axiomize, Axiomize>, <Axiomize as Imply>::Imply<In<'x, 'w>, In<'y, 'w>>>,
    > {
        <Axiomize as Zfc<Axiomize>>::extensionality()
            .pipe(<Axiomize as FirstOrder>::forall_elim::<'x, InLeftView2<Axiomize, Axiomize>>())
            .pipe(<Axiomize as FirstOrder>::forall_elim::<'y, crate::rel::ext::InLeftView1<'x, Axiomize, Axiomize>>())
            .pipe(<Axiomize as FirstOrder>::forall_elim::<'w, crate::rel::ext::InLeftView<'x, 'y, Axiomize, Axiomize>>())
    }
}

impl EqualityDef for Axiomize {
    type EqRel = Closed<Axiomize, Ext<Axiomize, Axiomize>>;
}

/// The concrete equality and the induced [`ExtEq`] are the same proposition.
#[expect(dead_code, reason = "typecheck-only proof assertion")]
fn eq_is_extensional<'x, 'y>(
    c: Cert<Axiomize, ExtEq<'x, 'y, Axiomize, Axiomize>>,
) -> Cert<Axiomize, ExtEq<'x, 'y, Axiomize, Axiomize>> {
    c
}
