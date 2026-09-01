//! The nine assumptions of ZFC, and nothing else.
//!
//! Every function here has the body `unsafe { cert() }`: it mints a certificate
//! from nothing, which is exactly what an axiom is. Keeping them alone in one
//! file means the trusted base of the whole development can be audited by
//! reading it end to end — the language they are stated in, and everything
//! derived from them, lives in [`crate::logic::set`].
//!
//! `cert` is reachable here and nowhere outside `axiom`, so this is the only
//! place new assumptions can enter.
#![expect(unsafe_code, reason = "this module states axioms; see `base.rs`")]
#![expect(
    unused_parens,
    reason = "`pred!` parses its body as an expression, so operands are \
              parenthesised for grouping; the parens survive into the type"
)]

use super::Axiomize;
use super::base::sealed_cert::cert;
use crate::logic::prop::View;
use crate::logic::set::{Applies, Eq, In, IsEmpty, IsFunction, IsPair, IsSuccOf, Rel2, Subset};
use crate::macros::thm;

// ---------------------------------------------------------------------------
// The axioms
// ---------------------------------------------------------------------------
//
// Each is minted by `unsafe { cert() }` — an assumption, not a derivation.
// Everything after this section is proved from them.

/// **Extensionality**, as the congruence law.
///
/// `∀x ∀y. x = y → ∀w. (x ∈ w ↔ y ∈ w)`
///
/// [`Eq`] is *defined* as having the same members, so the usual other direction
/// is free and this congruence is the axiom's entire content.
pub fn ext() -> thm!(
    { Axiomize },
    ForAll::<'x, 'y>((Eq::<'x, 'y>).imply(ForAll::<'w>((In::<'x, 'w>).iff(In::<'y, 'w>))))
) {
    unsafe { cert() }
}

/// **Pairing**: `∀x ∀y. ∃p. p = {x, y}`
pub fn pairing() -> thm!(
    { Axiomize },
    ForAll::<'x, 'y>(Exists::<'p>(IsPair::<'p, 'x, 'y>))
) {
    unsafe { cert() }
}

/// **Union**: `∀f. ∃u. ∀z. (z ∈ u ↔ ∃y. (z ∈ y ∧ y ∈ f))`
pub fn union() -> thm!(
    { Axiomize },
    ForAll::<'f>(Exists::<'u>(ForAll::<'z>(
        (In::<'z, 'u>).iff(Exists::<'y>((In::<'z, 'y>) && (In::<'y, 'f>)))
    )))
) {
    unsafe { cert() }
}

/// **Separation** (schema): `∀a. ∃s. ∀z. (z ∈ s ↔ (z ∈ a ∧ P(z)))`
///
/// `P` is a type parameter instantiated per predicate, not a quantified
/// variable — the same predicativity discipline as
/// [`crate::logic::nat::NaturalNumbers::induction`]. Carving only out of an
/// existing `a` is what keeps this from being naive comprehension, which would
/// be inconsistent.
pub fn separation<P>() -> thm!(
    { Axiomize },
    ForAll::<'a>(Exists::<'s>(ForAll::<'z>(
        (In::<'z, 's>).iff((In::<'z, 'a>) && (<P as View<'z>>::Output))
    )))
)
where
    P: for<'z> View<'z>,
{
    unsafe { cert() }
}

/// **Power set**: `∀x. ∃p. ∀z. (z ∈ p ↔ z ⊆ x)`
pub fn power_set() -> thm!(
    { Axiomize },
    ForAll::<'x>(Exists::<'p>(ForAll::<'z>(
        (In::<'z, 'p>).iff(Subset::<'z, 'x>)
    )))
) {
    unsafe { cert() }
}

/// **Regularity**: every nonempty set has an ∈-minimal member.
pub fn regularity() -> thm!(
    { Axiomize },
    ForAll::<'x>((Exists::<'y>(In::<'y, 'x>)).imply(Exists::<'y>(
        (In::<'y, 'x>) && (!(Exists::<'z>((In::<'z, 'y>) && (In::<'z, 'x>))))
    )))
) {
    unsafe { cert() }
}

/// **Infinity**: some set contains ∅ and is closed under `y ↦ y ∪ {y}`.
pub fn infinity() -> thm!(
    { Axiomize },
    Exists::<'i>(
        (Exists::<'e>((In::<'e, 'i>) && (IsEmpty::<'e>)))
            && (ForAll::<'y>(
                (In::<'y, 'i>).imply(Exists::<'s>((In::<'s, 'i>) && (IsSuccOf::<'s, 'y>)))
            ))
    )
) {
    unsafe { cert() }
}

/// **Replacement** (schema): the image of a set under a single-valued relation
/// is a set.
pub fn replacement<R>() -> thm!(
    { Axiomize },
    ForAll::<'a>(
        (ForAll::<'x>((In::<'x, 'a>).imply(ForAll::<'y, 'w>(
            ((<R as Rel2>::At::<'x, 'y>) && (<R as Rel2>::At::<'x, 'w>)).imply(Eq::<'y, 'w>)
        ))))
        .imply(Exists::<'b>(ForAll::<'y>(
            (In::<'y, 'b>).iff(Exists::<'x>((In::<'x, 'a>) && (<R as Rel2>::At::<'x, 'y>)))
        )))
    )
)
where
    R: Rel2,
{
    unsafe { cert() }
}

/// **Choice**: every set of nonempty sets admits a choice function.
pub fn choice() -> thm!(
    { Axiomize },
    ForAll::<'a>(
        (ForAll::<'x>((In::<'x, 'a>).imply(Exists::<'w>(In::<'w, 'x>)))).imply(Exists::<'c>(
            (IsFunction::<'c>)
                && (ForAll::<'x>(
                    (In::<'x, 'a>).imply(Exists::<'w>((Applies::<'c, 'x, 'w>) && (In::<'w, 'x>)))
                ))
        ))
    )
) {
    unsafe { cert() }
}
