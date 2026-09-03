//! The nine assumptions of ZFC, and nothing else.
//!
//! Every function here has the body `unsafe { cert() }`: it mints a certificate
//! from nothing, which is exactly what an axiom is. Keeping them alone in one
//! file means the trusted base of the whole development can be audited by
//! reading it end to end — the language they are stated in, and everything
//! derived from them, lives in the corresponding generic `logic` and `rel`
//! modules.
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
use super::lang::{
    Applies, Eq, ExtView, In, InductiveView, IsFunction, IsPair, Rel2, SeparationView, Subset,
};
use crate::logic::prop::{Cert, FirstOrder, View};
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
///
/// Stated against [`ExtView`] rather than an inline `pred!` body so the
/// quantifiers can be eliminated at a use site; `set.rs` carries a witness that
/// the two spellings are the same proposition.
pub fn ext() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<ExtView>> {
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
/// the generic induction development. Carving only out of an
/// existing `a` is what keeps this from being naive comprehension, which would
/// be inconsistent.
pub fn separation<P>() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SeparationView<P>>>
where
    P: for<'z> View<'z> + ?Sized,
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
///
/// Stated against [`InductiveView`] for the same reason as [`ext`]: an inline
/// body is anonymous, and this existential has to be eliminated to be of any
/// use. `set.rs` witnesses that the two spellings are the same proposition.
pub fn infinity() -> Cert<Axiomize, <Axiomize as FirstOrder>::Exists<InductiveView>> {
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
