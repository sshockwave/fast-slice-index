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
use ::core::marker::PhantomData;

use crate::logic::prop::{Cert, FirstOrder, View};
use crate::logic::zfc::Rel2;
use crate::macros::thm;
use crate::rel::empty::IsEmpty;
use crate::rel::ext::{InLeftView2, Membership};
use crate::rel::func::Application;
use crate::rel::pair::Pairing;
use crate::rel::succ::Successor;

/// The one primitive atom of Axiomize's set language.
///
/// This has to be public because it instantiates the public
/// [`Membership::In`] associated type. Composite set-language propositions are
/// expressed through the generic relation traits instead.
pub struct In<'a, 'b>(PhantomData<(&'a (), &'b ())>);

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
/// Equality is *defined* as having the same members, so the usual other
/// direction is free and this congruence is the axiom's entire content.
///
/// Stated using the generic extensionality view so quantifiers can be
/// eliminated at a use site.
pub fn ext() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<InLeftView2<Axiomize, Axiomize>>> {
    unsafe { cert() }
}

/// **Pairing**: `∀x ∀y. ∃p. p = {x, y}`
pub fn pairing() -> thm!(
    { Axiomize },
    ForAll::<'x, 'y>(Exists::<'p>(<Axiomize as Pairing<Axiomize>>::Pair::<'p, 'x, 'y>))
) {
    unsafe { cert() }
}

/// **Union**: `∀f. ∃u. ∀z. (z ∈ u ↔ ∃y. (z ∈ y ∧ y ∈ f))`
pub fn union() -> thm!(
    { Axiomize },
    ForAll::<'f>(Exists::<'u>(ForAll::<'z>(
        (<Axiomize as Membership<Axiomize>>::In::<'z, 'u>).iff(Exists::<'y>(
            (<Axiomize as Membership<Axiomize>>::In::<'z, 'y>)
                && (<Axiomize as Membership<Axiomize>>::In::<'y, 'f>)
        ))
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
pub fn separation<P>() -> thm!(
    { Axiomize },
    ForAll::<'a>(Exists::<'s>(ForAll::<'z>(
        (<Axiomize as Membership<Axiomize>>::In::<'z, 's>).iff(
            (<Axiomize as Membership<Axiomize>>::In::<'z, 'a>) && (<P as View<'z>>::Output)
        )
    )))
)
where
    P: for<'z> View<'z> + ?Sized,
{
    unsafe { cert() }
}

/// **Power set**: `∀x. ∃p. ∀z. (z ∈ p ↔ z ⊆ x)`
pub fn power_set() -> thm!(
    { Axiomize },
    ForAll::<'x>(Exists::<'p>(ForAll::<'z>(
        (<Axiomize as Membership<Axiomize>>::In::<'z, 'p>).iff(ForAll::<'w>(
            (<Axiomize as Membership<Axiomize>>::In::<'w, 'z>)
                >>= (<Axiomize as Membership<Axiomize>>::In::<'w, 'x>)
        ))
    )))
) {
    unsafe { cert() }
}

/// **Regularity**: every nonempty set has an ∈-minimal member.
pub fn regularity() -> thm!(
    { Axiomize },
    ForAll::<'x>((Exists::<'y>(<Axiomize as Membership<Axiomize>>::In::<'y, 'x>)).imply(Exists::<'y>(
        (<Axiomize as Membership<Axiomize>>::In::<'y, 'x>) && (!(Exists::<'z>(
            (<Axiomize as Membership<Axiomize>>::In::<'z, 'y>)
                && (<Axiomize as Membership<Axiomize>>::In::<'z, 'x>)
        )))
    )))
) {
    unsafe { cert() }
}

/// **Infinity**: some set contains ∅ and is closed under `y ↦ y ∪ {y}`.
///
/// Its generic spelling retains the quantified structure needed by clients.
pub fn infinity() -> thm!(
    { Axiomize },
    Exists::<'i>(
        (Exists::<'e>(
            (<Axiomize as Membership<Axiomize>>::In::<'e, 'i>)
                && (IsEmpty::<'e, Axiomize, Axiomize>)
        )) && (ForAll::<'y>(
            (<Axiomize as Membership<Axiomize>>::In::<'y, 'i>)
                >>= Exists::<'s>(
                    (<Axiomize as Membership<Axiomize>>::In::<'s, 'i>)
                        && (<Axiomize as Successor<Axiomize>>::Succ::<'s, 'y>)
                )
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
        (ForAll::<'x>((<Axiomize as Membership<Axiomize>>::In::<'x, 'a>).imply(ForAll::<'y, 'w>(
            ((<R as Rel2>::At::<'x, 'y>) && (<R as Rel2>::At::<'x, 'w>)).imply(
                crate::rel::ext::ExtEq::<'y, 'w, Axiomize, Axiomize>
            )
        ))))
        .imply(Exists::<'b>(ForAll::<'y>(
            (<Axiomize as Membership<Axiomize>>::In::<'y, 'b>).iff(Exists::<'x>(
                (<Axiomize as Membership<Axiomize>>::In::<'x, 'a>) && (<R as Rel2>::At::<'x, 'y>)
            ))
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
        (ForAll::<'x>((<Axiomize as Membership<Axiomize>>::In::<'x, 'a>).imply(Exists::<'w>(
            <Axiomize as Membership<Axiomize>>::In::<'w, 'x>
        )))).imply(Exists::<'c>(
            (<Axiomize as Application<Axiomize>>::IsFunction::<'c>)
                && (ForAll::<'x>(
                    (<Axiomize as Membership<Axiomize>>::In::<'x, 'a>).imply(Exists::<'w>(
                        (<Axiomize as Application<Axiomize>>::App::<'c, 'x, 'w>)
                            && (<Axiomize as Membership<Axiomize>>::In::<'w, 'x>)
                    ))
                ))
        ))
    )
) {
    unsafe { cert() }
}
