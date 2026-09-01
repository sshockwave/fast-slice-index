//! The language of set theory, and what can be derived in it.
//!
//! The assumptions live in [`crate::logic::axiom::zfc`] and nothing else in
//! this module may add to them: everything here is safe code, so a theorem
//! below is either a definition or a derivation. That split is the point —
//! `axiom` stays small enough to audit by reading it, and no `unsafe` sits next
//! to a proof where it could be mistaken for one.
//!
//! [`In`] is the sole primitive. Equality is *defined* ([`Eq`]) as having the
//! same members, which is why [`crate::logic::axiom::zfc::ext`] only has to
//! assume the converse congruence.
#![expect(
    unused_parens,
    reason = "`pred!` parses its body as an expression, so operands are \
              parenthesised for grouping; the parens survive into the type"
)]

use ::core::marker::PhantomData;

use crate::logic::axiom::Axiomize;
use crate::logic::prop::{
    And, Cert, Deduction, DeductionUpgrade, FirstOrder, ForAllProof, Generalise, Iff, Imply, View,
    forall_intro, reflexive, syllogism,
};
use crate::macros::pred;

/// A binary relation as a type-level schema parameter, for [`replacement`].
///
/// [`View`] carries one lifetime and replacement needs two, so this is its
/// two-argument counterpart. Like every schema here it is instantiated per
/// relation rather than quantified over, which keeps the development
/// predicative.
pub trait Rel2 {
    type At<'x, 'y>;
}

/// `'a ∈ 'b`. The one primitive relation.
pub struct In<'a, 'b>(PhantomData<(&'a (), &'b ())>);

/// `∀z. (z ∈ x ↔ z ∈ y)` — the body of [`Eq`], with `'z` still to bind.
pub type EqView<'x, 'y> =
    dyn for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'x>, In<'z, 'y>>> + 'static;

/// `'x = 'y`, *defined* as having the same members.
pub type Eq<'x, 'y> = <Axiomize as FirstOrder>::ForAll<EqView<'x, 'y>>;

/// `∀z. (z ∈ x → z ∈ y)` — the body of [`Subset`].
pub type SubsetView<'x, 'y> =
    dyn for<'z> View<'z, Output = <Axiomize as Imply>::Imply<In<'z, 'x>, In<'z, 'y>>> + 'static;

/// `'x ⊆ 'y`.
pub type Subset<'x, 'y> = <Axiomize as FirstOrder>::ForAll<SubsetView<'x, 'y>>;

// ---------------------------------------------------------------------------
// Defined notions
// ---------------------------------------------------------------------------

/// `IsEmpty(e) := ∀z. z ∉ e`
pub type IsEmpty<'e> = pred!({ Axiomize }, ForAll::<'z>(!(In::<'z, 'e>)));

/// `IsSingleton(s, a) := ∀z. (z ∈ s ↔ z = a)`, i.e. `s = {a}`.
pub type IsSingleton<'s, 'a> = pred!({ Axiomize }, ForAll::<'z>((In::<'z, 's>).iff(Eq::<'z, 'a>)));

/// `IsPair(p, a, b) := ∀z. (z ∈ p ↔ (z = a ∨ z = b))`, i.e. `p = {a, b}`.
pub type IsPair<'p, 'a, 'b> = pred!(
    { Axiomize },
    ForAll::<'z>((In::<'z, 'p>).iff((Eq::<'z, 'a>) || (Eq::<'z, 'b>)))
);

/// `IsSuccOf(s, y) := ∀w. (w ∈ s ↔ (w ∈ y ∨ w = y))`, i.e. `s = y ∪ {y}`.
///
/// The von Neumann successor, used only to state [`infinity`].
pub type IsSuccOf<'s, 'y> = pred!(
    { Axiomize },
    ForAll::<'w>((In::<'w, 's>).iff((In::<'w, 'y>) || (Eq::<'w, 'y>)))
);

/// `IsOrderedPair(p, a, b) := p = {{a}, {a, b}}` — the Kuratowski pair.
///
/// Stated as an existential over the two layers because this logic has no term
/// formers: `u` is `{a}`, `v` is `{a, b}`, `p` is `{u, v}`. [`pairing`] is what
/// makes all three exist. This is the construction
/// [`crate::algebra::group`]'s module docs call unavailable at the level of
/// lifetimes alone — it becomes available once sets are the elements.
pub type IsOrderedPair<'p, 'a, 'b> = pred!(
    { Axiomize },
    Exists::<'u, 'v>((IsSingleton::<'u, 'a>) && ((IsPair::<'v, 'a, 'b>) && (IsPair::<'p, 'u, 'v>)))
);

/// `Applies(f, a, b) := ⟨a, b⟩ ∈ f` — "f maps a to b".
///
/// A function *is* its graph, so application is membership of an ordered pair.
/// This is the reified counterpart of
/// [`crate::logic::function::Function`]'s type-level `F<'x, 'y>`: here `'f` is
/// an ordinary element, so it can be quantified over — which is what makes a
/// recursion theorem statable at all.
pub type Applies<'f, 'a, 'b> = pred!(
    { Axiomize },
    Exists::<'p>((IsOrderedPair::<'p, 'a, 'b>) && (In::<'p, 'f>))
);

/// `IsRelation(r) := every member of r is an ordered pair`
pub type IsRelation<'r> = pred!(
    { Axiomize },
    ForAll::<'z>((In::<'z, 'r>).imply(Exists::<'a, 'b>(IsOrderedPair::<'z, 'a, 'b>)))
);

/// `IsFunction(f) := IsRelation(f) ∧ f is single-valued`
pub type IsFunction<'f> = pred!(
    { Axiomize },
    (IsRelation::<'f>)
        && (ForAll::<'a, 'b, 'c>(
            ((Applies::<'f, 'a, 'b>) && (Applies::<'f, 'a, 'c>)).imply(Eq::<'b, 'c>)
        ))
);

/// `InDomain(f, a) := ∃b. f(a) = b`
pub type InDomain<'f, 'a> = pred!({ Axiomize }, Exists::<'b>(Applies::<'f, 'a, 'b>));

// ---------------------------------------------------------------------------
// Theorems: equality is an equivalence
// ---------------------------------------------------------------------------
//
// These need no axiom at all. `Eq` unfolds to a biconditional, and `↔` is
// reflexive and symmetric already from `PropLogic` + `And`. They are the first
// evidence that the encoding carries content rather than merely typechecking.

/// `λx. x = x`
pub type EqReflView = dyn for<'x> View<'x, Output = Eq<'x, 'x>> + 'static;

/// `∀x. x = x` — **proved**, not assumed.
pub fn eq_refl() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<EqReflView>> {
    forall_intro(EqRefl)
}

#[derive(Clone, Copy)]
struct EqRefl;
impl<Q> Generalise<Axiomize, Q> for EqRefl
where
    Q: for<'x> View<'x, Output = Eq<'x, 'x>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Axiomize, <Q as View<'x>>::Output> {
        forall_intro::<Axiomize, EqView<'x, 'x>, _>(IffRefl(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct IffRefl<'x>(PhantomData<&'x ()>);
impl<'x, Q> Generalise<Axiomize, Q> for IffRefl<'x>
where
    Q: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'x>, In<'z, 'x>>> + ?Sized,
{
    fn prove<'z>(self) -> Cert<Axiomize, <Q as View<'z>>::Output> {
        <Axiomize as And>::and_intro()
            .mp(reflexive::<In<'z, 'x>, Axiomize>())
            .mp(reflexive::<In<'z, 'x>, Axiomize>())
    }
}

/// `(P ∧ Q) → (Q ∧ P)`, at any logic with conjunction.
///
/// Purely propositional, so it is a plain function: no `dyn` reaches an impl
/// header and the nested-binder hazard does not arise.
fn and_comm<P, Q, L: And>() -> Cert<L, L::Imply<L::And<P, Q>, L::And<Q, P>>> {
    let h = Deduction::<L::And<P, Q>, L>::assume();
    L::and_intro()
        .upgrade()
        .mp(h.clone().pipe(L::and_right().upgrade()))
        .mp(h.pipe(L::and_left().upgrade()))
        .cast()
}

/// `λx. ∀y. x = y → y = x`
pub type EqSymmView =
    dyn for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqSymmView1<'x>>> + 'static;
/// `λy. x = y → y = x`
pub type EqSymmView1<'x> =
    dyn for<'y> View<'y, Output = <Axiomize as Imply>::Imply<Eq<'x, 'y>, Eq<'y, 'x>>> + 'static;

/// `∀x ∀y. x = y → y = x` — **proved**.
///
/// Still no axiom: unfolding `Eq` turns this into commuting the two halves of a
/// biconditional underneath a quantifier.
pub fn eq_symm() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<EqSymmView>> {
    forall_intro(EqSymm)
}

#[derive(Clone, Copy)]
struct EqSymm;
impl<Q> Generalise<Axiomize, Q> for EqSymm
where
    Q: for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqSymmView1<'x>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Axiomize, <Q as View<'x>>::Output> {
        forall_intro::<Axiomize, EqSymmView1<'x>, _>(EqSymm1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqSymm1<'x>(PhantomData<&'x ()>);
impl<'x, Q> Generalise<Axiomize, Q> for EqSymm1<'x>
where
    Q: for<'y> View<'y, Output = <Axiomize as Imply>::Imply<Eq<'x, 'y>, Eq<'y, 'x>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Axiomize, <Q as View<'y>>::Output> {
        // `forall_gen` produces exactly `P → ∀z. Q z`; take `P` to be the
        // hypothesis `x = y`, so no `Deduction` scope is needed here.
        <Axiomize as FirstOrder>::forall_gen(EqSymm2::<'x, 'y, EqView<'x, 'y>>(
            PhantomData,
            PhantomData,
        ))
    }
}

struct EqSymm2<'x, 'y, E: ?Sized>(PhantomData<(&'x (), &'y ())>, PhantomData<E>);
impl<E: ?Sized> Clone for EqSymm2<'_, '_, E> {
    fn clone(&self) -> Self {
        EqSymm2(PhantomData, PhantomData)
    }
}
impl<'x, 'y, E, Q> ForAllProof<Axiomize, <Axiomize as FirstOrder>::ForAll<E>, Q>
    for EqSymm2<'x, 'y, E>
where
    E: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'x>, In<'z, 'y>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'y>, In<'z, 'x>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<<Axiomize as FirstOrder>::ForAll<E>, <Q as View<'z>>::Output>,
    > {
        // x = y  ⊢  (z ∈ x ↔ z ∈ y)  ⊢  (z ∈ y ↔ z ∈ x)
        syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<'z, E>())
            .mp(and_comm())
    }
}

/// Typecheck witnesses: `cargo check` is the proof checker.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
const _: () = {
    use crate::logic::axiom::zfc::{
        choice, ext, infinity, pairing, power_set, regularity, replacement, separation, union,
    };

    /// Every axiom is stated and callable, both schemas included.
    fn axioms_are_callable() {
        struct P;
        impl<'z> View<'z> for P {
            type Output = In<'z, 'z>;
        }
        struct R;
        impl Rel2 for R {
            type At<'x, 'y> = In<'x, 'y>;
        }
        let _ = ext();
        let _ = pairing();
        let _ = union();
        let _ = separation::<P>();
        let _ = power_set();
        let _ = regularity();
        let _ = infinity();
        let _ = replacement::<R>();
        let _ = choice();
    }

    /// Reflexivity and symmetry of equality are derived from nothing at all —
    /// no axiom is invoked anywhere in their proofs.
    fn equality_is_an_equivalence() {
        let _ = eq_refl();
        let _ = eq_symm();
    }

    /// The defined notions all resolve, including the Kuratowski pair and the
    /// reified function application built on top of it. Stated as identities so
    /// that no certificate has to be manufactured in safe code.
    fn definitions_resolve<'f, 'p, 'a, 'b>(
        p: Cert<Axiomize, IsOrderedPair<'p, 'a, 'b>>,
        f: Cert<Axiomize, IsFunction<'f>>,
        ap: Cert<Axiomize, Applies<'f, 'a, 'b>>,
        d: Cert<Axiomize, InDomain<'f, 'a>>,
        sub: Cert<Axiomize, Subset<'a, 'b>>,
        e: Cert<Axiomize, IsEmpty<'a>>,
        s: Cert<Axiomize, IsSingleton<'a, 'b>>,
        pr: Cert<Axiomize, IsPair<'p, 'a, 'b>>,
        sc: Cert<Axiomize, IsSuccOf<'a, 'b>>,
        r: Cert<Axiomize, IsRelation<'f>>,
    ) -> (
        Cert<Axiomize, IsOrderedPair<'p, 'a, 'b>>,
        Cert<Axiomize, IsFunction<'f>>,
        Cert<Axiomize, Applies<'f, 'a, 'b>>,
        Cert<Axiomize, InDomain<'f, 'a>>,
        Cert<Axiomize, Subset<'a, 'b>>,
        Cert<Axiomize, IsEmpty<'a>>,
        Cert<Axiomize, IsSingleton<'a, 'b>>,
        Cert<Axiomize, IsPair<'p, 'a, 'b>>,
        Cert<Axiomize, IsSuccOf<'a, 'b>>,
        Cert<Axiomize, IsRelation<'f>>,
    ) {
        (p, f, ap, d, sub, e, s, pr, sc, r)
    }
};
