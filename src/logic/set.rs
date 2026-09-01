//! The language of set theory, and what can be derived in it.
//!
//! The assumptions live in [`crate::axiom::zfc`] and nothing else in
//! this module may add to them: everything here is safe code, so a theorem
//! below is either a definition or a derivation. That split is the point —
//! `axiom` stays small enough to audit by reading it, and no `unsafe` sits next
//! to a proof where it could be mistaken for one.
//!
//! [`In`] is the sole primitive. Equality is *defined* ([`Eq`]) as having the
//! same members, which is why [`crate::axiom::zfc::ext`] only has to
//! assume the converse congruence.
#![expect(
    unused_parens,
    reason = "`pred!` parses its body as an expression, so operands are \
              parenthesised for grouping; the parens survive into the type"
)]

use ::core::marker::PhantomData;

use crate::axiom::Axiomize;
use crate::axiom::zfc::ext;
use crate::logic::prop::{
    And, Cert, Deduction, DeductionUpgrade, FirstOrder, ForAllProof, Generalise, Iff, Imply, Or,
    PropLogic, View, curry, forall_intro, reflexive, syllogism,
};
use crate::macros::pred;

/// A binary relation as a type-level schema parameter, for [`crate::axiom::zfc::replacement`].
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

/// `λw. x ∈ w ↔ y ∈ w` — the congruence [`crate::axiom::zfc::ext`] hands back.
pub type ExtCongrView<'x, 'y> =
    dyn for<'w> View<'w, Output = Iff<Axiomize, In<'x, 'w>, In<'y, 'w>>> + 'static;

/// `λy. x = y → ∀w. (x ∈ w ↔ y ∈ w)`
pub type ExtView1<'x> = dyn for<'y> View<
        'y,
        Output = <Axiomize as Imply>::Imply<
            Eq<'x, 'y>,
            <Axiomize as FirstOrder>::ForAll<ExtCongrView<'x, 'y>>,
        >,
    > + 'static;

/// `λx. ∀y. x = y → ∀w. (x ∈ w ↔ y ∈ w)` — the body of extensionality.
///
/// Named here rather than left anonymous inside the axiom so that the axiom's
/// quantifiers can actually be eliminated: [`FirstOrder::forall_elim`] needs
/// the view as a type argument, and a `pred!` body gives it no name.
pub type ExtView =
    dyn for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<ExtView1<'x>>> + 'static;

// ---------------------------------------------------------------------------
// Defined notions
// ---------------------------------------------------------------------------

/// `IsEmpty(e) := ∀z. z ∉ e`
pub type IsEmpty<'e> = pred!({ Axiomize }, ForAll::<'z>(!(In::<'z, 'e>)));

/// `λz. z ∈ s ↔ z = a` — the body of [`IsSingleton`].
///
/// Named for the same reason as [`PairView`]: a proof about singletons has to
/// pin this view in an impl header.
pub type SingletonView<'s, 'a> =
    dyn for<'z> View<'z, Output = Iff<Axiomize, In<'z, 's>, Eq<'z, 'a>>> + 'static;

/// `IsSingleton(s, a) := ∀z. (z ∈ s ↔ z = a)`, i.e. `s = {a}`.
pub type IsSingleton<'s, 'a> = <Axiomize as FirstOrder>::ForAll<SingletonView<'s, 'a>>;

/// `λz. z ∈ p ↔ (z = a ∨ z = b)` — the body of [`IsPair`].
///
/// Named separately because a proof about pairs has to pin this view in an
/// impl header, and the `pred!` form gives it no name.
pub type PairView<'p, 'a, 'b> = dyn for<'z> View<'z, Output = pred!({ Axiomize }, In::<'z, 'p>.iff(Eq::<'z, 'a> || Eq::<'z, 'b>))>
    + 'static;

/// `IsPair(p, a, b) := ∀z. (z ∈ p ↔ (z = a ∨ z = b))`, i.e. `p = {a, b}`.
pub type IsPair<'p, 'a, 'b> = <Axiomize as FirstOrder>::ForAll<PairView<'p, 'a, 'b>>;

/// `IsSuccOf(s, y) := ∀w. (w ∈ s ↔ (w ∈ y ∨ w = y))`, i.e. `s = y ∪ {y}`.
///
/// The von Neumann successor, used only to state [`crate::axiom::zfc::infinity`].
pub type IsSuccOf<'s, 'y> = pred!(
    { Axiomize },
    ForAll::<'w>((In::<'w, 's>).iff((In::<'w, 'y>) || (Eq::<'w, 'y>)))
);

/// `IsOrderedPair(p, a, b) := p = {{a}, {a, b}}` — the Kuratowski pair.
///
/// Stated as an existential over the two layers because this logic has no term
/// formers: `u` is `{a}`, `v` is `{a, b}`, `p` is `{u, v}`. [`crate::axiom::zfc::pairing`] is what
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

/// `λc. (f(a)=b ∧ f(a)=c) → b = c`
pub type SingleValuedView2<'f, 'a, 'b> = dyn for<'c> View<
        'c,
        Output = pred!(
            { Axiomize },
            ((Applies::<'f, 'a, 'b>) && (Applies::<'f, 'a, 'c>)) >>= Eq::<'b, 'c>
        ),
    > + 'static;
/// `λb. ∀c. (f(a)=b ∧ f(a)=c) → b = c`
pub type SingleValuedView1<'f, 'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<SingleValuedView2<'f, 'a, 'b>>>
    + 'static;
/// `λa. ∀b ∀c. (f(a)=b ∧ f(a)=c) → b = c`
pub type SingleValuedView<'f> = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingleValuedView1<'f, 'a>>>
    + 'static;

/// `IsSingleValued(f) := ∀a ∀b ∀c. (f(a)=b ∧ f(a)=c) → b = c`
///
/// Split out of [`IsFunction`] and named so its quantifiers can be eliminated;
/// [`func_apply_unique`] is what that buys.
pub type IsSingleValued<'f> = <Axiomize as FirstOrder>::ForAll<SingleValuedView<'f>>;

/// `IsFunction(f) := IsRelation(f) ∧ f is single-valued`
pub type IsFunction<'f> = pred!({ Axiomize }, (IsRelation::<'f>) && (IsSingleValued::<'f>));

/// `λb. f(a) = b` — the body of [`InDomain`].
pub type InDomainView<'f, 'a> = dyn for<'b> View<'b, Output = Applies<'f, 'a, 'b>> + 'static;

/// `InDomain(f, a) := ∃b. f(a) = b`
pub type InDomain<'f, 'a> = <Axiomize as FirstOrder>::Exists<InDomainView<'f, 'a>>;

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

/// `(A → A') → (B → B') → ((A ∧ B) → (A' ∧ B'))`
fn and_map<A, B, A2, B2, L: And>(
    f: Cert<L, L::Imply<A, A2>>,
    g: Cert<L, L::Imply<B, B2>>,
) -> Cert<L, L::Imply<L::And<A, B>, L::And<A2, B2>>> {
    let h = Deduction::<L::And<A, B>, L>::assume();
    L::and_intro()
        .upgrade()
        .mp(h.clone().pipe(L::and_left().upgrade()).pipe(f.upgrade()))
        .mp(h.pipe(L::and_right().upgrade()).pipe(g.upgrade()))
        .cast()
}

/// `((A ↔ B) ∧ (B ↔ C)) → (A ↔ C)`
fn iff_trans<A, B, C, L: And>()
-> Cert<L, L::Imply<L::And<Iff<L, A, B>, Iff<L, B, C>>, Iff<L, A, C>>> {
    let h = Deduction::<L::And<Iff<L, A, B>, Iff<L, B, C>>, L>::assume();
    let left = h.clone().pipe(L::and_left().upgrade());
    let right = h.pipe(L::and_right().upgrade());
    let ab = left.clone().pipe(L::and_left().upgrade());
    let ba = left.pipe(L::and_right().upgrade());
    let bc = right.clone().pipe(L::and_left().upgrade());
    let cb = right.pipe(L::and_right().upgrade());
    L::and_intro()
        .upgrade()
        .mp(syllogism().mp(ab).mp(bc))
        .mp(syllogism().mp(cb).mp(ba))
        .cast()
}

/// `λx. ∀y ∀w. x = y → y = w → x = w`
pub type EqTransView =
    dyn for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqTransView1<'x>>> + 'static;
/// `λy. ∀w. x = y → y = w → x = w`
pub type EqTransView1<'x> =
    dyn for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<EqTransView2<'x, 'y>>> + 'static;
/// `λw. x = y → y = w → x = w`
pub type EqTransView2<'x, 'y> = dyn for<'w> View<
        'w,
        Output = <Axiomize as Imply>::Imply<
            Eq<'x, 'y>,
            <Axiomize as Imply>::Imply<Eq<'y, 'w>, Eq<'x, 'w>>,
        >,
    > + 'static;

/// `∀x ∀y ∀w. x = y → y = w → x = w` — **proved**.
///
/// With [`eq_refl`] and [`eq_symm`], defined equality is an equivalence, and
/// none of the three costs an axiom.
pub fn eq_trans() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<EqTransView>> {
    forall_intro(EqTrans)
}

#[derive(Clone, Copy)]
struct EqTrans;
impl<Q> Generalise<Axiomize, Q> for EqTrans
where
    Q: for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqTransView1<'x>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Axiomize, <Q as View<'x>>::Output> {
        forall_intro::<Axiomize, EqTransView1<'x>, _>(EqTrans1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqTrans1<'x>(PhantomData<&'x ()>);
impl<'x, Q> Generalise<Axiomize, Q> for EqTrans1<'x>
where
    Q: for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<EqTransView2<'x, 'y>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Axiomize, <Q as View<'y>>::Output> {
        forall_intro::<Axiomize, EqTransView2<'x, 'y>, _>(EqTrans2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqTrans2<'x, 'y>(PhantomData<(&'x (), &'y ())>);
impl<'x, 'y, Q> Generalise<Axiomize, Q> for EqTrans2<'x, 'y>
where
    Q: for<'w> View<
            'w,
            Output = <Axiomize as Imply>::Imply<
                Eq<'x, 'y>,
                <Axiomize as Imply>::Imply<Eq<'y, 'w>, Eq<'x, 'w>>,
            >,
        > + ?Sized,
{
    fn prove<'w>(self) -> Cert<Axiomize, <Q as View<'w>>::Output> {
        // `forall_gen` takes one antecedent, so the two hypotheses go in
        // conjoined and `curry` splits them again afterwards.
        curry().mp(<Axiomize as FirstOrder>::forall_gen(EqTrans3::<
            'x,
            'y,
            'w,
            EqView<'x, 'y>,
            EqView<'y, 'w>,
        >(
            PhantomData,
            PhantomData,
            PhantomData,
        )))
    }
}

struct EqTrans3<'x, 'y, 'w, E1: ?Sized, E2: ?Sized>(
    PhantomData<(&'x (), &'y (), &'w ())>,
    PhantomData<E1>,
    PhantomData<E2>,
);
impl<E1: ?Sized, E2: ?Sized> Clone for EqTrans3<'_, '_, '_, E1, E2> {
    fn clone(&self) -> Self {
        EqTrans3(PhantomData, PhantomData, PhantomData)
    }
}
impl<'x, 'y, 'w, E1, E2, Q>
    ForAllProof<
        Axiomize,
        <Axiomize as And>::And<
            <Axiomize as FirstOrder>::ForAll<E1>,
            <Axiomize as FirstOrder>::ForAll<E2>,
        >,
        Q,
    > for EqTrans3<'x, 'y, 'w, E1, E2>
where
    E1: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'x>, In<'z, 'y>>> + ?Sized,
    E2: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'y>, In<'z, 'w>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'x>, In<'z, 'w>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<
                <Axiomize as FirstOrder>::ForAll<E1>,
                <Axiomize as FirstOrder>::ForAll<E2>,
            >,
            <Q as View<'z>>::Output,
        >,
    > {
        // (x = y ∧ y = w) ⊢ ((z∈x ↔ z∈y) ∧ (z∈y ↔ z∈w)) ⊢ (z∈x ↔ z∈w)
        syllogism()
            .mp(and_map(
                <Axiomize as FirstOrder>::forall_elim::<'z, E1>(),
                <Axiomize as FirstOrder>::forall_elim::<'z, E2>(),
            ))
            .mp(iff_trans())
    }
}

// ---------------------------------------------------------------------------
// Pairs are unique
// ---------------------------------------------------------------------------
//
// `pairing` says a pair *exists*; nothing so far says it is the only one. This
// supplies the other half, and it needs no axiom either: two sets with the same
// membership condition satisfy `Eq` by definition.

/// `λa. ∀b ∀p ∀q. p = {a,b} → q = {a,b} → p = q`
pub type PairUniqueView =
    dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairUniqueView1<'a>>> + 'static;
/// `λb. ∀p ∀q. p = {a,b} → q = {a,b} → p = q`
pub type PairUniqueView1<'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairUniqueView2<'a, 'b>>>
    + 'static;
/// `λp. ∀q. p = {a,b} → q = {a,b} → p = q`
pub type PairUniqueView2<'a, 'b> = dyn for<'p> View<'p, Output = <Axiomize as FirstOrder>::ForAll<PairUniqueView3<'a, 'b, 'p>>>
    + 'static;
/// `λq. p = {a,b} → q = {a,b} → p = q`
pub type PairUniqueView3<'a, 'b, 'p> = dyn for<'q> View<
        'q,
        Output = pred!(
            { Axiomize },
            IsPair::<'p, 'a, 'b> >>= IsPair::<'q, 'a, 'b> >>= Eq::<'p, 'q>
        ),
    > + 'static;

/// `∀a ∀b ∀p ∀q. p = {a,b} → q = {a,b} → p = q` — **proved**.
///
/// Together with [`crate::axiom::zfc::pairing`] this pins the pair down:
/// it exists and is unique. Still no axiom — `Eq` is *defined* as sharing
/// members, and both sets share the membership condition `z = a ∨ z = b`.
pub fn pair_unique() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<PairUniqueView>> {
    forall_intro(PairUnique)
}

#[derive(Clone, Copy)]
struct PairUnique;
impl<Q> Generalise<Axiomize, Q> for PairUnique
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairUniqueView1<'a>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, PairUniqueView1<'a>, _>(PairUnique1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairUnique1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for PairUnique1<'a>
where
    Q: for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairUniqueView2<'a, 'b>>>
        + ?Sized,
{
    fn prove<'b>(self) -> Cert<Axiomize, <Q as View<'b>>::Output> {
        forall_intro::<Axiomize, PairUniqueView2<'a, 'b>, _>(PairUnique2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairUnique2<'a, 'b>(PhantomData<(&'a (), &'b ())>);
impl<'a, 'b, Q> Generalise<Axiomize, Q> for PairUnique2<'a, 'b>
where
    Q: for<'p> View<'p, Output = <Axiomize as FirstOrder>::ForAll<PairUniqueView3<'a, 'b, 'p>>>
        + ?Sized,
{
    fn prove<'p>(self) -> Cert<Axiomize, <Q as View<'p>>::Output> {
        forall_intro::<Axiomize, PairUniqueView3<'a, 'b, 'p>, _>(PairUnique3(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairUnique3<'a, 'b, 'p>(PhantomData<(&'a (), &'b (), &'p ())>);
impl<'a, 'b, 'p, Q> Generalise<Axiomize, Q> for PairUnique3<'a, 'b, 'p>
where
    Q: for<'q> View<
            'q,
            Output = pred!(
                { Axiomize },
                IsPair::<'p, 'a, 'b> >>= IsPair::<'q, 'a, 'b> >>= Eq::<'p, 'q>
            ),
        > + ?Sized,
{
    fn prove<'q>(self) -> Cert<Axiomize, <Q as View<'q>>::Output> {
        curry().mp(<Axiomize as FirstOrder>::forall_gen(PairUnique4::<
            'a,
            'b,
            'p,
            'q,
            PairView<'p, 'a, 'b>,
            PairView<'q, 'a, 'b>,
        >(
            PhantomData,
            PhantomData,
            PhantomData,
        )))
    }
}

struct PairUnique4<'a, 'b, 'p, 'q, E1: ?Sized, E2: ?Sized>(
    PhantomData<(&'a (), &'b (), &'p (), &'q ())>,
    PhantomData<E1>,
    PhantomData<E2>,
);
impl<E1: ?Sized, E2: ?Sized> Clone for PairUnique4<'_, '_, '_, '_, E1, E2> {
    fn clone(&self) -> Self {
        PairUnique4(PhantomData, PhantomData, PhantomData)
    }
}
impl<'a, 'b, 'p, 'q, E1, E2, Q>
    ForAllProof<
        Axiomize,
        <Axiomize as And>::And<
            <Axiomize as FirstOrder>::ForAll<E1>,
            <Axiomize as FirstOrder>::ForAll<E2>,
        >,
        Q,
    > for PairUnique4<'a, 'b, 'p, 'q, E1, E2>
where
    E1: for<'z> View<
            'z,
            Output = pred!({ Axiomize }, In::<'z, 'p>.iff(Eq::<'z, 'a> || Eq::<'z, 'b>)),
        > + ?Sized,
    E2: for<'z> View<
            'z,
            Output = pred!({ Axiomize }, In::<'z, 'q>.iff(Eq::<'z, 'a> || Eq::<'z, 'b>)),
        > + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'p>, In<'z, 'q>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<
                <Axiomize as FirstOrder>::ForAll<E1>,
                <Axiomize as FirstOrder>::ForAll<E2>,
            >,
            <Q as View<'z>>::Output,
        >,
    > {
        // (z∈p ↔ D) and (z∈q ↔ D) give (z∈p ↔ D) and (D ↔ z∈q), which compose.
        syllogism()
            .mp(and_map(
                <Axiomize as FirstOrder>::forall_elim::<'z, E1>(),
                syllogism()
                    .mp(<Axiomize as FirstOrder>::forall_elim::<'z, E2>())
                    .mp(and_comm()),
            ))
            .mp(iff_trans())
    }
}

// ---------------------------------------------------------------------------
// What a pair contains
// ---------------------------------------------------------------------------

/// `x = x` at one particular `'x`, for use inside a proof.
fn eq_refl_at<'x>() -> Cert<Axiomize, Eq<'x, 'x>> {
    eq_refl().pipe(<Axiomize as FirstOrder>::forall_elim::<'x, EqReflView>())
}

/// `p = {a,b} → c ∈ p`, given that `c` is one of `a`, `b`.
///
/// The shared core of [`pair_left`] and [`pair_right`]: read the pair's
/// defining biconditional right-to-left at `'c`.
fn pair_member<'a, 'b, 'c, 'p>(
    side: Cert<Axiomize, <Axiomize as Or>::Or<Eq<'c, 'a>, Eq<'c, 'b>>>,
) -> Cert<Axiomize, <Axiomize as Imply>::Imply<IsPair<'p, 'a, 'b>, In<'c, 'p>>> {
    <Axiomize as PropLogic>::l2()
        .mp(syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<
                'c,
                PairView<'p, 'a, 'b>,
            >())
            .mp(<Axiomize as And>::and_right()))
        .mp(<Axiomize as PropLogic>::l1().mp(side))
}

/// `λa. ∀b ∀p. p = {a,b} → a ∈ p`
pub type PairLeftView =
    dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairLeftView1<'a>>> + 'static;
/// `λb. ∀p. p = {a,b} → a ∈ p`
pub type PairLeftView1<'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairLeftView2<'a, 'b>>>
    + 'static;
/// `λp. p = {a,b} → a ∈ p`
pub type PairLeftView2<'a, 'b> = dyn for<'p> View<'p, Output = pred!({ Axiomize }, IsPair::<'p, 'a, 'b> >>= In::<'a, 'p>)>
    + 'static;

/// `∀a ∀b ∀p. p = {a,b} → a ∈ p` — **proved**.
pub fn pair_left() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<PairLeftView>> {
    forall_intro(PairLeft)
}

#[derive(Clone, Copy)]
struct PairLeft;
impl<Q> Generalise<Axiomize, Q> for PairLeft
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairLeftView1<'a>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, PairLeftView1<'a>, _>(PairLeft1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairLeft1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for PairLeft1<'a>
where
    Q: for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairLeftView2<'a, 'b>>> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Axiomize, <Q as View<'b>>::Output> {
        forall_intro::<Axiomize, PairLeftView2<'a, 'b>, _>(PairLeft2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairLeft2<'a, 'b>(PhantomData<(&'a (), &'b ())>);
impl<'a, 'b, Q> Generalise<Axiomize, Q> for PairLeft2<'a, 'b>
where
    Q: for<'p> View<'p, Output = pred!({ Axiomize }, IsPair::<'p, 'a, 'b> >>= In::<'a, 'p>)>
        + ?Sized,
{
    fn prove<'p>(self) -> Cert<Axiomize, <Q as View<'p>>::Output> {
        pair_member(<Axiomize as Or>::or_left().mp(eq_refl_at::<'a>()))
    }
}

/// `λa. ∀b ∀p. p = {a,b} → b ∈ p`
pub type PairRightView =
    dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairRightView1<'a>>> + 'static;
/// `λb. ∀p. p = {a,b} → b ∈ p`
pub type PairRightView1<'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairRightView2<'a, 'b>>>
    + 'static;
/// `λp. p = {a,b} → b ∈ p`
pub type PairRightView2<'a, 'b> = dyn for<'p> View<'p, Output = pred!({ Axiomize }, IsPair::<'p, 'a, 'b> >>= In::<'b, 'p>)>
    + 'static;

/// `∀a ∀b ∀p. p = {a,b} → b ∈ p` — **proved**.
pub fn pair_right() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<PairRightView>> {
    forall_intro(PairRight)
}

#[derive(Clone, Copy)]
struct PairRight;
impl<Q> Generalise<Axiomize, Q> for PairRight
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairRightView1<'a>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, PairRightView1<'a>, _>(PairRight1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairRight1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for PairRight1<'a>
where
    Q: for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairRightView2<'a, 'b>>> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Axiomize, <Q as View<'b>>::Output> {
        forall_intro::<Axiomize, PairRightView2<'a, 'b>, _>(PairRight2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairRight2<'a, 'b>(PhantomData<(&'a (), &'b ())>);
impl<'a, 'b, Q> Generalise<Axiomize, Q> for PairRight2<'a, 'b>
where
    Q: for<'p> View<'p, Output = pred!({ Axiomize }, IsPair::<'p, 'a, 'b> >>= In::<'b, 'p>)>
        + ?Sized,
{
    fn prove<'p>(self) -> Cert<Axiomize, <Q as View<'p>>::Output> {
        pair_member(<Axiomize as Or>::or_right().mp(eq_refl_at::<'b>()))
    }
}

// ---------------------------------------------------------------------------
// Singletons
// ---------------------------------------------------------------------------
//
// The singleton mirror of the pair lemmas above. `{a}` is the inner layer of a
// Kuratowski ordered pair, so everything the ordered-pair characterisation
// needs to know about `{a}` has to exist before that proof can start.

/// `s = {a} → a ∈ s`, at fixed `'a` and `'s`.
///
/// The singleton counterpart of [`pair_member`], and shorter: there is no
/// disjunction to choose a side of, only `a = a`.
fn singleton_member_at<'a, 's>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<IsSingleton<'s, 'a>, In<'a, 's>>> {
    <Axiomize as PropLogic>::l2()
        .mp(syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<
                'a,
                SingletonView<'s, 'a>,
            >())
            .mp(<Axiomize as And>::and_right()))
        .mp(<Axiomize as PropLogic>::l1().mp(eq_refl_at::<'a>()))
}

/// `λa. ∀s. s = {a} → a ∈ s`
pub type SingletonMemberView = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonMemberView1<'a>>>
    + 'static;
/// `λs. s = {a} → a ∈ s`
pub type SingletonMemberView1<'a> = dyn for<'s> View<'s, Output = pred!({ Axiomize }, IsSingleton::<'s, 'a> >>= In::<'a, 's>)>
    + 'static;

/// `∀a ∀s. s = {a} → a ∈ s` — **proved**.
///
/// A singleton is not empty. This is what stops the ordered-pair proof from
/// arguing vacuously about `{a}`.
pub fn singleton_member() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SingletonMemberView>> {
    forall_intro(SingletonMember)
}

#[derive(Clone, Copy)]
struct SingletonMember;
impl<Q> Generalise<Axiomize, Q> for SingletonMember
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonMemberView1<'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, SingletonMemberView1<'a>, _>(SingletonMember1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct SingletonMember1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for SingletonMember1<'a>
where
    Q: for<'s> View<'s, Output = pred!({ Axiomize }, IsSingleton::<'s, 'a> >>= In::<'a, 's>)>
        + ?Sized,
{
    fn prove<'s>(self) -> Cert<Axiomize, <Q as View<'s>>::Output> {
        singleton_member_at::<'a, 's>()
    }
}

/// `λa. ∀s ∀t. s = {a} → t = {a} → s = t`
pub type SingletonUniqueView = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonUniqueView1<'a>>>
    + 'static;
/// `λs. ∀t. s = {a} → t = {a} → s = t`
pub type SingletonUniqueView1<'a> = dyn for<'s> View<'s, Output = <Axiomize as FirstOrder>::ForAll<SingletonUniqueView2<'a, 's>>>
    + 'static;
/// `λt. s = {a} → t = {a} → s = t`
pub type SingletonUniqueView2<'a, 's> = dyn for<'t> View<
        't,
        Output = pred!(
            { Axiomize },
            IsSingleton::<'s, 'a> >>= IsSingleton::<'t, 'a> >>= Eq::<'s, 't>
        ),
    > + 'static;

/// `∀a ∀s ∀t. s = {a} → t = {a} → s = t` — **proved**.
///
/// The singleton counterpart of [`pair_unique`], and identical in shape: both
/// sets share the membership condition `z = a`, and `Eq` is *defined* as
/// sharing members.
pub fn singleton_unique() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SingletonUniqueView>> {
    forall_intro(SingletonUnique)
}

#[derive(Clone, Copy)]
struct SingletonUnique;
impl<Q> Generalise<Axiomize, Q> for SingletonUnique
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonUniqueView1<'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, SingletonUniqueView1<'a>, _>(SingletonUnique1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct SingletonUnique1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for SingletonUnique1<'a>
where
    Q: for<'s> View<'s, Output = <Axiomize as FirstOrder>::ForAll<SingletonUniqueView2<'a, 's>>>
        + ?Sized,
{
    fn prove<'s>(self) -> Cert<Axiomize, <Q as View<'s>>::Output> {
        forall_intro::<Axiomize, SingletonUniqueView2<'a, 's>, _>(SingletonUnique2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct SingletonUnique2<'a, 's>(PhantomData<(&'a (), &'s ())>);
impl<'a, 's, Q> Generalise<Axiomize, Q> for SingletonUnique2<'a, 's>
where
    Q: for<'t> View<
            't,
            Output = pred!(
                { Axiomize },
                IsSingleton::<'s, 'a> >>= IsSingleton::<'t, 'a> >>= Eq::<'s, 't>
            ),
        > + ?Sized,
{
    fn prove<'t>(self) -> Cert<Axiomize, <Q as View<'t>>::Output> {
        curry().mp(<Axiomize as FirstOrder>::forall_gen(SingletonUnique3::<
            'a,
            's,
            't,
            SingletonView<'s, 'a>,
            SingletonView<'t, 'a>,
        >(
            PhantomData,
            PhantomData,
            PhantomData,
        )))
    }
}

struct SingletonUnique3<'a, 's, 't, E1: ?Sized, E2: ?Sized>(
    PhantomData<(&'a (), &'s (), &'t ())>,
    PhantomData<E1>,
    PhantomData<E2>,
);
impl<E1: ?Sized, E2: ?Sized> Clone for SingletonUnique3<'_, '_, '_, E1, E2> {
    fn clone(&self) -> Self {
        SingletonUnique3(PhantomData, PhantomData, PhantomData)
    }
}
impl<'a, 's, 't, E1, E2, Q>
    ForAllProof<
        Axiomize,
        <Axiomize as And>::And<
            <Axiomize as FirstOrder>::ForAll<E1>,
            <Axiomize as FirstOrder>::ForAll<E2>,
        >,
        Q,
    > for SingletonUnique3<'a, 's, 't, E1, E2>
where
    E1: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 's>, Eq<'z, 'a>>> + ?Sized,
    E2: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 't>, Eq<'z, 'a>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 's>, In<'z, 't>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<
                <Axiomize as FirstOrder>::ForAll<E1>,
                <Axiomize as FirstOrder>::ForAll<E2>,
            >,
            <Q as View<'z>>::Output,
        >,
    > {
        // (z∈s ↔ z=a) and (z∈t ↔ z=a) give (z∈s ↔ z=a) and (z=a ↔ z∈t).
        syllogism()
            .mp(and_map(
                <Axiomize as FirstOrder>::forall_elim::<'z, E1>(),
                syllogism()
                    .mp(<Axiomize as FirstOrder>::forall_elim::<'z, E2>())
                    .mp(and_comm()),
            ))
            .mp(iff_trans())
    }
}

// ---------------------------------------------------------------------------
// A singleton is a pair of one thing with itself
// ---------------------------------------------------------------------------

/// `P ↔ (P ∨ P)`, at any logic with conjunction and disjunction.
fn or_idem<P, L: And + Or>() -> Cert<L, Iff<L, P, L::Or<P, P>>> {
    L::and_intro()
        .mp(L::or_left())
        .mp(L::or_elim().mp(reflexive()).mp(reflexive()))
}

/// `(B ↔ C) → ((A ↔ B) → (A ↔ C))`
///
/// [`iff_trans`] with the right-hand biconditional already in hand, which is
/// the shape needed to rewrite one side of a biconditional under a quantifier.
fn iff_extend<A, B, C, L: And>(
    bc: Cert<L, Iff<L, B, C>>,
) -> Cert<L, L::Imply<Iff<L, A, B>, Iff<L, A, C>>> {
    let h = Deduction::<Iff<L, A, B>, L>::assume();
    iff_trans::<A, B, C, L>()
        .upgrade()
        .mp(L::and_intro().upgrade().mp(h).mp(bc.upgrade()))
        .cast()
}

/// `λa. ∀s. s = {a} → s = {a,a}`
pub type SingletonIsPairView = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonIsPairView1<'a>>>
    + 'static;
/// `λs. s = {a} → s = {a,a}`
pub type SingletonIsPairView1<'a> = dyn for<'s> View<'s, Output = pred!({ Axiomize }, IsSingleton::<'s, 'a> >>= IsPair::<'s, 'a, 'a>)>
    + 'static;

/// `∀a ∀s. s = {a} → s = {a,a}` — **proved**.
///
/// The bridge that lets the singleton layer of a Kuratowski pair be treated as
/// an ordinary pair. Its content is just `P ↔ (P ∨ P)` pushed under the
/// quantifier by [`iff_extend`]; see [`pair_is_singleton`] for the converse.
pub fn singleton_is_pair() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SingletonIsPairView>>
{
    forall_intro(SingletonIsPair)
}

#[derive(Clone, Copy)]
struct SingletonIsPair;
impl<Q> Generalise<Axiomize, Q> for SingletonIsPair
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonIsPairView1<'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, SingletonIsPairView1<'a>, _>(SingletonIsPair1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct SingletonIsPair1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for SingletonIsPair1<'a>
where
    Q: for<'s> View<
            's,
            Output = pred!({ Axiomize }, IsSingleton::<'s, 'a> >>= IsPair::<'s, 'a, 'a>),
        > + ?Sized,
{
    fn prove<'s>(self) -> Cert<Axiomize, <Q as View<'s>>::Output> {
        <Axiomize as FirstOrder>::forall_gen(SingletonIsPair2::<'a, 's, SingletonView<'s, 'a>>(
            PhantomData,
            PhantomData,
        ))
    }
}

struct SingletonIsPair2<'a, 's, E: ?Sized>(PhantomData<(&'a (), &'s ())>, PhantomData<E>);
impl<E: ?Sized> Clone for SingletonIsPair2<'_, '_, E> {
    fn clone(&self) -> Self {
        SingletonIsPair2(PhantomData, PhantomData)
    }
}
impl<'a, 's, E, Q> ForAllProof<Axiomize, <Axiomize as FirstOrder>::ForAll<E>, Q>
    for SingletonIsPair2<'a, 's, E>
where
    E: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 's>, Eq<'z, 'a>>> + ?Sized,
    Q: for<'z> View<
            'z,
            Output = pred!({ Axiomize }, In::<'z, 's>.iff(Eq::<'z, 'a> || Eq::<'z, 'a>)),
        > + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<<Axiomize as FirstOrder>::ForAll<E>, <Q as View<'z>>::Output>,
    > {
        // (z∈s ↔ z=a), then rewrite the right side with z=a ↔ (z=a ∨ z=a).
        syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<'z, E>())
            .mp(iff_extend(or_idem::<Eq<'z, 'a>, Axiomize>()))
    }
}

/// `λa. ∀s. s = {a,a} → s = {a}`
pub type PairIsSingletonView = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairIsSingletonView1<'a>>>
    + 'static;
/// `λs. s = {a,a} → s = {a}`
pub type PairIsSingletonView1<'a> = dyn for<'s> View<'s, Output = pred!({ Axiomize }, IsPair::<'s, 'a, 'a> >>= IsSingleton::<'s, 'a>)>
    + 'static;

/// `∀a ∀s. s = {a,a} → s = {a}` — **proved**. The converse of
/// [`singleton_is_pair`], so the two notions coincide at a repeated element.
pub fn pair_is_singleton() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<PairIsSingletonView>>
{
    forall_intro(PairIsSingleton)
}

#[derive(Clone, Copy)]
struct PairIsSingleton;
impl<Q> Generalise<Axiomize, Q> for PairIsSingleton
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairIsSingletonView1<'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, PairIsSingletonView1<'a>, _>(PairIsSingleton1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairIsSingleton1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for PairIsSingleton1<'a>
where
    Q: for<'s> View<
            's,
            Output = pred!({ Axiomize }, IsPair::<'s, 'a, 'a> >>= IsSingleton::<'s, 'a>),
        > + ?Sized,
{
    fn prove<'s>(self) -> Cert<Axiomize, <Q as View<'s>>::Output> {
        <Axiomize as FirstOrder>::forall_gen(PairIsSingleton2::<'a, 's, PairView<'s, 'a, 'a>>(
            PhantomData,
            PhantomData,
        ))
    }
}

struct PairIsSingleton2<'a, 's, E: ?Sized>(PhantomData<(&'a (), &'s ())>, PhantomData<E>);
impl<E: ?Sized> Clone for PairIsSingleton2<'_, '_, E> {
    fn clone(&self) -> Self {
        PairIsSingleton2(PhantomData, PhantomData)
    }
}
impl<'a, 's, E, Q> ForAllProof<Axiomize, <Axiomize as FirstOrder>::ForAll<E>, Q>
    for PairIsSingleton2<'a, 's, E>
where
    E: for<'z> View<
            'z,
            Output = pred!({ Axiomize }, In::<'z, 's>.iff(Eq::<'z, 'a> || Eq::<'z, 'a>)),
        > + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Axiomize, In<'z, 's>, Eq<'z, 'a>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<<Axiomize as FirstOrder>::ForAll<E>, <Q as View<'z>>::Output>,
    > {
        // Same rewrite as `singleton_is_pair`, with the biconditional flipped.
        syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<'z, E>())
            .mp(iff_extend(and_comm().mp(or_idem::<Eq<'z, 'a>, Axiomize>())))
    }
}

// ---------------------------------------------------------------------------
// Reading a set back out of its description
// ---------------------------------------------------------------------------
//
// The lemmas above say what a described set *contains*. These say the converse:
// if two descriptions fit the same set, the described elements must agree.
// Together they are what the Kuratowski pair needs — `⟨a,b⟩` is only injective
// because `{a}` and `{a,b}` can each be read back.

/// `s = {a} → s = {c} → a = c`, at fixed points.
fn singleton_injective_at<'a, 'c, 's>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<
        IsSingleton<'s, 'a>,
        <Axiomize as Imply>::Imply<IsSingleton<'s, 'c>, Eq<'a, 'c>>,
    >,
> {
    Deduction::<IsSingleton<'s, 'a>, Axiomize>::scope(|sa| {
        Deduction::<IsSingleton<'s, 'c>, _>::scope(|sc| {
            // `{a}` contains `a` ...
            let a_in_s = sa
                .upgrade()
                .pipe(singleton_member_at::<'a, 's>().upgrade().upgrade());
            // ... and everything in `{c}` equals `c`.
            let to_c = sc
                .pipe(
                    <Axiomize as FirstOrder>::forall_elim::<'a, SingletonView<'s, 'c>>()
                        .upgrade()
                        .upgrade(),
                )
                .pipe(<Axiomize as And>::and_left().upgrade().upgrade());
            a_in_s.pipe(to_c)
        })
    })
}

/// `λa. ∀c ∀s. s = {a} → s = {c} → a = c`
pub type SingletonInjectiveView = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonInjectiveView1<'a>>>
    + 'static;
/// `λc. ∀s. s = {a} → s = {c} → a = c`
pub type SingletonInjectiveView1<'a> = dyn for<'c> View<'c, Output = <Axiomize as FirstOrder>::ForAll<SingletonInjectiveView2<'a, 'c>>>
    + 'static;
/// `λs. s = {a} → s = {c} → a = c`
pub type SingletonInjectiveView2<'a, 'c> = dyn for<'s> View<
        's,
        Output = pred!(
            { Axiomize },
            IsSingleton::<'s, 'a> >>= IsSingleton::<'s, 'c> >>= Eq::<'a, 'c>
        ),
    > + 'static;

/// `∀a ∀c ∀s. s = {a} → s = {c} → a = c` — **proved**.
///
/// Singletons are injective: a set determines its sole member. This is the
/// converse of [`singleton_unique`], which said the member determines the set,
/// and it is the first half of the ordered-pair characterisation.
pub fn singleton_injective()
-> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SingletonInjectiveView>> {
    forall_intro(SingletonInjective)
}

#[derive(Clone, Copy)]
struct SingletonInjective;
impl<Q> Generalise<Axiomize, Q> for SingletonInjective
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingletonInjectiveView1<'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, SingletonInjectiveView1<'a>, _>(SingletonInjective1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct SingletonInjective1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for SingletonInjective1<'a>
where
    Q: for<'c> View<'c, Output = <Axiomize as FirstOrder>::ForAll<SingletonInjectiveView2<'a, 'c>>>
        + ?Sized,
{
    fn prove<'c>(self) -> Cert<Axiomize, <Q as View<'c>>::Output> {
        forall_intro::<Axiomize, SingletonInjectiveView2<'a, 'c>, _>(SingletonInjective2(
            PhantomData,
        ))
    }
}

#[derive(Clone, Copy)]
struct SingletonInjective2<'a, 'c>(PhantomData<(&'a (), &'c ())>);
impl<'a, 'c, Q> Generalise<Axiomize, Q> for SingletonInjective2<'a, 'c>
where
    Q: for<'s> View<
            's,
            Output = pred!(
                { Axiomize },
                IsSingleton::<'s, 'a> >>= IsSingleton::<'s, 'c> >>= Eq::<'a, 'c>
            ),
        > + ?Sized,
{
    fn prove<'s>(self) -> Cert<Axiomize, <Q as View<'s>>::Output> {
        singleton_injective_at::<'a, 'c, 's>()
    }
}

/// `p = {a,b} → p = {a} → b = a`, at fixed points.
fn pair_collapses_at<'a, 'b, 'p>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<
        IsPair<'p, 'a, 'b>,
        <Axiomize as Imply>::Imply<IsSingleton<'p, 'a>, Eq<'b, 'a>>,
    >,
> {
    Deduction::<IsPair<'p, 'a, 'b>, Axiomize>::scope(|pab| {
        Deduction::<IsSingleton<'p, 'a>, _>::scope(|pa| {
            // `{a,b}` contains `b` ...
            let b_in_p = pab.upgrade().pipe(
                pair_member::<'a, 'b, 'b, 'p>(<Axiomize as Or>::or_right().mp(eq_refl_at::<'b>()))
                    .upgrade()
                    .upgrade(),
            );
            // ... and everything in `{a}` equals `a`.
            let to_a = pa
                .pipe(
                    <Axiomize as FirstOrder>::forall_elim::<'b, SingletonView<'p, 'a>>()
                        .upgrade()
                        .upgrade(),
                )
                .pipe(<Axiomize as And>::and_left().upgrade().upgrade());
            b_in_p.pipe(to_a)
        })
    })
}

/// `λa. ∀b ∀p. p = {a,b} → p = {a} → b = a`
pub type PairCollapsesView = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairCollapsesView1<'a>>>
    + 'static;
/// `λb. ∀p. p = {a,b} → p = {a} → b = a`
pub type PairCollapsesView1<'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairCollapsesView2<'a, 'b>>>
    + 'static;
/// `λp. p = {a,b} → p = {a} → b = a`
pub type PairCollapsesView2<'a, 'b> = dyn for<'p> View<
        'p,
        Output = pred!(
            { Axiomize },
            IsPair::<'p, 'a, 'b> >>= IsSingleton::<'p, 'a> >>= Eq::<'b, 'a>
        ),
    > + 'static;

/// `∀a ∀b ∀p. p = {a,b} → p = {a} → b = a` — **proved**.
///
/// A pair that is also a singleton had equal components all along. This is the
/// degenerate case the ordered-pair characterisation has to rule out
/// separately, and [`singleton_is_pair`] is its converse.
pub fn pair_collapses() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<PairCollapsesView>> {
    forall_intro(PairCollapses)
}

#[derive(Clone, Copy)]
struct PairCollapses;
impl<Q> Generalise<Axiomize, Q> for PairCollapses
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<PairCollapsesView1<'a>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, PairCollapsesView1<'a>, _>(PairCollapses1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairCollapses1<'a>(PhantomData<&'a ()>);
impl<'a, Q> Generalise<Axiomize, Q> for PairCollapses1<'a>
where
    Q: for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<PairCollapsesView2<'a, 'b>>>
        + ?Sized,
{
    fn prove<'b>(self) -> Cert<Axiomize, <Q as View<'b>>::Output> {
        forall_intro::<Axiomize, PairCollapsesView2<'a, 'b>, _>(PairCollapses2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct PairCollapses2<'a, 'b>(PhantomData<(&'a (), &'b ())>);
impl<'a, 'b, Q> Generalise<Axiomize, Q> for PairCollapses2<'a, 'b>
where
    Q: for<'p> View<
            'p,
            Output = pred!(
                { Axiomize },
                IsPair::<'p, 'a, 'b> >>= IsSingleton::<'p, 'a> >>= Eq::<'b, 'a>
            ),
        > + ?Sized,
{
    fn prove<'p>(self) -> Cert<Axiomize, <Q as View<'p>>::Output> {
        pair_collapses_at::<'a, 'b, 'p>()
    }
}

// ---------------------------------------------------------------------------
// Equals may be substituted for equals
// ---------------------------------------------------------------------------
//
// Two directions, and only one of them costs anything. `Eq` is *defined* as
// sharing members, so substituting on the right of `∈` is immediate. On the
// left it is not derivable at all — a set's members do not determine which sets
// contain it — and that is exactly what extensionality is assumed for.

/// `x = y → z ∈ x → z ∈ y`, at fixed points. Free from the definition of [`Eq`].
fn eq_in_right_at<'x, 'y, 'z>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<Eq<'x, 'y>, <Axiomize as Imply>::Imply<In<'z, 'x>, In<'z, 'y>>>,
> {
    syllogism()
        .mp(<Axiomize as FirstOrder>::forall_elim::<'z, EqView<'x, 'y>>())
        .mp(<Axiomize as And>::and_left())
}

/// `x = y → x ∈ w → y ∈ w`, at fixed points. This is [`crate::axiom::zfc::ext`]
/// with all three quantifiers eliminated.
fn eq_in_left_at<'x, 'y, 'w>() -> Cert<
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

/// `λx. ∀y ∀z. x = y → z ∈ x → z ∈ y`
pub type EqInRightView =
    dyn for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqInRightView1<'x>>> + 'static;
/// `λy. ∀z. x = y → z ∈ x → z ∈ y`
pub type EqInRightView1<'x> = dyn for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<EqInRightView2<'x, 'y>>>
    + 'static;
/// `λz. x = y → z ∈ x → z ∈ y`
pub type EqInRightView2<'x, 'y> = dyn for<'z> View<'z, Output = pred!({ Axiomize }, Eq::<'x, 'y> >>= In::<'z, 'x> >>= In::<'z, 'y>)>
    + 'static;

/// `∀x ∀y ∀z. x = y → z ∈ x → z ∈ y` — **proved**, no axiom.
///
/// Equal sets have the same members. That is what [`Eq`] *says*, so this is
/// really just the definition with its quantifier stripped; see
/// [`eq_in_left`] for the direction that is not free.
pub fn eq_in_right() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<EqInRightView>> {
    forall_intro(EqInRight)
}

#[derive(Clone, Copy)]
struct EqInRight;
impl<Q> Generalise<Axiomize, Q> for EqInRight
where
    Q: for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqInRightView1<'x>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Axiomize, <Q as View<'x>>::Output> {
        forall_intro::<Axiomize, EqInRightView1<'x>, _>(EqInRight1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqInRight1<'x>(PhantomData<&'x ()>);
impl<'x, Q> Generalise<Axiomize, Q> for EqInRight1<'x>
where
    Q: for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<EqInRightView2<'x, 'y>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Axiomize, <Q as View<'y>>::Output> {
        forall_intro::<Axiomize, EqInRightView2<'x, 'y>, _>(EqInRight2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqInRight2<'x, 'y>(PhantomData<(&'x (), &'y ())>);
impl<'x, 'y, Q> Generalise<Axiomize, Q> for EqInRight2<'x, 'y>
where
    Q: for<'z> View<
            'z,
            Output = pred!({ Axiomize }, Eq::<'x, 'y> >>= In::<'z, 'x> >>= In::<'z, 'y>),
        > + ?Sized,
{
    fn prove<'z>(self) -> Cert<Axiomize, <Q as View<'z>>::Output> {
        eq_in_right_at::<'x, 'y, 'z>()
    }
}

/// `λx. ∀y ∀w. x = y → x ∈ w → y ∈ w`
pub type EqInLeftView =
    dyn for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqInLeftView1<'x>>> + 'static;
/// `λy. ∀w. x = y → x ∈ w → y ∈ w`
pub type EqInLeftView1<'x> = dyn for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<EqInLeftView2<'x, 'y>>>
    + 'static;
/// `λw. x = y → x ∈ w → y ∈ w`
pub type EqInLeftView2<'x, 'y> = dyn for<'w> View<'w, Output = pred!({ Axiomize }, Eq::<'x, 'y> >>= In::<'x, 'w> >>= In::<'y, 'w>)>
    + 'static;

/// `∀x ∀y ∀w. x = y → x ∈ w → y ∈ w` — **proved from
/// [`crate::axiom::zfc::ext`]**.
///
/// The first theorem in this module that spends an axiom. Everything before it
/// followed from the definitions alone; this one cannot, because nothing about
/// a set's own members constrains which sets contain it.
pub fn eq_in_left() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<EqInLeftView>> {
    forall_intro(EqInLeft)
}

#[derive(Clone, Copy)]
struct EqInLeft;
impl<Q> Generalise<Axiomize, Q> for EqInLeft
where
    Q: for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<EqInLeftView1<'x>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Axiomize, <Q as View<'x>>::Output> {
        forall_intro::<Axiomize, EqInLeftView1<'x>, _>(EqInLeft1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqInLeft1<'x>(PhantomData<&'x ()>);
impl<'x, Q> Generalise<Axiomize, Q> for EqInLeft1<'x>
where
    Q: for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<EqInLeftView2<'x, 'y>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Axiomize, <Q as View<'y>>::Output> {
        forall_intro::<Axiomize, EqInLeftView2<'x, 'y>, _>(EqInLeft2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct EqInLeft2<'x, 'y>(PhantomData<(&'x (), &'y ())>);
impl<'x, 'y, Q> Generalise<Axiomize, Q> for EqInLeft2<'x, 'y>
where
    Q: for<'w> View<
            'w,
            Output = pred!({ Axiomize }, Eq::<'x, 'y> >>= In::<'x, 'w> >>= In::<'y, 'w>),
        > + ?Sized,
{
    fn prove<'w>(self) -> Cert<Axiomize, <Q as View<'w>>::Output> {
        eq_in_left_at::<'x, 'y, 'w>()
    }
}

// ---------------------------------------------------------------------------
// Functions
// ---------------------------------------------------------------------------
//
// A function here is not a type-level mapping but an ordinary element: its
// graph, a set of Kuratowski pairs. That is the whole point of reifying it —
// `'f` can be quantified over, so "there exists a function such that ..." is a
// first-order statement rather than a schema.
//
// These are the elimination rules. They unpack [`IsFunction`] and say nothing
// about which functions exist; that needs the axioms and comes later.

/// `IsFunction(f) → f is single-valued`, at a fixed `'f`.
fn func_single_valued_at<'f>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<IsFunction<'f>, IsSingleValued<'f>>> {
    <Axiomize as And>::and_right()
}

/// `IsFunction(f) → IsRelation(f)`, at a fixed `'f`.
fn func_is_relation_at<'f>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<IsFunction<'f>, IsRelation<'f>>> {
    <Axiomize as And>::and_left()
}

/// `IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`, at fixed points.
fn func_apply_unique_at<'f, 'a, 'b, 'c>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<
        IsFunction<'f>,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<Applies<'f, 'a, 'b>, Applies<'f, 'a, 'c>>,
            Eq<'b, 'c>,
        >,
    >,
> {
    syllogism().mp(func_single_valued_at::<'f>()).mp(syllogism()
        .mp(<Axiomize as FirstOrder>::forall_elim::<
            'a,
            SingleValuedView<'f>,
        >())
        .mp(syllogism()
            .mp(<Axiomize as FirstOrder>::forall_elim::<
                'b,
                SingleValuedView1<'f, 'a>,
            >())
            .mp(<Axiomize as FirstOrder>::forall_elim::<
                'c,
                SingleValuedView2<'f, 'a, 'b>,
            >())))
}

/// `f(a) = b → a ∈ dom f`, at fixed points.
fn applies_in_domain_at<'f, 'a, 'b>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<Applies<'f, 'a, 'b>, InDomain<'f, 'a>>> {
    <Axiomize as FirstOrder>::exists_elim::<'b, InDomainView<'f, 'a>, InDomain<'f, 'a>>()
}

/// `λf. IsFunction(f) → IsSingleValued(f)`
pub type FuncSingleValuedView = dyn for<'f> View<'f, Output = pred!({ Axiomize }, IsFunction::<'f> >>= IsSingleValued::<'f>)>
    + 'static;

/// `∀f. IsFunction(f) → f is single-valued` — **proved**.
pub fn func_single_valued() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<FuncSingleValuedView>>
{
    forall_intro(FuncSingleValued)
}

#[derive(Clone, Copy)]
struct FuncSingleValued;
impl<Q> Generalise<Axiomize, Q> for FuncSingleValued
where
    Q: for<'f> View<'f, Output = pred!({ Axiomize }, IsFunction::<'f> >>= IsSingleValued::<'f>)>
        + ?Sized,
{
    fn prove<'f>(self) -> Cert<Axiomize, <Q as View<'f>>::Output> {
        func_single_valued_at::<'f>()
    }
}

/// `λf. IsFunction(f) → IsRelation(f)`
pub type FuncIsRelationView = dyn for<'f> View<'f, Output = pred!({ Axiomize }, IsFunction::<'f> >>= IsRelation::<'f>)>
    + 'static;

/// `∀f. IsFunction(f) → IsRelation(f)` — **proved**.
///
/// Every function is a set of ordered pairs, so anything proved about relations
/// applies to it.
pub fn func_is_relation() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<FuncIsRelationView>> {
    forall_intro(FuncIsRelation)
}

#[derive(Clone, Copy)]
struct FuncIsRelation;
impl<Q> Generalise<Axiomize, Q> for FuncIsRelation
where
    Q: for<'f> View<'f, Output = pred!({ Axiomize }, IsFunction::<'f> >>= IsRelation::<'f>)>
        + ?Sized,
{
    fn prove<'f>(self) -> Cert<Axiomize, <Q as View<'f>>::Output> {
        func_is_relation_at::<'f>()
    }
}

/// `λf. ∀a ∀b ∀c. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`
pub type FuncApplyUniqueView = dyn for<'f> View<'f, Output = <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView1<'f>>>
    + 'static;
/// `λa. ∀b ∀c. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`
pub type FuncApplyUniqueView1<'f> = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView2<'f, 'a>>>
    + 'static;
/// `λb. ∀c. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`
pub type FuncApplyUniqueView2<'f, 'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView3<'f, 'a, 'b>>>
    + 'static;
/// `λc. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`
pub type FuncApplyUniqueView3<'f, 'a, 'b> = dyn for<'c> View<
        'c,
        Output = pred!(
            { Axiomize },
            IsFunction::<'f> >>=
                ((Applies::<'f, 'a, 'b>) && (Applies::<'f, 'a, 'c>)) >>= Eq::<'b, 'c>
        ),
    > + 'static;

/// `∀f ∀a ∀b ∀c. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c` — **proved**.
///
/// A function has at most one value at each argument. This is the defining
/// property unpacked into usable form: [`IsFunction`] states it behind three
/// quantifiers, and this is that statement with them eliminated.
pub fn func_apply_unique() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView>>
{
    forall_intro(FuncApplyUnique)
}

#[derive(Clone, Copy)]
struct FuncApplyUnique;
impl<Q> Generalise<Axiomize, Q> for FuncApplyUnique
where
    Q: for<'f> View<'f, Output = <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView1<'f>>>
        + ?Sized,
{
    fn prove<'f>(self) -> Cert<Axiomize, <Q as View<'f>>::Output> {
        forall_intro::<Axiomize, FuncApplyUniqueView1<'f>, _>(FuncApplyUnique1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct FuncApplyUnique1<'f>(PhantomData<&'f ()>);
impl<'f, Q> Generalise<Axiomize, Q> for FuncApplyUnique1<'f>
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView2<'f, 'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, FuncApplyUniqueView2<'f, 'a>, _>(FuncApplyUnique2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct FuncApplyUnique2<'f, 'a>(PhantomData<(&'f (), &'a ())>);
impl<'f, 'a, Q> Generalise<Axiomize, Q> for FuncApplyUnique2<'f, 'a>
where
    Q: for<'b> View<
            'b,
            Output = <Axiomize as FirstOrder>::ForAll<FuncApplyUniqueView3<'f, 'a, 'b>>,
        > + ?Sized,
{
    fn prove<'b>(self) -> Cert<Axiomize, <Q as View<'b>>::Output> {
        forall_intro::<Axiomize, FuncApplyUniqueView3<'f, 'a, 'b>, _>(FuncApplyUnique3(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct FuncApplyUnique3<'f, 'a, 'b>(PhantomData<(&'f (), &'a (), &'b ())>);
impl<'f, 'a, 'b, Q> Generalise<Axiomize, Q> for FuncApplyUnique3<'f, 'a, 'b>
where
    Q: for<'c> View<
            'c,
            Output = pred!(
                { Axiomize },
                IsFunction::<'f> >>=
                    ((Applies::<'f, 'a, 'b>) && (Applies::<'f, 'a, 'c>)) >>= Eq::<'b, 'c>
            ),
        > + ?Sized,
{
    fn prove<'c>(self) -> Cert<Axiomize, <Q as View<'c>>::Output> {
        func_apply_unique_at::<'f, 'a, 'b, 'c>()
    }
}

/// `λf. ∀a ∀b. f(a) = b → a ∈ dom f`
pub type AppliesInDomainView = dyn for<'f> View<'f, Output = <Axiomize as FirstOrder>::ForAll<AppliesInDomainView1<'f>>>
    + 'static;
/// `λa. ∀b. f(a) = b → a ∈ dom f`
pub type AppliesInDomainView1<'f> = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<AppliesInDomainView2<'f, 'a>>>
    + 'static;
/// `λb. f(a) = b → a ∈ dom f`
pub type AppliesInDomainView2<'f, 'a> = dyn for<'b> View<'b, Output = pred!({ Axiomize }, Applies::<'f, 'a, 'b> >>= InDomain::<'f, 'a>)>
    + 'static;

/// `∀f ∀a ∀b. f(a) = b → a ∈ dom f` — **proved**.
///
/// Anything a function maps somewhere is in its domain. The witness for the
/// existential is the value itself, so this is [`FirstOrder::exists_elim`] and
/// nothing more.
pub fn applies_in_domain() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<AppliesInDomainView>>
{
    forall_intro(AppliesInDomain)
}

#[derive(Clone, Copy)]
struct AppliesInDomain;
impl<Q> Generalise<Axiomize, Q> for AppliesInDomain
where
    Q: for<'f> View<'f, Output = <Axiomize as FirstOrder>::ForAll<AppliesInDomainView1<'f>>>
        + ?Sized,
{
    fn prove<'f>(self) -> Cert<Axiomize, <Q as View<'f>>::Output> {
        forall_intro::<Axiomize, AppliesInDomainView1<'f>, _>(AppliesInDomain1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct AppliesInDomain1<'f>(PhantomData<&'f ()>);
impl<'f, Q> Generalise<Axiomize, Q> for AppliesInDomain1<'f>
where
    Q: for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<AppliesInDomainView2<'f, 'a>>>
        + ?Sized,
{
    fn prove<'a>(self) -> Cert<Axiomize, <Q as View<'a>>::Output> {
        forall_intro::<Axiomize, AppliesInDomainView2<'f, 'a>, _>(AppliesInDomain2(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct AppliesInDomain2<'f, 'a>(PhantomData<(&'f (), &'a ())>);
impl<'f, 'a, Q> Generalise<Axiomize, Q> for AppliesInDomain2<'f, 'a>
where
    Q: for<'b> View<'b, Output = pred!({ Axiomize }, Applies::<'f, 'a, 'b> >>= InDomain::<'f, 'a>)>
        + ?Sized,
{
    fn prove<'b>(self) -> Cert<Axiomize, <Q as View<'b>>::Output> {
        applies_in_domain_at::<'f, 'a, 'b>()
    }
}

/// Typecheck witnesses: `cargo check` is the proof checker.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
const _: () = {
    use crate::axiom::zfc::{
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
        let _ = eq_trans();
        let _ = pair_unique();
        let _ = pair_left();
        let _ = pair_right();
        let _ = singleton_member();
        let _ = singleton_unique();
        let _ = singleton_is_pair();
        let _ = pair_is_singleton();
        let _ = singleton_injective();
        let _ = pair_collapses();
        let _ = eq_in_right();
    }

    /// The function elimination rules.
    fn functions_can_be_unpacked() {
        let _ = func_single_valued();
        let _ = func_is_relation();
        let _ = func_apply_unique();
        let _ = applies_in_domain();
    }

    /// Splitting [`IsSingleValued`] out of [`IsFunction`] must leave the
    /// proposition unchanged.
    fn is_function_is_the_definition<'f>(
        f: Cert<
            Axiomize,
            pred!(
                { Axiomize },
                (IsRelation::<'f>)
                    && (ForAll::<'x, 'y, 'z>(
                        ((Applies::<'f, 'x, 'y>) && (Applies::<'f, 'x, 'z>)).imply(Eq::<'y, 'z>)
                    ))
            ),
        >,
    ) -> Cert<Axiomize, IsFunction<'f>> {
        f
    }

    /// Likewise for naming [`InDomain`]'s body as [`InDomainView`].
    fn in_domain_is_the_definition<'f, 'q>(
        d: Cert<Axiomize, pred!({ Axiomize }, Exists::<'b>(Applies::<'f, 'q, 'b>))>,
    ) -> Cert<Axiomize, InDomain<'f, 'q>> {
        d
    }

    /// The one theorem so far that spends an axiom.
    fn congruence_needs_extensionality() {
        let _ = eq_in_left();
    }

    /// Restating [`crate::axiom::zfc::ext`] against [`ExtView`] must not have
    /// changed what it asserts, so the named form and the original inline
    /// spelling have to be the same proposition.
    fn ext_view_is_the_statement(
        c: Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<ExtView>>,
    ) -> Cert<
        Axiomize,
        pred!(
            { Axiomize },
            ForAll::<'x, 'y>((Eq::<'x, 'y>).imply(ForAll::<'w>((In::<'x, 'w>).iff(In::<'y, 'w>))))
        ),
    > {
        c
    }

    /// [`IsSingleton`] is still the proposition its doc comment claims: naming
    /// the body as [`SingletonView`] must not have changed the statement, so
    /// the two spellings have to be the same type.
    fn singleton_view_is_the_definition<'s, 'a>(
        c: Cert<Axiomize, pred!({ Axiomize }, ForAll::<'z>((In::<'z, 's>).iff(Eq::<'z, 'a>)))>,
    ) -> Cert<Axiomize, IsSingleton<'s, 'a>> {
        c
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
