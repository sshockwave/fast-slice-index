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
    And, Cert, Deduction, DeductionUpgrade, FirstOrder, ForAllProof, Generalise, Iff, Imply, Or,
    PropLogic, View, curry, forall_intro, reflexive, syllogism,
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
/// Together with [`crate::logic::axiom::zfc::pairing`] this pins the pair down:
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
        let _ = eq_trans();
        let _ = pair_unique();
        let _ = pair_left();
        let _ = pair_right();
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
