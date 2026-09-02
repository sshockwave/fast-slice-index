//! Everything derived from the axioms.
//!
//! `unsafe` is *forbidden* here, not merely denied: no edit to this module can
//! locally re-enable it, so every certificate below is either an axiom imported
//! from [`super::axioms`] or a derivation from one. That is the whole point of
//! the three-file split — the trusted base is [`super::base`] plus
//! [`super::axioms`], and it can be audited by reading two short files.
#![forbid(unsafe_code)]
#![expect(
    unused_parens,
    reason = "`pred!` parses its body as an expression, so operands are \
              parenthesised for grouping; the parens survive into the type"
)]

use ::core::marker::PhantomData;

use super::Axiomize;
use super::equality::{SetEq, SetIn};
use super::lang::*;
use crate::logic::prop::{
    And, Cert, Deduction, DeductionUpgrade, ExistsProof, FirstOrder, ForAllProof, Generalise, Iff,
    Imply, Or, PropLogic, View, and_comm, curry, exchange, forall_intro, or_idem, syllogism,
};
use crate::rel::desc::{
    DescUniqueView, DescUniqueView1, SameAs, desc_congr_at, desc_elim_at, desc_intro_at,
    desc_unique,
};
use crate::rel::empty::{
    EmptyUniqueView as GenEmptyUniqueView, EmptyUniqueView1 as GenEmptyUniqueView1,
    IsEmpty as GenIsEmpty, empty_unique as gen_empty_unique,
};
use crate::rel::eq::ClosedEq;
use crate::rel::ext::{ExtReflView, Extensional, in_left, in_right};
use crate::macros::pred;

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
///
/// Once `a` and `b` are fixed, `{a,b}` is just *the* set satisfying a
/// condition, so this is [`crate::rel::desc`]'s view at [`PairCond`].
pub type PairUniqueView2<'a, 'b> = DescUniqueView1<Axiomize, SetIn, PairCond<'a, 'b>>;

/// `∀a ∀b ∀p ∀q. p = {a,b} → q = {a,b} → p = q` — **proved**.
///
/// Together with [`super::axioms::pairing`] this pins the pair down:
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
        desc_unique::<Axiomize, SetIn, PairCond<'a, 'b>>()
    }
}

// ---------------------------------------------------------------------------
// What a pair contains
// ---------------------------------------------------------------------------

/// `x = x` at one particular `'x`, for use inside a proof.
///
/// Reflexivity itself is not proved here any more: it holds of the equality
/// *any* membership relation induces, so it lives in [`crate::rel::ext`] and
/// [`SetEq`] is the instance at [`In`].
fn eq_refl_at<'x>() -> Cert<Axiomize, Eq<'x, 'x>> {
    <SetEq as ClosedEq<Axiomize>>::refl()
        .pipe(<Axiomize as FirstOrder>::forall_elim::<'x, ExtReflView<Axiomize, SetIn>>())
}

/// `p = {a,b} → c ∈ p`, given that `c` is one of `a`, `b`.
///
/// The shared core of [`pair_left`] and [`pair_right`]: read the pair's
/// defining biconditional right-to-left at `'c`.
fn pair_member<'a, 'b, 'c, 'p>(
    side: Cert<Axiomize, <Axiomize as Or>::Or<Eq<'c, 'a>, Eq<'c, 'b>>>,
) -> Cert<Axiomize, <Axiomize as Imply>::Imply<IsPair<'p, 'a, 'b>, In<'c, 'p>>> {
    desc_intro_at::<'p, 'c, Axiomize, SetIn, PairCond<'a, 'b>>(side)
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
    desc_intro_at::<'s, 'a, Axiomize, SetIn, SingletonCond<'a>>(eq_refl_at::<'a>())
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
///
/// With `a` fixed, `{a}` is *the* set satisfying `z = a`, so this is
/// [`crate::rel::desc`]'s view at [`SingletonCond`].
pub type SingletonUniqueView1<'a> = DescUniqueView1<Axiomize, SetIn, SingletonCond<'a>>;

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
        desc_unique::<Axiomize, SetIn, SingletonCond<'a>>()
    }
}

// ---------------------------------------------------------------------------
// A singleton is a pair of one thing with itself
// ---------------------------------------------------------------------------
//
// The two directions are the same lemma — [`desc_congr_at`] — read each way.
// All that is specific to singletons and pairs is that `z = a` and `z = a ∨
// z = a` hold of the same things, which is `or_idem`.

impl<'a> SameAs<Axiomize, PairCond<'a, 'a>> for SingletonCond<'a> {
    fn iff_at<'z>() -> Cert<
        Axiomize,
        Iff<Axiomize, Eq<'z, 'a>, pred!({ Axiomize }, (Eq::<'z, 'a>) || (Eq::<'z, 'a>))>,
    > {
        or_idem::<Eq<'z, 'a>, Axiomize>()
    }
}

impl<'a> SameAs<Axiomize, SingletonCond<'a>> for PairCond<'a, 'a> {
    fn iff_at<'z>() -> Cert<
        Axiomize,
        Iff<Axiomize, pred!({ Axiomize }, (Eq::<'z, 'a>) || (Eq::<'z, 'a>)), Eq<'z, 'a>>,
    > {
        and_comm().mp(or_idem::<Eq<'z, 'a>, Axiomize>())
    }
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
        desc_congr_at::<'s, Axiomize, SetIn, SingletonCond<'a>, PairCond<'a, 'a>>()
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
        desc_congr_at::<'s, Axiomize, SetIn, PairCond<'a, 'a>, SingletonCond<'a>>()
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
            let to_c = sc.pipe(
                desc_elim_at::<'s, 'a, Axiomize, SetIn, SingletonCond<'c>>()
                    .upgrade()
                    .upgrade(),
            );
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
            let to_a = pa.pipe(
                desc_elim_at::<'p, 'b, Axiomize, SetIn, SingletonCond<'a>>()
                    .upgrade()
                    .upgrade(),
            );
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
//
// Both are proved generically in [`crate::rel::ext`], of an arbitrary
// membership relation; what is left here is the instantiation at [`In`], plus
// the axiom that discharges [`Extensional`] (in [`super::equality`]).

/// `x = y → x ∈ w → y ∈ w`, at fixed points. This is [`super::axioms::ext`]
/// with all three quantifiers eliminated.
fn eq_in_left_at<'x, 'y, 'w>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<Eq<'x, 'y>, <Axiomize as Imply>::Imply<In<'x, 'w>, In<'y, 'w>>>,
> {
    <SetIn as Extensional<Axiomize>>::in_left_at::<'x, 'y, 'w>()
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

// ---------------------------------------------------------------------------
// The empty set and the successor are unique
// ---------------------------------------------------------------------------
//
// `infinity` asserts that *some* set contains an empty set and is closed under
// the successor, but names neither. Going from "there is such a set" to "it is
// *the* set" needs the description to determine its subject — which it does,
// for the same reason pairs are unique: `Eq` is sharing members, and both sides
// are pinned to the same membership condition. No axiom is spent here either.

/// `λx. ∀y. IsEmpty(x) → IsEmpty(y) → x = y`
pub type EmptyUniqueView = GenEmptyUniqueView1<Axiomize, SetIn>;
/// `λy. IsEmpty(x) → IsEmpty(y) → x = y`
pub type EmptyUniqueView1<'x> = GenEmptyUniqueView<'x, Axiomize, SetIn>;

/// `∀x ∀y. IsEmpty(x) → IsEmpty(y) → x = y` — **proved**.
///
/// There is at most one empty set. Both directions of the biconditional hold
/// vacuously: neither side has a member to disagree about. Nothing about sets
/// enters, so the argument is [`crate::rel::empty`]'s.
pub fn empty_unique() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<EmptyUniqueView>> {
    gen_empty_unique::<Axiomize, SetIn>()
}

/// `λy. ∀s ∀t. s = y ∪ {y} → t = y ∪ {y} → s = t`
pub type SuccUniqueView =
    dyn for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<SuccUniqueView1<'y>>> + 'static;
/// `λs. ∀t. s = y ∪ {y} → t = y ∪ {y} → s = t`
///
/// With `y` fixed, the successor is *the* set satisfying `w ∈ y ∨ w = y`, so
/// this is [`crate::rel::desc`]'s view at [`SuccCond`].
pub type SuccUniqueView1<'y> = DescUniqueView1<Axiomize, SetIn, SuccCond<'y>>;

/// `∀y ∀s ∀t. IsSuccOf(s, y) → IsSuccOf(t, y) → s = t` — **proved**.
///
/// Each set has at most one successor. With [`super::axioms::infinity`]
/// supplying existence, this is what lets a successor be spoken of as *the*
/// successor.
pub fn succ_unique() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SuccUniqueView>> {
    forall_intro(SuccUnique)
}

#[derive(Clone, Copy)]
struct SuccUnique;
impl<Q> Generalise<Axiomize, Q> for SuccUnique
where
    Q: for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<SuccUniqueView1<'y>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Axiomize, <Q as View<'y>>::Output> {
        desc_unique::<Axiomize, SetIn, SuccCond<'y>>()
    }
}

// ---------------------------------------------------------------------------
// Zero and successor are natural numbers
// ---------------------------------------------------------------------------
//
// [`IsNat`] says "belongs to every inductive set", so proving something is a
// natural number means producing it inside an arbitrary inductive `i`. The
// inductive set only promises *some* empty set and *some* successor, never the
// one we are holding — which is what [`empty_unique`] and [`succ_unique`] are
// for. Extensionality then carries membership across that identification.

/// `IsEmpty(x) → IsEmpty(y) → x = y`, at fixed points.
fn empty_unique_at<'x, 'y>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<IsEmpty<'x>, <Axiomize as Imply>::Imply<IsEmpty<'y>, Eq<'x, 'y>>>,
> {
    empty_unique()
        .pipe(<Axiomize as FirstOrder>::forall_elim::<'x, EmptyUniqueView>())
        .pipe(<Axiomize as FirstOrder>::forall_elim::<
            'y,
            EmptyUniqueView1<'x>,
        >())
}

/// `IsSuccOf(s, y) → IsSuccOf(t, y) → s = t`, at fixed points.
fn succ_unique_at<'y, 's, 't>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<
        IsSuccOf<'s, 'y>,
        <Axiomize as Imply>::Imply<IsSuccOf<'t, 'y>, Eq<'s, 't>>,
    >,
> {
    succ_unique()
        .pipe(<Axiomize as FirstOrder>::forall_elim::<'y, SuccUniqueView>())
        .pipe(<Axiomize as FirstOrder>::forall_elim::<
            's,
            SuccUniqueView1<'y>,
        >())
        .pipe(<Axiomize as FirstOrder>::forall_elim::<
            't,
            DescUniqueView<'s, Axiomize, SetIn, SuccCond<'y>>,
        >())
}

/// `λe. IsEmpty(e) → IsNat(e)`
pub type ZeroIsNatView =
    dyn for<'e> View<'e, Output = <Axiomize as Imply>::Imply<IsEmpty<'e>, IsNat<'e>>> + 'static;

/// `∀e. IsEmpty(e) → IsNat(e)` — **proved**.
///
/// Zero is a natural number. Every inductive set contains an empty set, and
/// there is only one empty set to contain.
pub fn zero_is_nat() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<ZeroIsNatView>> {
    forall_intro(ZeroIsNat)
}

#[derive(Clone, Copy)]
struct ZeroIsNat;
impl<Q> Generalise<Axiomize, Q> for ZeroIsNat
where
    Q: for<'e> View<'e, Output = <Axiomize as Imply>::Imply<IsEmpty<'e>, IsNat<'e>>> + ?Sized,
{
    fn prove<'e>(self) -> Cert<Axiomize, <Q as View<'e>>::Output> {
        <Axiomize as FirstOrder>::forall_gen(ZeroIsNat1::<'e>(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct ZeroIsNat1<'e>(PhantomData<&'e ()>);
impl<'e, Q> ForAllProof<Axiomize, IsEmpty<'e>, Q> for ZeroIsNat1<'e>
where
    Q: for<'i> View<'i, Output = <Axiomize as Imply>::Imply<IsInductive<'i>, In<'e, 'i>>> + ?Sized,
{
    fn prove<'i>(
        self,
    ) -> Cert<Axiomize, <Axiomize as Imply>::Imply<IsEmpty<'e>, <Q as View<'i>>::Output>> {
        // Inductive(i) ⊢ HasEmpty(i) ⊢ (IsEmpty(e) → e ∈ i); exchange puts the
        // hypothesis back on the outside.
        exchange().mp(syllogism().mp(<Axiomize as And>::and_left()).mp(
            <Axiomize as FirstOrder>::exists_gen(ZeroIsNat2::<'e, 'i>(PhantomData)),
        ))
    }
}

#[derive(Clone, Copy)]
struct ZeroIsNat2<'e, 'i>(PhantomData<(&'e (), &'i ())>);
impl<'e, 'i>
    ExistsProof<Axiomize, HasEmptyView<'i>, <Axiomize as Imply>::Imply<IsEmpty<'e>, In<'e, 'i>>>
    for ZeroIsNat2<'e, 'i>
{
    fn prove<'t>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <HasEmptyView<'i> as View<'t>>::Output,
            <Axiomize as Imply>::Imply<IsEmpty<'e>, In<'e, 'i>>,
        >,
    > {
        let h =
            Deduction::<pred!({ Axiomize }, (In::<'t, 'i>) && (IsEmpty::<'t>)), Axiomize>::assume();
        let t_in_i = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
        let t_empty = h.pipe(<Axiomize as And>::and_right().upgrade());
        // t and e are both empty, so t = e; and t ∈ i, so e ∈ i.
        let to_eq = t_empty.pipe(empty_unique_at::<'t, 'e>().upgrade());
        let eq_to_in = t_in_i.pipe(exchange().mp(eq_in_left_at::<'t, 'e, 'i>()).upgrade());
        syllogism().upgrade().mp(to_eq).mp(eq_to_in).cast()
    }
}

/// `λy. ∀s. IsNat(y) → IsSuccOf(s, y) → IsNat(s)`
pub type SuccIsNatView =
    dyn for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<SuccIsNatView1<'y>>> + 'static;
/// `λs. IsNat(y) → IsSuccOf(s, y) → IsNat(s)`
pub type SuccIsNatView1<'y> = dyn for<'s> View<
        's,
        Output = pred!(
            { Axiomize },
            IsNat::<'y> >>= IsSuccOf::<'s, 'y> >>= IsNat::<'s>
        ),
    > + 'static;

/// `∀y ∀s. IsNat(y) → IsSuccOf(s, y) → IsNat(s)` — **proved**.
///
/// The naturals are closed under the successor. With [`zero_is_nat`] this is
/// the introduction half of arithmetic; induction, the elimination half, needs
/// ω to exist and so needs [`super::axioms::separation`].
pub fn succ_is_nat() -> Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SuccIsNatView>> {
    forall_intro(SuccIsNat)
}

#[derive(Clone, Copy)]
struct SuccIsNat;
impl<Q> Generalise<Axiomize, Q> for SuccIsNat
where
    Q: for<'y> View<'y, Output = <Axiomize as FirstOrder>::ForAll<SuccIsNatView1<'y>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Axiomize, <Q as View<'y>>::Output> {
        forall_intro::<Axiomize, SuccIsNatView1<'y>, _>(SuccIsNat1(PhantomData))
    }
}

#[derive(Clone, Copy)]
struct SuccIsNat1<'y>(PhantomData<&'y ()>);
impl<'y, Q> Generalise<Axiomize, Q> for SuccIsNat1<'y>
where
    Q: for<'s> View<
            's,
            Output = pred!(
                { Axiomize },
                IsNat::<'y> >>= IsSuccOf::<'s, 'y> >>= IsNat::<'s>
            ),
        > + ?Sized,
{
    fn prove<'s>(self) -> Cert<Axiomize, <Q as View<'s>>::Output> {
        curry().mp(<Axiomize as FirstOrder>::forall_gen(SuccIsNat2::<'y, 's>(
            PhantomData,
        )))
    }
}

#[derive(Clone, Copy)]
struct SuccIsNat2<'y, 's>(PhantomData<(&'y (), &'s ())>);
impl<'y, 's, Q> ForAllProof<Axiomize, <Axiomize as And>::And<IsNat<'y>, IsSuccOf<'s, 'y>>, Q>
    for SuccIsNat2<'y, 's>
where
    Q: for<'i> View<'i, Output = <Axiomize as Imply>::Imply<IsInductive<'i>, In<'s, 'i>>> + ?Sized,
{
    fn prove<'i>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<IsNat<'y>, IsSuccOf<'s, 'y>>,
            <Q as View<'i>>::Output,
        >,
    > {
        let h =
            Deduction::<<Axiomize as And>::And<IsNat<'y>, IsSuccOf<'s, 'y>>, Axiomize>::assume();
        let nat_y = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
        let succ_s = h.pipe(<Axiomize as And>::and_right().upgrade());
        // Inductive(i) → y ∈ i, from the hypothesis that y is a natural number.
        let y_in =
            nat_y.pipe(<Axiomize as FirstOrder>::forall_elim::<'i, IsNatView<'y>>().upgrade());
        // Inductive(i) → (y ∈ i → some successor of y is in i).
        let closed = syllogism().mp(<Axiomize as And>::and_right()).mp(
            <Axiomize as FirstOrder>::forall_elim::<'y, ClosedUnderSuccView<'i>>(),
        );
        // Distribute to drop the y ∈ i premise, then read the witness back out.
        let step = <Axiomize as PropLogic>::l2()
            .upgrade()
            .mp(closed.upgrade())
            .mp(y_in);
        let unpack = <Axiomize as FirstOrder>::exists_gen(SuccIsNat3::<'y, 's, 'i>(PhantomData));
        succ_s
            .pipe(
                exchange()
                    .upgrade()
                    .mp(syllogism().upgrade().mp(step).mp(unpack.upgrade())),
            )
            .cast()
    }
}

#[derive(Clone, Copy)]
struct SuccIsNat3<'y, 's, 'i>(PhantomData<(&'y (), &'s (), &'i ())>);
impl<'y, 's, 'i>
    ExistsProof<
        Axiomize,
        SuccStepView<'i, 'y>,
        <Axiomize as Imply>::Imply<IsSuccOf<'s, 'y>, In<'s, 'i>>,
    > for SuccIsNat3<'y, 's, 'i>
{
    fn prove<'t>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <SuccStepView<'i, 'y> as View<'t>>::Output,
            <Axiomize as Imply>::Imply<IsSuccOf<'s, 'y>, In<'s, 'i>>,
        >,
    > {
        let h =
            Deduction::<pred!({ Axiomize }, (In::<'t, 'i>) && (IsSuccOf::<'t, 'y>)), Axiomize>::assume();
        let t_in_i = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
        let t_succ = h.pipe(<Axiomize as And>::and_right().upgrade());
        // t and s are both successors of y, so t = s; and t ∈ i, so s ∈ i.
        let to_eq = t_succ.pipe(succ_unique_at::<'y, 't, 's>().upgrade());
        let eq_to_in = t_in_i.pipe(exchange().mp(eq_in_left_at::<'t, 's, 'i>()).upgrade());
        syllogism().upgrade().mp(to_eq).mp(eq_to_in).cast()
    }
}

// ---------------------------------------------------------------------------
// Induction
// ---------------------------------------------------------------------------
//
// The elimination rule, and the first theorem here that needs more than one
// axiom. [`IsNat`] says a natural number lies in *every* inductive set, so to
// use it we must produce an inductive set of our own: separation carves
// `{z ∈ i : IsNat(z) ∧ P(z)}` out of the set [`super::axioms::infinity`]
// hands us, the base and step hypotheses are exactly what make that carving
// inductive, and `IsNat(n)` then puts `n` inside it.

/// `λe. IsEmpty(e) → P(e)` — the base case.
pub type BaseView<P> = dyn for<'e> View<'e, Output = pred!({ Axiomize }, IsEmpty::<'e> >>= (<P as View<'e>>::Output))>
    + 'static;
/// `NatBase(P) := ∀e. IsEmpty(e) → P(e)`
pub type NatBase<P> = <Axiomize as FirstOrder>::ForAll<BaseView<P>>;

/// `λt. IsSuccOf(t, k) → P(t)`
pub type StepConclView<'k, P> = dyn for<'t> View<
        't,
        Output = pred!(
            { Axiomize },
            IsSuccOf::<'t, 'k> >>= (<P as View<'t>>::Output)
        ),
    > + 'static;
/// `λk. P(k) → ∀t. IsSuccOf(t, k) → P(t)` — the step case.
pub type StepView<P> = dyn for<'k> View<
        'k,
        Output = <Axiomize as Imply>::Imply<
            <P as View<'k>>::Output,
            <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
        >,
    > + 'static;
/// `NatStep(P) := ∀k ∀t. P(k) → IsSuccOf(t, k) → P(t)`
///
/// The step has no `IsNat(k)` premise. That is what keeps `P` alone as the
/// separating predicate: adding one would force the carving to be by
/// `λz. IsNat(z) ∧ P(z)`, whose projection rustc cannot normalise under the
/// `for<'z>` binder while `P` is still a parameter. The stronger rule is
/// recovered by instantiating this one at that conjunction, which normalises
/// fine once `P` is concrete.
pub type NatStep<P> = <Axiomize as FirstOrder>::ForAll<StepView<P>>;

/// `λn. IsNat(n) → P(n)` — what induction concludes.
pub type InductionView<P> = dyn for<'n> View<'n, Output = pred!({ Axiomize }, IsNat::<'n> >>= (<P as View<'n>>::Output))>
    + 'static;
/// `NatInduction(P) := ∀n. IsNat(n) → P(n)` — the conclusion of induction.
pub type NatInduction<P> = <Axiomize as FirstOrder>::ForAll<InductionView<P>>;

/// Everything the carving argument needs, bundled so it can pass through
/// [`FirstOrder::forall_gen`], which admits a single hypothesis.
///
/// The three views are parameters rather than the concrete
/// [`SeparatedView`]/[`BaseView`]/[`StepView`] so that proof `impl`s can name
/// the bundle without naming a `dyn for<'z> View<'z, Output = ..<P as
/// View<'z>>::Output..>`. In an `impl` header rustc drops the bound-ness of
/// `'z` in such a projection and the header then fails to match itself; behind
/// an opaque parameter pinned by a `where`-clause the projection is never
/// written under a binder in header position. See [`InductionHyps`].
type Bundle<'i, S, B, T> = <Axiomize as And>::And<
    <Axiomize as And>::And<<Axiomize as FirstOrder>::ForAll<S>, IsInductive<'i>>,
    <Axiomize as And>::And<
        <Axiomize as FirstOrder>::ForAll<B>,
        <Axiomize as FirstOrder>::ForAll<T>,
    >,
>;

/// `s = {z ∈ i : IsNat(z) ∧ P(z)}` contains an empty set.
///
/// `i` has one, it is a natural number by [`zero_is_nat`], and the base
/// hypothesis says `P` holds of it — so it survives the carving.
fn separated_has_empty<'s, 'i, P, S, B, T>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, HasEmpty<'s>>>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'x> View<'x> + ?Sized,
{
    let h = Deduction::<Bundle<'i, S, B, T>, Axiomize>::assume();
    let empty_in_i = h
        .clone()
        .pipe(<Axiomize as And>::and_left().upgrade())
        .pipe(<Axiomize as And>::and_right().upgrade())
        .pipe(<Axiomize as And>::and_left().upgrade());
    empty_in_i
        .pipe(
            <Axiomize as FirstOrder>::exists_gen::<
                HasEmptyView<'i>,
                <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, HasEmpty<'s>>,
                _,
            >(SeparatedHasEmpty::<'i, P, HasEmptyView<'i>, S, B, T>(
                PhantomData,
                PhantomData,
                PhantomData,
            ))
            .upgrade(),
        )
        .mp(h)
        .cast()
}

// Every view here is generic and pinned by a `where`-clause rather than named
// directly. Two separate rustc limitations force it: `'e` occurs both at the
// top of `HasEmptyView` and inside `IsEmpty<'e>`, and a `dyn` binder cannot be
// used at two nesting depths in an `impl` header; and a projection
// `<P as View<'z>>::Output` written under a `dyn for<'z>` binder in an `impl`
// header loses the bound-ness of `'z`. Both are fine inside a `where`-clause.
struct SeparatedHasEmpty<'i, P: ?Sized, E: ?Sized, S: ?Sized, B: ?Sized, T: ?Sized>(
    PhantomData<&'i ()>,
    PhantomData<(*const P, *const E)>,
    PhantomData<(*const S, *const B, *const T)>,
);
impl<P: ?Sized, E: ?Sized, S: ?Sized, B: ?Sized, T: ?Sized> Clone
    for SeparatedHasEmpty<'_, P, E, S, B, T>
{
    fn clone(&self) -> Self {
        SeparatedHasEmpty(PhantomData, PhantomData, PhantomData)
    }
}
impl<'s, 'i, P, E, S, B, T>
    ExistsProof<Axiomize, E, <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, HasEmpty<'s>>>
    for SeparatedHasEmpty<'i, P, E, S, B, T>
where
    P: for<'x> View<'x> + ?Sized,
    E: for<'e> View<'e, Output = pred!({ Axiomize }, (In::<'e, 'i>) && (IsEmpty::<'e>))> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'x> View<'x> + ?Sized,
{
    fn prove<'e>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <E as View<'e>>::Output,
            <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, HasEmpty<'s>>,
        >,
    > {
        curry().mp({
            let h = Deduction::<
                <Axiomize as And>::And<
                    pred!({ Axiomize }, (In::<'e, 'i>) && (IsEmpty::<'e>)),
                    Bundle<'i, S, B, T>,
                >,
                Axiomize,
            >::assume();
            let elem = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let hyps = h.pipe(<Axiomize as And>::and_right().upgrade());
            let e_in_i = elem.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let e_empty = elem.pipe(<Axiomize as And>::and_right().upgrade());
            let sep = hyps
                .clone()
                .pipe(<Axiomize as And>::and_left().upgrade())
                .pipe(<Axiomize as And>::and_left().upgrade());
            let base = hyps
                .pipe(<Axiomize as And>::and_right().upgrade())
                .pipe(<Axiomize as And>::and_left().upgrade());
            // P(∅) from the base case, IsNat(∅) from `zero_is_nat`.
            let p_e = e_empty
                .clone()
                .pipe(base.pipe(<Axiomize as FirstOrder>::forall_elim::<'e, B>().upgrade()));
            let payload = <Axiomize as And>::and_intro().upgrade().mp(e_in_i).mp(p_e);
            // The carving condition holds of ∅, so ∅ ∈ s.
            let e_in_s = payload.pipe(
                sep.pipe(<Axiomize as FirstOrder>::forall_elim::<'e, S>().upgrade())
                    .pipe(<Axiomize as And>::and_right().upgrade()),
            );
            <Axiomize as And>::and_intro()
                .upgrade()
                .mp(e_in_s)
                .mp(e_empty)
                .pipe(
                    <Axiomize as FirstOrder>::exists_elim::<'e, HasEmptyView<'s>, HasEmpty<'s>>()
                        .upgrade(),
                )
                .cast()
        })
    }
}

/// `s = {z ∈ i : P(z)}` is closed under successor.
///
/// `y ∈ s` gives `y ∈ i` and `P(y)`; `i`'s own closure produces a successor `t`
/// of `y` inside `i`, and the step hypothesis carries `P` across to it — so `t`
/// survives the carving too.
fn separated_closed_under_succ<'s, 'i, P, S, B, T>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, ClosedUnderSucc<'s>>>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x> + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
{
    <Axiomize as FirstOrder>::forall_gen::<Bundle<'i, S, B, T>, ClosedUnderSuccView<'s>, _>(
        SeparatedClosed::<'s, 'i, P, S, B, T>(PhantomData, PhantomData, PhantomData),
    )
}

struct SeparatedClosed<'s, 'i, P: ?Sized, S: ?Sized, B: ?Sized, T: ?Sized>(
    PhantomData<(&'s (), &'i ())>,
    PhantomData<*const P>,
    PhantomData<(*const S, *const B, *const T)>,
);
impl<P: ?Sized, S: ?Sized, B: ?Sized, T: ?Sized> Clone for SeparatedClosed<'_, '_, P, S, B, T> {
    fn clone(&self) -> Self {
        SeparatedClosed(PhantomData, PhantomData, PhantomData)
    }
}
impl<'s, 'i, P, S, B, T, C> ForAllProof<Axiomize, Bundle<'i, S, B, T>, C>
    for SeparatedClosed<'s, 'i, P, S, B, T>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x> + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
    C: for<'y> View<
            'y,
            Output = <Axiomize as Imply>::Imply<
                In<'y, 's>,
                <Axiomize as FirstOrder>::Exists<SuccStepView<'s, 'y>>,
            >,
        > + ?Sized,
{
    fn prove<'y>(
        self,
    ) -> Cert<Axiomize, <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, <C as View<'y>>::Output>>
    {
        curry().mp({
            let h = Deduction::<
                <Axiomize as And>::And<Bundle<'i, S, B, T>, In<'y, 's>>,
                Axiomize,
            >::assume();
            let hyps = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let y_in_s = h.pipe(<Axiomize as And>::and_right().upgrade());
            let left = hyps.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let sep = left.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let ind = left.pipe(<Axiomize as And>::and_right().upgrade());
            let step_all = hyps
                .pipe(<Axiomize as And>::and_right().upgrade())
                .pipe(<Axiomize as And>::and_right().upgrade());
            // Reading the carving forwards: y ∈ s gives y ∈ i and P(y).
            let pair = y_in_s.pipe(
                sep.clone()
                    .pipe(<Axiomize as FirstOrder>::forall_elim::<'y, S>().upgrade())
                    .pipe(<Axiomize as And>::and_left().upgrade()),
            );
            let y_in_i = pair.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let p_y = pair.pipe(<Axiomize as And>::and_right().upgrade());
            // i is inductive, so some successor of y lies in i.
            let ex = y_in_i.pipe(ind.pipe(<Axiomize as And>::and_right().upgrade()).pipe(
                <Axiomize as FirstOrder>::forall_elim::<'y, ClosedUnderSuccView<'i>>().upgrade(),
            ));
            // The step hypothesis, fired at P(y): every successor of y has P.
            let p_step =
                p_y.pipe(step_all.pipe(<Axiomize as FirstOrder>::forall_elim::<'y, T>().upgrade()));
            let aux = <Axiomize as And>::and_intro().upgrade().mp(sep).mp(p_step);
            ex.pipe(
                <Axiomize as FirstOrder>::exists_gen(SeparatedClosedWitness::<
                    's,
                    'i,
                    'y,
                    P,
                    S,
                    StepConclView<'y, P>,
                >(PhantomData, PhantomData))
                .upgrade(),
            )
            .mp(aux)
            .cast()
        })
    }
}

/// What is left once the successor of `y` inside `i` has a name: it satisfies
/// `P`, so the carving keeps it.
struct SeparatedClosedWitness<'s, 'i, 'y, P: ?Sized, S: ?Sized, K: ?Sized>(
    PhantomData<(&'s (), &'i (), &'y ())>,
    PhantomData<(*const P, *const S, *const K)>,
);
impl<P: ?Sized, S: ?Sized, K: ?Sized> Clone for SeparatedClosedWitness<'_, '_, '_, P, S, K> {
    fn clone(&self) -> Self {
        SeparatedClosedWitness(PhantomData, PhantomData)
    }
}
impl<'s, 'i, 'y, P, S, K>
    ExistsProof<
        Axiomize,
        SuccStepView<'i, 'y>,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<
                <Axiomize as FirstOrder>::ForAll<S>,
                <Axiomize as FirstOrder>::ForAll<K>,
            >,
            <Axiomize as FirstOrder>::Exists<SuccStepView<'s, 'y>>,
        >,
    > for SeparatedClosedWitness<'s, 'i, 'y, P, S, K>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    K: for<'t> View<
            't,
            Output = <Axiomize as Imply>::Imply<IsSuccOf<'t, 'y>, <P as View<'t>>::Output>,
        > + ?Sized,
{
    fn prove<'t>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <SuccStepView<'i, 'y> as View<'t>>::Output,
            <Axiomize as Imply>::Imply<
                <Axiomize as And>::And<
                    <Axiomize as FirstOrder>::ForAll<S>,
                    <Axiomize as FirstOrder>::ForAll<K>,
                >,
                <Axiomize as FirstOrder>::Exists<SuccStepView<'s, 'y>>,
            >,
        >,
    > {
        curry().mp({
            let h = Deduction::<
                <Axiomize as And>::And<
                    pred!({ Axiomize }, (In::<'t, 'i>) && (IsSuccOf::<'t, 'y>)),
                    <Axiomize as And>::And<
                        <Axiomize as FirstOrder>::ForAll<S>,
                        <Axiomize as FirstOrder>::ForAll<K>,
                    >,
                >,
                Axiomize,
            >::assume();
            let elem = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let aux = h.pipe(<Axiomize as And>::and_right().upgrade());
            let t_in_i = elem.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let t_succ = elem.pipe(<Axiomize as And>::and_right().upgrade());
            let sep = aux.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let step = aux.pipe(<Axiomize as And>::and_right().upgrade());
            let p_t = t_succ
                .clone()
                .pipe(step.pipe(<Axiomize as FirstOrder>::forall_elim::<'t, K>().upgrade()));
            let payload = <Axiomize as And>::and_intro().upgrade().mp(t_in_i).mp(p_t);
            let t_in_s = payload.pipe(
                sep.pipe(<Axiomize as FirstOrder>::forall_elim::<'t, S>().upgrade())
                    .pipe(<Axiomize as And>::and_right().upgrade()),
            );
            <Axiomize as And>::and_intro()
                .upgrade()
                .mp(t_in_s)
                .mp(t_succ)
                .pipe(
                    <Axiomize as FirstOrder>::exists_elim::<
                        't,
                        SuccStepView<'s, 'y>,
                        <Axiomize as FirstOrder>::Exists<SuccStepView<'s, 'y>>,
                    >()
                    .upgrade(),
                )
                .cast()
        })
    }
}

/// The carved set is itself inductive.
fn separated_is_inductive<'s, 'i, P, S, B, T>()
-> Cert<Axiomize, <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, IsInductive<'s>>>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
{
    let h = Deduction::<Bundle<'i, S, B, T>, Axiomize>::assume();
    let empty = h
        .clone()
        .pipe(separated_has_empty::<'s, 'i, P, S, B, T>().upgrade());
    let closed = h.pipe(separated_closed_under_succ::<'s, 'i, P, S, B, T>().upgrade());
    <Axiomize as And>::and_intro()
        .upgrade()
        .mp(empty)
        .mp(closed)
        .cast()
}

/// Induction, at a fixed carving: `Hyps → ∀n. IsNat(n) → P(n)`.
///
/// `s` is inductive, so being a natural number — being in *every* inductive set
/// — puts `n` in `s`; and membership of `s` was carved to mean `P`.
fn induction_at<'s, 'i, P, S, B, T, N>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, <Axiomize as FirstOrder>::ForAll<N>>,
>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
    N: for<'n> View<'n, Output = <Axiomize as Imply>::Imply<IsNat<'n>, <P as View<'n>>::Output>>
        + ?Sized,
{
    <Axiomize as FirstOrder>::forall_gen::<Bundle<'i, S, B, T>, N, _>(InductionAt::<
        's,
        'i,
        P,
        S,
        B,
        T,
    >(
        PhantomData,
        PhantomData,
        PhantomData,
    ))
}

struct InductionAt<'s, 'i, P: ?Sized, S: ?Sized, B: ?Sized, T: ?Sized>(
    PhantomData<(&'s (), &'i ())>,
    PhantomData<*const P>,
    PhantomData<(*const S, *const B, *const T)>,
);
impl<P: ?Sized, S: ?Sized, B: ?Sized, T: ?Sized> Clone for InductionAt<'_, '_, P, S, B, T> {
    fn clone(&self) -> Self {
        InductionAt(PhantomData, PhantomData, PhantomData)
    }
}
impl<'s, 'i, P, S, B, T, N> ForAllProof<Axiomize, Bundle<'i, S, B, T>, N>
    for InductionAt<'s, 'i, P, S, B, T>
where
    P: for<'x> View<'x> + ?Sized,
    S: for<'z> View<
            'z,
            Output = Iff<
                Axiomize,
                In<'z, 's>,
                <Axiomize as And>::And<In<'z, 'i>, <P as View<'z>>::Output>,
            >,
        > + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
    N: for<'n> View<'n, Output = <Axiomize as Imply>::Imply<IsNat<'n>, <P as View<'n>>::Output>>
        + ?Sized,
{
    fn prove<'n>(
        self,
    ) -> Cert<Axiomize, <Axiomize as Imply>::Imply<Bundle<'i, S, B, T>, <N as View<'n>>::Output>>
    {
        curry().mp({
            let h = Deduction::<
                <Axiomize as And>::And<Bundle<'i, S, B, T>, IsNat<'n>>,
                Axiomize,
            >::assume();
            let hyps = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let nat_n = h.pipe(<Axiomize as And>::and_right().upgrade());
            let sep = hyps
                .clone()
                .pipe(<Axiomize as And>::and_left().upgrade())
                .pipe(<Axiomize as And>::and_left().upgrade());
            let s_ind = hyps.pipe(separated_is_inductive::<'s, 'i, P, S, B, T>().upgrade());
            // n is in every inductive set, and s is one.
            let n_in_s = s_ind.pipe(
                nat_n.pipe(<Axiomize as FirstOrder>::forall_elim::<'s, IsNatView<'n>>().upgrade()),
            );
            // Membership of s was carved to mean n ∈ i together with P(n).
            n_in_s
                .pipe(
                    sep.pipe(<Axiomize as FirstOrder>::forall_elim::<'n, S>().upgrade())
                        .pipe(<Axiomize as And>::and_left().upgrade()),
                )
                .pipe(<Axiomize as And>::and_right().upgrade())
                .cast()
        })
    }
}

/// Once the carved set has a name, induction is [`induction_at`] at it.
struct SeparationStep<'i, P: ?Sized, G: ?Sized, B: ?Sized, T: ?Sized, N: ?Sized>(
    PhantomData<&'i ()>,
    PhantomData<(*const P, *const G)>,
    PhantomData<(*const B, *const T, *const N)>,
);
impl<P: ?Sized, G: ?Sized, B: ?Sized, T: ?Sized, N: ?Sized> Clone
    for SeparationStep<'_, P, G, B, T, N>
{
    fn clone(&self) -> Self {
        SeparationStep(PhantomData, PhantomData, PhantomData)
    }
}
impl<'i, P, G, B, T, N>
    ExistsProof<
        Axiomize,
        G,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<
                IsInductive<'i>,
                <Axiomize as And>::And<
                    <Axiomize as FirstOrder>::ForAll<B>,
                    <Axiomize as FirstOrder>::ForAll<T>,
                >,
            >,
            <Axiomize as FirstOrder>::ForAll<N>,
        >,
    > for SeparationStep<'i, P, G, B, T, N>
where
    P: for<'x> View<'x> + ?Sized,
    G: for<'s> View<'s, Output = IsSeparated<'s, 'i, P>> + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
    N: for<'n> View<'n, Output = <Axiomize as Imply>::Imply<IsNat<'n>, <P as View<'n>>::Output>>
        + ?Sized,
{
    fn prove<'s>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <G as View<'s>>::Output,
            <Axiomize as Imply>::Imply<
                <Axiomize as And>::And<
                    IsInductive<'i>,
                    <Axiomize as And>::And<
                        <Axiomize as FirstOrder>::ForAll<B>,
                        <Axiomize as FirstOrder>::ForAll<T>,
                    >,
                >,
                <Axiomize as FirstOrder>::ForAll<N>,
            >,
        >,
    > {
        curry().mp({
            let h = Deduction::<
                <Axiomize as And>::And<
                    IsSeparated<'s, 'i, P>,
                    <Axiomize as And>::And<
                        IsInductive<'i>,
                        <Axiomize as And>::And<
                            <Axiomize as FirstOrder>::ForAll<B>,
                            <Axiomize as FirstOrder>::ForAll<T>,
                        >,
                    >,
                >,
                Axiomize,
            >::assume();
            let sep = h.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let rest = h.pipe(<Axiomize as And>::and_right().upgrade());
            let ind = rest.clone().pipe(<Axiomize as And>::and_left().upgrade());
            let aux = rest.pipe(<Axiomize as And>::and_right().upgrade());
            // Reassociate into the bundle `induction_at` consumes.
            let left = <Axiomize as And>::and_intro().upgrade().mp(sep).mp(ind);
            <Axiomize as And>::and_intro()
                .upgrade()
                .mp(left)
                .mp(aux)
                .pipe(induction_at::<'s, 'i, P, SeparatedView<'s, 'i, P>, B, T, N>().upgrade())
                .cast()
        })
    }
}

/// Separation supplies the carved set, for a fixed inductive `i`.
struct InfinityStep<P: ?Sized, B: ?Sized, T: ?Sized, N: ?Sized>(
    PhantomData<*const P>,
    PhantomData<(*const B, *const T, *const N)>,
);
impl<P: ?Sized, B: ?Sized, T: ?Sized, N: ?Sized> Clone for InfinityStep<P, B, T, N> {
    fn clone(&self) -> Self {
        InfinityStep(PhantomData, PhantomData)
    }
}
impl<P, B, T, N>
    ExistsProof<
        Axiomize,
        InductiveView,
        <Axiomize as Imply>::Imply<
            <Axiomize as And>::And<
                <Axiomize as FirstOrder>::ForAll<B>,
                <Axiomize as FirstOrder>::ForAll<T>,
            >,
            <Axiomize as FirstOrder>::ForAll<N>,
        >,
    > for InfinityStep<P, B, T, N>
where
    P: for<'x> View<'x> + ?Sized,
    B: for<'x> View<'x, Output = <Axiomize as Imply>::Imply<IsEmpty<'x>, <P as View<'x>>::Output>>
        + ?Sized,
    T: for<'k> View<
            'k,
            Output = <Axiomize as Imply>::Imply<
                <P as View<'k>>::Output,
                <Axiomize as FirstOrder>::ForAll<StepConclView<'k, P>>,
            >,
        > + ?Sized,
    N: for<'n> View<'n, Output = <Axiomize as Imply>::Imply<IsNat<'n>, <P as View<'n>>::Output>>
        + ?Sized,
{
    fn prove<'i>(
        self,
    ) -> Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            IsInductive<'i>,
            <Axiomize as Imply>::Imply<
                <Axiomize as And>::And<
                    <Axiomize as FirstOrder>::ForAll<B>,
                    <Axiomize as FirstOrder>::ForAll<T>,
                >,
                <Axiomize as FirstOrder>::ForAll<N>,
            >,
        >,
    > {
        curry().mp(super::axioms::separation::<P>()
            .pipe(<Axiomize as FirstOrder>::forall_elim::<'i, SeparationView<P>>())
            .pipe(<Axiomize as FirstOrder>::exists_gen(SeparationStep::<
                'i,
                P,
                SeparationInnerView<'i, P>,
                B,
                T,
                N,
            >(
                PhantomData,
                PhantomData,
                PhantomData,
            ))))
    }
}

/// **Induction on the natural numbers.**
///
/// `(∀e. IsEmpty(e) → P(e)) → (∀k ∀t. P(k) → IsSuccOf(t, k) → P(t)) → ∀n. IsNat(n) → P(n)`
///
/// Infinity supplies some inductive `i`; separation carves
/// `s = {z ∈ i : P(z)}` out of it; the two hypotheses make `s` inductive; and
/// `IsNat(n)` — membership of *every* inductive set — then puts `n` in `s`,
/// where the carving reads `P(n)` back out.
pub fn induction<P>() -> Cert<
    Axiomize,
    <Axiomize as Imply>::Imply<NatBase<P>, <Axiomize as Imply>::Imply<NatStep<P>, NatInduction<P>>>,
>
where
    P: for<'x> View<'x> + ?Sized,
{
    curry().mp(
        super::axioms::infinity().pipe(<Axiomize as FirstOrder>::exists_gen(InfinityStep::<
            P,
            BaseView<P>,
            StepView<P>,
            InductionView<P>,
        >(
            PhantomData,
            PhantomData,
        ))),
    )
}

/// `λz. z = z` — a predicate with no free variables, for the induction witness.
type SelfEqView = dyn for<'z> View<'z, Output = Eq<'z, 'z>> + 'static;

/// Typecheck witnesses: `cargo check` is the proof checker.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
const _: () = {
    use super::axioms::{
        choice, ext, infinity, pairing, power_set, regularity, replacement, separation, union,
    };
    use crate::rel::desc::Describes;

    /// The three uniqueness theorems are now one theorem at three conditions,
    /// so each notion's `Is…` spelling has to *be* [`Describes`] at its
    /// condition. If a condition ever drifts from the notion it names, the
    /// uniqueness proof would still compile — while proving something else —
    /// and these are what would stop it.
    fn conditions_match_their_notions<'a, 'b, 'y, 's>(
        p: Cert<Axiomize, Describes<'s, Axiomize, SetIn, PairCond<'a, 'b>>>,
        t: Cert<Axiomize, Describes<'s, Axiomize, SetIn, SingletonCond<'a>>>,
        c: Cert<Axiomize, Describes<'s, Axiomize, SetIn, SuccCond<'y>>>,
    ) -> (
        Cert<Axiomize, IsPair<'s, 'a, 'b>>,
        Cert<Axiomize, IsSingleton<'s, 'a>>,
        Cert<Axiomize, IsSuccOf<'s, 'y>>,
    ) {
        (p, t, c)
    }

    /// Emptiness is not a [`Describes`], so it gets its own identification:
    /// [`crate::rel::empty::IsEmpty`] at [`SetIn`] has to be the [`IsEmpty`]
    /// the axioms are written in, or [`empty_unique`] proves the wrong thing.
    fn emptiness_matches_its_notion<'e>(
        e: Cert<Axiomize, GenIsEmpty<'e, Axiomize, SetIn>>,
    ) -> Cert<Axiomize, IsEmpty<'e>> {
        e
    }

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

    /// Equality is an equivalence, derived from nothing at all — no axiom is
    /// invoked anywhere in those three proofs, which is why they are generic
    /// and live in [`crate::rel::ext`] rather than here.
    fn equality_is_an_equivalence() {
        let _ = <SetEq as ClosedEq<Axiomize>>::refl();
        let _ = <SetEq as ClosedEq<Axiomize>>::sym();
        let _ = <SetEq as ClosedEq<Axiomize>>::trans();
        let _ = pair_unique();
        let _ = pair_left();
        let _ = pair_right();
        let _ = singleton_member();
        let _ = singleton_unique();
        let _ = singleton_is_pair();
        let _ = pair_is_singleton();
        let _ = singleton_injective();
        let _ = pair_collapses();
        let _ = in_right::<Axiomize, SetIn>();
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
        let _ = in_left::<Axiomize, SetIn>();
    }

    /// Restating [`super::axioms::ext`] against [`ExtView`] must not have
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

    /// Likewise for [`super::axioms::separation`] and [`SeparationView`].
    fn separation_view_is_the_statement<P: for<'z> View<'z> + ?Sized>(
        c: Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SeparationView<P>>>,
    ) -> Cert<
        Axiomize,
        pred!(
            { Axiomize },
            ForAll::<'a>(Exists::<'s>(ForAll::<'z>(
                (In::<'z, 's>).iff((In::<'z, 'a>) && (<P as View<'z>>::Output))
            )))
        ),
    > {
        c
    }

    /// Restating [`super::axioms::infinity`] against [`InductiveView`]
    /// must not have changed what it asserts.
    fn inductive_view_is_the_statement(
        c: Cert<Axiomize, <Axiomize as FirstOrder>::Exists<InductiveView>>,
    ) -> Cert<
        Axiomize,
        pred!(
            { Axiomize },
            Exists::<'i>(
                (Exists::<'e>((In::<'e, 'i>) && (IsEmpty::<'e>)))
                    && (ForAll::<'y>(
                        (In::<'y, 'i>).imply(Exists::<'s>((In::<'s, 'i>) && (IsSuccOf::<'s, 'y>)))
                    ))
            )
        ),
    > {
        c
    }

    /// Descriptions determine their subject.
    fn descriptions_are_unique() {
        let _ = empty_unique();
        let _ = succ_unique();
    }

    /// Naming the body of [`IsEmpty`] as [`EmptyView`] must not have changed
    /// what it says.
    fn empty_view_is_the_definition<'e>(
        c: Cert<Axiomize, pred!({ Axiomize }, ForAll::<'z>(!(In::<'z, 'e>)))>,
    ) -> Cert<Axiomize, IsEmpty<'e>> {
        c
    }

    /// Likewise for [`SuccView`].
    fn succ_view_is_the_definition<'s, 'y>(
        c: Cert<
            Axiomize,
            pred!(
                { Axiomize },
                ForAll::<'w>((In::<'w, 's>).iff((In::<'w, 'y>) || (Eq::<'w, 'y>)))
            ),
        >,
    ) -> Cert<Axiomize, IsSuccOf<'s, 'y>> {
        c
    }

    /// The two introduction rules for natural numbers.
    fn zero_and_successor_are_natural() {
        let _ = zero_is_nat();
        let _ = succ_is_nat();
    }

    /// [`IsNat`] is the proposition its doc comment claims.
    fn nat_view_is_the_definition<'n>(
        c: Cert<
            Axiomize,
            pred!(
                { Axiomize },
                ForAll::<'i>(
                    ((Exists::<'e>((In::<'e, 'i>) && (IsEmpty::<'e>)))
                        && (ForAll::<'w>(
                            (In::<'w, 'i>)
                                .imply(Exists::<'v>((In::<'v, 'i>) && (IsSuccOf::<'v, 'w>)))
                        )))
                    .imply(In::<'n, 'i>)
                )
            ),
        >,
    ) -> Cert<Axiomize, IsNat<'n>> {
        c
    }

    /// Induction, spelled out at a concrete predicate — `λn. n = n`, chosen so
    /// the shape shows through: base and step in, `∀n. IsNat(n) → P(n)` out.
    fn induction_is_the_elimination_rule() {
        let _: Cert<
            Axiomize,
            pred!(
                { Axiomize },
                (ForAll::<'e>((IsEmpty::<'e>).imply(Eq::<'e, 'e>))).imply(
                    (ForAll::<'k>(
                        (Eq::<'k, 'k>)
                            .imply(ForAll::<'t>((IsSuccOf::<'t, 'k>).imply(Eq::<'t, 't>)))
                    ))
                    .imply(ForAll::<'n>((IsNat::<'n>).imply(Eq::<'n, 'n>)))
                )
            ),
        > = induction::<SelfEqView>();
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
