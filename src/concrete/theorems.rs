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
use super::lang::*;
use crate::logic::prop::{
    And, Cert, Deduction, DeductionUpgrade, ExistsProof, FirstOrder, ForAllProof, Iff, Imply, View,
    curry,
};
use crate::macros::pred;

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
/// `i` has one, it is a natural number by the definition of [`IsNat`], and the base
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
            // P(∅) from the base case, together with the naturalness definition.
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

};
