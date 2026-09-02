//! Presenting a *closed* equivalence as a [`poset`](super::poset) relation.
//!
//! The two spellings differ by a guard. [`super::poset`]'s relations live on a
//! domain, `∀a. El(a) → …`; a logic's equality is normally proved closed,
//! `∀a. …`, because in a set theory every object is in the domain. Bridging
//! the two is pure weakening — `l1` under the quantifier prefix — but doing it
//! by hand needs a nest of [`Generalise`]/[`ForAllProof`] impls per theorem.
//!
//! So it is done once, here, at *generic* types. Everything below is
//! parameterised over the logic and over an opaque [`ClosedEq`], so every
//! `Rel<'a, 'b>` in these proofs is a rigid projection rustc cannot expand.
//! Substitution is not here. It is not a property of an equivalence relation
//! at all, and as a schema over every `P: View` it is not provable either --
//! see [`ClosedEq`]. An axiomatised system implements [`ClosedEq`] with
//! one-line delegations to its own theorems and pays no borrow-checking for
//! the bridge; see
//! [`crate::concrete::equality`]. Writing the same bridge against a *defined*
//! equality instead costs about twenty times the MIR — see [`super::set`].
#![forbid(unsafe_code)]

use ::core::marker::PhantomData;

use super::Set;
use super::poset::{BinRel, Reflexive, Symmetric, Transitive};
use crate::logic::prop::{
    Cert, FirstOrder, ForAllProof, Generalise, Imply, PropLogic, View, forall_intro,
};
use crate::macros::thm;

/// An equivalence relation stated as closed theorems.
///
/// The three statements carry no `El` guard. That is the normal shape for a
/// logic's own equality, and [`Closed`] adds the guards.
pub trait ClosedEq<Logic>
where
    Logic: FirstOrder + PropLogic,
{
    /// `'a` is an object of the domain.
    type El<'a>;

    /// The relation itself.
    type Rel<'a, 'b>;

    /// `∀a. a ~ a`
    fn refl() -> thm!({ Logic }, ForAll::<'a>(Self::Rel::<'a, 'a>));

    /// `∀a ∀b. a ~ b → b ~ a`
    fn sym() -> thm!(
        { Logic },
        ForAll::<'a, 'b>(Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'a>)
    );

    /// `∀a ∀b ∀c. a ~ b → b ~ c → a ~ c`
    fn trans() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'c>(
            Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'c> >>= Self::Rel::<'a, 'c>
        )
    );
}

/// [`ClosedEq`] presented on its domain, so it satisfies [`Equivalence`].
///
/// [`Equivalence`]: super::poset::Equivalence
pub struct Closed<Logic, S: ?Sized>(PhantomData<(Logic, *const S)>);

impl<Logic, S> Set for Closed<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
{
    type El<'a> = S::El<'a>;
}

impl<Logic, S> BinRel for Closed<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
{
    type Rel<'a, 'b> = S::Rel<'a, 'b>;
}

/// `Q → (El(a) → Q)`: the whole content of every guard below.
fn guard<'a, Logic, S, Q>(q: Cert<Logic, Q>) -> Cert<Logic, Logic::Imply<S::El<'a>, Q>>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
{
    Logic::l1().mp(q)
}

// ---------------------------------------------------------------------------
// Reflexivity
// ---------------------------------------------------------------------------

type ReflView<Logic, S> =
    dyn for<'a> View<'a, Output = <S as ClosedEq<Logic>>::Rel<'a, 'a>> + 'static;

impl<Logic, S> Reflexive<Logic> for Closed<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
{
    fn refl() -> thm!({ Logic }, 'a: { Self::El::<'a> }, Self::Rel::<'a, 'a>) {
        forall_intro(Refl::<Logic, S>(PhantomData))
    }
}

struct Refl<Logic, S: ?Sized>(PhantomData<(Logic, *const S)>);
impl<Logic, S: ?Sized> Clone for Refl<Logic, S> {
    fn clone(&self) -> Self {
        Refl(PhantomData)
    }
}

impl<Logic, S, Q> Generalise<Logic, Q> for Refl<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = Logic::Imply<S::El<'a>, S::Rel<'a, 'a>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        guard::<'a, Logic, S, _>(
            Logic::forall_elim::<'a, ReflView<Logic, S>>().mp(S::refl()),
        )
    }
}

// ---------------------------------------------------------------------------
// Symmetry
// ---------------------------------------------------------------------------

type SymView1<'a, Logic, S> = dyn for<'b> View<
        'b,
        Output = <Logic as Imply>::Imply<
            <S as ClosedEq<Logic>>::Rel<'a, 'b>,
            <S as ClosedEq<Logic>>::Rel<'b, 'a>,
        >,
    > + 'static;

type SymView<Logic, S> = dyn for<'a> View<
        'a,
        Output = <Logic as FirstOrder>::ForAll<SymView1<'a, Logic, S>>,
    > + 'static;

/// `λb. El(b) → (a ~ b → b ~ a)`, with `'a` fixed.
type SymGuarded<'a, Logic, S> = dyn for<'b> View<
        'b,
        Output = <Logic as Imply>::Imply<
            <S as ClosedEq<Logic>>::El<'b>,
            <Logic as Imply>::Imply<
                <S as ClosedEq<Logic>>::Rel<'a, 'b>,
                <S as ClosedEq<Logic>>::Rel<'b, 'a>,
            >,
        >,
    > + 'static;

impl<Logic, S> Symmetric<Logic> for Closed<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
{
    fn sym() -> thm!(
        { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'a>
    ) {
        forall_intro(Sym::<Logic, S>(PhantomData))
    }
}

struct Sym<Logic, S: ?Sized>(PhantomData<(Logic, *const S)>);
impl<Logic, S: ?Sized> Clone for Sym<Logic, S> {
    fn clone(&self) -> Self {
        Sym(PhantomData)
    }
}

impl<Logic, S, Q> Generalise<Logic, Q> for Sym<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
    Q: for<'a> View<
            'a,
            Output = Logic::Imply<S::El<'a>, Logic::ForAll<SymGuarded<'a, Logic, S>>>,
        > + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        Logic::forall_gen(Sym1::<'a, Logic, S>(PhantomData))
    }
}

struct Sym1<'a, Logic, S: ?Sized>(PhantomData<(&'a (), Logic, *const S)>);
impl<'a, Logic, S: ?Sized> Clone for Sym1<'a, Logic, S> {
    fn clone(&self) -> Self {
        Sym1(PhantomData)
    }
}

impl<'a, Logic, S, Q> ForAllProof<Logic, S::El<'a>, Q> for Sym1<'a, Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = Logic::Imply<S::El<'b>, Logic::Imply<S::Rel<'a, 'b>, S::Rel<'b, 'a>>>>
        + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, Logic::Imply<S::El<'a>, <Q as View<'b>>::Output>> {
        let at_a = Logic::forall_elim::<'a, SymView<Logic, S>>().mp(S::sym());
        let at_b = Logic::forall_elim::<'b, SymView1<'a, Logic, S>>().mp(at_a);
        guard::<'a, Logic, S, _>(guard::<'b, Logic, S, _>(at_b))
    }
}

// ---------------------------------------------------------------------------
// Transitivity
// ---------------------------------------------------------------------------

type TransView2<'a, 'b, Logic, S> = dyn for<'c> View<
        'c,
        Output = <Logic as Imply>::Imply<
            <S as ClosedEq<Logic>>::Rel<'a, 'b>,
            <Logic as Imply>::Imply<
                <S as ClosedEq<Logic>>::Rel<'b, 'c>,
                <S as ClosedEq<Logic>>::Rel<'a, 'c>,
            >,
        >,
    > + 'static;

type TransView1<'a, Logic, S> = dyn for<'b> View<
        'b,
        Output = <Logic as FirstOrder>::ForAll<TransView2<'a, 'b, Logic, S>>,
    > + 'static;

type TransView<Logic, S> = dyn for<'a> View<
        'a,
        Output = <Logic as FirstOrder>::ForAll<TransView1<'a, Logic, S>>,
    > + 'static;

/// `λc. El(c) → (a ~ b → b ~ c → a ~ c)`, with `'a` and `'b` fixed.
type TransGuarded2<'a, 'b, Logic, S> = dyn for<'c> View<
        'c,
        Output = <Logic as Imply>::Imply<
            <S as ClosedEq<Logic>>::El<'c>,
            <Logic as Imply>::Imply<
                <S as ClosedEq<Logic>>::Rel<'a, 'b>,
                <Logic as Imply>::Imply<
                    <S as ClosedEq<Logic>>::Rel<'b, 'c>,
                    <S as ClosedEq<Logic>>::Rel<'a, 'c>,
                >,
            >,
        >,
    > + 'static;

/// `λb. El(b) → ∀c. …`, with `'a` fixed.
type TransGuarded1<'a, Logic, S> = dyn for<'b> View<
        'b,
        Output = <Logic as Imply>::Imply<
            <S as ClosedEq<Logic>>::El<'b>,
            <Logic as FirstOrder>::ForAll<TransGuarded2<'a, 'b, Logic, S>>,
        >,
    > + 'static;

impl<Logic, S> Transitive<Logic> for Closed<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
{
    fn transitive() -> thm!(
        { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        'c: { Self::El::<'c> },
        Self::Rel::<'a, 'b>.imply(Self::Rel::<'b, 'c>.imply(Self::Rel::<'a, 'c>))
    ) {
        forall_intro(Trans::<Logic, S>(PhantomData))
    }
}

struct Trans<Logic, S: ?Sized>(PhantomData<(Logic, *const S)>);
impl<Logic, S: ?Sized> Clone for Trans<Logic, S> {
    fn clone(&self) -> Self {
        Trans(PhantomData)
    }
}

impl<Logic, S, Q> Generalise<Logic, Q> for Trans<Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
    Q: for<'a> View<
            'a,
            Output = Logic::Imply<S::El<'a>, Logic::ForAll<TransGuarded1<'a, Logic, S>>>,
        > + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        Logic::forall_gen(Trans1::<'a, Logic, S>(PhantomData))
    }
}

struct Trans1<'a, Logic, S: ?Sized>(PhantomData<(&'a (), Logic, *const S)>);
impl<'a, Logic, S: ?Sized> Clone for Trans1<'a, Logic, S> {
    fn clone(&self) -> Self {
        Trans1(PhantomData)
    }
}

impl<'a, Logic, S, Q> ForAllProof<Logic, S::El<'a>, Q> for Trans1<'a, Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
    Q: for<'b> View<
            'b,
            Output = Logic::Imply<S::El<'b>, Logic::ForAll<TransGuarded2<'a, 'b, Logic, S>>>,
        > + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, Logic::Imply<S::El<'a>, <Q as View<'b>>::Output>> {
        guard::<'a, Logic, S, _>(Logic::forall_gen(Trans2::<'a, 'b, Logic, S>(PhantomData)))
    }
}

struct Trans2<'a, 'b, Logic, S: ?Sized>(PhantomData<(&'a (), &'b (), Logic, *const S)>);
impl<'a, 'b, Logic, S: ?Sized> Clone for Trans2<'a, 'b, Logic, S> {
    fn clone(&self) -> Self {
        Trans2(PhantomData)
    }
}

impl<'a, 'b, Logic, S, Q> ForAllProof<Logic, S::El<'b>, Q> for Trans2<'a, 'b, Logic, S>
where
    Logic: FirstOrder + PropLogic,
    S: ClosedEq<Logic> + ?Sized,
    Q: for<'c> View<
            'c,
            Output = Logic::Imply<
                S::El<'c>,
                Logic::Imply<S::Rel<'a, 'b>, Logic::Imply<S::Rel<'b, 'c>, S::Rel<'a, 'c>>>,
            >,
        > + ?Sized,
{
    fn prove<'c>(self) -> Cert<Logic, Logic::Imply<S::El<'b>, <Q as View<'c>>::Output>> {
        let at_a = Logic::forall_elim::<'a, TransView<Logic, S>>().mp(S::trans());
        let at_b = Logic::forall_elim::<'b, TransView1<'a, Logic, S>>().mp(at_a);
        let at_c = Logic::forall_elim::<'c, TransView2<'a, 'b, Logic, S>>().mp(at_b);
        guard::<'b, Logic, S, _>(guard::<'c, Logic, S, _>(at_c))
    }
}
