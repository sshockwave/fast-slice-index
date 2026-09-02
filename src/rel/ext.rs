//! Extensional equality: the equality a membership relation induces.
//!
//! `x = y` is *defined* as `∀z. z ∈ x ↔ z ∈ y`, and with that definition the
//! three equivalence laws cost no axiom whatsoever. Reflexivity is reflexivity
//! of `↔`, symmetry is commuting the two halves of a biconditional under a
//! quantifier, transitivity is [`iff_trans`] under a quantifier. None of it
//! mentions a set-theoretic assumption, so none of it belongs in an
//! axiomatised system: an [`Ext`] over any [`Membership`] is a [`ClosedEq`],
//! and [`crate::rel::eq::Closed`] then makes it an
//! [`Equivalence`](super::poset::Equivalence).
//!
//! Only `In` is opaque here, so the proof terms below name
//! `M::In<'z, 'x>` — a rigid projection — where the concrete versions named the
//! eight-node `Eq` tree at every occurrence. That is the whole reason this is
//! generic; [`crate::rel::func`] makes the same trade one layer up.
#![forbid(unsafe_code)]

use ::core::marker::PhantomData;

use super::eq::ClosedEq;
use crate::logic::prop::{
    And, Cert, FirstOrder, ForAllProof, Generalise, Iff, Imply, PropLogic, View, and_comm, and_map,
    curry, forall_intro, iff_trans, reflexive, syllogism,
};
use crate::macros::pred;
use crate::macros::thm;

/// A membership relation, and the domain it ranges over.
///
/// This is the *only* primitive extensional equality needs. Everything in this
/// module is derived from it.
pub trait Membership<Logic>: 'static {
    /// `'a` is an object of the domain.
    type El<'a>;

    /// `'a ∈ 'b`
    type In<'a, 'b>;
}

/// The equality induced by [`Membership`]: `x = y ≡ ∀z. z ∈ x ↔ z ∈ y`.
pub struct Ext<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);

/// `λz. z ∈ x ↔ z ∈ y`
pub type ExtView<'x, 'y, Logic, M> = dyn for<'z> View<
        'z,
        Output = Iff<
            Logic,
            <M as Membership<Logic>>::In<'z, 'x>,
            <M as Membership<Logic>>::In<'z, 'y>,
        >,
    > + 'static;

/// `λx. x = x` — the body of [`ClosedEq::refl`], named so a use site can
/// eliminate the quantifier at a particular object.
pub type ExtReflView<Logic, M> =
    dyn for<'x> View<'x, Output = ExtEq<'x, 'x, Logic, M>> + 'static;

/// `x = y`, unfolded exactly one level.
pub type ExtEq<'x, 'y, Logic, M> =
    <Logic as FirstOrder>::ForAll<ExtView<'x, 'y, Logic, M>>;

impl<Logic, M> ClosedEq<Logic> for Ext<Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
{
    type El<'a> = M::El<'a>;
    type Rel<'a, 'b> = ExtEq<'a, 'b, Logic, M>;

    fn refl() -> thm!({ Logic }, ForAll::<'a>(Self::Rel::<'a, 'a>)) {
        forall_intro(Refl::<Logic, M>(PhantomData))
    }

    fn sym() -> thm!(
        { Logic },
        ForAll::<'a, 'b>(Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'a>)
    ) {
        forall_intro(Sym::<Logic, M>(PhantomData))
    }

    fn trans() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'c>(
            Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'c> >>= Self::Rel::<'a, 'c>
        )
    ) {
        forall_intro(Trans::<Logic, M>(PhantomData))
    }
}

/// `PhantomData<*const M>` is not `Clone`-derivable, and every prover below is
/// a unit, so the impls are written out rather than derived.
macro_rules! unit_clone {
    ($name:ident<$($lt:lifetime),*> $(, $view:ident)*) => {
        impl<$($lt,)* Logic, M: ?Sized $(, $view: ?Sized)*> Clone
            for $name<$($lt,)* Logic, M $(, $view)*>
        {
            fn clone(&self) -> Self {
                $name(PhantomData)
            }
        }
    };
}

// ---------------------------------------------------------------------------
// Reflexivity: `∀x. x = x`
// ---------------------------------------------------------------------------

struct Refl<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);
unit_clone!(Refl<>);

impl<Logic, M, Q> Generalise<Logic, Q> for Refl<Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'x> View<'x, Output = ExtEq<'x, 'x, Logic, M>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output> {
        forall_intro::<Logic, ExtView<'x, 'x, Logic, M>, _>(ReflAt::<'x, Logic, M>(PhantomData))
    }
}

struct ReflAt<'x, Logic, M: ?Sized>(PhantomData<(&'x (), Logic, *const M)>);
unit_clone!(ReflAt<'x>);

impl<'x, Logic, M, Q> Generalise<Logic, Q> for ReflAt<'x, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'x>, M::In<'z, 'x>>> + ?Sized,
{
    fn prove<'z>(self) -> Cert<Logic, <Q as View<'z>>::Output> {
        Logic::and_intro()
            .mp(reflexive::<M::In<'z, 'x>, Logic>())
            .mp(reflexive::<M::In<'z, 'x>, Logic>())
    }
}

// ---------------------------------------------------------------------------
// Symmetry: `∀x ∀y. x = y → y = x`
// ---------------------------------------------------------------------------

/// `λy. x = y → y = x`
type SymView<'x, Logic, M> = dyn for<'y> View<
        'y,
        Output = <Logic as Imply>::Imply<
            ExtEq<'x, 'y, Logic, M>,
            ExtEq<'y, 'x, Logic, M>,
        >,
    > + 'static;

struct Sym<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);
unit_clone!(Sym<>);

impl<Logic, M, Q> Generalise<Logic, Q> for Sym<Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'x> View<'x, Output = Logic::ForAll<SymView<'x, Logic, M>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output> {
        forall_intro::<Logic, SymView<'x, Logic, M>, _>(Sym1::<'x, Logic, M>(PhantomData))
    }
}

struct Sym1<'x, Logic, M: ?Sized>(PhantomData<(&'x (), Logic, *const M)>);
unit_clone!(Sym1<'x>);

impl<'x, Logic, M, Q> Generalise<Logic, Q> for Sym1<'x, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'y> View<'y, Output = Logic::Imply<ExtEq<'x, 'y, Logic, M>, ExtEq<'y, 'x, Logic, M>>>
        + ?Sized,
{
    fn prove<'y>(self) -> Cert<Logic, <Q as View<'y>>::Output> {
        // `forall_gen` produces exactly `P → ∀z. Q z`; take `P` to be the
        // hypothesis `x = y`, so no `Deduction` scope is needed here.
        Logic::forall_gen(Sym2::<'x, 'y, Logic, M, ExtView<'x, 'y, Logic, M>>(PhantomData))
    }
}

/// The hypothesis `x = y` is taken as the *parameter* `E` rather than written
/// out as `ForAll<ExtView<..>>`. Naming a nested `dyn for<..> View<..>` in an
/// impl header loses the boundness of its lifetime; pinning `E` in a
/// where-clause does not.
struct Sym2<'x, 'y, Logic, M: ?Sized, E: ?Sized>(
    PhantomData<(&'x (), &'y (), Logic, *const M, *const E)>,
);
unit_clone!(Sym2<'x, 'y>, E);

impl<'x, 'y, Logic, M, E, Q> ForAllProof<Logic, Logic::ForAll<E>, Q> for Sym2<'x, 'y, Logic, M, E>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    E: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'x>, M::In<'z, 'y>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'y>, M::In<'z, 'x>>> + ?Sized,
{
    fn prove<'z>(self) -> Cert<Logic, Logic::Imply<Logic::ForAll<E>, <Q as View<'z>>::Output>> {
        // x = y  ⊢  (z ∈ x ↔ z ∈ y)  ⊢  (z ∈ y ↔ z ∈ x)
        syllogism().mp(Logic::forall_elim::<'z, E>()).mp(and_comm())
    }
}

// ---------------------------------------------------------------------------
// Transitivity: `∀x ∀y ∀w. x = y → y = w → x = w`
// ---------------------------------------------------------------------------

/// `λw. x = y → y = w → x = w`
type TransView<'x, 'y, Logic, M> = dyn for<'w> View<
        'w,
        Output = <Logic as Imply>::Imply<
            ExtEq<'x, 'y, Logic, M>,
            <Logic as Imply>::Imply<ExtEq<'y, 'w, Logic, M>, ExtEq<'x, 'w, Logic, M>>,
        >,
    > + 'static;

/// `λy. ∀w. …`
type TransView1<'x, Logic, M> = dyn for<'y> View<
        'y,
        Output = <Logic as FirstOrder>::ForAll<TransView<'x, 'y, Logic, M>>,
    > + 'static;

struct Trans<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);
unit_clone!(Trans<>);

impl<Logic, M, Q> Generalise<Logic, Q> for Trans<Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'x> View<'x, Output = Logic::ForAll<TransView1<'x, Logic, M>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output> {
        forall_intro::<Logic, TransView1<'x, Logic, M>, _>(Trans1::<'x, Logic, M>(PhantomData))
    }
}

struct Trans1<'x, Logic, M: ?Sized>(PhantomData<(&'x (), Logic, *const M)>);
unit_clone!(Trans1<'x>);

impl<'x, Logic, M, Q> Generalise<Logic, Q> for Trans1<'x, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'y> View<'y, Output = Logic::ForAll<TransView<'x, 'y, Logic, M>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Logic, <Q as View<'y>>::Output> {
        forall_intro::<Logic, TransView<'x, 'y, Logic, M>, _>(Trans2::<'x, 'y, Logic, M>(
            PhantomData,
        ))
    }
}

struct Trans2<'x, 'y, Logic, M: ?Sized>(PhantomData<(&'x (), &'y (), Logic, *const M)>);
unit_clone!(Trans2<'x, 'y>);

impl<'x, 'y, Logic, M, Q> Generalise<Logic, Q> for Trans2<'x, 'y, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'w> View<
            'w,
            Output = Logic::Imply<
                ExtEq<'x, 'y, Logic, M>,
                Logic::Imply<ExtEq<'y, 'w, Logic, M>, ExtEq<'x, 'w, Logic, M>>,
            >,
        > + ?Sized,
{
    fn prove<'w>(self) -> Cert<Logic, <Q as View<'w>>::Output> {
        // `forall_gen` takes one antecedent, so the two hypotheses go in
        // conjoined and `curry` splits them again afterwards.
        curry().mp(Logic::forall_gen(Trans3::<
            'x,
            'y,
            'w,
            Logic,
            M,
            ExtView<'x, 'y, Logic, M>,
            ExtView<'y, 'w, Logic, M>,
        >(PhantomData)))
    }
}

/// Both hypotheses are parameters, for the reason given on [`Sym2`].
struct Trans3<'x, 'y, 'w, Logic, M: ?Sized, E1: ?Sized, E2: ?Sized>(
    PhantomData<(&'x (), &'y (), &'w (), Logic, *const M, *const E1, *const E2)>,
);
unit_clone!(Trans3<'x, 'y, 'w>, E1, E2);

impl<'x, 'y, 'w, Logic, M, E1, E2, Q>
    ForAllProof<Logic, Logic::And<Logic::ForAll<E1>, Logic::ForAll<E2>>, Q>
    for Trans3<'x, 'y, 'w, Logic, M, E1, E2>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    E1: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'x>, M::In<'z, 'y>>> + ?Sized,
    E2: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'y>, M::In<'z, 'w>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'x>, M::In<'z, 'w>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Logic,
        Logic::Imply<Logic::And<Logic::ForAll<E1>, Logic::ForAll<E2>>, <Q as View<'z>>::Output>,
    > {
        // (x = y ∧ y = w) ⊢ ((z∈x ↔ z∈y) ∧ (z∈y ↔ z∈w)) ⊢ (z∈x ↔ z∈w)
        syllogism()
            .mp(and_map(
                Logic::forall_elim::<'z, E1>(),
                Logic::forall_elim::<'z, E2>(),
            ))
            .mp(iff_trans())
    }
}

// ---------------------------------------------------------------------------
// Substituting equals for equals, at the two atoms
// ---------------------------------------------------------------------------
//
// These are the base cases of Leibniz's law. Every other case of substitution
// is a connective or a quantifier and goes through by the induction hypothesis,
// so between them they are the whole content of it -- see the note on
// [`EqualityDef`](crate::logic::function::EqualityDef).
//
// Only one of the two costs anything. `x = y` is *defined* as sharing members,
// so substituting on the right of `∈` is the definition with a quantifier
// stripped. On the left it is not derivable at all: a set's members do not
// determine which sets contain it, and a `Membership` for which that fails is
// a perfectly consistent structure -- just not an extensional one. So it is an
// obligation, [`Extensional`], and in ZFC the axiom of extensionality
// discharges it.

/// `x = y → z ∈ x → z ∈ y`, at fixed points. Free from the definition.
pub fn in_right_at<'x, 'y, 'z, Logic, M>() -> Cert<
    Logic,
    Logic::Imply<ExtEq<'x, 'y, Logic, M>, Logic::Imply<M::In<'z, 'x>, M::In<'z, 'y>>>,
>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
{
    syllogism()
        .mp(Logic::forall_elim::<'z, ExtView<'x, 'y, Logic, M>>())
        .mp(Logic::and_left())
}

/// A [`Membership`] whose induced equality substitutes on the *left* of `∈`.
///
/// Extensionality, in the form it is actually used. [`Ext`] is an equivalence
/// relation for any membership relation at all; this is the extra assumption
/// that makes it behave like identity.
pub trait Extensional<Logic>: Membership<Logic>
where
    Logic: PropLogic + And + FirstOrder,
{
    /// `x = y → x ∈ w → y ∈ w`, at fixed points.
    fn in_left_at<'x, 'y, 'w>() -> Cert<
        Logic,
        Logic::Imply<ExtEq<'x, 'y, Logic, Self>, Logic::Imply<Self::In<'x, 'w>, Self::In<'y, 'w>>>,
    >;
}

/// `λz. x = y → z ∈ x → z ∈ y`
pub type InRightView<'x, 'y, Logic, M> = dyn for<'z> View<
        'z,
        Output = pred!(
            { Logic },
            ExtEq::<'x, 'y, Logic, M>
                >>= <M as Membership<Logic>>::In::<'z, 'x>
                >>= <M as Membership<Logic>>::In::<'z, 'y>
        ),
    > + 'static;
/// `λy. ∀z. …`
pub type InRightView1<'x, Logic, M> = dyn for<'y> View<
        'y,
        Output = <Logic as FirstOrder>::ForAll<InRightView<'x, 'y, Logic, M>>,
    > + 'static;
/// `λx. ∀y ∀z. …`
pub type InRightView2<Logic, M> = dyn for<'x> View<
        'x,
        Output = <Logic as FirstOrder>::ForAll<InRightView1<'x, Logic, M>>,
    > + 'static;

/// `∀x ∀y ∀z. x = y → z ∈ x → z ∈ y` — proved, no assumption.
pub fn in_right<Logic, M>() -> thm!(
    { Logic },
    ForAll::<'x, 'y, 'z>(
        ExtEq::<'x, 'y, Logic, M>
            >>= <M as Membership<Logic>>::In::<'z, 'x>
            >>= <M as Membership<Logic>>::In::<'z, 'y>
    )
)
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
{
    forall_intro(InRight::<Logic, M>(PhantomData))
}

struct InRight<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);
unit_clone!(InRight<>);

impl<Logic, M, Q> Generalise<Logic, Q> for InRight<Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'x> View<'x, Output = Logic::ForAll<InRightView1<'x, Logic, M>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output> {
        forall_intro::<Logic, InRightView1<'x, Logic, M>, _>(InRight1::<'x, Logic, M>(PhantomData))
    }
}

struct InRight1<'x, Logic, M: ?Sized>(PhantomData<(&'x (), Logic, *const M)>);
unit_clone!(InRight1<'x>);

impl<'x, Logic, M, Q> Generalise<Logic, Q> for InRight1<'x, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'y> View<'y, Output = Logic::ForAll<InRightView<'x, 'y, Logic, M>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Logic, <Q as View<'y>>::Output> {
        forall_intro::<Logic, InRightView<'x, 'y, Logic, M>, _>(InRight2::<'x, 'y, Logic, M>(
            PhantomData,
        ))
    }
}

struct InRight2<'x, 'y, Logic, M: ?Sized>(PhantomData<(&'x (), &'y (), Logic, *const M)>);
unit_clone!(InRight2<'x, 'y>);

impl<'x, 'y, Logic, M, Q> Generalise<Logic, Q> for InRight2<'x, 'y, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    Q: for<'z> View<
            'z,
            Output = Logic::Imply<
                ExtEq<'x, 'y, Logic, M>,
                Logic::Imply<M::In<'z, 'x>, M::In<'z, 'y>>,
            >,
        > + ?Sized,
{
    fn prove<'z>(self) -> Cert<Logic, <Q as View<'z>>::Output> {
        in_right_at::<'x, 'y, 'z, Logic, M>()
    }
}

/// `λw. x = y → x ∈ w → y ∈ w`
pub type InLeftView<'x, 'y, Logic, M> = dyn for<'w> View<
        'w,
        Output = pred!(
            { Logic },
            ExtEq::<'x, 'y, Logic, M>
                >>= <M as Membership<Logic>>::In::<'x, 'w>
                >>= <M as Membership<Logic>>::In::<'y, 'w>
        ),
    > + 'static;
/// `λy. ∀w. …`
pub type InLeftView1<'x, Logic, M> = dyn for<'y> View<
        'y,
        Output = <Logic as FirstOrder>::ForAll<InLeftView<'x, 'y, Logic, M>>,
    > + 'static;
/// `λx. ∀y ∀w. …`
pub type InLeftView2<Logic, M> = dyn for<'x> View<
        'x,
        Output = <Logic as FirstOrder>::ForAll<InLeftView1<'x, Logic, M>>,
    > + 'static;

/// `∀x ∀y ∀w. x = y → x ∈ w → y ∈ w` — the quantified form of
/// [`Extensional::in_left_at`].
pub fn in_left<Logic, M>() -> thm!(
    { Logic },
    ForAll::<'x, 'y, 'w>(
        ExtEq::<'x, 'y, Logic, M>
            >>= <M as Membership<Logic>>::In::<'x, 'w>
            >>= <M as Membership<Logic>>::In::<'y, 'w>
    )
)
where
    Logic: PropLogic + And + FirstOrder,
    M: Extensional<Logic> + ?Sized,
{
    forall_intro(InLeft::<Logic, M>(PhantomData))
}

struct InLeft<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);
unit_clone!(InLeft<>);

impl<Logic, M, Q> Generalise<Logic, Q> for InLeft<Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Extensional<Logic> + ?Sized,
    Q: for<'x> View<'x, Output = Logic::ForAll<InLeftView1<'x, Logic, M>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output> {
        forall_intro::<Logic, InLeftView1<'x, Logic, M>, _>(InLeft1::<'x, Logic, M>(PhantomData))
    }
}

struct InLeft1<'x, Logic, M: ?Sized>(PhantomData<(&'x (), Logic, *const M)>);
unit_clone!(InLeft1<'x>);

impl<'x, Logic, M, Q> Generalise<Logic, Q> for InLeft1<'x, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Extensional<Logic> + ?Sized,
    Q: for<'y> View<'y, Output = Logic::ForAll<InLeftView<'x, 'y, Logic, M>>> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Logic, <Q as View<'y>>::Output> {
        forall_intro::<Logic, InLeftView<'x, 'y, Logic, M>, _>(InLeft2::<'x, 'y, Logic, M>(
            PhantomData,
        ))
    }
}

struct InLeft2<'x, 'y, Logic, M: ?Sized>(PhantomData<(&'x (), &'y (), Logic, *const M)>);
unit_clone!(InLeft2<'x, 'y>);

impl<'x, 'y, Logic, M, Q> Generalise<Logic, Q> for InLeft2<'x, 'y, Logic, M>
where
    Logic: PropLogic + And + FirstOrder,
    M: Extensional<Logic> + ?Sized,
    Q: for<'w> View<
            'w,
            Output = Logic::Imply<
                ExtEq<'x, 'y, Logic, M>,
                Logic::Imply<M::In<'x, 'w>, M::In<'y, 'w>>,
            >,
        > + ?Sized,
{
    fn prove<'w>(self) -> Cert<Logic, <Q as View<'w>>::Output> {
        M::in_left_at::<'x, 'y, 'w>()
    }
}
