//! The set with nothing in it.
//!
//! Not a [`Description`](crate::rel::desc::Description): the emptiness of `e`
//! is `∀z. z ∉ e`, a negation rather than a biconditional against a condition,
//! so it does not fit that shape on the nose. Its uniqueness is nonetheless the
//! same argument one step shorter — where two descriptions agree because they
//! share a condition, two empty sets agree because neither has a member to
//! disagree about.

use ::core::marker::PhantomData;

use crate::logic::prop::{
    And, Cert, FirstOrder, ForAllProof, Generalise, Intuitionistic, Iff, Negation, PropLogic, View,
    absurd_imply, and_map, curry, forall_intro, syllogism,
};
use crate::macros::{pred, thm};
use crate::rel::ext::{ExtEq, Membership};

/// `λz. z ∉ e` — the body of [`IsEmpty`], named so it can be eliminated.
pub type EmptyView<'e, Logic, M> = dyn for<'z> View<
        'z,
        Output = <Logic as Negation>::Neg<<M as Membership<Logic>>::In<'z, 'e>>,
    > + 'static;

/// `IsEmpty(e) := ∀z. z ∉ e`
pub type IsEmpty<'e, Logic, M> = <Logic as FirstOrder>::ForAll<EmptyView<'e, Logic, M>>;

/// `IsEmpty(x) → IsEmpty(y) → x = y`, at fixed points.
///
/// The two hypotheses arrive as one conjunction so that a single
/// [`FirstOrder::forall_gen`] can introduce the quantifier hidden in [`ExtEq`];
/// [`curry`] peels them apart again afterwards.
pub fn empty_unique_at<'x, 'y, Logic, M>() -> Cert<
    Logic,
    pred!(
        { Logic },
        IsEmpty::<'x, Logic, M> >>= IsEmpty::<'y, Logic, M> >>= ExtEq::<'x, 'y, Logic, M>
    ),
>
where
    Logic: PropLogic + And + FirstOrder + Intuitionistic,
    M: Membership<Logic> + ?Sized,
{
    curry().mp(Logic::forall_gen(EmptyUnique2::<
        'x,
        'y,
        Logic,
        M,
        EmptyView<'x, Logic, M>,
        EmptyView<'y, Logic, M>,
    >(PhantomData)))
}

/// `λy. IsEmpty(x) → IsEmpty(y) → x = y`
pub type EmptyUniqueView<'x, Logic, M> = dyn for<'y> View<
        'y,
        Output = pred!(
            { Logic },
            IsEmpty::<'x, Logic, M> >>= IsEmpty::<'y, Logic, M> >>= ExtEq::<'x, 'y, Logic, M>
        ),
    > + 'static;
/// `λx. ∀y. …`
pub type EmptyUniqueView1<Logic, M> = dyn for<'x> View<
        'x,
        Output = <Logic as FirstOrder>::ForAll<EmptyUniqueView<'x, Logic, M>>,
    > + 'static;

/// `∀x ∀y. IsEmpty(x) → IsEmpty(y) → x = y` — **proved**, no axiom.
///
/// There is at most one empty set, for any membership relation at all.
pub fn empty_unique<Logic, M>() -> thm!(
    { Logic },
    ForAll::<'x, 'y>(
        IsEmpty::<'x, Logic, M> >>= IsEmpty::<'y, Logic, M> >>= ExtEq::<'x, 'y, Logic, M>
    )
)
where
    Logic: PropLogic + And + FirstOrder + Intuitionistic,
    M: Membership<Logic> + ?Sized,
{
    forall_intro(EmptyUnique::<Logic, M>(PhantomData))
}

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

struct EmptyUnique<Logic, M: ?Sized>(PhantomData<(Logic, *const M)>);
unit_clone!(EmptyUnique<>);

impl<Logic, M, Q> Generalise<Logic, Q> for EmptyUnique<Logic, M>
where
    Logic: PropLogic + And + FirstOrder + Intuitionistic,
    M: Membership<Logic> + ?Sized,
    Q: for<'x> View<'x, Output = Logic::ForAll<EmptyUniqueView<'x, Logic, M>>> + ?Sized,
{
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output> {
        forall_intro::<Logic, EmptyUniqueView<'x, Logic, M>, _>(EmptyUnique1::<'x, Logic, M>(
            PhantomData,
        ))
    }
}

struct EmptyUnique1<'x, Logic, M: ?Sized>(PhantomData<(&'x (), Logic, *const M)>);
unit_clone!(EmptyUnique1<'x>);

impl<'x, Logic, M, Q> Generalise<Logic, Q> for EmptyUnique1<'x, Logic, M>
where
    Logic: PropLogic + And + FirstOrder + Intuitionistic,
    M: Membership<Logic> + ?Sized,
    Q: for<'y> View<
            'y,
            Output = pred!(
                { Logic },
                IsEmpty::<'x, Logic, M> >>= IsEmpty::<'y, Logic, M> >>= ExtEq::<'x, 'y, Logic, M>
            ),
        > + ?Sized,
{
    fn prove<'y>(self) -> Cert<Logic, <Q as View<'y>>::Output> {
        empty_unique_at::<'x, 'y, Logic, M>()
    }
}

/// Both emptiness hypotheses at once, for the same reason
/// [`crate::rel::desc`]'s uniqueness proof bundles its two descriptions.
struct EmptyUnique2<'x, 'y, Logic, M: ?Sized, E1: ?Sized, E2: ?Sized>(
    PhantomData<(&'x (), &'y (), Logic, *const M, *const E1, *const E2)>,
);
unit_clone!(EmptyUnique2<'x, 'y>, E1, E2);

impl<'x, 'y, Logic, M, E1, E2, Q> ForAllProof<Logic, Logic::And<Logic::ForAll<E1>, Logic::ForAll<E2>>, Q>
    for EmptyUnique2<'x, 'y, Logic, M, E1, E2>
where
    Logic: PropLogic + And + FirstOrder + Intuitionistic,
    M: Membership<Logic> + ?Sized,
    E1: for<'z> View<'z, Output = Logic::Neg<M::In<'z, 'x>>> + ?Sized,
    E2: for<'z> View<'z, Output = Logic::Neg<M::In<'z, 'y>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'x>, M::In<'z, 'y>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Logic,
        Logic::Imply<Logic::And<Logic::ForAll<E1>, Logic::ForAll<E2>>, <Q as View<'z>>::Output>,
    > {
        // z ∉ x gives z ∈ x → z ∈ y outright, and symmetrically.
        and_map(
            syllogism()
                .mp(Logic::forall_elim::<'z, E1>())
                .mp(absurd_imply::<M::In<'z, 'x>, M::In<'z, 'y>, Logic>()),
            syllogism()
                .mp(Logic::forall_elim::<'z, E2>())
                .mp(absurd_imply::<M::In<'z, 'y>, M::In<'z, 'x>, Logic>()),
        )
    }
}
