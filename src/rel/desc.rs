//! Sets named by a condition.
//!
//! Most of the vocabulary of set theory is *descriptions*: `{a,b}` is not a
//! primitive but the set whose members are exactly those `z` with `z = a ∨
//! z = b`, and `y ∪ {y}` is the one with `w ∈ y ∨ w = y`. An axiom says such a
//! set exists; nothing in the axiom says it is the only one.
//!
//! That second half is [`desc_unique`], and it is proved once here rather than
//! once per notion. Its proof never inspects the condition — two sets with the
//! same membership condition share their members, and sharing members is what
//! [`ExtEq`] *is* — so the condition can stay an opaque [`Description`].

use ::core::marker::PhantomData;

use crate::logic::prop::{
    And, Cert, FirstOrder, ForAllProof, Generalise, Iff, PropLogic, View, and_comm, and_map, curry,
    forall_intro, iff_trans, syllogism,
};
use crate::macros::{pred, thm};
use crate::rel::ext::{ExtEq, ExtView, Membership};

/// A condition on one element, as a type-level predicate.
///
/// The parameters a notion takes — the `a` and `b` of `{a,b}` — live on the
/// implementing type, so `Holds` is a predicate in one free variable, which is
/// all [`desc_unique`] needs.
pub trait Description<Logic> {
    /// `D(z)`
    type Holds<'z>;
}

/// `λz. z ∈ s ↔ D(z)` — the body of [`Describes`].
pub type DescView<'s, Logic, M, D> = dyn for<'z> View<
        'z,
        Output = Iff<
            Logic,
            <M as Membership<Logic>>::In<'z, 's>,
            <D as Description<Logic>>::Holds<'z>,
        >,
    > + 'static;

/// `Describes(s) := ∀z. (z ∈ s ↔ D(z))`, i.e. `s` is *the* set of `D`s.
pub type Describes<'s, Logic, M, D> = <Logic as FirstOrder>::ForAll<DescView<'s, Logic, M, D>>;

/// `Describes(p) → Describes(q) → p = q`, at fixed points.
///
/// The hypotheses are taken as the parameters `E1` and `E2` rather than
/// written as `ForAll<DescView<..>>`: naming a nested `dyn for<..> View<..>`
/// in an impl header loses the boundness of its lifetime, and this is passed
/// straight to one.
pub fn desc_unique_at<'p, 'q, Logic, M, D>() -> Cert<
    Logic,
    pred!(
        { Logic },
        Describes::<'p, Logic, M, D>
            >>= Describes::<'q, Logic, M, D>
            >>= ExtEq::<'p, 'q, Logic, M>
    ),
>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
{
    curry().mp(Logic::forall_gen(DescUnique2::<
        'p,
        'q,
        Logic,
        M,
        D,
        DescView<'p, Logic, M, D>,
        DescView<'q, Logic, M, D>,
    >(PhantomData)))
}

/// `λq. Describes(p) → Describes(q) → p = q`
pub type DescUniqueView<'p, Logic, M, D> = dyn for<'q> View<
        'q,
        Output = pred!(
            { Logic },
            Describes::<'p, Logic, M, D>
                >>= Describes::<'q, Logic, M, D>
                >>= ExtEq::<'p, 'q, Logic, M>
        ),
    > + 'static;
/// `λp. ∀q. …`
pub type DescUniqueView1<Logic, M, D> = dyn for<'p> View<
        'p,
        Output = <Logic as FirstOrder>::ForAll<DescUniqueView<'p, Logic, M, D>>,
    > + 'static;

/// `∀p ∀q. Describes(p) → Describes(q) → p = q` — **proved**, no axiom.
///
/// A description determines its set. The companion to whichever axiom asserts
/// the set exists; between them the notion is pinned down.
pub fn desc_unique<Logic, M, D>() -> thm!(
    { Logic },
    ForAll::<'p, 'q>(
        Describes::<'p, Logic, M, D>
            >>= Describes::<'q, Logic, M, D>
            >>= ExtEq::<'p, 'q, Logic, M>
    )
)
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
{
    forall_intro(DescUnique::<Logic, M, D>(PhantomData))
}

macro_rules! unit_clone {
    ($name:ident<$($lt:lifetime),*> $(, $view:ident)*) => {
        impl<$($lt,)* Logic, M: ?Sized, D: ?Sized $(, $view: ?Sized)*> Clone
            for $name<$($lt,)* Logic, M, D $(, $view)*>
        {
            fn clone(&self) -> Self {
                $name(PhantomData)
            }
        }
    };
}

struct DescUnique<Logic, M: ?Sized, D: ?Sized>(PhantomData<(Logic, *const M, *const D)>);
unit_clone!(DescUnique<>);

impl<Logic, M, D, Q> Generalise<Logic, Q> for DescUnique<Logic, M, D>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
    Q: for<'p> View<'p, Output = Logic::ForAll<DescUniqueView<'p, Logic, M, D>>> + ?Sized,
{
    fn prove<'p>(self) -> Cert<Logic, <Q as View<'p>>::Output> {
        forall_intro::<Logic, DescUniqueView<'p, Logic, M, D>, _>(DescUnique1::<'p, Logic, M, D>(
            PhantomData,
        ))
    }
}

struct DescUnique1<'p, Logic, M: ?Sized, D: ?Sized>(
    PhantomData<(&'p (), Logic, *const M, *const D)>,
);
unit_clone!(DescUnique1<'p>);

impl<'p, Logic, M, D, Q> Generalise<Logic, Q> for DescUnique1<'p, Logic, M, D>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
    Q: for<'q> View<
            'q,
            Output = pred!(
                { Logic },
                Describes::<'p, Logic, M, D>
                    >>= Describes::<'q, Logic, M, D>
                    >>= ExtEq::<'p, 'q, Logic, M>
            ),
        > + ?Sized,
{
    fn prove<'q>(self) -> Cert<Logic, <Q as View<'q>>::Output> {
        desc_unique_at::<'p, 'q, Logic, M, D>()
    }
}

/// Both hypotheses at once, as `E1 ∧ E2`, so that [`curry`] can peel them
/// apart after the quantifier is introduced.
struct DescUnique2<'p, 'q, Logic, M: ?Sized, D: ?Sized, E1: ?Sized, E2: ?Sized>(
    PhantomData<(
        &'p (),
        &'q (),
        Logic,
        *const M,
        *const D,
        *const E1,
        *const E2,
    )>,
);
unit_clone!(DescUnique2<'p, 'q>, E1, E2);

impl<'p, 'q, Logic, M, D, E1, E2, Q>
    ForAllProof<Logic, Logic::And<Logic::ForAll<E1>, Logic::ForAll<E2>>, Q>
    for DescUnique2<'p, 'q, Logic, M, D, E1, E2>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
    E1: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'p>, D::Holds<'z>>> + ?Sized,
    E2: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'q>, D::Holds<'z>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 'p>, M::In<'z, 'q>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<
        Logic,
        Logic::Imply<
            Logic::And<Logic::ForAll<E1>, Logic::ForAll<E2>>,
            <Q as View<'z>>::Output,
        >,
    > {
        // (z∈p ↔ D) and (z∈q ↔ D) give (z∈p ↔ D) and (D ↔ z∈q), which compose.
        syllogism()
            .mp(and_map(
                Logic::forall_elim::<'z, E1>(),
                syllogism().mp(Logic::forall_elim::<'z, E2>()).mp(and_comm()),
            ))
            .mp(iff_trans())
    }
}

/// The conclusion of [`desc_unique_at`] is [`ExtEq`], which is `∀z. z ∈ p ↔
/// z ∈ q`; [`DescUnique2`] proves that body pointwise. Typechecking this
/// witnesses that the two spellings agree.
#[expect(dead_code, reason = "typecheck-only proof assertion")]
fn ext_eq_is_shared_membership<'p, 'q, Logic, M>(
    c: Cert<Logic, <Logic as FirstOrder>::ForAll<ExtView<'p, 'q, Logic, M>>>,
) -> Cert<Logic, ExtEq<'p, 'q, Logic, M>>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
{
    c
}
