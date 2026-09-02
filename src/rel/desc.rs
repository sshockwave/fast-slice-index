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
    forall_intro, iff_extend, iff_trans, syllogism,
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

/// `Describes(s) → D(z) → z ∈ s` — reading the definition right-to-left.
///
/// The evidence `D(z)` is taken as an argument rather than as a hypothesis
/// because the notions instantiating this supply it in different ways: a
/// singleton offers `a = a`, a pair a choice of side.
pub fn desc_intro_at<'s, 'z, Logic, M, D>(
    d: Cert<Logic, D::Holds<'z>>,
) -> Cert<Logic, Logic::Imply<Describes<'s, Logic, M, D>, M::In<'z, 's>>>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
{
    Logic::l2()
        .mp(syllogism()
            .mp(Logic::forall_elim::<'z, DescView<'s, Logic, M, D>>())
            .mp(Logic::and_right()))
        .mp(Logic::l1().mp(d))
}

/// `Describes(s) → z ∈ s → D(z)` — reading it left-to-right.
///
/// The converse of [`desc_intro_at`]: a description says what its set
/// contains, so a member of it satisfies the condition.
pub fn desc_elim_at<'s, 'z, Logic, M, D>()
-> Cert<Logic, Logic::Imply<Describes<'s, Logic, M, D>, Logic::Imply<M::In<'z, 's>, D::Holds<'z>>>>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D: Description<Logic> + ?Sized,
{
    syllogism()
        .mp(Logic::forall_elim::<'z, DescView<'s, Logic, M, D>>())
        .mp(Logic::and_left())
}

/// Two conditions that hold of exactly the same things.
///
/// Stated pointwise, as an obligation rather than a quantified hypothesis, so
/// that [`desc_congr_at`]'s proof term stays a unit struct — the same shape
/// [`Extensional`](crate::rel::ext::Extensional) uses.
pub trait SameAs<Logic, D>: Description<Logic>
where
    Logic: PropLogic + And,
    D: Description<Logic> + ?Sized,
{
    /// `D₁(z) ↔ D₂(z)`
    fn iff_at<'z>() -> Cert<Logic, Iff<Logic, Self::Holds<'z>, D::Holds<'z>>>;
}

/// `Describes(s, D₁) → Describes(s, D₂)`, for conditions that agree pointwise.
///
/// A set is named by *what* its members satisfy, not by how the condition is
/// written, so an equivalent condition describes the same set.
pub fn desc_congr_at<'s, Logic, M, D1, D2>()
-> Cert<Logic, Logic::Imply<Describes<'s, Logic, M, D1>, Describes<'s, Logic, M, D2>>>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D1: SameAs<Logic, D2> + ?Sized,
    D2: Description<Logic> + ?Sized,
{
    Logic::forall_gen(DescCongr::<'s, Logic, M, D1, D2, DescView<'s, Logic, M, D1>>(
        PhantomData,
    ))
}

struct DescCongr<'s, Logic, M: ?Sized, D1: ?Sized, D2: ?Sized, E: ?Sized>(
    PhantomData<(&'s (), Logic, *const M, *const D1, *const D2, *const E)>,
);

impl<'s, Logic, M: ?Sized, D1: ?Sized, D2: ?Sized, E: ?Sized> Clone
    for DescCongr<'s, Logic, M, D1, D2, E>
{
    fn clone(&self) -> Self {
        DescCongr(PhantomData)
    }
}

impl<'s, Logic, M, D1, D2, E, Q> ForAllProof<Logic, Logic::ForAll<E>, Q>
    for DescCongr<'s, Logic, M, D1, D2, E>
where
    Logic: PropLogic + And + FirstOrder,
    M: Membership<Logic> + ?Sized,
    D1: SameAs<Logic, D2> + ?Sized,
    D2: Description<Logic> + ?Sized,
    E: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 's>, D1::Holds<'z>>> + ?Sized,
    Q: for<'z> View<'z, Output = Iff<Logic, M::In<'z, 's>, D2::Holds<'z>>> + ?Sized,
{
    fn prove<'z>(
        self,
    ) -> Cert<Logic, Logic::Imply<Logic::ForAll<E>, <Q as View<'z>>::Output>> {
        // (z∈s ↔ D₁ z), then rewrite the right side with D₁ z ↔ D₂ z.
        syllogism()
            .mp(Logic::forall_elim::<'z, E>())
            .mp(iff_extend(D1::iff_at::<'z>()))
    }
}

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
