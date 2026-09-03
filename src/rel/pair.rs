//! Singleton and unordered-pair descriptions.
//!
//! The ambient theory owns the spelling of `s = {a}` and `p = {a,b}`.  This
//! module only needs their one-level membership descriptions, so it keeps both
//! notions opaque behind [`Pairing`].  That prevents a concrete pair encoding
//! from being expanded throughout the quantified proof terms.
#![forbid(unsafe_code)]

use core::marker::PhantomData;

use crate::logic::prop::{
    forall_intro, or_idem, syllogism, And, Cert, Deduction, DeductionUpgrade, FirstOrder,
    Generalise, Iff, Imply, Or, PropLogic, View, and_comm,
};
use crate::rel::desc::{Describes, Description, desc_intro_at, desc_unique_at};
use crate::rel::desc::{SameAs, desc_congr_at, desc_elim_at};
use crate::rel::eq::ClosedEq;
use crate::rel::ext::{Ext, ExtEq, ExtReflView, Membership};
use crate::macros::{pred, thm};

/// The singleton and unordered-pair notions of a membership theory.
///
/// Each unfolding exposes only the defining membership condition.  The
/// derived proofs below therefore mention rigid associated-type projections
/// rather than a theory's concrete definitions.
pub trait Pairing<Logic>: 'static {
    /// The membership relation whose equality is used in these descriptions.
    type Mem: Membership<Logic> + ?Sized;

    /// `s = {a}`.
    type Singleton<'s, 'a>;
    /// `p = {a,b}`.
    type Pair<'p, 'a, 'b>;

    /// `s = {a} ↔ ∀z. (z ∈ s ↔ z = a)`.
    fn singleton_iff<'s, 'a>() -> Cert<
        Logic,
        Iff<
            Logic,
            Self::Singleton<'s, 'a>,
            Describes<'s, Logic, Self::Mem, SingletonCond<'a, Logic, Self>>,
        >,
    >
    where
        Logic: And + Imply + FirstOrder;

    /// `p = {a,b} ↔ ∀z. (z ∈ p ↔ (z = a ∨ z = b))`.
    fn pair_iff<'p, 'a, 'b>() -> Cert<
        Logic,
        Iff<
            Logic,
            Self::Pair<'p, 'a, 'b>,
            Describes<'p, Logic, Self::Mem, PairCond<'a, 'b, Logic, Self>>,
        >,
    >
    where
        Logic: And + Imply + Or + FirstOrder;
}

type PairAt<'p, 'a, 'b, Logic, P> = <P as Pairing<Logic>>::Pair<'p, 'a, 'b>;
type SingletonAt<'s, 'a, Logic, P> = <P as Pairing<Logic>>::Singleton<'s, 'a>;
type MemberAt<'a, 'b, Logic, P> =
    <<P as Pairing<Logic>>::Mem as Membership<Logic>>::In<'a, 'b>;

/// `λz. z = a`, the condition that describes a singleton.
pub struct SingletonCond<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);

impl<'a, Logic, P> Description<Logic> for SingletonCond<'a, Logic, P>
where
    Logic: And + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    type Holds<'z> = ExtEq<'z, 'a, Logic, <P as Pairing<Logic>>::Mem>;
}

/// `λz. z = a ∨ z = b`, the condition that describes an unordered pair.
pub struct PairCond<'a, 'b, Logic, P: ?Sized>(PhantomData<(&'a (), &'b (), Logic, *const P)>);

impl<'a, 'b, Logic, P> Description<Logic> for PairCond<'a, 'b, Logic, P>
where
    Logic: And + FirstOrder + Or,
    P: Pairing<Logic> + ?Sized,
{
    type Holds<'z> = Logic::Or<
        ExtEq<'z, 'a, Logic, <P as Pairing<Logic>>::Mem>,
        ExtEq<'z, 'b, Logic, <P as Pairing<Logic>>::Mem>,
    >;
}

impl<'a, Logic, P> SameAs<Logic, PairCond<'a, 'a, Logic, P>>
    for SingletonCond<'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    fn iff_at<'z>() -> Cert<Logic, Iff<Logic, ExtEq<'z, 'a, Logic, P::Mem>, Logic::Or<ExtEq<'z, 'a, Logic, P::Mem>, ExtEq<'z, 'a, Logic, P::Mem>>>> {
        or_idem::<ExtEq<'z, 'a, Logic, P::Mem>, Logic>()
    }
}

impl<'a, Logic, P> SameAs<Logic, SingletonCond<'a, Logic, P>>
    for PairCond<'a, 'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    fn iff_at<'z>() -> Cert<Logic, Iff<Logic, Logic::Or<ExtEq<'z, 'a, Logic, P::Mem>, ExtEq<'z, 'a, Logic, P::Mem>>, ExtEq<'z, 'a, Logic, P::Mem>>> {
        and_comm().mp(or_idem::<ExtEq<'z, 'a, Logic, P::Mem>, Logic>())
    }
}

fn pair_describes_at<'p, 'a, 'b, Logic, P>() -> Cert<
    Logic,
    <Logic as crate::logic::prop::Imply>::Imply<PairAt<'p, 'a, 'b, Logic, P>, Describes<'p, Logic, <P as Pairing<Logic>>::Mem, PairCond<'a, 'b, Logic, P>>>,
>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    Logic::and_left().mp(P::pair_iff::<'p, 'a, 'b>())
}

fn singleton_describes_at<'s, 'a, Logic, P>() -> Cert<
    Logic,
    <Logic as crate::logic::prop::Imply>::Imply<SingletonAt<'s, 'a, Logic, P>, Describes<'s, Logic, <P as Pairing<Logic>>::Mem, SingletonCond<'a, Logic, P>>>,
>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    Logic::and_left().mp(P::singleton_iff::<'s, 'a>())
}

fn eq_refl_at<'x, Logic, P>() -> Cert<Logic, ExtEq<'x, 'x, Logic, <P as Pairing<Logic>>::Mem>>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    <Ext<Logic, <P as Pairing<Logic>>::Mem> as ClosedEq<Logic>>::refl()
        .pipe(Logic::forall_elim::<'x, ExtReflView<Logic, <P as Pairing<Logic>>::Mem>>())
}

/// `p = {a,b} → c ∈ p`, when `c = a ∨ c = b`.
pub fn pair_member_at<'a, 'b, 'c, 'p, Logic, P>(
    side: Cert<Logic, Logic::Or<ExtEq<'c, 'a, Logic, <P as Pairing<Logic>>::Mem>, ExtEq<'c, 'b, Logic, <P as Pairing<Logic>>::Mem>>>,
) -> Cert<Logic, <Logic as crate::logic::prop::Imply>::Imply<PairAt<'p, 'a, 'b, Logic, P>, <<P as Pairing<Logic>>::Mem as Membership<Logic>>::In<'c, 'p>>>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    syllogism()
        .mp(pair_describes_at::<'p, 'a, 'b, Logic, P>())
        .mp(desc_intro_at::<
            'p,
            'c,
            Logic,
            <P as Pairing<Logic>>::Mem,
            PairCond<'a, 'b, Logic, P>,
        >(side))
}

/// `s = {a} → a ∈ s`.
pub fn singleton_member_at<'a, 's, Logic, P>(
) -> Cert<Logic, <Logic as crate::logic::prop::Imply>::Imply<SingletonAt<'s, 'a, Logic, P>, <<P as Pairing<Logic>>::Mem as Membership<Logic>>::In<'a, 's>>>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    syllogism()
        .mp(singleton_describes_at::<'s, 'a, Logic, P>())
        .mp(desc_intro_at::<
            's,
            'a,
            Logic,
            <P as Pairing<Logic>>::Mem,
            SingletonCond<'a, Logic, P>,
        >(eq_refl_at::<'a, Logic, P>()))
}

fn singleton_is_pair_at<'a, 's, Logic, P>() -> thm!(
    { Logic },
    SingletonAt::<'s, 'a, Logic, P> >>= PairAt::<'s, 'a, 'a, Logic, P>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    syllogism()
        .mp(singleton_describes_at::<'s, 'a, Logic, P>())
        .mp(syllogism()
            .mp(desc_congr_at::<'s, Logic, P::Mem, SingletonCond<'a, Logic, P>, PairCond<'a, 'a, Logic, P>>())
            .mp(Logic::and_right().mp(P::pair_iff::<'s, 'a, 'a>())))
}

fn pair_is_singleton_at<'a, 's, Logic, P>() -> thm!(
    { Logic },
    PairAt::<'s, 'a, 'a, Logic, P> >>= SingletonAt::<'s, 'a, Logic, P>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    syllogism()
        .mp(pair_describes_at::<'s, 'a, 'a, Logic, P>())
        .mp(syllogism()
            .mp(desc_congr_at::<'s, Logic, P::Mem, PairCond<'a, 'a, Logic, P>, SingletonCond<'a, Logic, P>>())
            .mp(Logic::and_right().mp(P::singleton_iff::<'s, 'a>())))
}

fn singleton_injective_at<'a, 'c, 's, Logic, P>() -> thm!(
    { Logic },
    SingletonAt::<'s, 'a, Logic, P> >>= SingletonAt::<'s, 'c, Logic, P>
        >>= ExtEq::<'a, 'c, Logic, P::Mem>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    Deduction::<SingletonAt<'s, 'a, Logic, P>, Logic>::scope(|sa| {
        Deduction::<SingletonAt<'s, 'c, Logic, P>, _>::scope(|sc| {
            let a_in_s = sa.upgrade().pipe(singleton_member_at::<'a, 's, Logic, P>().upgrade().upgrade());
            let sc_desc = sc.pipe(singleton_describes_at::<'s, 'c, Logic, P>().upgrade().upgrade());
            let to_c = sc_desc.pipe(desc_elim_at::<'s, 'a, Logic, P::Mem, SingletonCond<'c, Logic, P>>().upgrade().upgrade());
            a_in_s.pipe(to_c)
        })
    })
}

fn pair_collapses_at<'a, 'b, 'p, Logic, P>() -> thm!(
    { Logic },
    PairAt::<'p, 'a, 'b, Logic, P> >>= SingletonAt::<'p, 'a, Logic, P>
        >>= ExtEq::<'b, 'a, Logic, P::Mem>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    Deduction::<PairAt<'p, 'a, 'b, Logic, P>, Logic>::scope(|pab| {
        Deduction::<SingletonAt<'p, 'a, Logic, P>, _>::scope(|pa| {
            let b_in_p = pab.upgrade().pipe(pair_member_at::<'a, 'b, 'b, 'p, Logic, P>(Logic::or_right().mp(eq_refl_at::<'b, Logic, P>())).upgrade().upgrade());
            let pa_desc = pa.pipe(singleton_describes_at::<'p, 'a, Logic, P>().upgrade().upgrade());
            let to_a = pa_desc.pipe(desc_elim_at::<'p, 'b, Logic, P::Mem, SingletonCond<'a, Logic, P>>().upgrade().upgrade());
            b_in_p.pipe(to_a)
        })
    })
}

fn pair_unique_at<'a, 'b, 'p, 'q, Logic, P>() -> thm!(
    { Logic },
    PairAt::<'p, 'a, 'b, Logic, P>
        >>= PairAt::<'q, 'a, 'b, Logic, P>
        >>= ExtEq::<'p, 'q, Logic, <P as Pairing<Logic>>::Mem>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    Deduction::<PairAt<'p, 'a, 'b, Logic, P>, Logic>::scope(|p| {
        Deduction::<PairAt<'q, 'a, 'b, Logic, P>, _>::scope(|q| {
            let p_desc = p.pipe(pair_describes_at::<'p, 'a, 'b, Logic, P>().upgrade()).upgrade();
            let q_desc = q.pipe(pair_describes_at::<'q, 'a, 'b, Logic, P>().upgrade().upgrade());
            desc_unique_at::<'p, 'q, Logic, <P as Pairing<Logic>>::Mem, PairCond<'a, 'b, Logic, P>>()
                .upgrade()
                .upgrade()
                .mp(p_desc)
                .mp(q_desc)
        })
    })
}

fn singleton_unique_at<'a, 's, 't, Logic, P>() -> thm!(
    { Logic },
    SingletonAt::<'s, 'a, Logic, P>
        >>= SingletonAt::<'t, 'a, Logic, P>
        >>= ExtEq::<'s, 't, Logic, <P as Pairing<Logic>>::Mem>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    Deduction::<SingletonAt<'s, 'a, Logic, P>, Logic>::scope(|s| {
        Deduction::<SingletonAt<'t, 'a, Logic, P>, _>::scope(|t| {
            let s_desc = s.pipe(singleton_describes_at::<'s, 'a, Logic, P>().upgrade()).upgrade();
            let t_desc = t.pipe(singleton_describes_at::<'t, 'a, Logic, P>().upgrade().upgrade());
            desc_unique_at::<'s, 't, Logic, <P as Pairing<Logic>>::Mem, SingletonCond<'a, Logic, P>>()
                .upgrade()
                .upgrade()
                .mp(s_desc)
                .mp(t_desc)
        })
    })
}

macro_rules! unit_clone {
    ($name:ident<$($lt:lifetime),*>) => {
        impl<$($lt,)* Logic, P: ?Sized> Clone for $name<$($lt,)* Logic, P> {
            fn clone(&self) -> Self {
                $name(PhantomData)
            }
        }
    };
}

/// `∀a ∀b ∀p. p = {a,b} → a ∈ p`.
fn prove_pair_left<Logic, P>() -> thm!(
    { Logic },
    ForAll::<'a, 'b, 'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= MemberAt::<'a, 'p, Logic, P>)
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    forall_intro(PairLeft::<Logic, P>(PhantomData))
}

struct PairLeft<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(PairLeft<>);

impl<Logic, P, Q> Generalise<Logic, Q> for PairLeft<Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'b, 'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= MemberAt::<'a, 'p, Logic, P>))> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro(PairLeft1::<'a, Logic, P>(PhantomData))
    }
}

struct PairLeft1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(PairLeft1<'a>);

impl<'a, Logic, P, Q> Generalise<Logic, Q> for PairLeft1<'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = pred!({ Logic }, ForAll::<'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= MemberAt::<'a, 'p, Logic, P>))> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, <Q as View<'b>>::Output> {
        forall_intro(PairLeft2::<'a, 'b, Logic, P>(PhantomData))
    }
}

struct PairLeft2<'a, 'b, Logic, P: ?Sized>(PhantomData<(&'a (), &'b (), Logic, *const P)>);
unit_clone!(PairLeft2<'a, 'b>);

impl<'a, 'b, Logic, P, Q> Generalise<Logic, Q> for PairLeft2<'a, 'b, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'p> View<'p, Output = <Logic as crate::logic::prop::Imply>::Imply<PairAt<'p, 'a, 'b, Logic, P>, MemberAt<'a, 'p, Logic, P>>> + ?Sized,
{
    fn prove<'p>(self) -> Cert<Logic, <Q as View<'p>>::Output> {
        pair_member_at::<'a, 'b, 'a, 'p, Logic, P>(
            Logic::or_left().mp(eq_refl_at::<'a, Logic, P>()),
        )
    }
}

/// `∀a ∀b ∀p. p = {a,b} → b ∈ p`.
fn prove_pair_right<Logic, P>() -> thm!(
    { Logic },
    ForAll::<'a, 'b, 'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= MemberAt::<'b, 'p, Logic, P>)
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    forall_intro(PairRight::<Logic, P>(PhantomData))
}

struct PairRight<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(PairRight<>);

impl<Logic, P, Q> Generalise<Logic, Q> for PairRight<Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'b, 'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= MemberAt::<'b, 'p, Logic, P>))> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro(PairRight1::<'a, Logic, P>(PhantomData))
    }
}

struct PairRight1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(PairRight1<'a>);

impl<'a, Logic, P, Q> Generalise<Logic, Q> for PairRight1<'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = pred!({ Logic }, ForAll::<'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= MemberAt::<'b, 'p, Logic, P>))> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, <Q as View<'b>>::Output> {
        forall_intro(PairRight2::<'a, 'b, Logic, P>(PhantomData))
    }
}

struct PairRight2<'a, 'b, Logic, P: ?Sized>(PhantomData<(&'a (), &'b (), Logic, *const P)>);
unit_clone!(PairRight2<'a, 'b>);

impl<'a, 'b, Logic, P, Q> Generalise<Logic, Q> for PairRight2<'a, 'b, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'p> View<'p, Output = <Logic as crate::logic::prop::Imply>::Imply<PairAt<'p, 'a, 'b, Logic, P>, MemberAt<'b, 'p, Logic, P>>> + ?Sized,
{
    fn prove<'p>(self) -> Cert<Logic, <Q as View<'p>>::Output> {
        pair_member_at::<'a, 'b, 'b, 'p, Logic, P>(
            Logic::or_right().mp(eq_refl_at::<'b, Logic, P>()),
        )
    }
}

/// `∀a ∀s. s = {a} → a ∈ s`.
fn prove_singleton_member<Logic, P>() -> thm!(
    { Logic },
    ForAll::<'a, 's>(SingletonAt::<'s, 'a, Logic, P> >>= MemberAt::<'a, 's, Logic, P>)
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    forall_intro(SingletonMember::<Logic, P>(PhantomData))
}

struct SingletonMember<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(SingletonMember<>);

impl<Logic, P, Q> Generalise<Logic, Q> for SingletonMember<Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'s>(SingletonAt::<'s, 'a, Logic, P> >>= MemberAt::<'a, 's, Logic, P>))> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro(SingletonMember1::<'a, Logic, P>(PhantomData))
    }
}

struct SingletonMember1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(SingletonMember1<'a>);

impl<'a, Logic, P, Q> Generalise<Logic, Q> for SingletonMember1<'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'s> View<'s, Output = <Logic as crate::logic::prop::Imply>::Imply<SingletonAt<'s, 'a, Logic, P>, MemberAt<'a, 's, Logic, P>>> + ?Sized,
{
    fn prove<'s>(self) -> Cert<Logic, <Q as View<'s>>::Output> {
        singleton_member_at::<'a, 's, Logic, P>()
    }
}

/// Derived pair and singleton theorems over an opaque pairing vocabulary.
///
/// The blanket implementation keeps proof terms generic while `thm!` states
/// each quantified result without naming concrete view aliases.
pub trait PairingTheorems<Logic>: Pairing<Logic>
where
    Logic: PropLogic + And + Or + FirstOrder,
{
    fn pair_left() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'p>(PairAt::<'p, 'a, 'b, Logic, Self> >>= MemberAt::<'a, 'p, Logic, Self>)
    );

    fn pair_right() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'p>(PairAt::<'p, 'a, 'b, Logic, Self> >>= MemberAt::<'b, 'p, Logic, Self>)
    );

    fn singleton_member() -> thm!(
        { Logic },
        ForAll::<'a, 's>(SingletonAt::<'s, 'a, Logic, Self> >>= MemberAt::<'a, 's, Logic, Self>)
    );

    fn pair_unique() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'p, 'q>(
            PairAt::<'p, 'a, 'b, Logic, Self>
                >>= PairAt::<'q, 'a, 'b, Logic, Self>
                >>= ExtEq::<'p, 'q, Logic, Self::Mem>
        )
    );

    fn singleton_unique() -> thm!(
        { Logic },
        ForAll::<'a, 's, 't>(
            SingletonAt::<'s, 'a, Logic, Self>
                >>= SingletonAt::<'t, 'a, Logic, Self>
                >>= ExtEq::<'s, 't, Logic, Self::Mem>
        )
    );

    fn singleton_is_pair() -> thm!({ Logic }, ForAll::<'a, 's>(
        SingletonAt::<'s, 'a, Logic, Self> >>= PairAt::<'s, 'a, 'a, Logic, Self>
    ));

    fn pair_is_singleton() -> thm!({ Logic }, ForAll::<'a, 's>(
        PairAt::<'s, 'a, 'a, Logic, Self> >>= SingletonAt::<'s, 'a, Logic, Self>
    ));

    fn singleton_injective() -> thm!({ Logic }, ForAll::<'a, 'c, 's>(
        SingletonAt::<'s, 'a, Logic, Self> >>= SingletonAt::<'s, 'c, Logic, Self>
            >>= ExtEq::<'a, 'c, Logic, Self::Mem>
    ));

    fn pair_collapses() -> thm!({ Logic }, ForAll::<'a, 'b, 'p>(
        PairAt::<'p, 'a, 'b, Logic, Self> >>= SingletonAt::<'p, 'a, Logic, Self>
            >>= ExtEq::<'b, 'a, Logic, Self::Mem>
    ));
}

impl<Logic, P> PairingTheorems<Logic> for P
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
{
    fn pair_left() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'p>(PairAt::<'p, 'a, 'b, Logic, Self> >>= MemberAt::<'a, 'p, Logic, Self>)
    ) {
        prove_pair_left::<Logic, P>()
    }

    fn pair_right() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'p>(PairAt::<'p, 'a, 'b, Logic, Self> >>= MemberAt::<'b, 'p, Logic, Self>)
    ) {
        prove_pair_right::<Logic, P>()
    }

    fn singleton_member() -> thm!(
        { Logic },
        ForAll::<'a, 's>(SingletonAt::<'s, 'a, Logic, Self> >>= MemberAt::<'a, 's, Logic, Self>)
    ) {
        prove_singleton_member::<Logic, P>()
    }

    fn pair_unique() -> thm!(
        { Logic },
        ForAll::<'a, 'b, 'p, 'q>(
            PairAt::<'p, 'a, 'b, Logic, Self>
                >>= PairAt::<'q, 'a, 'b, Logic, Self>
                >>= ExtEq::<'p, 'q, Logic, Self::Mem>
        )
    ) {
        forall_intro(ProvePairUnique::<Logic, P>(PhantomData))
    }

    fn singleton_unique() -> thm!(
        { Logic },
        ForAll::<'a, 's, 't>(
            SingletonAt::<'s, 'a, Logic, Self>
                >>= SingletonAt::<'t, 'a, Logic, Self>
                >>= ExtEq::<'s, 't, Logic, Self::Mem>
        )
    ) {
        forall_intro(ProveSingletonUnique::<Logic, P>(PhantomData))
    }

    fn singleton_is_pair() -> thm!({ Logic }, ForAll::<'a, 's>(
        SingletonAt::<'s, 'a, Logic, Self> >>= PairAt::<'s, 'a, 'a, Logic, Self>
    )) { forall_intro(SingletonIsPair::<Logic, P>(PhantomData)) }

    fn pair_is_singleton() -> thm!({ Logic }, ForAll::<'a, 's>(
        PairAt::<'s, 'a, 'a, Logic, Self> >>= SingletonAt::<'s, 'a, Logic, Self>
    )) { forall_intro(PairIsSingleton::<Logic, P>(PhantomData)) }

    fn singleton_injective() -> thm!({ Logic }, ForAll::<'a, 'c, 's>(
        SingletonAt::<'s, 'a, Logic, Self> >>= SingletonAt::<'s, 'c, Logic, Self>
            >>= ExtEq::<'a, 'c, Logic, Self::Mem>
    )) { forall_intro(SingletonInjective::<Logic, P>(PhantomData)) }

    fn pair_collapses() -> thm!({ Logic }, ForAll::<'a, 'b, 'p>(
        PairAt::<'p, 'a, 'b, Logic, Self> >>= SingletonAt::<'p, 'a, Logic, Self>
            >>= ExtEq::<'b, 'a, Logic, Self::Mem>
    )) { forall_intro(PairCollapses::<Logic, P>(PhantomData)) }
}

struct SingletonIsPair<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(SingletonIsPair<>);
impl<Logic, P, Q> Generalise<Logic, Q> for SingletonIsPair<Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'s>(SingletonAt::<'s, 'a, Logic, P> >>= PairAt::<'s, 'a, 'a, Logic, P>))> + ?Sized,
{ fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> { forall_intro(SingletonIsPair1::<'a, Logic, P>(PhantomData)) } }
struct SingletonIsPair1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(SingletonIsPair1<'a>);
impl<'a, Logic, P, Q> Generalise<Logic, Q> for SingletonIsPair1<'a, Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'s> View<'s, Output = pred!({ Logic }, SingletonAt::<'s, 'a, Logic, P> >>= PairAt::<'s, 'a, 'a, Logic, P>)> + ?Sized,
{ fn prove<'s>(self) -> Cert<Logic, <Q as View<'s>>::Output> { singleton_is_pair_at::<'a, 's, Logic, P>() } }

struct PairIsSingleton<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(PairIsSingleton<>);
impl<Logic, P, Q> Generalise<Logic, Q> for PairIsSingleton<Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'s>(PairAt::<'s, 'a, 'a, Logic, P> >>= SingletonAt::<'s, 'a, Logic, P>))> + ?Sized,
{ fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> { forall_intro(PairIsSingleton1::<'a, Logic, P>(PhantomData)) } }
struct PairIsSingleton1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(PairIsSingleton1<'a>);
impl<'a, Logic, P, Q> Generalise<Logic, Q> for PairIsSingleton1<'a, Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'s> View<'s, Output = pred!({ Logic }, PairAt::<'s, 'a, 'a, Logic, P> >>= SingletonAt::<'s, 'a, Logic, P>)> + ?Sized,
{ fn prove<'s>(self) -> Cert<Logic, <Q as View<'s>>::Output> { pair_is_singleton_at::<'a, 's, Logic, P>() } }

struct SingletonInjective<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(SingletonInjective<>);
impl<Logic, P, Q> Generalise<Logic, Q> for SingletonInjective<Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'c, 's>(SingletonAt::<'s, 'a, Logic, P> >>= SingletonAt::<'s, 'c, Logic, P> >>= ExtEq::<'a, 'c, Logic, P::Mem>))> + ?Sized,
{ fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> { forall_intro(SingletonInjective1::<'a, Logic, P>(PhantomData)) } }
struct SingletonInjective1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(SingletonInjective1<'a>);
impl<'a, Logic, P, Q> Generalise<Logic, Q> for SingletonInjective1<'a, Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'c> View<'c, Output = pred!({ Logic }, ForAll::<'s>(SingletonAt::<'s, 'a, Logic, P> >>= SingletonAt::<'s, 'c, Logic, P> >>= ExtEq::<'a, 'c, Logic, P::Mem>))> + ?Sized,
{ fn prove<'c>(self) -> Cert<Logic, <Q as View<'c>>::Output> { forall_intro(SingletonInjective2::<'a, 'c, Logic, P>(PhantomData)) } }
struct SingletonInjective2<'a, 'c, Logic, P: ?Sized>(PhantomData<(&'a (), &'c (), Logic, *const P)>);
unit_clone!(SingletonInjective2<'a, 'c>);
impl<'a, 'c, Logic, P, Q> Generalise<Logic, Q> for SingletonInjective2<'a, 'c, Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'s> View<'s, Output = pred!({ Logic }, SingletonAt::<'s, 'a, Logic, P> >>= SingletonAt::<'s, 'c, Logic, P> >>= ExtEq::<'a, 'c, Logic, P::Mem>)> + ?Sized,
{ fn prove<'s>(self) -> Cert<Logic, <Q as View<'s>>::Output> { singleton_injective_at::<'a, 'c, 's, Logic, P>() } }

struct PairCollapses<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(PairCollapses<>);
impl<Logic, P, Q> Generalise<Logic, Q> for PairCollapses<Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'b, 'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= SingletonAt::<'p, 'a, Logic, P> >>= ExtEq::<'b, 'a, Logic, P::Mem>))> + ?Sized,
{ fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> { forall_intro(PairCollapses1::<'a, Logic, P>(PhantomData)) } }
struct PairCollapses1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(PairCollapses1<'a>);
impl<'a, Logic, P, Q> Generalise<Logic, Q> for PairCollapses1<'a, Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = pred!({ Logic }, ForAll::<'p>(PairAt::<'p, 'a, 'b, Logic, P> >>= SingletonAt::<'p, 'a, Logic, P> >>= ExtEq::<'b, 'a, Logic, P::Mem>))> + ?Sized,
{ fn prove<'b>(self) -> Cert<Logic, <Q as View<'b>>::Output> { forall_intro(PairCollapses2::<'a, 'b, Logic, P>(PhantomData)) } }
struct PairCollapses2<'a, 'b, Logic, P: ?Sized>(PhantomData<(&'a (), &'b (), Logic, *const P)>);
unit_clone!(PairCollapses2<'a, 'b>);
impl<'a, 'b, Logic, P, Q> Generalise<Logic, Q> for PairCollapses2<'a, 'b, Logic, P>
where Logic: PropLogic + And + Or + FirstOrder, P: Pairing<Logic> + ?Sized,
    Q: for<'p> View<'p, Output = pred!({ Logic }, PairAt::<'p, 'a, 'b, Logic, P> >>= SingletonAt::<'p, 'a, Logic, P> >>= ExtEq::<'b, 'a, Logic, P::Mem>)> + ?Sized,
{ fn prove<'p>(self) -> Cert<Logic, <Q as View<'p>>::Output> { pair_collapses_at::<'a, 'b, 'p, Logic, P>() } }

struct ProvePairUnique<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(ProvePairUnique<>);

impl<Logic, P, Q> Generalise<Logic, Q> for ProvePairUnique<Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'b, 'p, 'q>(PairAt::<'p, 'a, 'b, Logic, P> >>= PairAt::<'q, 'a, 'b, Logic, P> >>= ExtEq::<'p, 'q, Logic, P::Mem>))> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro(ProvePairUnique1::<'a, Logic, P>(PhantomData))
    }
}

struct ProvePairUnique1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(ProvePairUnique1<'a>);

impl<'a, Logic, P, Q> Generalise<Logic, Q> for ProvePairUnique1<'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = pred!({ Logic }, ForAll::<'p, 'q>(PairAt::<'p, 'a, 'b, Logic, P> >>= PairAt::<'q, 'a, 'b, Logic, P> >>= ExtEq::<'p, 'q, Logic, P::Mem>))> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, <Q as View<'b>>::Output> {
        forall_intro(ProvePairUnique2::<'a, 'b, Logic, P>(PhantomData))
    }
}

struct ProvePairUnique2<'a, 'b, Logic, P: ?Sized>(PhantomData<(&'a (), &'b (), Logic, *const P)>);
unit_clone!(ProvePairUnique2<'a, 'b>);

impl<'a, 'b, Logic, P, Q> Generalise<Logic, Q> for ProvePairUnique2<'a, 'b, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'p> View<'p, Output = pred!({ Logic }, ForAll::<'q>(PairAt::<'p, 'a, 'b, Logic, P> >>= PairAt::<'q, 'a, 'b, Logic, P> >>= ExtEq::<'p, 'q, Logic, P::Mem>))> + ?Sized,
{
    fn prove<'p>(self) -> Cert<Logic, <Q as View<'p>>::Output> {
        forall_intro(ProvePairUnique3::<'a, 'b, 'p, Logic, P>(PhantomData))
    }
}

struct ProvePairUnique3<'a, 'b, 'p, Logic, P: ?Sized>(PhantomData<(&'a (), &'b (), &'p (), Logic, *const P)>);
unit_clone!(ProvePairUnique3<'a, 'b, 'p>);

impl<'a, 'b, 'p, Logic, P, Q> Generalise<Logic, Q> for ProvePairUnique3<'a, 'b, 'p, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'q> View<'q, Output = Logic::Imply<PairAt<'p, 'a, 'b, Logic, P>, Logic::Imply<PairAt<'q, 'a, 'b, Logic, P>, ExtEq<'p, 'q, Logic, P::Mem>>>> + ?Sized,
{
    fn prove<'q>(self) -> Cert<Logic, <Q as View<'q>>::Output> {
        pair_unique_at::<'a, 'b, 'p, 'q, Logic, P>()
    }
}

struct ProveSingletonUnique<Logic, P: ?Sized>(PhantomData<(Logic, *const P)>);
unit_clone!(ProveSingletonUnique<>);

impl<Logic, P, Q> Generalise<Logic, Q> for ProveSingletonUnique<Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = pred!({ Logic }, ForAll::<'s, 't>(SingletonAt::<'s, 'a, Logic, P> >>= SingletonAt::<'t, 'a, Logic, P> >>= ExtEq::<'s, 't, Logic, P::Mem>))> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro(ProveSingletonUnique1::<'a, Logic, P>(PhantomData))
    }
}

struct ProveSingletonUnique1<'a, Logic, P: ?Sized>(PhantomData<(&'a (), Logic, *const P)>);
unit_clone!(ProveSingletonUnique1<'a>);

impl<'a, Logic, P, Q> Generalise<Logic, Q> for ProveSingletonUnique1<'a, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'s> View<'s, Output = pred!({ Logic }, ForAll::<'t>(SingletonAt::<'s, 'a, Logic, P> >>= SingletonAt::<'t, 'a, Logic, P> >>= ExtEq::<'s, 't, Logic, P::Mem>))> + ?Sized,
{
    fn prove<'s>(self) -> Cert<Logic, <Q as View<'s>>::Output> {
        forall_intro(ProveSingletonUnique2::<'a, 's, Logic, P>(PhantomData))
    }
}

struct ProveSingletonUnique2<'a, 's, Logic, P: ?Sized>(PhantomData<(&'a (), &'s (), Logic, *const P)>);
unit_clone!(ProveSingletonUnique2<'a, 's>);

impl<'a, 's, Logic, P, Q> Generalise<Logic, Q> for ProveSingletonUnique2<'a, 's, Logic, P>
where
    Logic: PropLogic + And + Or + FirstOrder,
    P: Pairing<Logic> + ?Sized,
    Q: for<'t> View<'t, Output = Logic::Imply<SingletonAt<'s, 'a, Logic, P>, Logic::Imply<SingletonAt<'t, 'a, Logic, P>, ExtEq<'s, 't, Logic, P::Mem>>>> + ?Sized,
{
    fn prove<'t>(self) -> Cert<Logic, <Q as View<'t>>::Output> {
        singleton_unique_at::<'a, 's, 't, Logic, P>()
    }
}
