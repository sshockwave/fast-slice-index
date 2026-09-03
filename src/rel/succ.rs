//! Successor descriptions and their uniqueness theorem.
#![forbid(unsafe_code)]

use core::marker::PhantomData;

use crate::logic::prop::{forall_intro, And, Cert, Deduction, DeductionUpgrade, FirstOrder, Generalise, Iff, Imply, Or, PropLogic, View};
use crate::macros::{pred, thm};
use crate::rel::desc::{Describes, Description, desc_unique_at};
use crate::rel::ext::{ExtEq, Membership};

/// A membership theory's successor vocabulary.
pub trait Successor<Logic>: 'static {
    type Mem: Membership<Logic> + ?Sized;
    type Succ<'s, 'y>;

    /// `s = y ∪ {y} ↔ ∀w. w ∈ s ↔ (w ∈ y ∨ w = y)`.
    fn succ_iff<'s, 'y>() -> Cert<
        Logic,
        Iff<Logic, Self::Succ<'s, 'y>, Describes<'s, Logic, Self::Mem, SuccCond<'y, Logic, Self>>>,
    >
    where
        Logic: And + Imply + Or + FirstOrder;
}

/// `λw. w ∈ y ∨ w = y`.
pub struct SuccCond<'y, Logic, S: ?Sized>(PhantomData<(&'y (), Logic, *const S)>);

impl<'y, Logic, S> Description<Logic> for SuccCond<'y, Logic, S>
where
    Logic: And + FirstOrder + Or,
    S: Successor<Logic> + ?Sized,
{
    type Holds<'w> = Logic::Or<
        <<S as Successor<Logic>>::Mem as Membership<Logic>>::In<'w, 'y>,
        ExtEq<'w, 'y, Logic, <S as Successor<Logic>>::Mem>,
    >;
}

/// `s = succ(y) → t = succ(y) → s = t`, at fixed points.
pub fn unique_at<'y, 's, 't, Logic, S>() -> thm!({ Logic },
    S::Succ::<'s, 'y> >>= S::Succ::<'t, 'y> >>= ExtEq::<'s, 't, Logic, S::Mem>
)
where
    Logic: PropLogic + And + Or + FirstOrder,
    S: Successor<Logic> + ?Sized,
{
    Deduction::<S::Succ::<'s, 'y>, Logic>::scope(|s| {
        Deduction::<S::Succ::<'t, 'y>, _>::scope(|t| {
            let s_desc = s.pipe(Logic::and_left().mp(S::succ_iff::<'s, 'y>()).upgrade()).upgrade();
            let t_desc = t.pipe(Logic::and_left().mp(S::succ_iff::<'t, 'y>()).upgrade().upgrade());
            desc_unique_at::<'s, 't, Logic, S::Mem, SuccCond<'y, Logic, S>>()
                .upgrade().upgrade().mp(s_desc).mp(t_desc)
        })
    })
}

/// Derived theorems valid for every successor vocabulary.
pub trait SuccessorTheorems<Logic>: Successor<Logic>
where
    Logic: PropLogic + And + Or + FirstOrder,
{
    fn unique() -> thm!({ Logic }, ForAll::<'y, 's, 't>(
        Self::Succ::<'s, 'y> >>= Self::Succ::<'t, 'y>
            >>= ExtEq::<'s, 't, Logic, Self::Mem>
    ));
}

impl<Logic, S> SuccessorTheorems<Logic> for S
where
    Logic: PropLogic + And + Or + FirstOrder,
    S: Successor<Logic> + ?Sized,
{
    fn unique() -> thm!({ Logic }, ForAll::<'y, 's, 't>(
        Self::Succ::<'s, 'y> >>= Self::Succ::<'t, 'y>
            >>= ExtEq::<'s, 't, Logic, Self::Mem>
    )) {
        forall_intro(SuccUnique::<Logic, S>(PhantomData))
    }
}

struct SuccUnique<Logic, S: ?Sized>(PhantomData<(Logic, *const S)>);
impl<Logic, S: ?Sized> Clone for SuccUnique<Logic, S> { fn clone(&self) -> Self { Self(PhantomData) } }
impl<Logic, S, Q> Generalise<Logic, Q> for SuccUnique<Logic, S>
where
    Logic: PropLogic + And + Or + FirstOrder,
    S: Successor<Logic> + ?Sized,
    Q: for<'y> View<'y, Output = pred!({ Logic }, ForAll::<'s, 't>(S::Succ::<'s, 'y> >>= S::Succ::<'t, 'y> >>= ExtEq::<'s, 't, Logic, S::Mem>))> + ?Sized,
{
    fn prove<'y>(self) -> Cert<Logic, <Q as View<'y>>::Output> { forall_intro(SuccUnique1::<'y, Logic, S>(PhantomData)) }
}

struct SuccUnique1<'y, Logic, S: ?Sized>(PhantomData<(&'y (), Logic, *const S)>);
impl<'y, Logic, S: ?Sized> Clone for SuccUnique1<'y, Logic, S> { fn clone(&self) -> Self { Self(PhantomData) } }
impl<'y, Logic, S, Q> Generalise<Logic, Q> for SuccUnique1<'y, Logic, S>
where
    Logic: PropLogic + And + Or + FirstOrder,
    S: Successor<Logic> + ?Sized,
    Q: for<'s> View<'s, Output = pred!({ Logic }, ForAll::<'t>(S::Succ::<'s, 'y> >>= S::Succ::<'t, 'y> >>= ExtEq::<'s, 't, Logic, S::Mem>))> + ?Sized,
{
    fn prove<'s>(self) -> Cert<Logic, <Q as View<'s>>::Output> { forall_intro(SuccUnique2::<'y, 's, Logic, S>(PhantomData)) }
}

struct SuccUnique2<'y, 's, Logic, S: ?Sized>(PhantomData<(&'y (), &'s (), Logic, *const S)>);
impl<'y, 's, Logic, S: ?Sized> Clone for SuccUnique2<'y, 's, Logic, S> { fn clone(&self) -> Self { Self(PhantomData) } }
impl<'y, 's, Logic, S, Q> Generalise<Logic, Q> for SuccUnique2<'y, 's, Logic, S>
where
    Logic: PropLogic + And + Or + FirstOrder,
    S: Successor<Logic> + ?Sized,
    Q: for<'t> View<'t, Output = pred!({ Logic }, S::Succ::<'s, 'y> >>= S::Succ::<'t, 'y> >>= ExtEq::<'s, 't, Logic, S::Mem>)> + ?Sized,
{
    fn prove<'t>(self) -> Cert<Logic, <Q as View<'t>>::Output> {
        unique_at::<'y, 's, 't, Logic, S>()
    }
}
