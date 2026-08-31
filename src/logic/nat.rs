use std::marker::PhantomData;

use crate::logic::function::{Equality, Function, Injection};
use crate::logic::prop::{And, FirstOrder, Negation, View};
use crate::macros::{pred, thm};
use crate::rel::Set;

macro_rules! expr {
    // Type alias: "x is a natural number"
    // Equivalent to: x ∈ Dom(SuccFn)
    ($x:lifetime in Nat) => {
        <Self::SuccFn as Function<'l, Logic>>::Dom::<$x>
    };
    // Type alias: "x is zero-like"
    // Equivalent to: ∀p∀s. Succ(p,s) → s≠x (no element's successor equals x)
    // Note: doesn't require x to be a natural number
    ($x:lifetime like 0) => {
        pred!(
            'l: { Logic },
            ForAll::<'p>(!<Self::SuccFn as Function<'l, Logic>>::F::<'p, $x>)
        )
    };
    // Type alias: "x is zero"
    // Equivalent to: x is a natural number AND x is zero-like
    ($x:lifetime == 0) => {
        pred!(
            'l: { Logic },
            expr!($x in Nat) && expr!($x like 0)
        )
    }
}

/// Natural numbers trait using function-based approach
///
/// Design:
/// - SuccFn is a Function (and Injection) from ℕ → ℕ
/// - SuccFn::F<'x, 'y> means "y is the successor of x"
/// - SuccFn::Dom and SuccFn::Codom define what counts as a natural number
/// - Zero is defined existentially: ∃z. ∀n∀s. Succ(n,s) → s≠z
/// - Induction uses P as a type parameter (schema) to remain predicative
pub trait NaturalNumbers<'l, Logic>
where
    Logic: FirstOrder<'l> + Equality<'l> + Negation<'l> + And<'l>,
{
    /// Successor function: ℕ → ℕ
    /// An injection from natural numbers to natural numbers
    /// SuccFn::F<'x, 'y> means "y is the successor of x"
    type SuccFn: Function<'l, Logic> + Injection<'l, Logic>;

    /// Zero is defined existentially: ∃z. IsNat(z) ∧ IsZeroLike(z)
    /// "There exists a natural number such that no natural's successor equals it"
    fn zero_exists() -> thm!('l: { Logic }, Exists::<'z>(expr!('z == 0)));

    /// Induction: ∀P. [P(0) ∧ (∀n. n is nat ∧ P(n) → ∀s. Succ(n,s) → P(s))] → ∀n. n is nat → P(n)
    ///
    /// NOTE: P is a type parameter, not a quantified predicate.
    /// We're defining induction for each specific P separately.
    /// This is predicative and avoids Russell's paradox.
    fn induction<P>() -> thm!(
        'l: { Logic },
        'z: { expr!('z == 0) },
        (
            'n: { expr!('n in Nat) },
            Call::<'s> = <Self::SuccFn as Function<'l, Logic>>::F::<'n>,
            <P as View<'n>>::Output.imply(<P as View<'s>>::Output)
        )
            .imply('n: { expr!('n in Nat) }, <P as View<'n>>::Output)
    )
    where
        P: for<'n> View<'n> + 'l;

    /// Zero is unique: ∀x∀y. IsZero(x) ∧ IsZero(y) → x = y
    fn zero_unique() -> thm!(
        'l: { Logic },
        'x: { expr!('x in Nat) && expr!('x == 0) },
        'y: { expr!('y in Nat) && expr!('y == 0) },
        Logic::Eq::<'x, 'y>,
    );
}

pub struct NatTheorems<'l, Logic, T>(PhantomData<(&'l (), Logic, T)>);

impl<'l, Logic, T> Set<'l> for NatTheorems<'l, Logic, T>
where
    Logic: FirstOrder<'l> + Equality<'l> + Negation<'l> + And<'l>,
    T: NaturalNumbers<'l, Logic>,
{
    type El<'a: 'l> = <<T as NaturalNumbers<'l, Logic>>::SuccFn as Function<'l, Logic>>::Dom<'a>;
}
