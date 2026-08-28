use crate::logic::function::{Equality, Function, Injection, View};
use crate::logic::prop::Neg;

/// Type alias: "x is a natural number"
/// Equivalent to: x ∈ Dom(SuccFn)
pub type IsNat<'l, 'x, N> = <<N as NaturalNumbers<'l>>::SuccFn as Function<'l, N>>::Dom<'x>;

/// Natural numbers trait using function-based approach
///
/// Design:
/// - SuccFn is a Function (and Injection) from ℕ → ℕ
/// - SuccFn::F<'x, 'y> means "y is the successor of x"
/// - SuccFn::Dom and SuccFn::Codom define what counts as a natural number
/// - Zero is defined existentially: ∃z. ∀n∀s. Succ(n,s) → s≠z
/// - Induction uses P as a type parameter (schema) to remain predicative
pub trait NaturalNumbers<'l>: Equality<'l>
where
    Self: 'l,
{
    /// Successor function: ℕ → ℕ
    /// An injection from natural numbers to natural numbers
    /// SuccFn::F<'x, 'y> means "y is the successor of x"
    type SuccFn: Function<'l, Self> + Injection<'l, Self>;

    /// Zero is defined existentially: ∃z. z is a nat ∧ ∀n. ∀s. Succ(n, s) → s ≠ z
    /// "There exists something such that no natural's successor equals it"
    fn zero_exists() -> Self::Cert<
        Neg<&'l dyn for<'z> View<
            'z,
            Output = Self::Imply<
                IsNat<'l, 'z, Self>,
                &'l dyn for<'n> View<
                    'n,
                    Output = Self::Imply<
                        IsNat<'l, 'n, Self>,
                        &'l dyn for<'s> View<
                            's,
                            Output = Self::Imply<
                                <Self::SuccFn as Function<'l, Self>>::F<'n, 's>,
                                Neg<Self::Eq<'s, 'z>>
                            >
                        >
                    >
                >
            >
        >>
    >;

    /// Induction: ∀P. [P(0) ∧ (∀n. n is nat ∧ P(n) → ∀s. Succ(n,s) → P(s))] → ∀n. n is nat → P(n)
    ///
    /// NOTE: P is a type parameter, not a quantified predicate.
    /// We're defining induction for each specific P separately.
    /// This is predicative and avoids Russell's paradox.
    fn induction<P>() -> Self::Cert<
        Self::Imply<
            // P(0) - predicate holds for zero
            &'l dyn for<'z> View<
                'z,
                Output = Self::Imply<
                    IsNat<'l, 'z, Self>,
                    Self::Imply<
                        // z is zero (no predecessor)
                        &'l dyn for<'p> View<
                            'p,
                            Output = &'l dyn for<'s> View<
                                's,
                                Output = Self::Imply<
                                    <Self::SuccFn as Function<'l, Self>>::F<'p, 's>,
                                    Neg<Self::Eq<'s, 'z>>
                                >
                            >
                        >,
                        <P as View<'z>>::Output
                    >
                >
            >,
            Self::Imply<
                // ∀n. P(n) → P(succ(n))
                &'l dyn for<'n> View<
                    'n,
                    Output = Self::Imply<
                        IsNat<'l, 'n, Self>,
                        Self::Imply<
                            <P as View<'n>>::Output,
                            &'l dyn for<'s> View<
                                's,
                                Output = Self::Imply<
                                    <Self::SuccFn as Function<'l, Self>>::F<'n, 's>,
                                    <P as View<'s>>::Output
                                >
                            >
                        >
                    >
                >,
                // ∀n. P(n)
                &'l dyn for<'n> View<
                    'n,
                    Output = Self::Imply<
                        IsNat<'l, 'n, Self>,
                        <P as View<'n>>::Output
                    >
                >
            >
        >
    >
    where
        P: for<'n> View<'n> + 'l;
}
