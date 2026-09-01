use super::group::Monoid;
use crate::{
    algebra::group::{AbelianGroup, BinOp, Commutative, IsUnitLike},
    logic::{
        function::Equality,
        prop::{And, FirstOrder, Negation, Or},
    },
    macros::thm,
    rel::Set,
};

macro_rules! expr {
    ($a:lifetime in El) => {
        <Self::Add as Set>::El::<$a>
    };
    ($a:lifetime = $b:lifetime + $c:lifetime) => {
        <Self::Add as BinOp<Logic>>::Op::<$b, $c, $a>
    };
    ($a:lifetime = $b:lifetime * $c:lifetime) => {
        <Self::Mul as BinOp<Logic>>::Op::<$b, $c, $a>
    };
    ($a:lifetime == 0) => {
        IsUnitLike::<$a, Self::Add, Logic>
    };
    ($a:lifetime == 1) => {
        IsUnitLike::<$a, Self::Mul, Logic>
    };
}

pub trait SemiRing<Logic>
where
    Logic: Equality + And + FirstOrder,
{
    type Add: Monoid<Logic> + Commutative<Logic>;
    type Mul: Monoid<Logic>;

    /// Both operations share one carrier: ∀x. IsRat(x) ↔ IsRatMul(x)
    ///
    /// Each of [`Rationals::Add`] and [`Rationals::Mul`] carries its own
    /// `El`, so nothing otherwise forces `+` and `×` to range over the same
    /// set.
    fn same_carrier() -> thm!(
        { Logic },
        ForAll::<'x>(expr!('x in El).iff(<Self::Mul as Set>::El::<'x>))
    );

    fn left_distributive() -> thm!(
        { Logic },
        'a: { expr!('a in El) },
        'b: { expr!('b in El) },
        'c: { expr!('c in El) },
        'b_c: { expr!('b_c = 'b + 'c) },
        'ab: { expr!('ab = 'a * 'b) },
        'ac: { expr!('ac = 'a * 'c) },
        'ab_ac: { expr!('ab_ac = 'ab + 'ac) },
        expr!('ab_ac = 'a * 'b_c)
    );

    fn right_distributive() -> thm!(
        { Logic },
        'a: { expr!('a in El) },
        'b: { expr!('b in El) },
        'c: { expr!('c in El) },
        'b_c: { expr!('b_c = 'b + 'c) },
        'ba: { expr!('ba = 'b * 'a) },
        'ca: { expr!('ca = 'c * 'a) },
        'ba_ca: { expr!('ba_ca = 'ba + 'ca) },
        expr!('ba_ca = 'b_c * 'a)
    );
}

pub trait Ring<Logic>: SemiRing<Logic, Add: AbelianGroup<Logic>>
where
    Logic: Equality + And + FirstOrder,
{
}
impl<Logic, T> Ring<Logic> for T
where
    Logic: Equality + And + FirstOrder,
    T: SemiRing<Logic, Add: AbelianGroup<Logic>>,
{
}

pub trait CommutativeRing<Logic>: Ring<Logic, Mul: Commutative<Logic>>
where
    Logic: Equality + And + FirstOrder,
{
}
impl<Logic, T> CommutativeRing<Logic> for T
where
    Logic: Equality + And + FirstOrder,
    T: Ring<Logic, Mul: Commutative<Logic>>,
{
}

pub trait IntegralDomain<Logic>: CommutativeRing<Logic>
where
    Logic: Equality + And + Or + FirstOrder,
{
    fn no_zero_divisors() -> thm!(
        { Logic },
        'a: { expr!('a in El) },
        'b: { expr!('b in El) },
        'ab: { expr!('ab = 'a * 'b) },
        expr!('ab == 0).imply(expr!('a == 0) || expr!('b == 0))
    );
}

pub trait NonZero<Logic>: SemiRing<Logic>
where
    Logic: Negation + Equality + And + FirstOrder,
{
    /// Nontriviality: ∀x. IsOneLike(x) → ¬IsZeroLike(x), i.e. 1 ≠ 0
    ///
    /// Rules out the one-element degenerate "field". This cannot come from
    /// [`CommutativeMonoid`], which knows nothing of the other operation;
    /// together with `Mul`'s identity and [`Rationals::same_carrier`] it
    /// upgrades that identity to a full [`IsOne`].
    fn nontrivial() -> thm!(
        { Logic },
        'x: { expr!('x in El) },
        !(expr!('x == 0) && expr!('x == 1))
    );
}

pub trait Field<Logic>: CommutativeRing<Logic> + NonZero<Logic>
where
    Logic: FirstOrder + Equality + And + Negation,
{
    /// Multiplicative inverse: every *nonzero* rational has a reciprocal
    ///
    /// ∀x. IsRat(x) → ¬IsZeroLike(x) → ∃y. IsRat(y) ∧ (x · y is one)
    ///
    /// The `¬IsZeroLike` guard is what keeps this from being false at 0, and
    /// is exactly why [`Rationals::Mul`] is a monoid rather than an
    /// [`AbelianGroup`].
    fn mul_inverse() -> thm!(
        { Logic },
        'x: { expr!('x in El) && !expr!('x == 0) },
        Exists::<'y>(expr!('y in El) && ('z: { expr!('z = 'x * 'y) }, expr!('z == 1)))
    );
}
