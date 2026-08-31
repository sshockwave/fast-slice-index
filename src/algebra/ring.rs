use super::group::Monoid;
use crate::{
    algebra::group::{AbelianGroup, BinOp, Commutative, IdentityExists},
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
        <Self::Add as BinOp<'l, Logic>>::Op::<$b, $c, $a>
    };
    ($a:lifetime = $b:lifetime * $c:lifetime) => {
        <Self::Mul as BinOp<'l, Logic>>::Op::<$b, $c, $a>
    };
    ($a:lifetime == 0) => {
        <Self::Add as IdentityExists<'l, Logic>>::IsIdentity::<$a>
    };
    ($a:lifetime == 1) => {
        <Self::Mul as IdentityExists<'l, Logic>>::IsIdentity::<$a>
    };
}

pub trait SemiRing<'l, Logic>
where
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
{
    type Add: Monoid<'l, Logic> + Commutative<'l, Logic>;
    type Mul: Monoid<'l, Logic>;

    /// Both operations share one carrier: ∀x. IsRat(x) ↔ IsRatMul(x)
    ///
    /// Each of [`Rationals::Add`] and [`Rationals::Mul`] carries its own
    /// `El`, so nothing otherwise forces `+` and `×` to range over the same
    /// set.
    fn same_carrier() -> thm!(
        'l: { Logic },
        ForAll::<'x>(expr!('x in El).iff(<Self::Mul as Set>::El::<'x>))
    );

    fn left_distributive() -> thm!(
        'l: { Logic },
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
        'l: { Logic },
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

pub trait Ring<'l, Logic>: SemiRing<'l, Logic, Add: AbelianGroup<'l, Logic>>
where
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
{
}
impl<'l, Logic, T> Ring<'l, Logic> for T
where
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
    T: SemiRing<'l, Logic, Add: AbelianGroup<'l, Logic>>,
{
}

pub trait CommutativeRing<'l, Logic>: Ring<'l, Logic, Mul: Commutative<'l, Logic>>
where
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
{
}
impl<'l, Logic, T> CommutativeRing<'l, Logic> for T
where
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
    Self: Ring<'l, Logic, Mul: Commutative<'l, Logic>>,
{
}

pub trait IntegralDomain<'l, Logic>: CommutativeRing<'l, Logic>
where
    Logic: Equality<'l> + And<'l> + Or<'l> + FirstOrder<'l>,
{
    fn no_zero_divisors() -> thm!(
        'l: { Logic },
        'a: { expr!('a in El) },
        'b: { expr!('b in El) },
        'ab: { expr!('ab = 'a * 'b) },
        expr!('ab == 0).imply(expr!('a == 0) || expr!('b == 0))
    );
}

pub trait NonZero<'l, Logic>: SemiRing<'l, Logic>
where
    Logic: Negation<'l> + Equality<'l> + And<'l> + FirstOrder<'l>,
{
    /// Nontriviality: ∀x. IsOneLike(x) → ¬IsZeroLike(x), i.e. 1 ≠ 0
    ///
    /// Rules out the one-element degenerate "field". This cannot come from
    /// [`CommutativeMonoid`], which knows nothing of the other operation;
    /// together with `Mul`'s identity and [`Rationals::same_carrier`] it
    /// upgrades that identity to a full [`IsOne`].
    fn nontrivial() -> thm!(
        'l: { Logic },
        'x: { expr!('x in El) },
        !(expr!('x == 0) && expr!('x == 1))
    );
}

pub trait Field<'l, Logic>: CommutativeRing<'l, Logic> + NonZero<'l, Logic>
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l> + Negation<'l>,
{
    fn mul_inverse() -> thm!(
        'l: { Logic },
        'x: { expr!('x in El) && !expr!('x == 0) },
        Exists::<'y>(expr!('y in El) && ('z: { expr!('z = 'x * 'y) }, expr!('z == 1)))
    );
}
