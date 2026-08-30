use crate::logic::function::Equality;
use crate::logic::group::{AbelianGroup, CommutativeMonoid, IsUnitLike};
use crate::logic::macros::thm;
use crate::logic::prop::{And, Cert, FirstOrder, Negation, Or, View};

/// Type alias: "x is a rational"
/// Equivalent to: x is in the additive group's carrier
pub type IsRat<'l, 'x, Q> = <<Q as Rationals<'l>>::Add as CommutativeMonoid<'l, Q>>::El<'x>;

/// Type alias: "x is in the multiplicative carrier"
/// Pinned to [`IsRat`] by [`Rationals::same_carrier`]
pub type IsRatMul<'l, 'x, Q> = <<Q as Rationals<'l>>::Mul as CommutativeMonoid<'l, Q>>::El<'x>;

/// Type alias: "x + y = z"
pub type Sum<'l, 'x, 'y, 'z, Q> =
    <<Q as Rationals<'l>>::Add as CommutativeMonoid<'l, Q>>::Op<'x, 'y, 'z>;

/// Type alias: "x · y = z"
pub type Prod<'l, 'x, 'y, 'z, Q> =
    <<Q as Rationals<'l>>::Mul as CommutativeMonoid<'l, Q>>::Op<'x, 'y, 'z>;

/// Type alias: "x is additively neutral"
/// Equivalent to: ∀y. IsRat(y) → x + y = y
///
/// Just the additive group's [`IsUnitLike`]. Doesn't require x to be a
/// rational; [`IsZero`] adds that conjunct.
pub type IsZeroLike<'l, 'x, Q> = IsUnitLike<'l, 'x, <Q as Rationals<'l>>::Add, Q>;

/// Type alias: "x is zero"
/// Equivalent to: x is a rational AND x is additively neutral
pub type IsZero<'l, 'x, Q> = <Q as And<'l>>::And<IsRat<'l, 'x, Q>, IsZeroLike<'l, 'x, Q>>;

/// Type alias: "x is multiplicatively neutral"
/// Equivalent to: ∀y. IsRatMul(y) → x · y = y
pub type IsOneLike<'l, 'x, Q> = IsUnitLike<'l, 'x, <Q as Rationals<'l>>::Mul, Q>;

/// Type alias: "x is one"
///
/// A rational that is multiplicatively neutral and *not* additively neutral.
/// The `Neg<IsZeroLike>` conjunct is the field's nontriviality condition
/// (1 ≠ 0), which rules out the one-element degenerate "field"; it is
/// discharged by [`Rationals::nontrivial`].
pub type IsOne<'l, 'x, Q> = <Q as And<'l>>::And<
    IsRat<'l, 'x, Q>,
    <Q as And<'l>>::And<IsOneLike<'l, 'x, Q>, <Q as Negation<'l>>::Neg<IsZeroLike<'l, 'x, Q>>>,
>;

macro_rules! expr {
    (Cert::<$l:lifetime>, $($P:tt)*) => {
        Cert<$l, Self, expr!($l, $($P)*)>
    };
    ($l:lifetime, ForAll::<$x:lifetime, $($y:lifetime),+$(,)?>( $($P:tt)+ )) => {
        expr!($l, ForAll::<$x>(ForAll::<$($y),+>( $($P)+ )))
    };
    ($l:lifetime, ForAll::<$x:lifetime$(,)?>( $($P:tt)+ )) => {
        <Self as $crate::logic::prop::FirstOrder<$l>>::ForAll<
            dyn for<$x> $crate::logic::prop::View<
                $x,
                Output = expr!($l, $($P)+)
            > + $l,
        >
    };
    ($l:lifetime, !($($P:tt)*)) => {
        <Self as Negation<$l>>::Neg<expr!($l, $($P)*)>
    };
    ($l:lifetime, ($($P:tt)*).iff($($Q:tt)*)) => {
        $crate::logic::prop::Iff<$l, Self, expr!($l, $($P)*), expr!($l, $($Q)*)>
    };
    ($l:lifetime, ($($P:tt)*).imply($($Q:tt)*)) => {
        <Self as $crate::logic::prop::Imply<$l>>::Imply<
            expr!($l, ($($P)*)),
            expr!($l, ($($Q)*)),
        >
    };
    ($l:lifetime, ($($P:tt)*) && ($($Q:tt)*)) => {
        <Self as $crate::logic::prop::And<$l>>::And<
            expr!($l, $($P)*),
            expr!($l, $($Q)*),
        >
    };
    ($l:lifetime, ($($P:tt)*) || ($($Q:tt)*)) => {
        <Self as $crate::logic::prop::Or<$l>>::Or<
            expr!($l, ($($P)*)),
            expr!($l, ($($Q)*)),
        >
    };
    ($l:lifetime, e!($x:lifetime < $y:lifetime)) => {
        Self::Lt::<$x, $y>
    };
    ($l:lifetime, ($($P:tt)*)) => {
        expr!($l, $($P)*)
    };
    ($l:lifetime, $P:ty) => {
        $P
    };
}

/// Rational numbers as the prime ordered field
///
/// Design:
/// - `Add` is an [`AbelianGroup`] and `Mul` a [`CommutativeMonoid`] over one
///   shared carrier. Everything true of both operations — totality,
///   single-valuedness, closure, commutativity, associativity, a neutral
///   element — comes from those traits, so this trait states only what is
///   specific to a *field*: the two ways `+` and `×` interact, plus the order.
/// - 0 and 1 are characterized by neutrality ([`IsZero`], [`IsOne`]), not
///   introduced as terms — this logic has no term formers
/// - `Lt` axiomatizes a strict order compatible with both operations
/// - What pins the field down to ℚ (rather than ℝ, or ℚ(√2)) is
///   [`Rationals::prime_field`]: ℚ has no proper subfield
///
/// Every axiom is therefore relational: `x + y = z` appears as
/// [`Sum`]`<'x, 'y, 'z>`, and equations chain by quantifying over the
/// intermediate results.
///
/// Existentials use the classical encoding
/// `∃x. A(x) ∧ B(x)` ≡ `¬∀x. A(x) → ¬B(x)`. That equivalence is *classical*,
/// so [`Contraposition`] is a supertrait here (as in [`crate::logic::zfc::ZF`])
/// rather than just [`Equality`]'s intuitionistic `L1`/`L2` — without it the
/// encoding is strictly weaker than the existential it stands for, and the
/// witnesses in [`AbelianGroup::inverse`] and [`Rationals::mul_inverse`] could
/// not be extracted.
pub trait Rationals<'l>:
    Equality<'l> + Negation<'l> + And<'l> + Or<'l> + FirstOrder<'l> + 'l
{
    /// Addition: an abelian group on all of ℚ
    ///
    /// [`AbelianGroup::inverse`] is the additive inverse axiom, and
    /// [`CommutativeMonoid::identity_exists`] asserts 0.
    type Add: AbelianGroup<'l, Self>;

    /// Multiplication: only a commutative *monoid*, not a group
    ///
    /// `×` is total on ℚ, so 0 is in its carrier, so it cannot have inverses
    /// everywhere. [`Rationals::mul_inverse`] supplies the guarded version.
    type Mul: CommutativeMonoid<'l, Self>;

    /// Strict order: `Lt<'x, 'y>` means "x < y"
    type Lt<'x: 'l, 'y: 'l>;

    /// Both operations share one carrier: ∀x. IsRat(x) ↔ IsRatMul(x)
    ///
    /// Each of [`Rationals::Add`] and [`Rationals::Mul`] carries its own
    /// `El`, so nothing otherwise forces `+` and `×` to range over the same
    /// set.
    fn same_carrier() -> expr!(
        Cert::<'l>,
        ForAll::<'x>((IsRat::<'l, 'x, Self>).iff(IsRatMul::<'l, 'x, Self>))
    );

    /// Nontriviality: ∀x. IsOneLike(x) → ¬IsZeroLike(x), i.e. 1 ≠ 0
    ///
    /// Rules out the one-element degenerate "field". This cannot come from
    /// [`CommutativeMonoid`], which knows nothing of the other operation;
    /// together with `Mul`'s identity and [`Rationals::same_carrier`] it
    /// upgrades that identity to a full [`IsOne`].
    fn nontrivial() -> expr!(
        Cert::<'l>,
        ForAll::<'x>((IsOneLike::<'l, 'x, Self>).imply(!(IsZeroLike::<'l, 'x, Self>)))
    );

    /// Multiplicative inverse: every *nonzero* rational has a reciprocal
    ///
    /// ∀x. IsRat(x) → ¬IsZeroLike(x) → ∃y. IsRat(y) ∧ (x · y is one)
    ///
    /// The `¬IsZeroLike` guard is what keeps this from being false at 0, and
    /// is exactly why [`Rationals::Mul`] is a monoid rather than an
    /// [`AbelianGroup`].
    fn mul_inverse() -> thm!(
        'l: {},
        ForAll::<'x>(
            IsRat::<'l, 'x, Self>.imply((!IsZeroLike::<'l, 'x, Self>).imply(!ForAll::<'y>(
                IsRat::<'l, 'y, Self>.imply(!(
                    Call::<'z> = <Self::Mul as CommutativeMonoid<'l, Self>>::Op::<'x, 'y>,
                    IsOneLike::<'l, 'z, Self>
                ))
            )))
        )
    );

    /// Distributivity: x · (y + z) = x · y + x · z
    ///
    /// Relationally: `s = y+z`, `a = x·y`, `b = x·z`, `t = a+b`, and then
    /// `x·s = t`. This is the axiom linking `+` to `×`.
    fn distributive() -> thm!(
        'l: {},
        ForAll::<'x, 'y, 'z>(
            Call::<'s> = <Self::Add as CommutativeMonoid<'l, Self>>::Op::<'y, 'z>,
            Call::<'a> = <Self::Mul as CommutativeMonoid<'l, Self>>::Op::<'x, 'y>,
            Call::<'b> = <Self::Mul as CommutativeMonoid<'l, Self>>::Op::<'x, 'z>,
            Call::<'t> = <Self::Add as CommutativeMonoid<'l, Self>>::Op::<'a, 'b>,
            Prod::<'l, 'x, 's, 't, Self>
        )
    );

    /// The order only relates rationals: ∀x ∀y. x < y → IsRat(x) ∧ IsRat(y)
    fn lt_typed() -> expr!(
        Cert::<'l>,
        ForAll::<'x, 'y>((e!('x < 'y)).imply((IsRat::<'l, 'x, Self>) && (IsRat::<'l, 'y, Self>)))
    );

    /// Irreflexive: ∀x. ¬(x < x)
    fn lt_irrefl() -> Cert<'l, Self, &'l dyn for<'x> View<'x, Output = Self::Neg<Self::Lt<'x, 'x>>>>;

    /// Transitive: ∀x ∀y ∀z. x < y → y < z → x < z
    fn lt_trans() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = Self::Imply<
                        Self::Lt<'x, 'y>,
                        Self::Imply<Self::Lt<'y, 'z>, Self::Lt<'x, 'z>>,
                    >,
                >,
            >,
        >,
    >;

    /// Trichotomy: ∀x ∀y. IsRat(x) → IsRat(y) → (x < y) ∨ (x = y ∨ y < x)
    ///
    /// Together with [`Rationals::lt_irrefl`] this makes the order total.
    fn trichotomy() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = Self::Imply<
                    IsRat<'l, 'x, Self>,
                    Self::Imply<
                        IsRat<'l, 'y, Self>,
                        Self::Or<Self::Lt<'x, 'y>, Self::Or<Self::Eq<'x, 'y>, Self::Lt<'y, 'x>>>,
                    >,
                >,
            >,
        >,
    >;

    /// Translation invariance: x < y → x + z < y + z
    ///
    /// Relationally: `u = x+z`, `v = y+z`, then `u < v`.
    fn lt_add() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = &'l dyn for<'u> View<
                        'u,
                        Output = &'l dyn for<'v> View<
                            'v,
                            Output = Self::Imply<
                                Self::Lt<'x, 'y>,
                                Self::Imply<
                                    Sum<'l, 'x, 'z, 'u, Self>,
                                    Self::Imply<Sum<'l, 'y, 'z, 'v, Self>, Self::Lt<'u, 'v>>,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >;

    /// Positive scaling preserves order: 0 < w → x < y → x · w < y · w
    ///
    /// "Positive" is stated as `IsZeroLike(n) ∧ n < w`: the order relates
    /// elements, so zero has to be quantified in rather than named.
    fn lt_mul() -> Cert<
        'l,
        Self,
        &'l dyn for<'n> View<
            'n,
            Output = &'l dyn for<'w> View<
                'w,
                Output = &'l dyn for<'x> View<
                    'x,
                    Output = &'l dyn for<'y> View<
                        'y,
                        Output = &'l dyn for<'u> View<
                            'u,
                            Output = &'l dyn for<'v> View<
                                'v,
                                Output = Self::Imply<
                                    IsZeroLike<'l, 'n, Self>,
                                    Self::Imply<
                                        Self::Lt<'n, 'w>,
                                        Self::Imply<
                                            Self::Lt<'x, 'y>,
                                            Self::Imply<
                                                Prod<'l, 'x, 'w, 'u, Self>,
                                                Self::Imply<
                                                    Prod<'l, 'y, 'w, 'v, Self>,
                                                    Self::Lt<'u, 'v>,
                                                >,
                                            >,
                                        >,
                                    >,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >;

    /// Prime field: ℚ has no proper subfield
    ///
    /// If `P` holds at 1 and is closed under `+`, additive inverse, and
    /// reciprocal of nonzero elements, then `P` holds at every rational.
    ///
    /// This is what separates ℚ from ℝ or ℚ(√2): those satisfy every axiom
    /// above, but each has a proper subfield containing 1. Note that closure
    /// under `×` is *not* required — repeated addition of `1/q` already
    /// reaches every `p/q` — and `P(0)` follows from `P(1)` with closure
    /// under `+` and additive inverse.
    ///
    /// `P` is a type parameter, not a quantified predicate, so this is a
    /// schema instantiated per `P`. Same predicativity argument as
    /// [`crate::logic::nat::NaturalNumbers::induction`].
    fn prime_field<P>() -> Cert<
        'l,
        Self,
        Self::Imply<
            // P(1)
            &'l dyn for<'o> View<
                'o,
                Output = Self::Imply<IsOne<'l, 'o, Self>, <P as View<'o>>::Output>,
            >,
            Self::Imply<
                // closed under +: ∀x ∀y ∀z. P(x) → P(y) → x + y = z → P(z)
                &'l dyn for<'x> View<
                    'x,
                    Output = &'l dyn for<'y> View<
                        'y,
                        Output = &'l dyn for<'z> View<
                            'z,
                            Output = Self::Imply<
                                <P as View<'x>>::Output,
                                Self::Imply<
                                    <P as View<'y>>::Output,
                                    Self::Imply<Sum<'l, 'x, 'y, 'z, Self>, <P as View<'z>>::Output>,
                                >,
                            >,
                        >,
                    >,
                >,
                Self::Imply<
                    // closed under additive inverse:
                    // ∀x ∀y ∀z. P(x) → x + y = z → IsZeroLike(z) → P(y)
                    &'l dyn for<'x> View<
                        'x,
                        Output = &'l dyn for<'y> View<
                            'y,
                            Output = &'l dyn for<'z> View<
                                'z,
                                Output = Self::Imply<
                                    <P as View<'x>>::Output,
                                    Self::Imply<
                                        Sum<'l, 'x, 'y, 'z, Self>,
                                        Self::Imply<
                                            IsZeroLike<'l, 'z, Self>,
                                            <P as View<'y>>::Output,
                                        >,
                                    >,
                                >,
                            >,
                        >,
                    >,
                    Self::Imply<
                        // closed under reciprocal:
                        // ∀x ∀y ∀z. P(x) → ¬IsZeroLike(x) → x · y = z → IsOneLike(z) → P(y)
                        &'l dyn for<'x> View<
                            'x,
                            Output = &'l dyn for<'y> View<
                                'y,
                                Output = &'l dyn for<'z> View<
                                    'z,
                                    Output = Self::Imply<
                                        <P as View<'x>>::Output,
                                        Self::Imply<
                                            Self::Neg<IsZeroLike<'l, 'x, Self>>,
                                            Self::Imply<
                                                Prod<'l, 'x, 'y, 'z, Self>,
                                                Self::Imply<
                                                    IsOneLike<'l, 'z, Self>,
                                                    <P as View<'y>>::Output,
                                                >,
                                            >,
                                        >,
                                    >,
                                >,
                            >,
                        >,
                        // ∀x. IsRat(x) → P(x)
                        &'l dyn for<'x> View<
                            'x,
                            Output = Self::Imply<IsRat<'l, 'x, Self>, <P as View<'x>>::Output>,
                        >,
                    >,
                >,
            >,
        >,
    >
    where
        P: for<'n> View<'n> + 'l;
}

#[cfg(test)]
mod tests {
    use super::{IsOne, IsRat, IsZero, Prod, Rationals, Sum, View};
    use crate::logic::group::{AbelianGroup, CommutativeMonoid};

    /// The field-specific axioms are reachable from outside this module, and
    /// the `IsZero` / `IsOne` / `Sum` / `Prod` aliases all resolve against a
    /// generic `Q`.
    fn _axioms_are_callable<'l, Q: Rationals<'l>>() {
        let _ = Q::same_carrier();
        let _ = Q::nontrivial();
        let _ = Q::mul_inverse();
        let _ = Q::distributive();
        let _ = Q::lt_typed();
        let _ = Q::lt_irrefl();
        let _ = Q::lt_trans();
        let _ = Q::trichotomy();
        let _ = Q::lt_add();
        let _ = Q::lt_mul();
    }

    /// The shared structure really does come from the group traits: totality,
    /// single-valuedness, closure, commutativity, associativity and the
    /// neutral element are stated once each and reused by both operations.
    fn _group_axioms_cover_both<'l, Q: Rationals<'l>>() {
        let _ = <Q::Add as CommutativeMonoid<'l, Q>>::total();
        let _ = <Q::Add as CommutativeMonoid<'l, Q>>::functional();
        let _ = <Q::Add as CommutativeMonoid<'l, Q>>::closed();
        let _ = <Q::Add as CommutativeMonoid<'l, Q>>::comm();
        let _ = <Q::Add as CommutativeMonoid<'l, Q>>::assoc();
        let _ = <Q::Add as CommutativeMonoid<'l, Q>>::identity_exists();
        // Only addition is a group: this is the additive inverse axiom.
        let _ = <Q::Add as AbelianGroup<'l, Q>>::inverse();

        let _ = <Q::Mul as CommutativeMonoid<'l, Q>>::total();
        let _ = <Q::Mul as CommutativeMonoid<'l, Q>>::functional();
        let _ = <Q::Mul as CommutativeMonoid<'l, Q>>::closed();
        let _ = <Q::Mul as CommutativeMonoid<'l, Q>>::comm();
        let _ = <Q::Mul as CommutativeMonoid<'l, Q>>::assoc();
        let _ = <Q::Mul as CommutativeMonoid<'l, Q>>::identity_exists();
    }

    /// A predicate usable with the [`Rationals::prime_field`] schema: the
    /// witness that `P` may mention the field's own vocabulary.
    #[expect(dead_code, reason = "type-level marker; only its View impl is used")]
    struct IsRatPred<'l, Q>(::core::marker::PhantomData<(&'l (), Q)>);

    impl<'l, 'x, Q: Rationals<'l>> View<'x> for IsRatPred<'l, Q> {
        type Output = IsRat<'l, 'x, Q>;
    }

    fn _prime_field_instantiates<'l, Q: Rationals<'l>>() {
        let _ = Q::prime_field::<IsRatPred<'l, Q>>();
    }

    /// Zero uniqueness needs no axiom: neutrality pins it down, unlike
    /// `nat`'s "not a successor" characterization.
    type _ZeroAndOne<'l, 'x, Q> = (IsZero<'l, 'x, Q>, IsOne<'l, 'x, Q>);
    type _Ops<'l, 'x, 'y, 'z, Q> = (Sum<'l, 'x, 'y, 'z, Q>, Prod<'l, 'x, 'y, 'z, Q>);
}
