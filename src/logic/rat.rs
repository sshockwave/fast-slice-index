use crate::algebra::group::{AbelianGroup, BinOp, CommutativeMonoid, IsUnitLike};
use crate::logic::function::{Eq, Equality};
use crate::logic::prop::{And, Cert, FirstOrder, Negation, Or, View};
use crate::macros::thm;
use crate::rel::Set;

/// Type alias: "x is a rational"
/// Equivalent to: x is in the additive group's carrier
pub type IsRat<'x, Q> = <<Q as Rationals>::Add as Set>::El<'x>;

/// Type alias: "x is in the multiplicative carrier"
/// Pinned to [`IsRat`] by [`Rationals::same_carrier`]
pub type IsRatMul<'x, Q> = <<Q as Rationals>::Mul as Set>::El<'x>;

/// Type alias: "x + y = z"
pub type Sum<'x, 'y, 'z, Q> = <<Q as Rationals>::Add as BinOp<Q>>::Op<'x, 'y, 'z>;

/// Type alias: "x · y = z"
pub type Prod<'x, 'y, 'z, Q> = <<Q as Rationals>::Mul as BinOp<Q>>::Op<'x, 'y, 'z>;

/// Type alias: "x is additively neutral"
/// Equivalent to: ∀y. IsRat(y) → x + y = y
///
/// Just the additive group's [`IsUnitLike`]. Doesn't require x to be a
/// rational; [`IsZero`] adds that conjunct.
pub type IsZeroLike<'x, Q> = IsUnitLike<'x, <Q as Rationals>::Add, Q>;

/// Type alias: "x is zero"
/// Equivalent to: x is a rational AND x is additively neutral
pub type IsZero<'x, Q> = <Q as And>::And<IsRat<'x, Q>, IsZeroLike<'x, Q>>;

/// Type alias: "x is multiplicatively neutral"
/// Equivalent to: ∀y. IsRatMul(y) → x · y = y
pub type IsOneLike<'x, Q> = IsUnitLike<'x, <Q as Rationals>::Mul, Q>;

/// Type alias: "x is one"
///
/// A rational that is multiplicatively neutral and *not* additively neutral.
/// The `Neg<IsZeroLike>` conjunct is the field's nontriviality condition
/// (1 ≠ 0), which rules out the one-element degenerate "field"; it is
/// discharged by [`Rationals::nontrivial`].
pub type IsOne<'x, Q> = <Q as And>::And<
    IsRat<'x, Q>,
    <Q as And>::And<IsOneLike<'x, Q>, <Q as Negation>::Neg<IsZeroLike<'x, Q>>>,
>;

macro_rules! expr {
    (Cert::<$l:lifetime>, $($P:tt)*) => {
        Cert<Self, expr!($($P)*)>
    };
    (ForAll::<$x:lifetime, $($y:lifetime),+$(,)?>( $($P:tt)+ )) => {
        expr!(ForAll::<$x>(ForAll::<$($y),+>( $($P)+ )))
    };
    (ForAll::<$x:lifetime$(,)?>( $($P:tt)+ )) => {
        <Self as $crate::logic::prop::FirstOrder>::ForAll<
            dyn for<$x> $crate::logic::prop::View<
                $x,
                Output = expr!($($P)+)
            > +'static
        >
    };
    (!($($P:tt)*)) => {
        <Self as Negation>::Neg<expr!($($P)*)>
    };
    (($($P:tt)*).iff($($Q:tt)*)) => {
        $crate::logic::prop::Iff<Self, expr!($($P)*), expr!($($Q)*)>
    };
    (($($P:tt)*).imply($($Q:tt)*)) => {
        <Self as $crate::logic::prop::Imply>::Imply<
            expr!(($($P)*)),
            expr!(($($Q)*)),
        >
    };
    (($($P:tt)*) && ($($Q:tt)*)) => {
        <Self as $crate::logic::prop::And>::And<
            expr!($($P)*),
            expr!($($Q)*),
        >
    };
    (($($P:tt)*) || ($($Q:tt)*)) => {
        <Self as $crate::logic::prop::Or>::Or<
            expr!(($($P)*)),
            expr!(($($Q)*)),
        >
    };
    (e!($x:lifetime < $y:lifetime)) => {
        Self::Lt::<$x, $y>
    };
    (($($P:tt)*)) => {
        expr!($($P)*)
    };
    ($P:ty) => {
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
pub trait Rationals: Equality + Negation + And + Or + FirstOrder
where
    Self: 'static,
{
    /// Addition: an abelian group on all of ℚ
    ///
    /// [`AbelianGroup::inverse`] is the additive inverse axiom, and
    /// [`CommutativeMonoid::identity_exists`] asserts 0.
    type Add: AbelianGroup<Self>;

    /// Multiplication: only a commutative *monoid*, not a group
    ///
    /// `×` is total on ℚ, so 0 is in its carrier, so it cannot have inverses
    /// everywhere. [`Rationals::mul_inverse`] supplies the guarded version.
    type Mul: CommutativeMonoid<Self>;

    /// Strict order: `Lt<'x, 'y>` means "x < y"
    type Lt<'x, 'y>;

    /// Distributivity: x · (y + z) = x · y + x · z
    ///
    /// Relationally: `s = y+z`, `a = x·y`, `b = x·z`, `t = a+b`, and then
    /// `x·s = t`. This is the axiom linking `+` to `×`.
    fn distributive() -> thm!(
        {},
        ForAll::<'x, 'y, 'z>(
            Call::<'s> = <Self::Add as BinOp<Self>>::Op::<'y, 'z>,
            Call::<'a> = <Self::Mul as BinOp<Self>>::Op::<'x, 'y>,
            Call::<'b> = <Self::Mul as BinOp<Self>>::Op::<'x, 'z>,
            Call::<'t> = <Self::Add as BinOp<Self>>::Op::<'a, 'b>,
            Prod::<'x, 's, 't, Self>
        )
    );

    /// The order only relates rationals: ∀x ∀y. x < y → IsRat(x) ∧ IsRat(y)
    fn lt_typed() -> expr!(
        Cert::<'l>,
        ForAll::<'x, 'y>((e!('x < 'y)).imply((IsRat::<'x, Self>) && (IsRat::<'y, Self>)))
    );

    /// Irreflexive: ∀x. ¬(x < x)
    fn lt_irrefl() -> Cert<Self, &'static dyn for<'x> View<'x, Output = Self::Neg<Self::Lt<'x, 'x>>>>;

    /// Transitive: ∀x ∀y ∀z. x < y → y < z → x < z
    fn lt_trans() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = &'static dyn for<'z> View<
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
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = Self::Imply<
                    IsRat<'x, Self>,
                    Self::Imply<
                        IsRat<'y, Self>,
                        Self::Or<Self::Lt<'x, 'y>, Self::Or<Eq<'x, 'y, Self>, Self::Lt<'y, 'x>>>,
                    >,
                >,
            >,
        >,
    >;

    /// Translation invariance: x < y → x + z < y + z
    ///
    /// Relationally: `u = x+z`, `v = y+z`, then `u < v`.
    fn lt_add() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = &'static dyn for<'z> View<
                    'z,
                    Output = &'static dyn for<'u> View<
                        'u,
                        Output = &'static dyn for<'v> View<
                            'v,
                            Output = Self::Imply<
                                Self::Lt<'x, 'y>,
                                Self::Imply<
                                    Sum<'x, 'z, 'u, Self>,
                                    Self::Imply<Sum<'y, 'z, 'v, Self>, Self::Lt<'u, 'v>>,
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
        Self,
        &'static dyn for<'n> View<
            'n,
            Output = &'static dyn for<'w> View<
                'w,
                Output = &'static dyn for<'x> View<
                    'x,
                    Output = &'static dyn for<'y> View<
                        'y,
                        Output = &'static dyn for<'u> View<
                            'u,
                            Output = &'static dyn for<'v> View<
                                'v,
                                Output = Self::Imply<
                                    IsZeroLike<'n, Self>,
                                    Self::Imply<
                                        Self::Lt<'n, 'w>,
                                        Self::Imply<
                                            Self::Lt<'x, 'y>,
                                            Self::Imply<
                                                Prod<'x, 'w, 'u, Self>,
                                                Self::Imply<
                                                    Prod<'y, 'w, 'v, Self>,
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
    fn prime_field<P: 'static>() -> Cert<
        Self,
        Self::Imply<
            // P(1)
            &'static dyn for<'o> View<
                'o,
                Output = Self::Imply<IsOne<'o, Self>, <P as View<'o>>::Output>,
            >,
            Self::Imply<
                // closed under +: ∀x ∀y ∀z. P(x) → P(y) → x + y = z → P(z)
                &'static dyn for<'x> View<
                    'x,
                    Output = &'static dyn for<'y> View<
                        'y,
                        Output = &'static dyn for<'z> View<
                            'z,
                            Output = Self::Imply<
                                <P as View<'x>>::Output,
                                Self::Imply<
                                    <P as View<'y>>::Output,
                                    Self::Imply<Sum<'x, 'y, 'z, Self>, <P as View<'z>>::Output>,
                                >,
                            >,
                        >,
                    >,
                >,
                Self::Imply<
                    // closed under additive inverse:
                    // ∀x ∀y ∀z. P(x) → x + y = z → IsZeroLike(z) → P(y)
                    &'static dyn for<'x> View<
                        'x,
                        Output = &'static dyn for<'y> View<
                            'y,
                            Output = &'static dyn for<'z> View<
                                'z,
                                Output = Self::Imply<
                                    <P as View<'x>>::Output,
                                    Self::Imply<
                                        Sum<'x, 'y, 'z, Self>,
                                        Self::Imply<IsZeroLike<'z, Self>, <P as View<'y>>::Output>,
                                    >,
                                >,
                            >,
                        >,
                    >,
                    Self::Imply<
                        // closed under reciprocal:
                        // ∀x ∀y ∀z. P(x) → ¬IsZeroLike(x) → x · y = z → IsOneLike(z) → P(y)
                        &'static dyn for<'x> View<
                            'x,
                            Output = &'static dyn for<'y> View<
                                'y,
                                Output = &'static dyn for<'z> View<
                                    'z,
                                    Output = Self::Imply<
                                        <P as View<'x>>::Output,
                                        Self::Imply<
                                            Self::Neg<IsZeroLike<'x, Self>>,
                                            Self::Imply<
                                                Prod<'x, 'y, 'z, Self>,
                                                Self::Imply<
                                                    IsOneLike<'z, Self>,
                                                    <P as View<'y>>::Output,
                                                >,
                                            >,
                                        >,
                                    >,
                                >,
                            >,
                        >,
                        // ∀x. IsRat(x) → P(x)
                        &'static dyn for<'x> View<
                            'x,
                            Output = Self::Imply<IsRat<'x, Self>, <P as View<'x>>::Output>,
                        >,
                    >,
                >,
            >,
        >,
    >
    where
        P: for<'n> View<'n>;
}

#[cfg(test)]
mod tests {
    use super::{IsOne, IsRat, IsZero, Prod, Rationals, Sum, View};

    /// The field-specific axioms are reachable from outside this module, and
    /// the `IsZero` / `IsOne` / `Sum` / `Prod` aliases all resolve against a
    /// generic `Q`.
    fn _axioms_are_callable<Q: Rationals>() {
        // let _ = Q::same_carrier();
        // let _ = Q::nontrivial();
        // let _ = Q::mul_inverse();
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
    fn _group_axioms_cover_both<Q: Rationals>() {
        use crate::algebra::group::*;
        let _ = <Q::Add as Total<Q>>::total();
        let _ = <Q::Add as BinOp<Q>>::single_valued();
        let _ = <Q::Add as Closed<Q>>::closed();
        let _ = <Q::Add as Commutative<Q>>::comm();
        let _ = <Q::Add as Associative<Q>>::assoc();
        let _ = <Q::Add as IdentityExists<Q>>::identity_exists();
        // Only addition is a group: this is the additive inverse axiom.
        let _ = <Q::Add as InverseExists<Q>>::inverse();

        let _ = <Q::Mul as Total<Q>>::total();
        let _ = <Q::Mul as BinOp<Q>>::single_valued();
        let _ = <Q::Mul as Closed<Q>>::closed();
        let _ = <Q::Mul as Commutative<Q>>::comm();
        let _ = <Q::Mul as Associative<Q>>::assoc();
        let _ = <Q::Mul as IdentityExists<Q>>::identity_exists();
    }

    /// A predicate usable with the [`Rationals::prime_field`] schema: the
    /// witness that `P` may mention the field's own vocabulary.
    #[expect(dead_code, reason = "type-level marker; only its View impl is used")]
    struct IsRatPred<Q>(::core::marker::PhantomData<Q>);

    impl<'x, Q: Rationals> View<'x> for IsRatPred<Q> {
        type Output = IsRat<'x, Q>;
    }

    fn _prime_field_instantiates<Q: Rationals>() {
        // let _ = Q::prime_field::<IsRatPred<Q>>();
    }

    /// Zero uniqueness needs no axiom: neutrality pins it down, unlike
    /// `nat`'s "not a successor" characterization.
    type _ZeroAndOne<'x, Q> = (IsZero<'x, Q>, IsOne<'x, Q>);
    type _Ops<'x, 'y, 'z, Q> = (Sum<'x, 'y, 'z, Q>, Prod<'x, 'y, 'z, Q>);
}
