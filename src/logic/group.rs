//! Commutative monoids and abelian groups, shared by a field's two operations.
//!
//! # Why the operation is a ternary relation, not a function on a product
//!
//! The obvious move for a binary operation is to make it a unary
//! [`Function`](crate::logic::function::Function) out of `ℚ × ℚ`. That needs a
//! Cartesian product, and this logic cannot build one.
//!
//! Elements of a domain are *lifetimes*. Quantification is `for<'x> View<'x>`,
//! one lifetime at a time, and there is no type-level pairing of lifetimes: no
//! way to form a single `'p` standing for `⟨'x, 'y⟩`, and no way to project
//! back out. The three routes to getting one are all heavier than a ternary
//! relation:
//!
//! - **Take pairs from [`ZF`](crate::logic::zfc::ZF).** `ZF::pairing` gives
//!   genuine ordered pairs, but then these traits and
//!   [`Rationals`](crate::logic::rat::Rationals) would have to extend `ZF` —
//!   dragging all of set theory in to state a group axiom — and every use of
//!   the operation would carry Kuratowski projections plus their
//!   well-definedness lemmas.
//! - **Add a pair former** as a new kind of element. That changes the *domain
//!   of quantification*, so every `for<'x> View<'x>` schema needs a companion
//!   over paired domains, and `Function` has to be restated for it.
//! - **Curry it.** `x ∘ ·` would have to be an *element* of some domain, which
//!   means function spaces as objects — ZF again, or higher-order
//!   quantification, which the predicativity design deliberately avoids (see
//!   the warning on [`Function`](crate::logic::function::Function)).
//!
//! So `Op<'x, 'y, 'z>` — read "x ∘ y = z" — is the minimum. Taking two
//! argument lifetimes *is* the Cartesian product, uncurried and left implicit,
//! and the graph is the operation. The cost is one extra lifetime parameter;
//! the benefit is that it gets axiomatized once and both of a field's
//! operations reuse it.
//!
//! # Why two traits
//!
//! [`AbelianGroup`] is [`CommutativeMonoid`] plus inverses, because ℚ needs
//! exactly that asymmetry: `+` is an abelian group on all of ℚ, but `×` is
//! only a commutative *monoid* there. Multiplication has to stay total — `x·0`
//! is a rational — while [`Group::inverse`](AbelianGroup::inverse) is false at
//! 0. Restricting `×`'s carrier to ℚ∖{0} to recover a group would make
//! `Op<'x, 'n, 'z>` unprovable for zero `n`, since
//! [`CommutativeMonoid::closed`] forces both arguments into the carrier. So
//! multiplicative inverses stay a *guarded* field axiom, and this module
//! supplies the part that really is shared.
//!
//! `Self` here is a plain marker for the operation and carries no logic of its
//! own: every proposition and certificate comes from the ambient `Eq`. That
//! keeps a consumer such as [`crate::logic::rat`] in one logic throughout,
//! instead of mixing the operation's `Imply` with the field's.

use crate::logic::function::{Equality, View};
use crate::logic::prop::{And, Contraposition, Negation, PropLogic};

/// Type alias: "e is neutral for the operation"
/// Equivalent to: ∀y. El(y) → e ∘ y = y
///
/// Note: doesn't require e to be in the carrier.
/// [`CommutativeMonoid::identity_exists`] adds that conjunct, mirroring how
/// `nat` splits `IsZeroLike` from `IsZero`.
pub type IsUnitLike<'l, 'e, M, Eq> = &'l dyn for<'y> View<
    'y,
    Output = <Eq as PropLogic<'l>>::Imply<
        <M as CommutativeMonoid<'l, Eq>>::El<'y>,
        &'l dyn for<'z> View<
            'z,
            Output = <Eq as PropLogic<'l>>::Imply<
                <M as CommutativeMonoid<'l, Eq>>::Op<'e, 'y, 'z>,
                <Eq as Equality<'l>>::Eq<'z, 'y>,
            >,
        >,
    >,
>;

/// A commutative monoid: a carrier closed under a total, associative,
/// commutative operation with a two-sided identity.
///
/// `Op<'x, 'y, 'z>` is the operation's graph, read "x ∘ y = z". See the module
/// docs on why this is a ternary relation rather than a function on a
/// Cartesian product.
///
/// The lifetime parameters of [`CommutativeMonoid::El`] and
/// [`CommutativeMonoid::Op`] carry no `: 'l` bound. That bound would make them
/// ill-formed inside a concrete `for<'n> View<'n>` predicate, which would
/// render schemas like [`crate::logic::rat::Rationals::prime_field`]
/// uninstantiable.
pub trait CommutativeMonoid<'l, Eq>
where
    Self: 'l,
    Eq: PropLogic<'l> + Negation<'l> + Equality<'l> + ?Sized,
{
    /// Carrier predicate: which elements the operation is defined on
    type El<'x>;

    /// The operation's graph: `Op<'x, 'y, 'z>` means "x ∘ y = z"
    type Op<'x, 'y, 'z>;

    /// Total: ∀x ∀y. El(x) → El(y) → ∃z. El(z) ∧ x ∘ y = z
    fn total() -> Eq::Cert<
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = Eq::Imply<
                    Self::El<'x>,
                    Eq::Imply<
                        Self::El<'y>,
                        Eq::Neg<
                            &'l dyn for<'z> View<
                                'z,
                                Output = Eq::Imply<Self::El<'z>, Eq::Neg<Self::Op<'x, 'y, 'z>>>,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >;

    /// Functional (single-valued): ∀x ∀y ∀z ∀w. x ∘ y = z → x ∘ y = w → z = w
    fn functional() -> Eq::Cert<
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = &'l dyn for<'w> View<
                        'w,
                        Output = Eq::Imply<
                            Self::Op<'x, 'y, 'z>,
                            Eq::Imply<Self::Op<'x, 'y, 'w>, Eq::Eq<'z, 'w>>,
                        >,
                    >,
                >,
            >,
        >,
    >;

    /// Closed: ∀x ∀y ∀z. x ∘ y = z → El(x) ∧ (El(y) ∧ El(z))
    fn closed() -> Eq::Cert<
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = Eq::Imply<
                        Self::Op<'x, 'y, 'z>,
                        And<'l, Self::El<'x>, And<'l, Self::El<'y>, Self::El<'z>, Eq>, Eq>,
                    >,
                >,
            >,
        >,
    >;

    /// Commutative: ∀x ∀y ∀z. x ∘ y = z → y ∘ x = z
    fn comm() -> Eq::Cert<
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = Eq::Imply<Self::Op<'x, 'y, 'z>, Self::Op<'y, 'x, 'z>>,
                >,
            >,
        >,
    >;

    /// Associative: (x ∘ y) ∘ z = x ∘ (y ∘ z)
    ///
    /// Relationally: `u = x∘y`, `v = y∘z`, `w = u∘z`, and then `x∘v = w`.
    fn assoc() -> Eq::Cert<
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
                            Output = &'l dyn for<'w> View<
                                'w,
                                Output = Eq::Imply<
                                    Self::Op<'x, 'y, 'u>,
                                    Eq::Imply<
                                        Self::Op<'y, 'z, 'v>,
                                        Eq::Imply<Self::Op<'u, 'z, 'w>, Self::Op<'x, 'v, 'w>>,
                                    >,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >;

    /// Identity exists: ∃e. El(e) ∧ IsUnitLike(e)
    fn identity_exists() -> Eq::Cert<
        Eq::Neg<
            &'l dyn for<'e> View<
                'e,
                Output = Eq::Imply<Self::El<'e>, Eq::Neg<IsUnitLike<'l, 'e, Self, Eq>>>,
            >,
        >,
    >;
}

/// An abelian group: a [`CommutativeMonoid`] in which every element has an
/// inverse.
///
/// This is the only axiom separating the two, and it is exactly the one a
/// field's multiplication fails at 0 — see the module docs.
pub trait AbelianGroup<'l, Eq>: CommutativeMonoid<'l, Eq>
where
    Self: 'l,
    Eq: Contraposition<'l> + Equality<'l> + ?Sized,
{
    /// Inverses: ∀x. El(x) → ∃y. El(y) ∧ (x ∘ y is neutral)
    fn inverse() -> Eq::Cert<
        &'l dyn for<'x> View<
            'x,
            Output = Eq::Imply<
                Self::El<'x>,
                Eq::Neg<
                    &'l dyn for<'y> View<
                        'y,
                        Output = Eq::Imply<
                            Self::El<'y>,
                            Eq::Neg<
                                &'l dyn for<'z> View<
                                    'z,
                                    Output = Eq::Imply<
                                        Self::Op<'x, 'y, 'z>,
                                        IsUnitLike<'l, 'z, Self, Eq>,
                                    >,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >;
}
