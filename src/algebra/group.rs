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
//! is a rational — while [`Group::inverse`](InverseExists::inverse) is false at
//! 0. Restricting `×`'s carrier to ℚ∖{0} to recover a group would make
//! `Op<'x, 'n, 'z>` unprovable for zero `n`, since
//! [`Closed::closed`] forces both arguments into the carrier. So
//! multiplicative inverses stay a *guarded* field axiom, and this module
//! supplies the part that really is shared.
//!
//! `Self` here is a plain marker for the operation and carries no logic of its
//! own: every proposition and certificate comes from the ambient `Eq`. That
//! keeps a consumer such as [`crate::logic::rat`] in one logic throughout,
//! instead of mixing the operation's `Imply` with the field's.

use crate::logic::function::Equality;
use crate::logic::prop::{And, FirstOrder};
use crate::macros::thm;
use crate::rel::Set;

macro_rules! expr {
    ($x:lifetime == $y:lifetime) => {
        Logic::Eq::<$x, $y>
    };
    ($x:lifetime * $y:lifetime == $z:lifetime) => {
        <Self as BinOp<'l, Logic>>::Op::<$x, $y, $z>
    };
}

pub trait BinOp<'l, Logic>
where
    Logic: FirstOrder<'l> + Equality<'l>,
{
    /// The operation's graph: `Op<'x, 'y, 'z>` means "x ∘ y = z"
    type Op<'x, 'y, 'z>;

    /// Functional (single-valued): ∀x ∀y ∀z ∀w. x ∘ y = z → x ∘ y = w → z = w
    fn single_valued() -> thm!(
        'l: { Logic },
        ForAll::<'x, 'y>(
            Call::<'z> = Self::Op::<'x, 'y>,
            Call::<'w> = Self::Op::<'x, 'y>,
            expr!('z == 'w)
        )
    );
}

pub trait Total<'l, Logic>: BinOp<'l, Logic> + Set
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l>,
{
    /// Total: ∀x ∀y. El(x) → El(y) → ∃z. El(z) ∧ x ∘ y = z
    fn total() -> thm!(
        'l: { Logic },
        Call::<'x> = Self::El,
        Call::<'y> = Self::El,
        Exists::<'z>(Self::El::<'z> && expr!('x * 'y == 'z))
    );
}

pub trait Closed<'l, Logic>: BinOp<'l, Logic> + Set
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l>,
{
    /// Closed: ∀x ∀y ∀z. x ∘ y = z → El(x) ∧ (El(y) ∧ El(z))
    fn closed() -> thm!(
        'l: { Logic },
        ForAll::<'x, 'y, 'z>(
            expr!('x * 'y == 'z).imply(Self::El::<'x> && Self::El::<'y> && Self::El::<'z>)
        )
    );
}

pub trait Commutative<'l, Logic>: BinOp<'l, Logic>
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l>,
{
    /// Commutative: ∀x ∀y ∀z. x ∘ y = z → y ∘ x = z
    fn comm() -> thm!(
        'l: { Logic },
        ForAll::<'x, 'y, 'z>(expr!('x * 'y == 'z).imply(expr!('y * 'x == 'z)))
    );
}

pub trait Associative<'l, Logic>: BinOp<'l, Logic>
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l>,
{
    /// Associative: (x ∘ y) ∘ z = x ∘ (y ∘ z)
    ///
    /// Relationally: `u = x∘y`, `v = y∘z`, `w = (u=x∘y)∘z`, and then `x∘v = w`.
    fn assoc() -> thm!(
        'l: { Logic },
        ForAll::<'x, 'y, 'z>(
            Call::<'xy> = Self::Op::<'x, 'y>,
            Call::<'yz> = Self::Op::<'y, 'z>,
            Call::<'xy_z> = Self::Op::<'xy, 'z>,
            expr!('x * 'yz == 'xy_z)
        )
    );
}

pub trait IdentityExists<'l, Logic>: BinOp<'l, Logic> + Set
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l>,
{
    /// Type alias: "e is neutral for the operation"
    /// Equivalent to: ∀y. El(y) → e ∘ y = y
    ///
    /// Note: doesn't require e to be in the carrier.
    /// [`IdentityExists::identity_exists`] adds that conjunct.
    type IsIdentity<'e>;
    fn identity_intro() -> thm!(
        'l: { Logic },
        ForAll::<'e>(Self::IsIdentity::<'e>.iff(Call::<'y> = Self::El, Self::Op::<'e, 'y, 'y>))
    );

    /// Identity exists: ∃e. El(e) ∧ IsUnitLike(e)
    fn identity_exists() -> thm!(
        'l: { Logic },
        Exists::<'e>(Self::El::<'e> && Self::IsIdentity::<'e>)
    );
}

pub trait InverseExists<'l, Logic>: BinOp<'l, Logic> + IdentityExists<'l, Logic>
where
    Logic: FirstOrder<'l> + Equality<'l> + And<'l>,
{
    /// Inverses: ∀x. El(x) → ∃y. El(y) ∧ (x ∘ y is neutral)
    fn inverse() -> thm!(
        'l: { Logic },
        Call::<'x> = Self::El,
        Exists::<'y>(Self::El::<'y> && (Call::<'z> = Self::Op::<'x, 'y>, Self::IsIdentity::<'z>))
    );
}

pub trait Monoid<'l, Eq>:
    Total<'l, Eq> + Closed<'l, Eq> + Associative<'l, Eq> + IdentityExists<'l, Eq> + 'l
where
    Eq: FirstOrder<'l> + Equality<'l> + And<'l>,
{
}
impl<'l, Eq, T: 'l> Monoid<'l, Eq> for T
where
    T: Total<'l, Eq> + Closed<'l, Eq> + Associative<'l, Eq> + IdentityExists<'l, Eq> + 'l,
    Eq: FirstOrder<'l> + Equality<'l> + And<'l>,
{
}

pub trait CommutativeMonoid<'l, Eq>
where
    Self: Monoid<'l, Eq> + Commutative<'l, Eq> + 'l,
    Eq: Equality<'l> + And<'l> + FirstOrder<'l>,
{
}
impl<'l, Eq, T: 'l> CommutativeMonoid<'l, Eq> for T
where
    Self: Monoid<'l, Eq> + Commutative<'l, Eq> + 'l,
    Eq: Equality<'l> + And<'l> + FirstOrder<'l>,
{
}

/// An abelian group: a [`CommutativeMonoid`] in which every element has an
/// inverse.
///
/// This is the only axiom separating the two, and it is exactly the one a
/// field's multiplication fails at 0 — see the module docs.
pub trait AbelianGroup<'l, Logic>:
    CommutativeMonoid<'l, Logic> + InverseExists<'l, Logic> + 'l
where
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
{
}
impl<'l, Logic, T: 'l> AbelianGroup<'l, Logic> for T
where
    T: CommutativeMonoid<'l, Logic> + InverseExists<'l, Logic> + 'l,
    Logic: Equality<'l> + And<'l> + FirstOrder<'l>,
{
}
