//! ZFC as a generic set-theory interface.
//!
//! The vocabulary is inherited from the smaller relation traits. Each method
//! states one axiom directly, in the same style as the algebraic law traits.
//! At a generic `Z: Zfc<Logic>` boundary, membership, pairing, successor, and
//! application remain rigid associated projections rather than expanding a
//! concrete set-language encoding.

use crate::algebra::group::BinOp;
use crate::logic::function::Equality;
use crate::logic::prop::{And, FirstOrder, Negation, Or, PropLogic, View};
use crate::macros::thm;
use crate::rel::empty::IsEmpty;
use crate::rel::ext::{ExtEq, Membership};
use crate::rel::func::Application;
use crate::rel::pair::Pairing;
use crate::rel::succ::Successor;

/// A set theory satisfying the ZFC axioms.
pub trait Zfc<Logic>:
    Membership<Logic>
    + Pairing<Logic, Mem = Self>
    + Successor<Logic, Mem = Self>
    + Application<Logic, Mem = Self>
    + 'static
where
    Logic: PropLogic + And + Or + Negation + FirstOrder + Equality,
{
    /// Extensionality, in the congruence direction not supplied by the
    /// definition of [`ExtEq`].
    fn extensionality() -> thm!(
        { Logic },
        ForAll::<'x, 'y, 'w>(
            ExtEq::<'x, 'y, Logic, Self>
                >>= Self::In::<'x, 'w>
                >>= Self::In::<'y, 'w>
        )
    );

    /// Pairing: `forall x y. exists p. p = {x, y}`.
    fn pairing() -> thm!(
        { Logic },
        ForAll::<'x, 'y>(Exists::<'p>(Self::Pair::<'p, 'x, 'y>))
    );

    /// Union: every set has a union.
    fn union() -> thm!(
        { Logic },
        ForAll::<'f>(Exists::<'u>(ForAll::<'z>(
            Self::In::<'z, 'u>.iff(Exists::<'y>(
                Self::In::<'z, 'y> && Self::In::<'y, 'f>
            ))
        )))
    );

    /// Separation schema.
    fn separation<P>() -> thm!(
        { Logic },
        ForAll::<'a>(Exists::<'s>(ForAll::<'z>(
            Self::In::<'z, 's>.iff(Self::In::<'z, 'a> && <P as View<'z>>::Output)
        )))
    )
    where
        P: for<'z> View<'z> + ?Sized;

    /// Power set: every set has a set of all its subsets.
    fn power_set() -> thm!(
        { Logic },
        ForAll::<'x>(Exists::<'p>(ForAll::<'z>(
            Self::In::<'z, 'p>.iff(ForAll::<'w>(
                Self::In::<'w, 'z> >>= Self::In::<'w, 'x>
            ))
        )))
    );

    /// Regularity: every nonempty set has a membership-minimal member.
    fn regularity() -> thm!(
        { Logic },
        ForAll::<'x>(
            Exists::<'y>(Self::In::<'y, 'x>).imply(Exists::<'y>(
                Self::In::<'y, 'x>
                    && !Exists::<'z>(Self::In::<'z, 'y> && Self::In::<'z, 'x>)
            ))
        )
    );

    /// Infinity: an inductive set exists.
    fn infinity() -> thm!(
        { Logic },
        Exists::<'i>(
            Exists::<'e>(Self::In::<'e, 'i> && IsEmpty::<'e, Logic, Self>)
                && ForAll::<'y>(
                    Self::In::<'y, 'i>
                        >>= Exists::<'s>(Self::In::<'s, 'i> && Self::Succ::<'s, 'y>)
                )
        )
    );

    /// Replacement for the unary function obtained by fixing the second
    /// argument of `R`. [`BinOp::single_valued`] supplies functionality.
    fn replacement<'parameter, R>() -> thm!(
        { Logic },
        ForAll::<'a>(Exists::<'b>(ForAll::<'y>(
            Self::In::<'y, 'b>.iff(Exists::<'x>(
                Self::In::<'x, 'a> && R::Op::<'x, 'parameter, 'y>
            ))
        )))
    )
    where
        R: BinOp<Logic>;

    /// Choice: every set of nonempty sets admits a choice function.
    fn choice() -> thm!(
        { Logic },
        ForAll::<'a>(
            ForAll::<'x>(
                Self::In::<'x, 'a>.imply(Exists::<'w>(Self::In::<'w, 'x>))
            ).imply(Exists::<'c>(
                Self::IsFunction::<'c>
                    && ForAll::<'x>(
                        Self::In::<'x, 'a>.imply(Exists::<'w>(
                            Self::App::<'c, 'x, 'w> && Self::In::<'w, 'x>
                        ))
                    )
            ))
        )
    );
}
