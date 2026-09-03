//! [`Axiomize`]'s singleton and unordered-pair vocabulary.
//!
//! The proofs about those notions live in [`crate::rel::pair`].  This module
//! only identifies its vocabulary with the generic descriptions, one
//! unfolding at a time.
#![forbid(unsafe_code)]

use super::Axiomize;
use crate::logic::prop::{And, Cert, Iff, reflexive};
use crate::rel::desc::Describes;
use crate::rel::pair::{PairCond, Pairing, SingletonCond};

/// Singletons and unordered pairs on the universe of sets.
impl Pairing<Axiomize> for Axiomize {
    type Mem = Axiomize;

    type Singleton<'s, 'a> = Describes<'s, Axiomize, Axiomize, SingletonCond<'a, Axiomize, Axiomize>>;
    type Pair<'p, 'a, 'b> = Describes<'p, Axiomize, Axiomize, PairCond<'a, 'b, Axiomize, Axiomize>>;

    fn singleton_iff<'s, 'a>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            Self::Singleton<'s, 'a>,
            Describes<'s, Axiomize, Axiomize, SingletonCond<'a, Axiomize, Axiomize>>,
        >,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }

    fn pair_iff<'p, 'a, 'b>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            Self::Pair<'p, 'a, 'b>,
            Describes<'p, Axiomize, Axiomize, PairCond<'a, 'b, Axiomize, Axiomize>>,
        >,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }
}
