//! [`Axiomize`]'s singleton and unordered-pair vocabulary.
//!
//! The proofs about those notions live in [`crate::rel::pair`].  This module
//! only identifies its opaque vocabulary with the definitions in
//! [`super::lang`], one unfolding at a time.
#![forbid(unsafe_code)]

use super::Axiomize;
use super::lang::{IsPair, IsSingleton};
use crate::logic::prop::{And, Cert, Iff, reflexive};
use crate::rel::desc::Describes;
use crate::rel::pair::{PairCond, Pairing, SingletonCond};

/// Singletons and unordered pairs on the universe of sets.
impl Pairing<Axiomize> for Axiomize {
    type Mem = Axiomize;

    type Singleton<'s, 'a> = IsSingleton<'s, 'a>;
    type Pair<'p, 'a, 'b> = IsPair<'p, 'a, 'b>;

    fn singleton_iff<'s, 'a>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            IsSingleton<'s, 'a>,
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
            IsPair<'p, 'a, 'b>,
            Describes<'p, Axiomize, Axiomize, PairCond<'a, 'b, Axiomize, Axiomize>>,
        >,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }
}
