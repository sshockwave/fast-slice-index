//! [`Axiomize`]'s successor vocabulary.
#![forbid(unsafe_code)]

use super::Axiomize;
use crate::logic::prop::{And, Cert, Iff, reflexive};
use crate::rel::desc::Describes;
use crate::rel::succ::{SuccCond, Successor};

impl Successor<Axiomize> for Axiomize {
    type Mem = Axiomize;
    type Succ<'s, 'y> = Describes<'s, Axiomize, Axiomize, SuccCond<'y, Axiomize, Axiomize>>;

    fn succ_iff<'s, 'y>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            Self::Succ<'s, 'y>,
            Describes<'s, Axiomize, Axiomize, SuccCond<'y, Axiomize, Axiomize>>,
        >,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }
}
