//! [`Axiomize`]'s successor vocabulary.
#![forbid(unsafe_code)]

use super::Axiomize;
use super::equality::SetIn;
use super::lang::IsSuccOf;
use crate::logic::prop::{And, Cert, Iff, reflexive};
use crate::rel::desc::Describes;
use crate::rel::succ::{SuccCond, Successor};

pub struct SetSucc;

impl Successor<Axiomize> for SetSucc {
    type Mem = SetIn;
    type Succ<'s, 'y> = IsSuccOf<'s, 'y>;

    fn succ_iff<'s, 'y>() -> Cert<Axiomize, Iff<Axiomize, IsSuccOf<'s, 'y>, Describes<'s, Axiomize, SetIn, SuccCond<'y, Axiomize, Self>>>> {
        <Axiomize as And>::and_intro().mp(reflexive()).mp(reflexive())
    }
}
