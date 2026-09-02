//! [`Axiomize`]'s equality, packaged as a structure.
//!
//! Nothing is proved here. The mathematics is in [`super::theorems`]
//! ([`eq_refl`], [`eq_symm`], [`eq_trans`]); the bridge from those closed
//! theorems to the guarded shape [`crate::rel::poset`] asks for is in
//! [`crate::rel::eq`], generic over the logic. This module only names the two and lets them meet, which is the
//! delegation pattern the whole `concrete` layer is headed for.
//!
//! Keeping the bridge generic is not tidiness. Its proof terms mention
//! `S::Rel<'a, 'b>` at a type parameter, which rustc cannot expand; written
//! here against the defined [`Eq`] they would mention a 116 KB type instead,
//! and `mir_borrowck` cost scales with that. See [`crate::rel::set`].
#![forbid(unsafe_code)]

use super::Axiomize;
use super::lang::{Eq, IsSet};
use super::theorems::{eq_refl, eq_symm, eq_trans};
use crate::logic::function::EqualityDef;
use crate::macros::thm;
use crate::rel::eq::{Closed, ClosedEq};

/// `=` on the universe of sets, as closed theorems.
pub struct SetEq;

impl ClosedEq<Axiomize> for SetEq {
    type El<'a> = IsSet<'a>;
    type Rel<'a, 'b> = Eq<'a, 'b>;

    fn refl() -> thm!({ Axiomize }, ForAll::<'a>(Self::Rel::<'a, 'a>)) {
        eq_refl()
    }

    fn sym() -> thm!(
        { Axiomize },
        ForAll::<'a, 'b>(Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'a>)
    ) {
        eq_symm()
    }

    fn trans() -> thm!(
        { Axiomize },
        ForAll::<'a, 'b, 'c>(
            Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'c> >>= Self::Rel::<'a, 'c>
        )
    ) {
        eq_trans()
    }
}

/// The universe of sets under `=`, as a [`poset`](crate::rel::poset) relation.
pub type SetEqRel = Closed<Axiomize, SetEq>;

impl EqualityDef for Axiomize {
    type EqRel = SetEqRel;
}
