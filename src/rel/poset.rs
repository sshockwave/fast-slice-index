use super::Set;
use crate::logic::function::Equality;
use crate::logic::prop::{FirstOrder, Imply};
use crate::macros::thm;

pub trait BinRel {
    type Rel<'a, 'b>;
}

pub trait Reflexive<Logic>: Set + BinRel
where
    Logic: Imply + FirstOrder,
{
    fn refl() -> thm!({ Logic }, 'a: { Self::El::<'a> }, Self::Rel::<'a, 'a>);
}

pub trait Symmetric<Logic>: Set + BinRel
where
    Logic: Imply + FirstOrder,
{
    fn sym() -> thm!(
        { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        Self::Rel::<'a, 'b> >>= Self::Rel::<'b, 'a>
    );
}

pub trait Antisymmetric<Logic>: Set + BinRel
where
    Logic: Imply + FirstOrder + Equality,
{
    fn antisym() -> thm!(
        { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        Self::Rel::<'a, 'b>.imply(Self::Rel::<'b, 'a>.imply(Logic::Eq::<'a, 'b>))
    );
}

pub trait Transitive<Logic>: Set + BinRel
where
    Logic: Imply + FirstOrder,
{
    fn transitive() -> thm!(
        { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        'c: { Self::El::<'c> },
        Self::Rel::<'a, 'b>.imply(Self::Rel::<'b, 'c>.imply(Self::Rel::<'a, 'c>))
    );
}

pub trait Poset<Logic>: Reflexive<Logic> + Antisymmetric<Logic> + Transitive<Logic>
where
    Logic: Imply + FirstOrder + Equality,
{
}
impl<Logic, T> Poset<Logic> for T
where
    T: Reflexive<Logic> + Antisymmetric<Logic> + Transitive<Logic>,
    Logic: Imply + FirstOrder + Equality,
{
}

pub trait Equivalence<Logic>: Reflexive<Logic> + Transitive<Logic> + Symmetric<Logic>
where
    Logic: Imply + FirstOrder,
{
}
impl<Logic, T> Equivalence<Logic> for T
where
    Self: Reflexive<Logic> + Transitive<Logic> + Symmetric<Logic>,
    Logic: Imply + FirstOrder,
{
}
