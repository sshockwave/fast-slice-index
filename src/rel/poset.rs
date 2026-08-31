use super::Set;
use crate::logic::function::Equality;
use crate::logic::prop::{FirstOrder, Imply};
use crate::macros::thm;

pub trait BinRel {
    type Rel<'a, 'b>;
}

pub trait Reflexive<'l, Logic>: Set + BinRel + 'l
where
    Logic: Imply<'l> + FirstOrder<'l>,
{
    fn refl() -> thm!('l: { Logic }, 'a: { Self::El::<'a> }, Self::Rel::<'a, 'a>);
}

pub trait Antisymmetric<'l, Logic>: Set + BinRel + 'l
where
    Logic: Imply<'l> + FirstOrder<'l> + Equality<'l>,
{
    fn antisym() -> thm!(
        'l: { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        Self::Rel::<'a, 'b>.imply(Self::Rel::<'b, 'a>.imply(Logic::Eq::<'a, 'b>))
    );
}

pub trait Transitive<'l, Logic>: Set + BinRel + 'l
where
    Logic: Imply<'l> + FirstOrder<'l>,
{
    fn transitive() -> thm!(
        'l: { Logic },
        'a: { Self::El::<'a> },
        'b: { Self::El::<'b> },
        'c: { Self::El::<'c> },
        Self::Rel::<'a, 'b>.imply(Self::Rel::<'b, 'c>.imply(Self::Rel::<'a, 'c>))
    );
}

pub trait Poset<'l, Logic>:
    Reflexive<'l, Logic> + Antisymmetric<'l, Logic> + Transitive<'l, Logic>
where
    Logic: Imply<'l> + FirstOrder<'l> + Equality<'l>,
{
}
impl<'l, Logic, T> Poset<'l, Logic> for T
where
    Self: Reflexive<'l, Logic> + Antisymmetric<'l, Logic> + Transitive<'l, Logic>,
    Logic: Imply<'l> + FirstOrder<'l> + Equality<'l>,
{
}
