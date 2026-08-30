use crate::logic::prop::{And, Imply, Intuitionistic, Negation, Or, neg::ProofRing};

mod base;

pub struct Axiomize;

impl<'l> Negation<'l> for Axiomize {
    type Neg<P: 'l> = <Self as Imply<'l>>::Imply<P, <Self as Intuitionistic<'l>>::False>;
}

impl<'l> And<'l> for Axiomize {
    type And<P: Clone + 'l, Q: Clone + 'l> = <ProofRing<Self> as And<'l>>::And<P, Q>;
    fn and_intro<P: Clone, Q: Clone>()
    -> super::prop::Cert<'l, Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>> {
        <ProofRing<Self> as And<'l>>::and_intro().cast()
    }
    fn and_left<P: Clone, Q: Clone>() -> super::prop::Cert<'l, Self, Self::Imply<Self::And<P, Q>, P>>
    {
        <ProofRing<Self> as And<'l>>::and_left().cast()
    }
    fn and_right<P: Clone, Q: Clone>()
    -> super::prop::Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>> {
        <ProofRing<Self> as And<'l>>::and_right().cast()
    }
}

impl<'l> Or<'l> for Axiomize {
    type Or<P: Clone + 'l, Q: Clone + 'l> = <ProofRing<Self> as Or<'l>>::Or<P, Q>;
    fn or_elim<P: Clone, Q: Clone, R: Clone>() -> super::prop::Cert<
        'l,
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        <ProofRing<Self> as Or<'l>>::or_elim().cast()
    }
    fn or_left<P: Clone, Q: Clone>() -> super::prop::Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>>
    {
        <ProofRing<Self> as Or<'l>>::or_left().cast()
    }
    fn or_right<P: Clone, Q: Clone>() -> super::prop::Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>>
    {
        <ProofRing<Self> as Or<'l>>::or_right().cast()
    }
}
