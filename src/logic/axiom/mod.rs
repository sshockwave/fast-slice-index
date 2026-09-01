use crate::logic::prop::{And, Imply, Intuitionistic, Negation, Or, neg::ProofRing};

mod base;

pub struct Axiomize;

impl Negation for Axiomize {
    type Neg<P> = <Self as Imply>::Imply<P, <Self as Intuitionistic>::False>;
}

impl And for Axiomize {
    type And<P, Q> = <ProofRing<Self> as And>::And<P, Q>;
    fn and_intro<P, Q>() -> super::prop::Cert<Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>>
    {
        <ProofRing<Self> as And>::and_intro().cast()
    }
    fn and_left<P, Q>() -> super::prop::Cert<Self, Self::Imply<Self::And<P, Q>, P>> {
        <ProofRing<Self> as And>::and_left().cast()
    }
    fn and_right<P, Q>() -> super::prop::Cert<Self, Self::Imply<Self::And<P, Q>, Q>> {
        <ProofRing<Self> as And>::and_right().cast()
    }
}

impl Or for Axiomize {
    type Or<P, Q> = <ProofRing<Self> as Or>::Or<P, Q>;
    fn or_elim<P, Q, R>() -> super::prop::Cert<
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        <ProofRing<Self> as Or>::or_elim().cast()
    }
    fn or_left<P, Q>() -> super::prop::Cert<Self, Self::Imply<P, Self::Or<P, Q>>> {
        <ProofRing<Self> as Or>::or_left().cast()
    }
    fn or_right<P, Q>() -> super::prop::Cert<Self, Self::Imply<Q, Self::Or<P, Q>>> {
        <ProofRing<Self> as Or>::or_right().cast()
    }
}
