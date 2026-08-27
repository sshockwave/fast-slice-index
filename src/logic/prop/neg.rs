use crate::logic::prop::{PropLogic, reflexive, syllogism};
use ::core::marker::PhantomData;

pub struct Neg<P>(PhantomData<P>);

impl<P> Clone for Neg<P> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<P> Copy for Neg<P> {}

pub trait Contraposition<'a>: PropLogic<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Imply<Neg<P>, Neg<Q>>, Self::Imply<Q, P>>>;
}

pub trait DoubleNegation<'a>: PropLogic<'a> {
    fn l3<P>() -> Self::Cert<Self::Imply<Neg<Neg<P>>, P>>;
}

pub trait PeirceLaw<'a>: PropLogic<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>>;
}

pub struct ProofRing<'a, Prop>(PhantomData<(&'a (), Prop)>);

impl<'a, Prop> PropLogic<'a> for ProofRing<'a, Prop>
where
    Prop: PropLogic<'a>,
{
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    fn l1<P: Clone + 'a, Q>() -> Self::Imply<P, Self::Imply<Q, P>> {
        Prop::l1()
    }
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Self::Imply<
        Self::Imply<P, Self::Imply<Q, R>>,
        Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
    > {
        Prop::l2()
    }
    type BaseCert<P: Clone + 'a> = Prop::Cert<P>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Self::Cert<Self::Imply<P, Q>>,
        p: Self::Cert<P>,
    ) -> Self::Cert<Q> {
        Prop::mp(pq, p)
    }
    fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P> {
        value
    }
}

impl<'a, Prop> DoubleNegation<'a> for ProofRing<'a, Prop>
where
    Prop: Contraposition<'a>,
{
    fn l3<P>() -> Self::Cert<Self::Imply<Neg<Neg<P>>, P>>
    where
        P: 'a,
    {
        // https://math.stackexchange.com/questions/4634566/prove-that-contrapositive-rule-is-equivalent-to-the-rule-of-double-negation
        Prop::mp(
            Prop::mp(
                Prop::l2().into(),
                Prop::mp(
                    Prop::mp(
                        syllogism::<_, _, _, Prop>(),
                        Prop::mp(
                            Prop::mp(syllogism::<_, _, _, Prop>(), Prop::l1().into()),
                            Prop::l3(),
                        ),
                    ),
                    Prop::l3(),
                ),
            ),
            reflexive::<_, Prop>(),
        )
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a>> ExFalsoQuodlibet<'a> for ProofRing<'a, Prop> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Neg<P>, Self::Imply<P, Q>>> {
        Prop::mp(
            Prop::mp(syllogism::<_, _, _, Prop>(), Prop::l1().into()),
            Prop::l3(),
        )
    }
}

// TODO: Prove Peirce's law
