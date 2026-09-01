use super::{Cert, Imply as Implication, Negation, PropLogic, Reductio, exchange};
use ::core::{convert::Infallible, marker::PhantomData};

pub struct IntuitionisticImpl<Prop>(PhantomData<Prop>);

impl<Prop: PropLogic> Implication for IntuitionisticImpl<Prop> {
    type Imply<P, Q> = Prop::Imply<P, Q>;
    type Cert<P> = Prop::Cert<P>;
    fn mp<P, Q>(pq: Cert<Self, Self::Imply<P, Q>>, p: Cert<Self, P>) -> Cert<Self, Q> {
        pq.mp(p)
    }
}
impl<Prop: PropLogic> PropLogic for IntuitionisticImpl<Prop> {
    fn l1<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, P>>> {
        Prop::l1().cast()
    }
    fn l2<P, Q, R>() -> Cert<
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        Prop::l2().cast()
    }
}

impl<Prop: PropLogic> Negation for IntuitionisticImpl<Prop> {
    type Neg<P> = Prop::Imply<P, Infallible>;
}

/// `Reductio` needs no classical axiom: under `¬P := P → ⊥` it is just
/// [`exchange`] of antecedents, provable from L1/L2 alone. This is what
/// separates it from [`super::neg::Contraposition`], whose classical content
/// cannot be recovered here.
impl<Prop: PropLogic> Reductio for IntuitionisticImpl<Prop> {
    fn reductio<P, Q>()
    -> Cert<Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>> {
        exchange::<P, Q, Infallible, Prop>().cast()
    }
}
