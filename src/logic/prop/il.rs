use super::{Cert, Imply, Negation, PropLogic, Reductio, exchange};
use ::core::{convert::Infallible, marker::PhantomData};

pub struct IntuitionisticImpl<'l, Prop>(PhantomData<(&'l (), Prop)>);

impl<'a, Prop: PropLogic<'a>> Imply<'a> for IntuitionisticImpl<'a, Prop> {
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Cert<'a, Self, Self::Imply<P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        pq.mp(p)
    }
    fn def<P, Q>() -> Cert<'a, Self, Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a,
    {
        Prop::def().cast()
    }
}
impl<'a, Prop: PropLogic<'a>> PropLogic<'a> for IntuitionisticImpl<'a, Prop> {
    fn l1<P: Clone + 'a, Q>() -> Cert<'a, Self, Self::Imply<P, Self::Imply<Q, P>>> {
        Prop::l1().cast()
    }
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<
        'a,
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        Prop::l2().cast()
    }
}

impl<'l, Prop: PropLogic<'l>> Negation<'l> for IntuitionisticImpl<'l, Prop> {
    type Neg<P: 'l> = Prop::Imply<P, Infallible>;
}

/// `Reductio` needs no classical axiom: under `¬P := P → ⊥` it is just
/// [`exchange`] of antecedents, provable from L1/L2 alone. This is what
/// separates it from [`super::neg::Contraposition`], whose classical content
/// cannot be recovered here.
impl<'l, Prop: PropLogic<'l>> Reductio<'l> for IntuitionisticImpl<'l, Prop> {
    fn reductio<P: Clone + 'l, Q: Clone + 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>> {
        exchange::<P, Q, Infallible, Prop>().cast()
    }
}
