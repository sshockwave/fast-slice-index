#![forbid(unsafe_code)]

mod imply;
mod neg;

pub use self::{
    imply::{PropLogic, PropLogicThm},
    neg::{Contraposition, DoubleNegation, Neg, PeirceLaw, ProofRing as NegProofRing},
};

pub fn reflexive<'a, P, Prop: PropLogic<'a>>() -> Prop::Cert<Prop::Imply<P, P>>
where
    P: Clone + 'a,
{
    Prop::mp(
        Prop::mp(Prop::l2().into(), Prop::l1::<_, Prop::Imply<P, _>>().into()),
        Prop::l1().into(),
    )
}

mod sealed_deduction {
    use crate::logic::prop::reflexive;

    use super::PropLogic;
    use ::core::marker::PhantomData;

    /// Deduction theorem: If
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);

    pub struct Cert<'a, A: 'a, P: 'a, Prop: PropLogic<'a>> {
        witness: Prop::Cert<Prop::Imply<A, P>>,
        _marker: PhantomData<P>,
    }
    impl<'a, A, P: Clone, Prop: PropLogic<'a>> From<P> for Cert<'a, A, P, Prop> {
        fn from(value: P) -> Self {
            Cert {
                witness: Prop::mp(Prop::l1().into(), value.into()),
                _marker: PhantomData,
            }
        }
    }
    impl<'a, A, P, Prop: PropLogic<'a>> Clone for Cert<'a, A, P, Prop> {
        fn clone(&self) -> Self {
            Cert {
                witness: self.witness.clone(),
                _marker: PhantomData,
            }
        }
    }

    impl<'a, A, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn assume() -> <Self as PropLogic<'a>>::Cert<A>
        where
            A: Clone,
        {
            Cert {
                witness: reflexive::<_, Prop>(),
                _marker: PhantomData,
            }
        }
    }
    impl<'a, A: 'a, P: 'a, Prop: PropLogic<'a>> Cert<'a, A, P, Prop> {
        pub fn finish(self) -> Prop::Cert<Prop::Imply<A, P>> {
            self.witness
        }
    }

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> PropLogic<'a> for Deduction<A, Prop> {
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
        type Cert<P: Clone + 'a> = Cert<'a, A, P, Prop>;
        fn mp<P: Clone, Q: Clone>(
            pq: Self::Cert<Self::Imply<P, Q>>,
            p: Self::Cert<P>,
        ) -> Self::Cert<Q> {
            Cert {
                witness: Prop::mp(Prop::mp(Prop::l2().into(), pq.witness), p.witness),
                _marker: PhantomData,
            }
        }
        fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P> {
            Cert {
                witness: Prop::mp(Prop::l1().into(), value),
                _marker: PhantomData,
            }
        }
    }
}
pub use sealed_deduction::Deduction;

pub fn syllogism<'a, P, Q, R, Prop: PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
    R: Clone + 'a,
{
    let pq = Deduction::<_, Prop>::assume();
    let qr = Deduction::<_, Deduction<_, _>>::assume();
    let p = Deduction::<_, Deduction<_, _>>::assume();
    let r = Deduction::mp(
        Deduction::upgrade(qr),
        Deduction::mp(Deduction::upgrade(Deduction::upgrade(pq)), p),
    );
    r.finish().finish().finish()
}
