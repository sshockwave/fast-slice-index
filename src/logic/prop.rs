#![forbid(unsafe_code)]

mod imply;

pub use self::imply::{PropLogic, PropLogicThm};

mod sealed_deduction {
    use super::PropLogic;
    use ::core::marker::PhantomData;

    /// Deduction theorem: If
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);

    pub struct Cert<P, T> {
        witness: T,
        _marker: PhantomData<P>,
    }
    impl<'a, A, P: Clone, Prop: PropLogic<'a>> From<P>
        for Cert<(A, Prop), Prop::Cert<Prop::Imply<A, P>>>
    {
        fn from(value: P) -> Self {
            Cert {
                witness: Prop::mp(Prop::l1().into(), value.into()),
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
                witness: Prop::mp(
                    Prop::mp(Prop::l2().into(), Prop::l1::<_, Prop::Imply<A, _>>().into()),
                    Prop::l1().into(),
                ),
                _marker: PhantomData,
            }
        }
        pub fn finish<P: Clone>(
            value: <Self as PropLogic<'a>>::Cert<P>,
        ) -> Prop::Cert<Prop::Imply<A, P>>
        where
            A: Clone,
        {
            value.witness
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
        type Cert<P: Clone + 'a> = Cert<(A, Prop), Prop::Cert<Prop::Imply<A, P>>>;
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
    Deduction::finish(Deduction::finish(Deduction::finish(r)))
}
