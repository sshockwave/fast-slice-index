#![forbid(unsafe_code)]

mod imply;

pub use self::imply::{PropLogic, PropLogicThm};
use ::core::marker::PhantomData;

/// Deduction theorem: If
pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);
mod sealed_deduction {
    use super::{Deduction, PropLogic};
    pub struct Cert<'a, A: 'a, P: 'a, Prop: PropLogic<'a>>(Prop::Cert<Prop::Imply<A, P>>);
    impl<'a, A, P: Clone, Prop: PropLogic<'a>> From<P> for Cert<'a, A, P, Prop> {
        fn from(value: P) -> Self {
            Cert(Prop::mp(Prop::l1().into(), value.into()))
        }
    }

    impl<'a, A, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn finish<P: Clone>(
            value: <Self as PropLogic<'a>>::Cert<P>,
        ) -> Prop::Cert<Prop::Imply<A, P>>
        where
            A: Clone,
        {
            value.0
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
        type Cert<P: Clone + 'a> = Cert<'a, A, P, Prop>;
        fn mp<P: Clone, Q: Clone>(
            pq: Self::Cert<Self::Imply<P, Q>>,
            p: Self::Cert<P>,
        ) -> Self::Cert<Q> {
            Cert(Prop::mp(Prop::mp(Prop::l2().into(), pq.0), p.0))
        }
    }
}
