#![forbid(unsafe_code)]

mod imply;

pub use self::imply::{Infer, L1, L2, PropLogic, PropLogicThm, ZeroCert};
use ::core::marker::PhantomData;

pub trait DeductionLogic<A>: PropLogic {
    type Assumption: Infer<A, A>;
    type MP<P, Q, PQ: Infer<P, Q>, APQ: Infer<A, PQ>, AP: Infer<A, P>>: Infer<A, Q>;
    fn mp<P, Q, PQ: Infer<P, Q>, APQ: Infer<A, PQ>, AP: Infer<A, P>>(
        pq: APQ,
        p: AP,
    ) -> Self::MP<P, Q, PQ, APQ, AP>;
}

pub trait Deduce {
    type P: Clone;
    type Q;
    type Output<Prop: DeductionLogic<Self::P>>: Infer<Self::P, Self::Q>;
    fn deduce<Prop: DeductionLogic<Self::P>>(p: Prop::Assumption) -> Self::Output<Prop>;
}

pub fn deduce<D: Deduce, Prop: PropLogic>() -> impl Infer<D::P, D::Q> {
    struct DeduceImpl<D, Prop>(PhantomData<(D, Prop)>);
    impl<D, Prop: PropLogic> PropLogic for DeduceImpl<D, Prop> {
        type L1<P, Q> = Prop::L1<P, Q>;
        type L2<P, Q, R, PQR, QR, PQ>
            = Prop::L2<P, Q, R, PQR, QR, PQ>
        where
            P: Clone,
            PQR: Infer<P, QR>,
            QR: Infer<Q, R>,
            PQ: Infer<P, Q>;
    }
    impl<D: Deduce, Prop: PropLogic> DeductionLogic<D::P> for DeduceImpl<D, Prop> {
        type Assumption = Reflexive<D::P, Prop>;
        type MP<P, Q, PQ: Infer<P, Q>, APQ: Infer<D::P, PQ>, AP: Infer<D::P, P>> =
            <Prop::L2<D::P, P, Q, APQ, PQ, AP> as L2<D::P, P, Q, APQ, PQ, AP>>::PR;
        fn mp<P, Q, PQ: Infer<P, Q>, APQ: Infer<D::P, PQ>, AP: Infer<D::P, P>>(
            pq: APQ,
            p: AP,
        ) -> Self::MP<P, Q, PQ, APQ, AP> {
            Prop::L2::default().mp(pq.into()).mp(p.into())
        }
    }
    D::deduce::<DeduceImpl<D, Prop>>(
        Prop::L2::default()
            .mp(Prop::L1::default().into())
            .mp(Prop::L1::default().into()),
    )
}

mod sealed_refl {
    use super::{L1, L2, PropLogic};

    type PQ<P, Prop> = <Prop as PropLogic>::L1<P, P>;
    type Q<P, Prop> = <PQ<P, Prop> as L1<P, P>>::QP;
    type PQR<P, Prop> = <Prop as PropLogic>::L1<P, Q<P, Prop>>;
    type QR<P, Prop> = <PQR<P, Prop> as L1<P, Q<P, Prop>>>::QP;
    pub type FullL2<P, Prop> =
        <Prop as PropLogic>::L2<P, Q<P, Prop>, P, PQR<P, Prop>, QR<P, Prop>, PQ<P, Prop>>;
    pub type Reflexive<P, Prop> =
        <FullL2<P, Prop> as L2<P, Q<P, Prop>, P, PQR<P, Prop>, QR<P, Prop>, PQ<P, Prop>>>::PR;
}
use self::sealed_refl::Reflexive;
