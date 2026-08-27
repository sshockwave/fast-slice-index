#![forbid(unsafe_code)]

mod imply;

pub use self::imply::{Imply, Infer, IntoInfer, L1, L2, PropLogic, PropLogicThm, ZeroCert};
use ::core::marker::PhantomData;

pub trait DeductionLogic<A>: PropLogic {
    type Assumption: Infer<A, A>;
    type MP<P, Q, PQ: Infer<P, Q>, APQ: Infer<A, PQ>, AP: Infer<A, P>>: Infer<A, Q>;
    fn mp<P, Q, PQ: Infer<P, Q>, APQ: Infer<A, PQ>, AP: Infer<A, P>>(
        pq: APQ,
        p: AP,
    ) -> Self::MP<P, Q, PQ, APQ, AP>;
    type Cert<P>: Infer<A, P>;
    fn make_cert<P>(p: P) -> Self::Cert<P>;
}

pub trait Deduce {
    type P: Clone;
    type Q;
    type Output<Prop: DeductionLogic<Self::P>>: Infer<Self::P, Self::Q>;
    fn deduce<Prop: DeductionLogic<Self::P>>(self, p: Prop::Assumption) -> Self::Output<Prop>;
}
/// Deduction theorem: If we can derive Q from P, then we can derive (P → Q) from nothing.
pub struct Deduction<D, Prop>(PhantomData<Prop>, D);
impl<D, Prop> From<D> for Deduction<D, Prop> {
    fn from(value: D) -> Self {
        Self(PhantomData, value)
    }
}
impl<D, Prop: PropLogic> PropLogic for Deduction<D, Prop> {
    type L1<P, Q> = Prop::L1<P, Q>;
    type L2<P, Q, R, PQR, QR, PQ>
        = Prop::L2<P, Q, R, PQR, QR, PQ>
    where
        P: Clone,
        PQR: Infer<P, QR>,
        QR: Infer<Q, R>,
        PQ: Infer<P, Q>;
}
impl<D: Deduce, Prop: PropLogic> DeductionLogic<D::P> for Deduction<D, Prop> {
    type Assumption = Imply<Reflexive<D::P, Prop>>;
    type MP<P, Q, PQ: Infer<P, Q>, APQ: Infer<D::P, PQ>, AP: Infer<D::P, P>> =
        <Prop::L2<D::P, P, Q, APQ, PQ, AP> as L2<D::P, P, Q, APQ, PQ, AP>>::PR;
    fn mp<P, Q, PQ: Infer<P, Q>, APQ: Infer<D::P, PQ>, AP: Infer<D::P, P>>(
        pq: APQ,
        p: AP,
    ) -> Self::MP<P, Q, PQ, APQ, AP> {
        Prop::L2::default().mp(pq.into()).mp(p.into())
    }
    type Cert<P> = <Prop::L1<P, D::P> as L1<P, D::P>>::QP;
    fn make_cert<P>(p: P) -> Self::Cert<P> {
        Prop::L1::default().mp(p.into())
    }
}
impl<D: Deduce, Prop: PropLogic> IntoInfer<D::P, D::Q> for Deduction<D, Prop> {
    type Infer = D::Output<Self>;
    fn into_infer(self) -> Self::Infer {
        self.1.deduce(Default::default())
    }
}

mod sealed_refl {
    use super::{Infer, IntoInfer, L1, L2, PropLogic};
    use ::core::marker::PhantomData;

    type PQ<P, Prop> = <Prop as PropLogic>::L1<P, P>;
    type Q<P, Prop> = <PQ<P, Prop> as L1<P, P>>::QP;
    type PQR<P, Prop> = <Prop as PropLogic>::L1<P, Q<P, Prop>>;
    type QR<P, Prop> = <PQR<P, Prop> as L1<P, Q<P, Prop>>>::QP;
    pub struct Reflexive<P, Prop>(PhantomData<(P, Prop)>);
    impl<P, Prop> Default for Reflexive<P, Prop> {
        fn default() -> Self {
            Self(PhantomData)
        }
    }
    impl<P: Clone, Prop: PropLogic> IntoInfer<P, P> for Reflexive<P, Prop> {
        type Infer = <Prop::L2<P, Q<P, Prop>, P, PQR<P, Prop>, QR<P, Prop>, PQ<P, Prop>> as L2<
            P,
            Q<P, Prop>,
            P,
            PQR<P, Prop>,
            QR<P, Prop>,
            PQ<P, Prop>,
        >>::PR;
        fn into_infer(self) -> Self::Infer {
            Prop::L2::default()
                .mp(Prop::L1::default().into())
                .mp(Prop::L1::default().into())
        }
    }
}
use self::sealed_refl::Reflexive;
