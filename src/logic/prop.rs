#![forbid(unsafe_code)]

mod sealed_infer {
    pub trait Sealed {}
}
use self::sealed_infer::Sealed;
use ::core::marker::PhantomData;

/// Implication: P implies Q
pub trait Infer<P, Q>: Sealed {
    type Cert: From<P>;

    /// Modus Ponens: Given (P → Q) and P, derive Q
    /// This is the only inference rule - all others are axioms
    fn mp(self, p: Self::Cert) -> Q;
}

mod sealed_cert {
    use ::core::marker::PhantomData;

    pub struct ZeroCert<P>(PhantomData<P>);
    impl<P> Default for ZeroCert<P> {
        fn default() -> Self {
            Self(PhantomData)
        }
    }
}
pub use sealed_cert::ZeroCert;

impl<P> Clone for ZeroCert<P> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<P> Copy for ZeroCert<P> {}
impl<P> From<P> for ZeroCert<P> {
    fn from(_: P) -> Self {
        Default::default()
    }
}

/// Axiom L1: P → (Q → P)
/// If P is true, then Q implies P
pub trait L1<P, Q>: Infer<P, Self::QP> {
    type QP: Infer<Q, P>;
}

/// Axiom L2: (P → (Q → R)) → ((P → Q) → (P → R))
/// Distribution of implication
pub trait L2<P, Q, R, PQR, QR, PQ>: Infer<PQR, Self::PQPR> {
    type PQPR: Infer<PQ, Self::PR>;
    type PR: Infer<P, R>;
}

/// Axiomatic propositional logic
///
/// This is a logic system where all theorems are derived from axioms using inference rules.
/// Rust type system implies propositional logic,
/// so we can prove this in [`PropLogicThm`] without any unsafe code.
pub trait PropLogic {
    type L1<P, Q>: L1<P, Q> + Default + Copy;
    type L2<P, Q, R, PQR, QR, PQ>: L2<P, Q, R, PQR, QR, PQ> + Default + Copy
    where
        P: Clone,
        PQR: Infer<P, QR>,
        QR: Infer<Q, R>,
        PQ: Infer<P, Q>;
}

pub struct PropLogicThm;

mod sealed_prop_logic {
    use super::{Infer, L1, L2, PropLogic, PropLogicThm, Sealed, ZeroCert};
    use ::core::marker::PhantomData;

    pub struct Store<P>(P);

    impl<P> Sealed for Store<P> {}
    impl<P, Q> Infer<P, Q> for Store<Q> {
        type Cert = ZeroCert<P>;
        fn mp(self, _: Self::Cert) -> Q {
            self.0
        }
    }
    pub struct L1Proof<P, Q>(PhantomData<(P, Q)>);
    impl<P, Q> Sealed for L1Proof<P, Q> {}
    impl<P, Q> L1<P, Q> for L1Proof<P, Q> {
        type QP = Store<P>;
    }
    impl<P, Q> Infer<P, Store<P>> for L1Proof<P, Q> {
        type Cert = P;
        fn mp(self, p: P) -> Store<P> {
            Store(p)
        }
    }
    impl<P, Q> Clone for L1Proof<P, Q> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<P, Q> Copy for L1Proof<P, Q> {}
    impl<P, Q> Default for L1Proof<P, Q> {
        fn default() -> Self {
            Self(PhantomData)
        }
    }
    pub trait Params {
        type P: Clone;
        type Q;
        type R;
        type PQR: Infer<Self::P, Self::QR>;
        type QR: Infer<Self::Q, Self::R>;
        type PQ: Infer<Self::P, Self::Q>;
    }
    impl<P: Clone, Q, R, PQR: Infer<P, QR>, QR: Infer<Q, R>, PQ: Infer<P, Q>> Params
        for (P, Q, R, PQR, QR, PQ)
    {
        type P = P;
        type Q = Q;
        type R = R;
        type PQR = PQR;
        type QR = QR;
        type PQ = PQ;
    }
    pub struct Store1<L: Params> {
        pqr: L::PQR,
    }
    impl<L: Params> Sealed for Store1<L> {}
    impl<L: Params> Infer<L::PQ, Store2<L>> for Store1<L> {
        type Cert = L::PQ;
        fn mp(self, pq: L::PQ) -> Store2<L> {
            Store2 { pqr: self.pqr, pq }
        }
    }
    pub struct Store2<L: Params> {
        pqr: L::PQR,
        pq: L::PQ,
    }
    impl<L: Params> Sealed for Store2<L> {}
    impl<L: Params> Infer<L::P, L::R> for Store2<L> {
        type Cert = L::P;
        fn mp(self, p: L::P) -> L::R {
            self.pqr
                .mp(p.clone().into())
                .mp(self.pq.mp(p.into()).into())
        }
    }
    pub struct L2Proof<L>(PhantomData<L>);
    impl<L: Params> Sealed for L2Proof<L> {}
    impl<L: Params> L2<L::P, L::Q, L::R, L::PQR, L::QR, L::PQ> for L2Proof<L> {
        type PQPR = Store1<L>;
        type PR = Store2<L>;
    }
    impl<L: Params> Infer<L::PQR, Store1<L>> for L2Proof<L> {
        type Cert = L::PQR;
        fn mp(self, pqr: L::PQR) -> Store1<L> {
            Store1 { pqr }
        }
    }
    impl<L> Clone for L2Proof<L> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<L> Copy for L2Proof<L> {}
    impl<L> Default for L2Proof<L> {
        fn default() -> Self {
            Self(PhantomData)
        }
    }
    impl PropLogic for PropLogicThm {
        type L1<P, Q> = L1Proof<P, Q>;
        type L2<P: Clone, Q, R, PQR: Infer<P, QR>, QR: Infer<Q, R>, PQ: Infer<P, Q>> =
            L2Proof<(P, Q, R, PQR, QR, PQ)>;
    }
}

pub trait DeductionLogic<A>: PropLogic {
    type Assumption: Infer<A, A>;
    fn mp<P, Q, PQ: Infer<P, Q>>(pq: impl Infer<A, PQ>, p: impl Infer<A, P>) -> impl Infer<A, Q>;
}

pub trait Deduce {
    type P: Clone;
    type Q;
    fn deduce<Prop: DeductionLogic<Self::P>>(p: Prop::Assumption) -> impl Infer<Self::P, Self::Q>;
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
        fn mp<P, Q, PQ: Infer<P, Q>>(
            pq: impl Infer<D::P, PQ>,
            p: impl Infer<D::P, P>,
        ) -> impl Infer<D::P, Q> {
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
