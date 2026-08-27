#![forbid(unsafe_code)]

/// Implication: P implies Q
pub trait Infer<P, Q> {
    /// Modus Ponens: Given (P → Q) and P, derive Q
    /// This is the only inference rule - all others are axioms
    fn mp(self, p: P) -> Q;
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
    type L2<P: Clone, Q, R, PQR: Infer<P, QR>, QR: Infer<Q, R>, PQ: Infer<P, Q>>: L2<P, Q, R, PQR, QR, PQ>
        + Default
        + Copy;
}

pub struct PropLogicThm;

mod prop_logic_sealed {
    use super::{Infer, L1, L2, PropLogic, PropLogicThm};
    use ::core::marker::PhantomData;

    pub struct Store<P>(P);

    impl<P, Q> Infer<P, Q> for Store<Q> {
        fn mp(self, _: P) -> Q {
            self.0
        }
    }
    pub struct L1Proof<P, Q>(PhantomData<(P, Q)>);
    impl<P, Q> L1<P, Q> for L1Proof<P, Q> {
        type QP = Store<P>;
    }
    impl<P, Q> Infer<P, Store<P>> for L1Proof<P, Q> {
        fn mp(self, p: P) -> Store<P> {
            Store(p)
        }
    }
    impl<P, Q> Clone for L1Proof<P, Q> {
        fn clone(&self) -> Self {
            L1Proof(PhantomData)
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
    impl<L: Params> Infer<L::PQ, Store2<L>> for Store1<L> {
        fn mp(self, pq: L::PQ) -> Store2<L> {
            Store2 { pqr: self.pqr, pq }
        }
    }
    pub struct Store2<L: Params> {
        pqr: L::PQR,
        pq: L::PQ,
    }
    impl<L: Params> Infer<L::P, L::R> for Store2<L> {
        fn mp(self, p: L::P) -> L::R {
            self.pqr.mp(p.clone()).mp(self.pq.mp(p))
        }
    }
    pub struct L2Proof<L>(PhantomData<L>);
    impl<L: Params> L2<L::P, L::Q, L::R, L::PQR, L::QR, L::PQ> for L2Proof<L> {
        type PQPR = Store1<L>;
        type PR = Store2<L>;
    }
    impl<L: Params> Infer<L::PQR, Store1<L>> for L2Proof<L> {
        fn mp(self, pqr: L::PQR) -> Store1<L> {
            Store1 { pqr }
        }
    }
    impl<L> Clone for L2Proof<L> {
        fn clone(&self) -> Self {
            L2Proof(PhantomData)
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
