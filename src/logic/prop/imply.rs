/// This trait is sealed to hide the assumptions from the Rust type system.
trait Infer<'a, P, Q> {
    /// Modus Ponens: Given (P → Q) and P, derive Q
    /// This is the only inference rule - all others are axioms
    fn mp(&self, p: P) -> Q;
    fn clone_dyn(&self) -> Imply<'a, P, Q>
    where
        Q: 'a;
}
pub struct Imply<'a, P, Q>(Box<dyn Infer<'a, P, Q> + 'a>);

impl<'a, P, Q> Imply<'a, P, Q> {
    fn new(infer: impl Infer<'a, P, Q> + 'a) -> Self {
        Self(Box::new(infer))
    }
}
impl<'a, P, Q: 'a> Clone for Imply<'a, P, Q> {
    fn clone(&self) -> Self {
        self.0.clone_dyn()
    }
}

/// Axiomatic propositional logic
///
/// This is a logic system where all theorems are derived from axioms using inference rules.
/// Rust type system implies propositional logic,
/// so we can prove this in [`PropLogicThm`] without any unsafe code.
pub trait PropLogic<'a> {
    /// Implication: P implies Q
    type Imply<P: 'a, Q: 'a>: Clone + 'a;

    /// Axiom L1: P → (Q → P)
    /// If P is true, then Q implies P
    fn l1<P: Clone + 'a, Q>() -> Self::Imply<P, Self::Imply<Q, P>>;

    /// Axiom L2: (P → (Q → R)) → ((P → Q) → (P → R))
    /// Distribution of implication
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Self::Imply<
        Self::Imply<P, Self::Imply<Q, R>>,
        Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
    >;

    type BaseCert<P: Clone + 'a>;
    type Cert<P: Clone + 'a>: From<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Self::Cert<Self::Imply<P, Q>>,
        p: Self::Cert<P>,
    ) -> Self::Cert<Q>;

    fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P>;
}

pub struct PropLogicThm;

mod sealed_prop_logic {
    use super::{Imply, Infer, PropLogic, PropLogicThm};

    type L1<'a, P, Q> = Imply<'a, P, Imply<'a, Q, P>>;
    type L2<'a, P, Q, R> =
        Imply<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>;

    pub struct Store<P>(P);

    impl<'a, P, Q: Clone> Infer<'a, P, Q> for Store<Q> {
        fn mp(&self, _: P) -> Q {
            self.0.clone()
        }
        fn clone_dyn(&self) -> super::Imply<'a, P, Q>
        where
            Q: 'a,
        {
            Imply::new(Store(self.0.clone()))
        }
    }
    pub struct L1Proof;
    impl<'a, P: Clone + 'a, Q> Infer<'a, P, Imply<'a, Q, P>> for L1Proof {
        fn mp(&self, p: P) -> Imply<'a, Q, P> {
            Imply::new(Store(p))
        }
        fn clone_dyn(&self) -> L1<'a, P, Q> {
            Imply::new(L1Proof)
        }
    }
    pub struct Store1<'a, P, Q, R> {
        pqr: Imply<'a, P, Imply<'a, Q, R>>,
    }
    impl<'a, P: Clone + 'a, Q: 'a, R: 'a> Infer<'a, Imply<'a, P, Q>, Imply<'a, P, R>>
        for Store1<'a, P, Q, R>
    {
        fn mp(&self, pq: Imply<'a, P, Q>) -> Imply<'a, P, R> {
            Imply::new(Store2 {
                pqr: self.pqr.clone(),
                pq,
            })
        }
        fn clone_dyn(&self) -> Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>> {
            Imply::new(Self {
                pqr: self.pqr.clone(),
            })
        }
    }
    pub struct Store2<'a, P, Q, R> {
        pqr: Imply<'a, P, Imply<'a, Q, R>>,
        pq: Imply<'a, P, Q>,
    }
    impl<'a, P: Clone + 'a, Q: 'a, R: 'a> Infer<'a, P, R> for Store2<'a, P, Q, R> {
        fn mp(&self, p: P) -> R {
            self.pqr.0.mp(p.clone()).0.mp(self.pq.0.mp(p.into()).into())
        }
        fn clone_dyn(&self) -> Imply<'a, P, R> {
            Imply::new(Store2 {
                pqr: self.pqr.clone(),
                pq: self.pq.clone(),
            })
        }
    }
    pub struct L2Proof;
    impl<'a, P: Clone + 'a, Q: 'a, R: 'a>
        Infer<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>
        for L2Proof
    {
        fn mp(
            &self,
            p: Imply<'a, P, Imply<'a, Q, R>>,
        ) -> Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>> {
            Imply::new(Store1 { pqr: p })
        }
        fn clone_dyn(&self) -> L2<'a, P, Q, R> {
            Imply::new(L2Proof)
        }
    }
    impl<'a> PropLogic<'a> for PropLogicThm {
        type Imply<P: 'a, Q: 'a> = Imply<'a, P, Q>;
        fn l1<P: Clone + 'a, Q>() -> Imply<'a, P, Imply<'a, Q, P>> {
            Imply::new(L1Proof)
        }
        fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> L2<'a, P, Q, R> {
            Imply::new(L2Proof)
        }
        type BaseCert<P: Clone + 'a> = P;
        type Cert<P: Clone + 'a> = P;
        fn mp<P: Clone + 'a, Q: Clone + 'a>(
            pq: Self::Cert<Imply<'a, P, Q>>,
            p: Self::Cert<P>,
        ) -> Self::Cert<Q> {
            pq.0.mp(p)
        }
        fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P> {
            value
        }
    }
}
