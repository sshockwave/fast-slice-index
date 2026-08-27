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

type L1<'a, P, Q> = Imply<'a, P, Imply<'a, Q, P>>;
type L2<'a, P, Q, R> =
    Imply<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>;

/// Axiomatic propositional logic
///
/// This is a logic system where all theorems are derived from axioms using inference rules.
/// Rust type system implies propositional logic,
/// so we can prove this in [`PropLogicThm`] without any unsafe code.
pub trait PropLogic {
    /// Implication: P implies Q
    type Imply<'a, P, Q>;

    /// Axiom L1: P → (Q → P)
    /// If P is true, then Q implies P
    fn l1<'a, P: Clone + 'a, Q>() -> L1<'a, P, Q>;

    /// Axiom L2: (P → (Q → R)) → ((P → Q) → (P → R))
    /// Distribution of implication
    fn l2<'a, P: Clone + 'a, Q: 'a, R: 'a>() -> L2<'a, P, Q, R>;

    type Cert<P>: From<P>;
    fn mp<'a, P, Q>(pq: Self::Cert<Self::Imply<'a, P, Q>>, p: Self::Cert<P>) -> Self::Cert<Q>;
}

pub struct PropLogicThm;

mod sealed_prop_logic {
    use super::{Imply, Infer, L1, L2, PropLogic, PropLogicThm};

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
    impl PropLogic for PropLogicThm {
        type Imply<'a, P, Q> = Imply<'a, P, Q>;
        fn l1<'a, P: Clone + 'a, Q>() -> Imply<'a, P, Imply<'a, Q, P>> {
            Imply::new(L1Proof)
        }
        fn l2<'a, P: Clone + 'a, Q: 'a, R: 'a>() -> L2<'a, P, Q, R> {
            Imply::new(L2Proof)
        }
        type Cert<P> = P;
        fn mp<'a, P, Q>(pq: Imply<'a, P, Q>, p: P) -> Q {
            pq.0.mp(p)
        }
    }
}
