use super::{Imply as Implication, PropLogic};

/// This trait is sealed to hide the assumptions from the Rust type system.
mod sealed_imply {
    pub trait Infer<'a, P, Q> {
        fn mp(&self, p: &P) -> Q;
        fn clone_dyn(&self) -> Imply<'a, P, Q>
        where
            Q: 'a;
    }
    pub struct Imply<'a, P: ?Sized, Q>(pub Box<dyn Infer<'a, P, Q> + 'a>);
}
use self::sealed_imply::{Imply, Infer};

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

pub struct PropLogicThm;

mod sealed_prop_logic {
    use super::{Implication, Imply, Infer, PropLogic, PropLogicThm};

    type L1<'a, P, Q> = Imply<'a, P, Imply<'a, Q, P>>;
    type L2<'a, P, Q, R> =
        Imply<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>;

    pub struct Store<P>(P);

    impl<'a, P, Q: Clone> Infer<'a, P, Q> for Store<Q> {
        fn mp(&self, _: &P) -> Q {
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
        fn mp(&self, p: &P) -> Imply<'a, Q, P> {
            Imply::new(Store(p.clone()))
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
        fn mp(&self, pq: &Imply<'a, P, Q>) -> Imply<'a, P, R> {
            Imply::new(Store2 {
                pqr: self.pqr.clone(),
                pq: pq.clone(),
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
        fn mp(&self, p: &P) -> R {
            self.pqr.0.mp(p).0.mp(&self.pq.0.mp(p.into()).into())
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
            p: &Imply<'a, P, Imply<'a, Q, R>>,
        ) -> Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>> {
            Imply::new(Store1 { pqr: p.clone() })
        }
        fn clone_dyn(&self) -> L2<'a, P, Q, R> {
            Imply::new(L2Proof)
        }
    }
    impl<'a> PropLogic<'a> for PropLogicThm {
        fn l1<P: Clone + 'a, Q: 'a>() -> Self::Cert<Imply<'a, P, Imply<'a, Q, P>>> {
            Imply::new(L1Proof).into()
        }
        fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Self::Cert<L2<'a, P, Q, R>> {
            Imply::new(L2Proof).into()
        }
    }
    impl<'a> Implication<'a> for PropLogicThm {
        type Imply<P: 'a, Q: 'a> = Imply<'a, P, Q>;
        type Cert<P: Clone + 'a> = P;
        fn mp<P: Clone + 'a, Q: Clone + 'a>(
            pq: Self::Cert<Imply<'a, P, Q>>,
            p: Self::Cert<P>,
        ) -> Self::Cert<Q> {
            pq.0.mp(&p).into()
        }
        fn def<P, Q>() -> Self::Cert<Self::Imply<P, Q>>
        where
            P: Into<Q> + Clone + 'a,
            Q: Clone + 'a,
        {
            struct DefProof;
            impl<'a, P, Q> Infer<'a, P, Q> for DefProof
            where
                P: Into<Q> + Clone,
                Q: Clone,
            {
                fn mp(&self, p: &P) -> Q {
                    p.clone().into()
                }
                fn clone_dyn(&self) -> Imply<'a, P, Q> {
                    Imply::new(DefProof)
                }
            }
            Imply::new(DefProof).into()
        }
    }
}
