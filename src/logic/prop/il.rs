use crate::logic::prop::reflexive;

use super::{And, Cert, Imply, Intuitionistic, Negation, Or, PropLogic, Reductio, exchange};
use ::core::{convert::Infallible, marker::PhantomData};

/// This trait is sealed to hide the assumptions from the Rust type system.
mod sealed_imply {
    pub trait Infer<'a, P, Q> {
        fn mp(&self, p: &P) -> Q;
        fn clone_dyn(&self) -> Implication<'a, P, Q>
        where
            Q: 'a;
    }
    /// We have to use `dyn` until https://github.com/rust-lang/rfcs/issues/2999 is resolved.
    pub struct Implication<'a, P: ?Sized, Q>(pub Box<dyn Infer<'a, P, Q> + 'a>);
}
use self::sealed_imply::{Implication, Infer};

impl<'a, P, Q> Implication<'a, P, Q> {
    fn new(infer: impl Infer<'a, P, Q> + 'a) -> Self {
        Self(Box::new(infer))
    }
}
impl<'a, P, Q: 'a> Clone for Implication<'a, P, Q> {
    fn clone(&self) -> Self {
        self.0.clone_dyn()
    }
}

pub struct PropLogicThm;

mod sealed_prop_logic {
    use super::{Cert, Implication as Imply, Infer, PropLogic, PropLogicThm};

    type L1<'a, P, Q> = Imply<'a, P, Imply<'a, Q, P>>;
    type L2<'a, P, Q, R> =
        Imply<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>;

    pub struct Store<P>(P);

    impl<'a, P, Q: Clone> Infer<'a, P, Q> for Store<Q> {
        fn mp(&self, _: &P) -> Q {
            self.0.clone()
        }
        fn clone_dyn(&self) -> Imply<'a, P, Q>
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
        fn l1<P: Clone + 'a, Q: 'a>() -> Cert<'a, Self, Imply<'a, P, Imply<'a, Q, P>>> {
            Cert::new(Imply::new(L1Proof))
        }
        fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<'a, Self, L2<'a, P, Q, R>> {
            Cert::new(Imply::new(L2Proof))
        }
    }
}
impl<'a> Imply<'a> for PropLogicThm {
    type Imply<P: 'a, Q: 'a> = Implication<'a, P, Q>;
    type Cert<P: Clone + 'a> = P;
    fn mp<P: Clone + 'a, Q: Clone + 'a>(
        pq: Cert<'a, Self, Implication<'a, P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        Cert::new(pq.into_inner().0.mp(&p.into_inner()).into())
    }
    fn def<P, Q>() -> Cert<'a, Self, Self::Imply<P, Q>>
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
            fn clone_dyn(&self) -> Implication<'a, P, Q> {
                Implication::new(DefProof)
            }
        }
        Cert::new(Implication::new(DefProof).into())
    }
}

pub struct IntuitionisticImpl<Prop>(PhantomData<Prop>);

impl<'a, Prop: PropLogic<'a>> Imply<'a> for IntuitionisticImpl<Prop> {
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Cert<'a, Self, Self::Imply<P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        pq.mp(p)
    }
    fn def<P, Q>() -> Cert<'a, Self, Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a,
    {
        Prop::def().cast()
    }
}
impl<'a, Prop: PropLogic<'a>> PropLogic<'a> for IntuitionisticImpl<Prop> {
    fn l1<P: Clone + 'a, Q>() -> Cert<'a, Self, Self::Imply<P, Self::Imply<Q, P>>> {
        Prop::l1().cast()
    }
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<
        'a,
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        Prop::l2().cast()
    }
}

impl<'l, Prop: PropLogic<'l>> Negation<'l> for IntuitionisticImpl<Prop> {
    type Neg<P: 'l> = Prop::Imply<P, Infallible>;
}

/// `Reductio` needs no classical axiom: under `¬P := P → ⊥` it is just
/// [`exchange`] of antecedents, provable from L1/L2 alone. This is what
/// separates it from [`super::neg::Contraposition`], whose classical content
/// cannot be recovered here.
impl<'l, Prop: PropLogic<'l>> Reductio<'l> for IntuitionisticImpl<Prop> {
    fn reductio<P: Clone + 'l, Q: Clone + 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>> {
        exchange::<P, Q, Infallible, Prop>().cast()
    }
}

impl<'l> And<'l> for IntuitionisticImpl<PropLogicThm> {
    type And<P: Clone + 'l, Q: Clone + 'l> = (P, Q);
    fn and_intro<P: Clone, Q: Clone>()
    -> Cert<'l, Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>> {
        struct Store1;
        impl<'l, P: Clone + 'l, Q: Clone> Infer<'l, P, Implication<'l, Q, (P, Q)>> for Store1 {
            fn mp(&self, p: &P) -> Implication<'l, Q, (P, Q)> {
                Implication::new(Store2(p.clone()))
            }
            fn clone_dyn(&self) -> Implication<'l, P, Implication<'l, Q, (P, Q)>> {
                Implication::new(Store1)
            }
        }
        struct Store2<P>(P);
        impl<'l, P: Clone, Q: Clone> Infer<'l, Q, (P, Q)> for Store2<P> {
            fn mp(&self, q: &Q) -> (P, Q) {
                (self.0.clone(), q.clone())
            }
            fn clone_dyn(&self) -> Implication<'l, Q, (P, Q)>
            where
                (P, Q): 'l,
            {
                Implication::new(Store2(self.0.clone()))
            }
        }
        Cert::new(Implication::new(Store1))
    }
    fn and_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, P>> {
        struct Proof;
        impl<'l, P: Clone, Q> Infer<'l, (P, Q), P> for Proof {
            fn mp(&self, pq: &(P, Q)) -> P {
                pq.0.clone()
            }
            fn clone_dyn(&self) -> Implication<'l, (P, Q), P>
            where
                P: 'l,
            {
                Implication::new(Proof)
            }
        }
        Cert::new(Implication::new(Proof))
    }
    fn and_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>> {
        struct Proof;
        impl<'l, P, Q: Clone> Infer<'l, (P, Q), Q> for Proof {
            fn mp(&self, pq: &(P, Q)) -> Q {
                pq.1.clone()
            }
            fn clone_dyn(&self) -> Implication<'l, (P, Q), Q>
            where
                Q: 'l,
            {
                Implication::new(Proof)
            }
        }
        Cert::new(Implication::new(Proof))
    }
}

impl<'l> Or<'l> for IntuitionisticImpl<PropLogicThm> {
    type Or<P: Clone + 'l, Q: Clone + 'l> = Result<P, Q>;
    fn or_elim<P: Clone, Q: Clone, R: Clone>() -> Cert<
        'l,
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        todo!()
    }
    fn or_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>> {
        todo!()
    }
    fn or_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>> {
        todo!()
    }
}

impl<'l> Intuitionistic<'l> for IntuitionisticImpl<PropLogicThm> {
    type False = Infallible;
    fn explosion<P: Clone>() -> Cert<'l, Self, Self::Imply<Self::False, P>> {
        struct Proof;
        impl<'l, P: Clone> Infer<'l, Infallible, P> for Proof {
            fn mp(&self, p: &Infallible) -> P {
                match *p {}
            }
            fn clone_dyn(&self) -> Implication<'l, Infallible, P>
            where
                P: 'l,
            {
                Implication::new(Proof)
            }
        }
        Cert::new(Implication::new(Proof))
    }
    fn neg_def<P: Clone>()
    -> Cert<'l, Self, super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        Self::and_intro().mp(reflexive()).mp(reflexive())
    }
}
