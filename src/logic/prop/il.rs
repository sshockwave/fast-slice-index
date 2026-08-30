use super::{
    And, Cert, ExistsProof, FirstOrder, ForAllProof, Imply as Implication, Intuitionistic,
    Negation, Or, PropLogic, Reductio, View, exchange, reflexive,
};
use crate::utils::{IsSome, TrustedOption, option_scope};
use ::core::{convert::Infallible, marker::PhantomData};

/// This trait is sealed to hide the assumptions from the Rust type system.
mod sealed_imply {
    pub trait Infer<'a, P, Q> {
        fn mp(&self, p: P) -> Q;
        fn clone_dyn(&self) -> Imply<'a, P, Q>
        where
            Q: 'a;
    }
    /// We have to use `dyn` until https://github.com/rust-lang/rfcs/issues/2999 is resolved.
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
    use super::{Cert, Imply, Infer, PropLogic, PropLogicThm};

    type L1<'a, P, Q> = Imply<'a, P, Imply<'a, Q, P>>;
    type L2<'a, P, Q, R> =
        Imply<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>;

    pub struct Store<P>(P);

    impl<'a, P, Q: Clone> Infer<'a, P, Q> for Store<Q> {
        fn mp(&self, _: P) -> Q {
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
        fn l1<P: Clone + 'a, Q: 'a>() -> Cert<'a, Self, Imply<'a, P, Imply<'a, Q, P>>> {
            Cert::new(Imply::new(L1Proof))
        }
        fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<'a, Self, L2<'a, P, Q, R>> {
            Cert::new(Imply::new(L2Proof))
        }
    }
}
impl<'a> Implication<'a> for PropLogicThm {
    type Imply<P: 'a, Q: 'a> = Imply<'a, P, Q>;
    type Cert<P: Clone + 'a> = P;
    fn mp<P: Clone + 'a, Q: Clone + 'a>(
        pq: Cert<'a, Self, Imply<'a, P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        Cert::new(pq.into_inner().0.mp(p.into_inner()).into())
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
            fn mp(&self, p: P) -> Q {
                p.into()
            }
            fn clone_dyn(&self) -> Imply<'a, P, Q> {
                Imply::new(DefProof)
            }
        }
        Cert::new(Imply::new(DefProof).into())
    }
}

pub struct IntuitionisticImpl<Prop>(PhantomData<Prop>);

impl<'a, Prop: PropLogic<'a>> Implication<'a> for IntuitionisticImpl<Prop> {
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
        impl<'l, P: Clone + 'l, Q: Clone> Infer<'l, P, Imply<'l, Q, (P, Q)>> for Store1 {
            fn mp(&self, p: P) -> Imply<'l, Q, (P, Q)> {
                Imply::new(Store2(p))
            }
            fn clone_dyn(&self) -> Imply<'l, P, Imply<'l, Q, (P, Q)>> {
                Imply::new(Store1)
            }
        }
        struct Store2<P>(P);
        impl<'l, P: Clone, Q: Clone> Infer<'l, Q, (P, Q)> for Store2<P> {
            fn mp(&self, q: Q) -> (P, Q) {
                (self.0.clone(), q)
            }
            fn clone_dyn(&self) -> Imply<'l, Q, (P, Q)>
            where
                (P, Q): 'l,
            {
                Imply::new(Store2(self.0.clone()))
            }
        }
        Cert::new(Imply::new(Store1))
    }
    fn and_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, P>> {
        struct Proof;
        impl<'l, P: Clone, Q> Infer<'l, (P, Q), P> for Proof {
            fn mp(&self, pq: (P, Q)) -> P {
                pq.0
            }
            fn clone_dyn(&self) -> Imply<'l, (P, Q), P>
            where
                P: 'l,
            {
                Imply::new(Proof)
            }
        }
        Cert::new(Imply::new(Proof))
    }
    fn and_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>> {
        struct Proof;
        impl<'l, P, Q: Clone> Infer<'l, (P, Q), Q> for Proof {
            fn mp(&self, pq: (P, Q)) -> Q {
                pq.1
            }
            fn clone_dyn(&self) -> Imply<'l, (P, Q), Q>
            where
                Q: 'l,
            {
                Imply::new(Proof)
            }
        }
        Cert::new(Imply::new(Proof))
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
            fn mp(&self, p: Infallible) -> P {
                match p {}
            }
            fn clone_dyn(&self) -> Imply<'l, Infallible, P>
            where
                P: 'l,
            {
                Imply::new(Proof)
            }
        }
        Cert::new(Imply::new(Proof))
    }
    fn neg_def<P: Clone>()
    -> Cert<'l, Self, super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        Self::and_intro().mp(reflexive()).mp(reflexive())
    }
}

use sealed_forall::{ForAll, ViewGet};
mod sealed_forall {
    use super::View;
    use ::core::marker::PhantomData;

    pub trait ViewGet<'l, V: for<'x> View<'x> + ?Sized> {
        fn get<'x: 'l>(&self) -> <V as View<'x>>::Output;
        fn clone_dyn(&self) -> ForAll<'l, V>;
    }

    pub struct ForAll<'l, V: ?Sized>(pub PhantomData<&'l ()>, pub Box<dyn ViewGet<'l, V> + 'l>);

    impl<'l, V: for<'x> View<'x> + ?Sized> Clone for ForAll<'l, V> {
        fn clone(&self) -> Self {
            self.1.clone_dyn()
        }
    }
}

use self::sealed_exists::{Exists, ExistsSupply, GetHandler};
mod sealed_exists {
    use super::View;
    use crate::utils::IsSome;
    pub trait GetHandler<'l, 'o, V: for<'x> View<'x> + ?Sized> {
        fn handle<'t: 'l>(&mut self, value: <V as View<'t>>::Output) -> IsSome<'o>;
    }
    pub trait ExistsSupply<'l, V: for<'x> View<'x> + ?Sized> {
        fn get<'o, 'm>(&self, f: Box<dyn GetHandler<'l, 'o, V> + 'm>) -> IsSome<'o>;
        fn clone_dyn(&self) -> Box<dyn ExistsSupply<'l, V>>;
    }
    pub struct Exists<'l, V: ?Sized>(pub Box<dyn ExistsSupply<'l, V>>);
    impl<V: for<'x> View<'x> + ?Sized> Clone for Exists<'_, V> {
        fn clone(&self) -> Self {
            Self(self.0.clone_dyn())
        }
    }
}

type Logic = IntuitionisticImpl<PropLogicThm>;
impl<'l> FirstOrder<'l> for Logic {
    type ForAll<V: for<'x> View<'x> + ?Sized> = ForAll<'l, V>;
    fn forall_gen<
        P: Clone,
        Q: for<'x> View<'x, Output: Clone> + ?Sized,
        S: ForAllProof<'l, Self, P, Q> + Clone + 'l,
    >(
        proof: S,
    ) -> Cert<'l, Self, Self::Imply<P, Self::ForAll<Q>>> {
        struct Deriver<P, S, Q: ?Sized>(PhantomData<Q>, P, S);
        impl<'x, P, S, Q: for<'y> View<'y> + ?Sized> View<'x> for Deriver<P, S, Q> {
            type Output = <Q as View<'x>>::Output;
        }
        impl<'l, P: Clone + 'l, S: ForAllProof<'l, Logic, P, Q>, Q: ?Sized + for<'x> View<'x> + 'l>
            ViewGet<'l, Q> for Deriver<P, S, Q>
        where
            for<'x> <Q as View<'x>>::Output: Clone,
        {
            fn get<'x: 'l>(&self) -> <Q as View<'x>>::Output {
                self.2.clone().prove().into_inner().0.mp(self.1.clone())
            }
            fn clone_dyn(&self) -> ForAll<'l, Q> {
                ForAll(
                    PhantomData,
                    Box::new(Deriver(PhantomData, self.1.clone(), self.2.clone())),
                )
            }
        }
        struct Proof<S, Q: ?Sized>(PhantomData<Q>, S);
        impl<'l, P: Clone + 'l, Q: ?Sized + for<'x> View<'x> + 'l, S: ForAllProof<'l, Logic, P, Q>>
            Infer<'l, P, ForAll<'l, Q>> for Proof<S, Q>
        where
            for<'x> <Q as View<'x>>::Output: Clone,
        {
            fn mp(&self, p: P) -> ForAll<'l, Q> {
                ForAll(
                    PhantomData,
                    Box::new(Deriver(PhantomData, p.clone(), self.1.clone())),
                )
            }
            fn clone_dyn(&self) -> Imply<'l, P, ForAll<'l, Q>>
            where
                ForAll<'l, Q>: 'l,
            {
                Imply::new(Proof::<_, _>(PhantomData, self.1.clone()))
            }
        }
        Cert::new(Imply::new(Proof::<_, _>(PhantomData, proof)))
    }
    fn forall_elim<'t: 'l, P: for<'x> View<'x> + ?Sized>()
    -> Cert<'l, Self, Self::Imply<Self::ForAll<P>, <P as View<'t>>::Output>>
    where
        <P as View<'t>>::Output: Clone,
    {
        struct Proof;
        impl<'t: 'l, 'l, V> Infer<'l, ForAll<'l, V>, <V as View<'t>>::Output> for Proof
        where
            V: for<'x> View<'x> + ?Sized + 'l,
            <V as View<'t>>::Output: Clone + 'l,
        {
            fn mp(&self, forall: ForAll<'l, V>) -> <V as View<'t>>::Output {
                forall.1.get()
            }
            fn clone_dyn(&self) -> Imply<'l, ForAll<'l, V>, <V as View<'t>>::Output>
            where
                <V as View<'t>>::Output: 'l,
            {
                Imply::new(Proof)
            }
        }
        Cert::new(Imply::new(Proof))
    }

    type Exists<P: for<'x> View<'x> + ?Sized> = Exists<'l, P>;
    fn exists_gen<P: for<'x> View<'x> + ?Sized + 'l, Q, S: ExistsProof<'l, Self, P, Q>>(
        proof: S,
    ) -> Cert<'l, Self, Self::Imply<Self::Exists<P>, Q>> {
        struct Store<P: ?Sized, S>(PhantomData<P>, S);
        impl<'l, P: for<'x> View<'x> + ?Sized + 'l, Q: 'l, S: ExistsProof<'l, Logic, P, Q>>
            Infer<'l, <Logic as FirstOrder<'l>>::Exists<P>, Q> for Store<P, S>
        {
            fn mp(&self, p: <Logic as FirstOrder<'l>>::Exists<P>) -> Q {
                let prover = self.1.clone();
                option_scope(move |mut store| {
                    struct Handler<'o, 'b, Q, S>(&'b mut TrustedOption<'o, Q>, S);
                    impl<
                        'l,
                        'o,
                        Q: 'l,
                        S: ExistsProof<'l, Logic, V, Q>,
                        V: for<'x> View<'x> + ?Sized + 'l,
                    > GetHandler<'l, 'o, V> for Handler<'o, '_, Q, S>
                    {
                        fn handle<'t: 'l>(&mut self, value: <V as View<'t>>::Output) -> IsSome<'o> {
                            let s: S = self.1.clone();
                            let cert: Cert<
                                'l,
                                Logic,
                                <Logic as Implication<'l>>::Imply<<V as View<'t>>::Output, Q>,
                            > = s.prove();
                            let q: Q = cert.into_inner().0.mp(value);
                            self.0.set(q)
                        }
                    }
                    let proof = p.0.get(Box::new(Handler(&mut store, prover)));
                    store.take(proof)
                })
            }
            fn clone_dyn(&self) -> Imply<'l, <Logic as FirstOrder<'l>>::Exists<P>, Q>
            where
                Q: 'l,
            {
                Imply::new(Store(PhantomData, self.1.clone()))
            }
        }
        Cert::new(Imply::new(Store(PhantomData, proof)))
    }
    fn exists_elim<'t, P: for<'x> View<'x> + ?Sized, Q>()
    -> Cert<'l, Self, Self::Imply<<P as View<'t>>::Output, Self::Exists<P>>> {
        todo!()
    }
}
