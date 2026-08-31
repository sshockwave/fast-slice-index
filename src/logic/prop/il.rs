use super::{
    And, Cert, ExistsProof, FirstOrder, ForAllProof, Imply as Implication, Intuitionistic,
    Negation, Or, PropLogic, Reductio, View, exchange, reflexive,
};
use crate::utils::{IsSome, TrustedOption, option_scope};
use ::core::{convert::Infallible, marker::PhantomData};
use ::std::rc::Rc;

/// This trait is sealed to hide the assumptions from the Rust type system.
mod sealed_imply {
    use ::std::rc::Rc;

    pub trait Infer<'a, P, Q> {
        fn mp(&self, p: Rc<P>) -> Rc<Q>;
    }
    /// We have to use `dyn` until https://github.com/rust-lang/rfcs/issues/2999 is resolved.
    /// Here we use a [`Box`] to prevent adding `?Sized` everywhere
    pub type Imply<'a, P, Q> = Box<dyn Infer<'a, P, Q> + 'a>;
}
use self::sealed_imply::{Imply, Infer};

pub struct PropLogicThm;

mod sealed_prop_logic {
    use super::{Cert, Imply, Infer, PropLogic, PropLogicThm};
    use ::std::rc::Rc;

    type L1<'a, P, Q> = Imply<'a, P, Imply<'a, Q, P>>;
    type L2<'a, P, Q, R> =
        Imply<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>;

    pub struct Store<P>(Rc<P>);

    impl<'a, P, Q> Infer<'a, P, Q> for Store<Q> {
        fn mp(&self, _: Rc<P>) -> Rc<Q> {
            self.0.clone()
        }
    }
    pub struct L1Proof;
    impl<'a, P: 'a, Q> Infer<'a, P, Imply<'a, Q, P>> for L1Proof {
        fn mp(&self, p: Rc<P>) -> Rc<Imply<'a, Q, P>> {
            Rc::new(Box::new(Store(p)))
        }
    }
    pub struct Store1<'a, P, Q, R> {
        pqr: Rc<Imply<'a, P, Imply<'a, Q, R>>>,
    }
    impl<'a, P: 'a, Q: 'a, R: 'a> Infer<'a, Imply<'a, P, Q>, Imply<'a, P, R>> for Store1<'a, P, Q, R> {
        fn mp(&self, pq: Rc<Imply<'a, P, Q>>) -> Rc<Imply<'a, P, R>> {
            Rc::new(Box::new(Store2 {
                pqr: self.pqr.clone(),
                pq: pq,
            }))
        }
    }
    pub struct Store2<'a, P, Q, R> {
        pqr: Rc<Imply<'a, P, Imply<'a, Q, R>>>,
        pq: Rc<Imply<'a, P, Q>>,
    }
    impl<'a, P: 'a, Q: 'a, R: 'a> Infer<'a, P, R> for Store2<'a, P, Q, R> {
        fn mp(&self, p: Rc<P>) -> Rc<R> {
            self.pqr.mp(p.clone()).mp(self.pq.mp(p))
        }
    }
    pub struct L2Proof;
    impl<'a, P: 'a, Q: 'a, R: 'a>
        Infer<'a, Imply<'a, P, Imply<'a, Q, R>>, Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>>
        for L2Proof
    {
        fn mp(
            &self,
            p: Rc<Imply<'a, P, Imply<'a, Q, R>>>,
        ) -> Rc<Imply<'a, Imply<'a, P, Q>, Imply<'a, P, R>>> {
            Rc::new(Box::new(Store1 { pqr: p }))
        }
    }
    impl<'a> PropLogic<'a> for PropLogicThm {
        fn l1<P: 'a, Q: 'a>() -> Cert<'a, Self, Imply<'a, P, Imply<'a, Q, P>>> {
            let proof: L1<_, _> = Box::new(L1Proof);
            Cert::new(Rc::new(proof))
        }
        fn l2<P: 'a, Q: 'a, R: 'a>() -> Cert<'a, Self, L2<'a, P, Q, R>> {
            let proof: L2<_, _, _> = Box::new(L2Proof);
            Cert::new(Rc::new(proof))
        }
    }
}
impl<'a> Implication<'a> for PropLogicThm {
    type Imply<P: 'a, Q: 'a> = Imply<'a, P, Q>;
    type Cert<P: 'a> = Rc<P>;
    fn mp<P: 'a, Q: 'a>(
        pq: Cert<'a, Self, Imply<'a, P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        Cert::new(pq.into_inner().mp(p.into_inner()).into())
    }
}

pub struct IntuitionisticImpl<Prop>(PhantomData<Prop>);

impl<'a, Prop: PropLogic<'a>> Implication<'a> for IntuitionisticImpl<Prop> {
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    type Cert<P: 'a> = Prop::Cert<P>;
    fn mp<P, Q: 'a>(
        pq: Cert<'a, Self, Self::Imply<P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        pq.mp(p)
    }
}
impl<'a, Prop: PropLogic<'a>> PropLogic<'a> for IntuitionisticImpl<Prop> {
    fn l1<P: 'a, Q>() -> Cert<'a, Self, Self::Imply<P, Self::Imply<Q, P>>> {
        Prop::l1().cast()
    }
    fn l2<P: 'a, Q: 'a, R: 'a>() -> Cert<
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
    fn reductio<P: 'l, Q: 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>> {
        exchange::<P, Q, Infallible, Prop>().cast()
    }
}

type A<P, Q> = (Rc<P>, Rc<Q>);
impl<'l> And<'l> for IntuitionisticImpl<PropLogicThm> {
    type And<P: 'l, Q: 'l> = (Rc<P>, Rc<Q>);
    fn and_intro<P, Q>() -> Cert<'l, Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>> {
        struct Store1;
        impl<'l, P: 'l, Q> Infer<'l, P, Imply<'l, Q, A<P, Q>>> for Store1 {
            fn mp(&self, p: Rc<P>) -> Rc<Imply<'l, Q, A<P, Q>>> {
                let proof: Imply<'l, _, _> = Box::new(Store2(p));
                Rc::new(proof)
            }
        }
        struct Store2<P>(Rc<P>);
        impl<'l, P, Q> Infer<'l, Q, (Rc<P>, Rc<Q>)> for Store2<P> {
            fn mp(&self, q: Rc<Q>) -> Rc<(Rc<P>, Rc<Q>)> {
                Rc::new((self.0.clone(), q))
            }
        }
        let proof: Imply<_, _> = Box::new(Store1);
        Cert::new(Rc::new(proof))
    }
    fn and_left<P, Q>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, P>> {
        struct Proof;
        impl<'l, P, Q> Infer<'l, (Rc<P>, Rc<Q>), P> for Proof {
            fn mp(&self, pq: Rc<A<P, Q>>) -> Rc<P> {
                pq.0.clone()
            }
        }
        let proof: Imply<_, _> = Box::new(Proof);
        Cert::new(Rc::new(proof))
    }
    fn and_right<P, Q>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>> {
        struct Proof;
        impl<'l, P, Q> Infer<'l, A<P, Q>, Q> for Proof {
            fn mp(&self, pq: Rc<A<P, Q>>) -> Rc<Q> {
                pq.1.clone()
            }
        }
        let proof: Imply<_, _> = Box::new(Proof);
        Cert::new(Rc::new(proof))
    }
}

impl<'l> Or<'l> for IntuitionisticImpl<PropLogicThm> {
    type Or<P: 'l, Q: 'l> = Result<P, Q>;
    fn or_elim<P, Q, R>() -> Cert<
        'l,
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        todo!()
    }
    fn or_left<P, Q>() -> Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>> {
        todo!()
    }
    fn or_right<P, Q>() -> Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>> {
        todo!()
    }
}

impl<'l> Intuitionistic<'l> for IntuitionisticImpl<PropLogicThm> {
    type False = Infallible;
    fn explosion<P>() -> Cert<'l, Self, Self::Imply<Self::False, P>> {
        struct Proof;
        impl<'l, P> Infer<'l, Infallible, P> for Proof {
            fn mp(&self, p: Rc<Infallible>) -> Rc<P> {
                match *p {}
            }
        }
        let proof: Imply<_, _> = Box::new(Proof);
        Cert::new(Rc::new(proof))
    }
    fn neg_def<P>()
    -> Cert<'l, Self, super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        Self::and_intro().mp(reflexive()).mp(reflexive())
    }
}

use sealed_forall::{ForAll, ViewGet};
mod sealed_forall {
    use super::View;
    use ::core::marker::PhantomData;
    use ::std::rc::Rc;

    pub trait ViewGet<'l, V: for<'x> View<'x> + ?Sized> {
        fn get<'x: 'l>(&self) -> Rc<<V as View<'x>>::Output>;
    }

    pub struct ForAll<'l, V: ?Sized>(pub PhantomData<&'l ()>, pub Box<dyn ViewGet<'l, V> + 'l>);
}

use self::sealed_exists::{Exists, ExistsSupply, GetHandler};
mod sealed_exists {
    use super::View;
    use crate::utils::IsSome;
    use ::std::rc::Rc;

    pub trait GetHandler<'l, 'o, V: for<'x> View<'x> + ?Sized> {
        fn handle<'t: 'l>(&mut self, value: Rc<<V as View<'t>>::Output>) -> IsSome<'o>;
    }
    pub trait ExistsSupply<'l, V: for<'x> View<'x> + ?Sized> {
        fn get<'o, 'm>(&self, f: Box<dyn GetHandler<'l, 'o, V> + 'm>) -> IsSome<'o>;
    }
    pub struct Exists<'l, V: ?Sized>(pub Box<dyn ExistsSupply<'l, V> + 'l>);
}

type Logic = IntuitionisticImpl<PropLogicThm>;
impl<'l> FirstOrder<'l> for Logic {
    type ForAll<V: for<'x> View<'x> + ?Sized + 'l> = ForAll<'l, V>;
    fn forall_gen<P, Q: for<'x> View<'x> + ?Sized, S: ForAllProof<'l, Self, P, Q> + 'l>(
        proof: S,
    ) -> Cert<'l, Self, Self::Imply<P, Self::ForAll<Q>>> {
        struct Deriver<P, S, Q: ?Sized>(PhantomData<Q>, Rc<P>, S);
        impl<'x, P, S, Q: for<'y> View<'y> + ?Sized> View<'x> for Deriver<P, S, Q> {
            type Output = <Q as View<'x>>::Output;
        }
        impl<'l, P: 'l, S: ForAllProof<'l, Logic, P, Q>, Q: ?Sized + for<'x> View<'x> + 'l>
            ViewGet<'l, Q> for Deriver<P, S, Q>
        {
            fn get<'x: 'l>(&self) -> Rc<<Q as View<'x>>::Output> {
                self.2.clone().prove().into_inner().mp(self.1.clone())
            }
        }
        struct Proof<S, Q: ?Sized>(PhantomData<Q>, S);
        impl<'l, P: 'l, Q: ?Sized + for<'x> View<'x> + 'l, S: ForAllProof<'l, Logic, P, Q>>
            Infer<'l, P, ForAll<'l, Q>> for Proof<S, Q>
        {
            fn mp(&self, p: Rc<P>) -> Rc<ForAll<'l, Q>> {
                Rc::new(ForAll(
                    PhantomData,
                    Box::new(Deriver(PhantomData, p.clone(), self.1.clone())),
                ))
            }
        }
        let proof: Imply<_, _> = Box::new(Proof(PhantomData, proof));
        Cert::new(Rc::new(proof))
    }
    fn forall_elim<'t: 'l, P: for<'x> View<'x> + ?Sized>()
    -> Cert<'l, Self, Self::Imply<Self::ForAll<P>, <P as View<'t>>::Output>> {
        struct Proof;
        impl<'t: 'l, 'l, V> Infer<'l, ForAll<'l, V>, <V as View<'t>>::Output> for Proof
        where
            V: for<'x> View<'x> + ?Sized + 'l,
        {
            fn mp(&self, forall: Rc<ForAll<'l, V>>) -> Rc<<V as View<'t>>::Output> {
                forall.1.get()
            }
        }
        let proof: Imply<_, _> = Box::new(Proof);
        Cert::new(Rc::new(proof))
    }

    type Exists<P: for<'x> View<'x> + ?Sized> = Exists<'l, P>;
    fn exists_gen<P: for<'x> View<'x> + ?Sized + 'l, Q, S: ExistsProof<'l, Self, P, Q>>(
        proof: S,
    ) -> Cert<'l, Self, Self::Imply<Self::Exists<P>, Q>> {
        struct Store<P: ?Sized, S>(PhantomData<P>, S);
        impl<'l, P: for<'x> View<'x> + ?Sized + 'l, Q: 'l, S: ExistsProof<'l, Logic, P, Q>>
            Infer<'l, <Logic as FirstOrder<'l>>::Exists<P>, Q> for Store<P, S>
        {
            fn mp(&self, p: Rc<<Logic as FirstOrder<'l>>::Exists<P>>) -> Rc<Q> {
                let prover = self.1.clone();
                option_scope(move |mut store| {
                    struct Handler<'o, 'b, Q, S>(&'b mut TrustedOption<'o, Rc<Q>>, S);
                    impl<
                        'l,
                        'o,
                        Q: 'l,
                        S: ExistsProof<'l, Logic, V, Q>,
                        V: for<'x> View<'x> + ?Sized + 'l,
                    > GetHandler<'l, 'o, V> for Handler<'o, '_, Q, S>
                    {
                        fn handle<'t: 'l>(
                            &mut self,
                            value: Rc<<V as View<'t>>::Output>,
                        ) -> IsSome<'o> {
                            let s: S = self.1.clone();
                            let cert: Cert<
                                'l,
                                Logic,
                                <Logic as Implication<'l>>::Imply<<V as View<'t>>::Output, Q>,
                            > = s.prove();
                            let q = cert.into_inner().mp(value);
                            self.0.set(q)
                        }
                    }
                    let proof = p.0.get(Box::new(Handler(&mut store, prover)));
                    store.take(proof)
                })
            }
        }
        let proof: Imply<_, _> = Box::new(Store(PhantomData, proof));
        Cert::new(Rc::new(proof))
    }
    fn exists_elim<'t: 'l, P: for<'x> View<'x> + ?Sized, Q>()
    -> Cert<'l, Self, Self::Imply<<P as View<'t>>::Output, Self::Exists<P>>> {
        struct Witness<P>(Rc<P>);
        impl<'l, 't: 'l, P: for<'x> View<'x> + ?Sized> ExistsSupply<'l, P>
            for Witness<<P as View<'t>>::Output>
        {
            fn get<'o, 'm>(&self, mut f: Box<dyn GetHandler<'l, 'o, P> + 'm>) -> IsSome<'o> {
                f.handle(self.0.clone())
            }
        }
        struct Proof;
        impl<'l, 't: 'l, P: for<'x> View<'x> + ?Sized + 'l>
            Infer<'l, <P as View<'t>>::Output, Exists<'l, P>> for Proof
        {
            fn mp(&self, p: Rc<<P as View<'t>>::Output>) -> Rc<Exists<'l, P>> {
                Rc::new(Exists(Box::new(Witness(p))))
            }
        }
        let proof: Imply<_, _> = Box::new(Proof);
        Cert::new(Rc::new(proof))
    }
}
