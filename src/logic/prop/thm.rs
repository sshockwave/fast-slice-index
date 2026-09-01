use super::{Cert, Imply, Negation, PropLogic};

impl<PQ, Prop: Imply + ?Sized> Cert<Prop, PQ> {
    pub fn mp<P, Q>(self, p: Cert<Prop, P>) -> Cert<Prop, Q>
    where
        Self: Into<Cert<Prop, Prop::Imply<P, Q>>>,
    {
        Prop::mp(self.into(), p)
    }
    pub fn pipe<Q>(self, pq: Cert<Prop, Prop::Imply<PQ, Q>>) -> Cert<Prop, Q> {
        pq.mp(self)
    }
    pub fn cast<Logic, R>(self) -> Cert<Logic, R>
    where
        Logic: Imply<Cert<R> = Prop::Cert<PQ>>,
    {
        Cert::new(self.into_inner())
    }
}

pub fn reflexive<P, Prop: PropLogic>() -> Cert<Prop, Prop::Imply<P, P>> {
    Prop::l2().mp(Prop::l1()).mp(Prop::l1::<_, P>())
}

mod sealed_deduction {
    use super::{Cert, Imply, PropLogic, reflexive};
    use ::core::marker::PhantomData;

    /// Deduction theorem: If we can derive Q from P, then we can derive P → Q.
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);

    impl<A, Prop: PropLogic> Deduction<A, Prop> {
        pub fn assume() -> Cert<Self, A> {
            reflexive::<_, Prop>().cast()
        }
        pub fn upgrade<P>(value: Cert<Prop, P>) -> Cert<Self, P> {
            Prop::l1().mp(value).cast()
        }
        pub fn scope<R>(
            f: impl FnOnce(Cert<Self, A>) -> Cert<Self, R>,
        ) -> Cert<Prop, Prop::Imply<A, R>> {
            f(Self::assume()).cast()
        }
    }

    impl<A, Prop: PropLogic> Imply for Deduction<A, Prop> {
        type Imply<P, Q> = Prop::Imply<P, Q>;
        type Cert<P> = Prop::Cert<Prop::Imply<A, P>>;
        fn mp<P, Q>(pq: Cert<Self, Self::Imply<P, Q>>, p: Cert<Self, P>) -> Cert<Self, Q> {
            Prop::l2().mp(pq.cast()).mp(p.cast()).cast()
        }
    }
    impl<A, Prop: PropLogic> PropLogic for Deduction<A, Prop> {
        fn l1<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, P>>> {
            Self::upgrade(Prop::l1())
        }
        fn l2<P, Q, R>() -> Cert<
            Self,
            Self::Imply<
                Self::Imply<P, Self::Imply<Q, R>>,
                Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
            >,
        > {
            Self::upgrade(Prop::l2())
        }
    }
}
pub use sealed_deduction::Deduction;

pub trait DeductionUpgrade<A, P, Prop: PropLogic> {
    fn upgrade(self) -> Cert<Deduction<A, Prop>, P>;
    fn qed<Prop2: PropLogic>(self) -> Cert<Prop2, Prop2::Imply<A, P>>
    where
        Cert<Prop, P>: Into<Cert<Deduction<A, Prop2>, P>>;
}
impl<A, P, Prop: PropLogic> DeductionUpgrade<A, P, Prop> for Cert<Prop, P> {
    fn upgrade(self) -> Cert<Deduction<A, Prop>, P> {
        Deduction::upgrade(self)
    }
    fn qed<Prop2: PropLogic>(self) -> Cert<Prop2, Prop2::Imply<A, P>>
    where
        Cert<Prop, P>: Into<Cert<Deduction<A, Prop2>, P>>,
    {
        self.into().cast()
    }
}

impl<A, Logic: Negation> Negation for Deduction<A, Logic> {
    type Neg<P> = Logic::Neg<P>;
}

pub fn syllogism<P, Q, R, Prop: PropLogic>()
-> Cert<Prop, Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>> {
    Deduction::assume()
        .pipe(Deduction::assume().upgrade().upgrade())
        .pipe(Deduction::assume().upgrade())
        .qed()
        .qed()
        .qed()
}

/// Exchange of antecedents: (P → (Q → R)) → (Q → (P → R))
pub fn exchange<P, Q, R, Prop: PropLogic>()
-> Cert<Prop, Prop::Imply<Prop::Imply<P, Prop::Imply<Q, R>>, Prop::Imply<Q, Prop::Imply<P, R>>>> {
    Deduction::assume()
        .pipe(Deduction::assume().upgrade().upgrade())
        .mp(Deduction::assume().upgrade())
        .qed()
        .qed()
        .qed()
}
