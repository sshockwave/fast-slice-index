use super::{Cert, Imply, Negation, PropLogic};

impl<'l, PQ: Clone + 'l, Prop: Imply<'l> + ?Sized> Cert<'l, Prop, PQ> {
    pub fn mp<P: Clone, Q: Clone>(self, p: Cert<'l, Prop, P>) -> Cert<'l, Prop, Q>
    where
        Self: Into<Cert<'l, Prop, Prop::Imply<P, Q>>>,
    {
        Prop::mp(self.into(), p)
    }
    pub fn pipe<Q: Clone>(self, pq: Cert<'l, Prop, Prop::Imply<PQ, Q>>) -> Cert<'l, Prop, Q> {
        pq.mp(self)
    }
    pub fn cast<Logic, R: Clone>(self) -> Cert<'l, Logic, R>
    where
        Logic: Imply<'l, Cert<R> = Prop::Cert<PQ>>,
    {
        Cert::new(self.into_inner())
    }
}

pub fn reflexive<'a, P, Prop: PropLogic<'a>>() -> Cert<'a, Prop, Prop::Imply<P, P>>
where
    P: Clone + 'a,
{
    Prop::l2().mp(Prop::l1()).mp(Prop::l1::<_, P>())
}

mod sealed_deduction {
    use super::{Cert, Imply, PropLogic, reflexive};
    use ::core::marker::PhantomData;

    /// Deduction theorem: If we can derive Q from P, then we can derive P → Q.
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);
    impl<A, Prop> Clone for Deduction<A, Prop> {
        fn clone(&self) -> Self {
            struct A<P> {
                inner: P,
            }
            *self
        }
    }
    impl<A, Prop> Copy for Deduction<A, Prop> {}

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn assume() -> Cert<'a, Self, A> {
            reflexive::<_, Prop>().cast()
        }
        pub fn upgrade<P: Clone + 'a>(value: Cert<'a, Prop, P>) -> Cert<'a, Self, P> {
            Prop::l1().mp(value).cast()
        }
        pub fn scope<R: Clone>(
            f: impl FnOnce(Cert<'a, Self, A>) -> Cert<'a, Self, R>,
        ) -> Cert<'a, Prop, Prop::Imply<A, R>> {
            f(Self::assume()).cast()
        }
    }

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> Imply<'a> for Deduction<A, Prop> {
        type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
        type Cert<P: Clone + 'a> = Prop::Cert<Prop::Imply<A, P>>;
        fn mp<P: Clone, Q: Clone>(
            pq: Cert<'a, Self, Self::Imply<P, Q>>,
            p: Cert<'a, Self, P>,
        ) -> Cert<'a, Self, Q> {
            Prop::l2().mp(pq.cast()).mp(p.cast()).cast()
        }
    }
    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> PropLogic<'a> for Deduction<A, Prop> {
        fn l1<P: Clone + 'a, Q>() -> Cert<'a, Self, Self::Imply<P, Self::Imply<Q, P>>> {
            Self::upgrade(Prop::l1())
        }
        fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<
            'a,
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

pub trait DeductionUpgrade<'l, A: Clone + 'l, P: Clone, Prop: PropLogic<'l>> {
    fn upgrade(self) -> Cert<'l, Deduction<A, Prop>, P>;
    fn qed<Prop2: PropLogic<'l>>(self) -> Cert<'l, Prop2, Prop2::Imply<A, P>>
    where
        Cert<'l, Prop, P>: Into<Cert<'l, Deduction<A, Prop2>, P>>;
}
impl<'l, A: Clone + 'l, P: Clone, Prop: PropLogic<'l>> DeductionUpgrade<'l, A, P, Prop>
    for Cert<'l, Prop, P>
{
    fn upgrade(self) -> Cert<'l, Deduction<A, Prop>, P> {
        Deduction::upgrade(self)
    }
    fn qed<Prop2: PropLogic<'l>>(self) -> Cert<'l, Prop2, Prop2::Imply<A, P>>
    where
        Cert<'l, Prop, P>: Into<Cert<'l, Deduction<A, Prop2>, P>>,
    {
        self.into().cast()
    }
}

impl<'l, A, Logic: Negation<'l>> Negation<'l> for Deduction<A, Logic> {
    type Neg<P: 'l> = Logic::Neg<P>;
}

pub fn syllogism<'a, P, Q, R, Prop: PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
    R: Clone + 'a,
{
    Deduction::assume()
        .pipe(Deduction::assume().upgrade().upgrade())
        .pipe(Deduction::assume().upgrade())
        .qed()
        .qed()
        .qed()
}

/// Exchange of antecedents: (P → (Q → R)) → (Q → (P → R))
pub fn exchange<'a, P, Q, R, Prop: PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Imply<P, Prop::Imply<Q, R>>, Prop::Imply<Q, Prop::Imply<P, R>>>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
    R: Clone + 'a,
{
    Deduction::assume()
        .pipe(Deduction::assume().upgrade().upgrade())
        .mp(Deduction::assume().upgrade())
        .qed()
        .qed()
        .qed()
}
