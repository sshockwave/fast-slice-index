use super::{Cert, Imply, Negation, PropLogic};

impl<'l, PQ: Clone + 'l, Prop: Imply<'l> + ?Sized> Cert<'l, Prop, PQ> {
    pub fn apply<P: Clone, Q: Clone>(self, p: Cert<'l, Prop, P>) -> Cert<'l, Prop, Q>
    where
        Self: Into<Cert<'l, Prop, Prop::Imply<P, Q>>>,
    {
        Prop::mp(self.into(), p)
    }
    pub fn pipe<Q: Clone>(self, pq: Cert<'l, Prop, Prop::Imply<PQ, Q>>) -> Cert<'l, Prop, Q> {
        Prop::mp(pq, self)
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
    Prop::l2().apply(Prop::l1()).apply(Prop::l1::<_, P>())
}

mod sealed_deduction {
    use super::{Cert, Imply, PropLogic, reflexive};
    use ::core::marker::PhantomData;

    /// Deduction theorem: If we can derive Q from P, then we can derive P → Q.
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);
    impl<A, Prop> Clone for Deduction<A, Prop> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<A, Prop> Copy for Deduction<A, Prop> {}

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn assume() -> Cert<'a, Self, A> {
            reflexive::<_, Prop>().cast()
        }
        pub fn upgrade<P: Clone + 'a>(value: Cert<'a, Prop, P>) -> Cert<'a, Self, P> {
            Prop::l1().apply(value).cast()
        }
        pub fn scope<R: Clone>(
            f: impl FnOnce(Cert<'a, Self, A>, Self) -> Cert<'a, Self, R>,
        ) -> Cert<'a, Prop, Prop::Imply<A, R>> {
            f(Self::assume(), Deduction(PhantomData)).cast()
        }
    }

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> Imply<'a> for Deduction<A, Prop> {
        type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
        type Cert<P: Clone + 'a> = Prop::Cert<Prop::Imply<A, P>>;
        fn mp<P: Clone, Q: Clone>(
            pq: Cert<'a, Self, Self::Imply<P, Q>>,
            p: Cert<'a, Self, P>,
        ) -> Cert<'a, Self, Q> {
            Prop::l2().apply(pq.cast()).apply(p.cast()).cast()
        }
        fn def<P, Q>() -> Cert<'a, Self, Self::Imply<P, Q>>
        where
            P: Into<Q> + Clone + 'a,
            Q: Clone + 'a,
        {
            Self::upgrade(Prop::def())
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

impl<'l, A: Clone + 'l, Logic: PropLogic<'l>> Deduction<A, Logic> {
    pub fn nest<B: Clone, R: Clone>(
        &self,
        f: impl FnOnce(
            Cert<'l, Deduction<B, Self>, B>,
            Deduction<B, Self>,
        ) -> Cert<'l, Deduction<B, Self>, R>,
    ) -> Cert<'l, Self, Logic::Imply<B, R>> {
        Deduction::scope(f)
    }
    pub fn up<P: Clone>(&self, p: Cert<'l, Logic, P>) -> Cert<'l, Self, P> {
        Deduction::upgrade(p)
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
    Deduction::<_, Prop>::scope(|pq, s1| {
        s1.nest(|qr, s2| {
            let pq = s2.up(pq);
            s2.nest(|p, s3| {
                let pq = s3.up(pq);
                let qr = s3.up(qr);
                qr.apply(pq.apply(p))
            })
        })
    })
}
