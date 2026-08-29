use super::{Imply, Negation, PropLogic};

use self::sealed_type_eq::TypeEq;
mod sealed_type_eq {
    pub trait TypeEq<P>: From<P> + Into<P> {}
    impl<T> TypeEq<T> for T {}
}

pub trait Chain<'l, Prop: Imply<'l> + ?Sized, PQ: Clone + 'l> {
    fn apply<P: Clone, Q: Clone>(self, p: Prop::Cert<P>) -> Prop::Cert<Q>
    where
        Prop::Cert<PQ>: TypeEq<Prop::Cert<Prop::Imply<P, Q>>>;
    fn pipe<Q: Clone>(self, pq: Prop::Cert<Prop::Imply<PQ, Q>>) -> Prop::Cert<Q>;
}

impl<'l, PQ: Clone + 'l, Prop: Imply<'l> + ?Sized> Chain<'l, Prop, PQ> for Prop::Cert<PQ> {
    fn apply<P: Clone, Q: Clone>(self, p: Prop::Cert<P>) -> Prop::Cert<Q>
    where
        Prop::Cert<PQ>: Into<Prop::Cert<Prop::Imply<P, Q>>>,
    {
        Prop::mp(self.into(), p)
    }
    fn pipe<Q: Clone>(self, pq: Prop::Cert<Prop::Imply<PQ, Q>>) -> Prop::Cert<Q> {
        Prop::mp(pq, self)
    }
}

pub fn reflexive<'a, P, Prop: PropLogic<'a>>() -> Prop::Cert<Prop::Imply<P, P>>
where
    P: Clone + 'a,
{
    Prop::l2().apply(Prop::l1()).apply(Prop::l1::<_, P>())
}

mod sealed_deduction {
    use super::{Chain, Imply, PropLogic, reflexive};
    use ::core::marker::PhantomData;

    /// Deduction theorem: If we can derive Q from P, then we can derive P → Q.
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);
    impl<A, Prop> Clone for Deduction<A, Prop> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<A, Prop> Copy for Deduction<A, Prop> {}

    impl<'a, A: Clone, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn assume() -> <Self as Imply<'a>>::Cert<A> {
            reflexive::<_, Prop>()
        }
        pub fn upgrade<P: Clone + 'a>(value: Prop::Cert<P>) -> <Self as Imply<'a>>::Cert<P> {
            Prop::l1().apply(value)
        }
        pub fn scope<R: Clone>(
            f: impl FnOnce(
                <Self as Imply<'a>>::Cert<A>,
                Deduction<A, Self>,
            ) -> <Self as Imply<'a>>::Cert<R>,
        ) -> Prop::Cert<Prop::Imply<A, R>> {
            f(Self::assume(), Deduction(PhantomData))
        }
    }

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> Imply<'a> for Deduction<A, Prop> {
        type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
        type Cert<P: Clone + 'a> = Prop::Cert<Prop::Imply<A, P>>;
        fn mp<P: Clone, Q: Clone>(
            pq: Self::Cert<Self::Imply<P, Q>>,
            p: Self::Cert<P>,
        ) -> Self::Cert<Q> {
            Prop::l2().apply(pq).apply(p)
        }
        fn def<P, Q>() -> Self::Cert<Self::Imply<P, Q>>
        where
            P: Into<Q> + Clone + 'a,
            Q: Clone + 'a,
        {
            Self::upgrade(Prop::def())
        }
    }
    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> PropLogic<'a> for Deduction<A, Prop> {
        fn l1<P: Clone + 'a, Q>() -> Self::Cert<Self::Imply<P, Self::Imply<Q, P>>> {
            Self::upgrade(Prop::l1())
        }
        fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Self::Cert<
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

impl<'l, A: Clone, Logic: PropLogic<'l>> Deduction<A, Logic> {
    pub fn mp<P: Clone, Q: Clone>(
        &self,
        pq: Logic::Cert<Logic::Imply<P, Q>>,
        p: Logic::Cert<P>,
    ) -> Logic::Cert<Q> {
        Logic::mp(pq, p)
    }
    pub fn nest<B: Clone, R: Clone>(
        &self,
        f: impl FnOnce(
            Logic::Cert<Logic::Imply<B, B>>,
            Deduction<B, Deduction<B, Logic>>,
        ) -> Logic::Cert<Logic::Imply<B, R>>,
    ) -> Logic::Cert<Logic::Imply<B, R>> {
        Deduction::scope(f)
    }
}
impl<'l, A: Clone, Logic: PropLogic<'l>> Deduction<A, Deduction<A, Logic>> {
    pub fn up<P: Clone>(&self, p: Logic::Cert<P>) -> <Deduction<A, Logic> as Imply<'l>>::Cert<P> {
        Deduction::<A, Logic>::upgrade(p)
    }
}

impl<'l, A, Logic: Negation<'l>> Negation<'l> for Deduction<A, Logic> {
    type Neg<P: 'l> = Logic::Neg<P>;
}

pub fn syllogism<'a, P, Q, R, Prop: PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>>
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
                s3.mp(qr, s3.mp(pq, p))
            })
        })
    })
}
