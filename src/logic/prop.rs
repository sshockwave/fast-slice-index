#![forbid(unsafe_code)]

mod imply;
mod neg;

pub use self::{
    imply::{Chain, PropLogic, PropLogicThm},
    neg::{
        Contraposition, DoubleNegIntro, DoubleNegation, ExFalsoQuodlibet, Neg, PeirceLaw,
        ProofRing as NegProofRing, simplification, transposition,
    },
};

impl<'l, PQ: Clone + 'l, Prop: PropLogic<'l> + ?Sized> Chain<'l, Prop, PQ> for Prop::Cert<PQ> {
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
    use crate::logic::prop::reflexive;

    use super::{Chain, PropLogic};
    use ::core::marker::PhantomData;

    /// Deduction theorem: If
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);

    pub struct Cert<'a, A: 'a, P: 'a, Prop: PropLogic<'a>> {
        witness: Prop::Cert<Prop::Imply<A, P>>,
        _marker: PhantomData<P>,
    }
    impl<'a, A, P, Prop: PropLogic<'a>> Clone for Cert<'a, A, P, Prop> {
        fn clone(&self) -> Self {
            Cert::new(self.witness.clone())
        }
    }

    impl<'a, A, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn assume() -> <Self as PropLogic<'a>>::Cert<A>
        where
            A: Clone,
        {
            Cert::new(reflexive::<_, Prop>())
        }
    }
    impl<'a, A: 'a, P: 'a, Prop: PropLogic<'a>> Cert<'a, A, P, Prop> {
        fn new(witness: Prop::Cert<Prop::Imply<A, P>>) -> Self {
            Cert {
                witness,
                _marker: PhantomData,
            }
        }
        pub fn finish(self) -> Prop::Cert<Prop::Imply<A, P>> {
            self.witness
        }
    }

    impl<'a, A: Clone + 'a, Prop: PropLogic<'a>> PropLogic<'a> for Deduction<A, Prop> {
        type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
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
        type BaseCert<P: Clone + 'a> = Prop::Cert<P>;
        type Cert<P: Clone + 'a> = Cert<'a, A, P, Prop>;
        fn mp<P: Clone, Q: Clone>(
            pq: Self::Cert<Self::Imply<P, Q>>,
            p: Self::Cert<P>,
        ) -> Self::Cert<Q> {
            Cert::new(Prop::l2().apply(pq.witness).apply(p.witness))
        }
        fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P> {
            Cert::new(Prop::l1().apply(value))
        }
        fn def<P, Q>() -> Self::Cert<Self::Imply<P, Q>>
        where
            P: Into<Q> + Clone + 'a,
            Q: Clone + 'a,
        {
            Self::upgrade(Prop::def())
        }
    }
}
pub use sealed_deduction::Deduction;
impl<'l, A: Clone, Props: PropLogic<'l>> Deduction<A, Props> {
    fn scope<R: Clone>(
        f: impl FnOnce(<Self as PropLogic<'l>>::Cert<A>) -> <Self as PropLogic<'l>>::Cert<R>,
    ) -> Props::Cert<Props::Imply<A, R>> {
        f(Self::assume()).finish()
    }
}

pub fn syllogism<'a, P, Q, R, Prop: PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
    R: Clone + 'a,
{
    Deduction::<_, Prop>::scope(|pq| {
        Deduction::<_, Deduction<_, _>>::scope(|qr| {
            Deduction::<_, Deduction<_, _>>::scope(|p| {
                let pq = Deduction::upgrade(Deduction::upgrade(pq));
                let qr = Deduction::upgrade(qr);
                Deduction::mp(qr, Deduction::mp(pq, p))
            })
        })
    })
}

pub struct Or<'a, P: 'a, Q: 'a, Prop: PropLogic<'a>>(Prop::Cert<Prop::Imply<Neg<P>, Q>>);
pub struct And<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + ?Sized>(
    Prop::Cert<Neg<Prop::Imply<Q, Neg<P>>>>,
);

impl<'a, P: 'a, Q: 'a, Prop: Contraposition<'a>> And<'a, P, Q, Prop> {
    pub fn intro(p: Prop::Cert<P>, q: Prop::Cert<Q>) -> Self
    where
        P: Clone,
        Q: Clone,
    {
        Self(
            // From Q, derive (Q → ¬P) → ¬P by modus ponens on the assumption.
            Prop::l2()
                .apply(reflexive::<_, Prop>())
                .apply(Prop::l1().apply(q))
                // Transposing gives ¬¬P → ¬(Q → ¬P), and ¬¬P follows from P.
                .pipe(transposition::<_, _, Prop>())
                .apply(<NegProofRing<Prop> as DoubleNegIntro<'_>>::l3().apply(p)),
        )
    }

    /// Left elimination: P ∧ Q → P
    pub fn left(self) -> Prop::Cert<P>
    where
        P: Clone,
        Q: Clone,
    {
        // ¬P → (Q → ¬P) transposes to ¬(Q → ¬P) → ¬¬P, then double negation.
        transposition::<_, _, Prop>()
            .apply(Prop::l1::<Neg<P>, Q>())
            .apply(self.0)
            .pipe(<NegProofRing<Prop> as DoubleNegation<'_>>::l3())
    }

    /// Right elimination: P ∧ Q → Q
    pub fn right(self) -> Prop::Cert<Q>
    where
        Q: Clone,
    {
        simplification::<_, _, Prop>().apply(self.0)
    }
}

impl<'a, P: 'a, Q: 'a, Prop: Contraposition<'a>> Or<'a, P, Q, Prop> {
    pub fn intro_left(p: Prop::Cert<P>) -> Self
    where
        P: Clone,
    {
        Self(
            <NegProofRing<Prop> as DoubleNegIntro<'_>>::l3()
                .apply(p)
                .pipe(Prop::l1())
                .pipe(Prop::l3()),
        )
    }
    pub fn intro_right(q: Prop::Cert<Q>) -> Self
    where
        Q: Clone,
    {
        Self(Prop::l1().apply(q))
    }
    pub fn p_to_q(self) -> Prop::Cert<Prop::Imply<Neg<P>, Q>> {
        self.0
    }
    pub fn q_to_p(self) -> Prop::Cert<Prop::Imply<Neg<Q>, P>>
    where
        P: Clone,
    {
        Prop::l1()
            .apply(<NegProofRing<Prop> as DoubleNegIntro<'_>>::l3())
            .pipe(Prop::l2())
            .apply(self.0)
            .pipe(Prop::l3())
    }
}

pub struct Iff<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + ?Sized>(
    And<'a, Prop::Imply<P, Q>, Prop::Imply<Q, P>, Prop>,
);
