#![forbid(unsafe_code)]

mod imply;
mod neg;

pub use self::{
    imply::{PropLogic, PropLogicThm},
    neg::{
        Contraposition, DoubleNegIntro, DoubleNegation, ExFalsoQuodlibet, Neg, PeirceLaw,
        ProofRing as NegProofRing, transposition,
    },
};

pub fn reflexive<'a, P, Prop: PropLogic<'a>>() -> Prop::Cert<Prop::Imply<P, P>>
where
    P: Clone + 'a,
{
    Prop::mp(
        Prop::mp(Prop::l2(), Prop::l1::<_, Prop::Imply<P, _>>()),
        Prop::l1(),
    )
}

mod sealed_deduction {
    use crate::logic::prop::reflexive;

    use super::PropLogic;
    use ::core::marker::PhantomData;

    /// Deduction theorem: If
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);

    pub struct Cert<'a, A: 'a, P: 'a, Prop: PropLogic<'a>> {
        witness: Prop::Cert<Prop::Imply<A, P>>,
        _marker: PhantomData<P>,
    }
    impl<'a, A, P, Prop: PropLogic<'a>> Clone for Cert<'a, A, P, Prop> {
        fn clone(&self) -> Self {
            Cert {
                witness: self.witness.clone(),
                _marker: PhantomData,
            }
        }
    }

    impl<'a, A, Prop: PropLogic<'a>> Deduction<A, Prop> {
        pub fn assume() -> <Self as PropLogic<'a>>::Cert<A>
        where
            A: Clone,
        {
            Cert {
                witness: reflexive::<_, Prop>(),
                _marker: PhantomData,
            }
        }
    }
    impl<'a, A: 'a, P: 'a, Prop: PropLogic<'a>> Cert<'a, A, P, Prop> {
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
            Cert {
                witness: Prop::mp(Prop::mp(Prop::l2(), pq.witness), p.witness),
                _marker: PhantomData,
            }
        }
        fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P> {
            Cert {
                witness: Prop::mp(Prop::l1(), value),
                _marker: PhantomData,
            }
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

pub fn syllogism<'a, P, Q, R, Prop: PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
    R: Clone + 'a,
{
    let pq = Deduction::<_, Prop>::assume();
    let qr = Deduction::<_, Deduction<_, _>>::assume();
    let p = Deduction::<_, Deduction<_, _>>::assume();
    let r = Deduction::mp(
        Deduction::upgrade(qr),
        Deduction::mp(Deduction::upgrade(Deduction::upgrade(pq)), p),
    );
    r.finish().finish().finish()
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
        // From Q, derive (Q → ¬P) → ¬P by modus ponens on the assumption.
        let apply_q = Prop::mp(
            Prop::mp(Prop::l2(), reflexive::<_, Prop>()),
            Prop::mp(Prop::l1(), q),
        );
        // Transposing gives ¬¬P → ¬(Q → ¬P), and ¬¬P follows from P.
        Self(Prop::mp(
            Prop::mp(transposition::<_, _, Prop>(), apply_q),
            Prop::mp(<NegProofRing<Prop> as DoubleNegIntro<'_>>::l3(), p),
        ))
    }
}

impl<'a, P: 'a, Q: 'a, Prop: Contraposition<'a>> Or<'a, P, Q, Prop> {
    pub fn intro_left(p: Prop::Cert<P>) -> Self
    where
        P: Clone,
    {
        Self(Prop::mp(
            Prop::l3(),
            Prop::mp(
                Prop::l1(),
                Prop::mp(<NegProofRing<Prop> as DoubleNegIntro<'_>>::l3(), p),
            ),
        ))
    }
    pub fn intro_right(q: Prop::Cert<Q>) -> Self
    where
        Q: Clone,
    {
        Self(Prop::mp(Prop::l1(), q))
    }
    pub fn p_to_q(self) -> Prop::Cert<Prop::Imply<Neg<P>, Q>> {
        self.0
    }
    pub fn q_to_p(self) -> Prop::Cert<Prop::Imply<Neg<Q>, P>>
    where
        P: Clone,
    {
        Prop::mp(
            Prop::l3(),
            Prop::mp(
                Prop::mp(
                    Prop::l2(),
                    Prop::mp(Prop::l1(), <NegProofRing<Prop> as DoubleNegIntro<'_>>::l3()),
                ),
                self.0,
            ),
        )
    }
}

pub struct Iff<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + ?Sized>(
    And<'a, Prop::Imply<P, Q>, Prop::Imply<Q, P>, Prop>,
);
