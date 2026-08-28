use crate::logic::prop::{Deduction, PropLogic, reflexive, syllogism};
use ::core::marker::PhantomData;

pub struct Neg<P>(PhantomData<P>);

impl<P> Clone for Neg<P> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<P> Copy for Neg<P> {}

pub trait Contraposition<'a>: PropLogic<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Imply<Neg<P>, Neg<Q>>, Self::Imply<Q, P>>>;
}

pub trait DoubleNegation<'a>: PropLogic<'a> {
    fn l3<P>() -> Self::Cert<Self::Imply<Neg<Neg<P>>, P>>;
}

pub trait DoubleNegIntro<'a>: PropLogic<'a> {
    fn l3<P>() -> Self::Cert<Self::Imply<P, Neg<Neg<P>>>>;
}

pub trait PeirceLaw<'a>: PropLogic<'a> {
    fn peirce<P, Q>() -> Self::Cert<Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>>;
}

pub struct ProofRing<'a, Prop>(PhantomData<(&'a (), Prop)>);

impl<'a, Prop> PropLogic<'a> for ProofRing<'a, Prop>
where
    Prop: PropLogic<'a>,
{
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    fn l1<P: Clone + 'a, Q>() -> Self::Cert<Self::Imply<P, Self::Imply<Q, P>>> {
        Prop::l1()
    }
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Self::Cert<
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        Prop::l2()
    }
    type BaseCert<P: Clone + 'a> = Prop::Cert<P>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Self::Cert<Self::Imply<P, Q>>,
        p: Self::Cert<P>,
    ) -> Self::Cert<Q> {
        Prop::mp(pq, p)
    }
    fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P> {
        value
    }
    fn def<P, Q>() -> Self::Cert<Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a,
    {
        Prop::def()
    }
}

impl<'a, Prop> DoubleNegation<'a> for ProofRing<'a, Prop>
where
    Prop: Contraposition<'a>,
{
    fn l3<P>() -> Self::Cert<Self::Imply<Neg<Neg<P>>, P>>
    where
        P: 'a,
    {
        // https://math.stackexchange.com/questions/4634566/prove-that-contrapositive-rule-is-equivalent-to-the-rule-of-double-negation
        Prop::mp(
            Prop::mp(
                Prop::l2(),
                Prop::mp(
                    Prop::mp(
                        syllogism::<_, _, _, Prop>(),
                        Prop::mp(
                            Prop::mp(syllogism::<_, _, _, Prop>(), Prop::l1()),
                            Prop::l3(),
                        ),
                    ),
                    Prop::l3(),
                ),
            ),
            reflexive::<_, Prop>(),
        )
    }
}

impl<'a, Prop: Contraposition<'a>> DoubleNegIntro<'a> for ProofRing<'a, Prop> {
    fn l3<P>() -> Self::Cert<Self::Imply<P, Neg<Neg<P>>>> {
        Prop::mp(Prop::l3(), <ProofRing<Prop> as DoubleNegation<'_>>::l3())
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a>> ExFalsoQuodlibet<'a> for ProofRing<'a, Prop> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Neg<P>, Self::Imply<P, Q>>> {
        Prop::mp(
            Prop::mp(syllogism::<_, _, _, Prop>(), Prop::l1()),
            Prop::l3(),
        )
    }
}

pub fn simplification<'a, P, Q, Prop: Contraposition<'a>>()
-> Prop::Cert<Prop::Imply<Neg<Prop::Imply<P, Q>>, P>> {
    Prop::mp(
        Prop::l3(),
        Prop::mp(
            Prop::mp(
                syllogism::<_, _, _, Prop>(),
                <ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3(),
            ),
            <ProofRing<Prop> as DoubleNegIntro<'_>>::l3(),
        ),
    )
}

/// Transposition: (P → Q) → (¬Q → ¬P)
///
/// The converse of [`Contraposition`], obtained by wrapping both sides in a
/// double negation so that [`Contraposition::l3`] applies.
pub fn transposition<'a, P: Clone + 'a, Q: Clone + 'a, Prop: Contraposition<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Neg<Q>, Neg<P>>>> {
    // (P → Q) → (¬¬P → Q)
    let pre = Prop::mp(
        syllogism::<_, _, _, Prop>(),
        <ProofRing<Prop> as DoubleNegation<'_>>::l3::<P>(),
    );
    // (¬¬P → Q) → (¬¬P → ¬¬Q)
    let post = Prop::mp(
        Prop::l2(),
        Prop::mp(
            Prop::l1(),
            <ProofRing<Prop> as DoubleNegIntro<'_>>::l3::<Q>(),
        ),
    );
    Prop::mp(
        Prop::mp(
            syllogism::<_, _, _, Prop>(),
            // (P → Q) → (¬¬P → ¬¬Q)
            Prop::mp(Prop::mp(syllogism::<_, _, _, Prop>(), pre), post),
        ),
        Prop::l3(),
    )
}

impl<'a, Prop: Contraposition<'a>> PeirceLaw<'a> for ProofRing<'a, Prop> {
    fn peirce<P, Q>() -> Self::Cert<Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>> {
        todo!()
    }
}
