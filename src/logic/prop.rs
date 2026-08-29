#![forbid(unsafe_code)]

pub mod il;
mod imply;
mod neg;
mod thm;

pub use self::{
    imply::PropLogicThm,
    neg::{
        Contraposition, DoubleNegIntro, DoubleNegation, ExFalsoQuodlibet, Negation, PeirceLaw,
        ProofRing as NegProofRing, consequentia_mirabilis, simplification, transposition,
    },
    thm::*,
};

use self::sealed_type_eq::TypeEq;
mod sealed_type_eq {
    pub trait TypeEq<P>: From<P> + Into<P> {}
    impl<T> TypeEq<T> for T {}
}

pub trait Chain<'l, Prop: PropLogic<'l> + ?Sized, PQ: Clone + 'l> {
    fn apply<P: Clone, Q: Clone>(self, p: Prop::Cert<P>) -> Prop::Cert<Q>
    where
        Prop::Cert<PQ>: TypeEq<Prop::Cert<Prop::Imply<P, Q>>>;
    fn pipe<Q: Clone>(self, pq: Prop::Cert<Prop::Imply<PQ, Q>>) -> Prop::Cert<Q>;
}

/// Axiomatic propositional logic
///
/// This is a logic system where all theorems are derived from axioms using inference rules.
/// Rust type system implies propositional logic,
/// so we can prove this in [`PropLogicThm`] without any unsafe code.
pub trait PropLogic<'a>: Sized {
    /// Implication: P implies Q
    type Imply<P: 'a, Q: 'a>: Clone + 'a;

    /// Axiom L1: P → (Q → P)
    /// If P is true, then Q implies P
    fn l1<P: Clone + 'a, Q>() -> Self::Cert<Self::Imply<P, Self::Imply<Q, P>>>;

    /// Axiom L2: (P → (Q → R)) → ((P → Q) → (P → R))
    /// Distribution of implication
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Self::Cert<
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    >;

    type BaseCert<P: Clone + 'a>;
    type Cert<P: Clone + 'a>: Clone + Chain<'a, Self, P>;

    /// Modus Ponens: Given (P → Q) and P, derive Q
    /// This is the only inference rule - all others are axioms
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Self::Cert<Self::Imply<P, Q>>,
        p: Self::Cert<P>,
    ) -> Self::Cert<Q>;

    fn upgrade<P: Clone + 'a>(value: Self::BaseCert<P>) -> Self::Cert<P>;
    fn def<P, Q>() -> Self::Cert<Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a;
}

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

pub struct Or<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + Negation<'a>>(
    Prop::Cert<Prop::Imply<Prop::Neg<P>, Q>>,
);
pub struct And<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + Negation<'a>>(
    Prop::Cert<Prop::Neg<Prop::Imply<Q, Prop::Neg<P>>>>,
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
            .apply(Prop::l1::<Prop::Neg<P>, Q>())
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
    pub fn p_to_q(self) -> Prop::Cert<Prop::Imply<Prop::Neg<P>, Q>> {
        self.0
    }
    pub fn q_to_p(self) -> Prop::Cert<Prop::Imply<Prop::Neg<Q>, P>>
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

pub struct Iff<'a, P: 'a, Q: 'a, Prop: Contraposition<'a>>(
    And<'a, Prop::Imply<P, Q>, Prop::Imply<Q, P>, Prop>,
);
