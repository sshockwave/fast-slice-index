#![forbid(unsafe_code)]

pub mod il;
mod imply;
pub mod neg;
mod thm;

pub use self::{
    imply::PropLogicThm,
    neg::{
        Contraposition, DoubleNegIntro, DoubleNegation, ExFalsoQuodlibet, PeirceLaw,
        ProofRing as NegProofRing, consequentia_mirabilis, simplification, transposition,
    },
    thm::*,
};

pub trait PropLogic<'a>: Imply<'a> {
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
}

pub trait Imply<'a>: Sized {
    /// Implication: P implies Q
    type Imply<P: 'a, Q: 'a>: Clone + 'a;
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

pub trait Negation<'l> {
    type Neg<P: 'l>: Clone + 'l;
}

pub trait LogicalAnd<'l>: PropLogic<'l> {
    type And<P, Q>: Clone;
}

pub trait Intuitionistic<'l>: PropLogic<'l> {}
