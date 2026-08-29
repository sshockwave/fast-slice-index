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
use ::core::convert::Infallible;

pub trait View<'x> {
    type Output;
}

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

pub trait And<'l>: PropLogic<'l> {
    type And<P, Q>: Clone;
    fn and_left<P, Q>() -> Self::Cert<Self::Imply<Self::And<P, Q>, P>>;
    fn and_right<P, Q>() -> Self::Cert<Self::Imply<Self::And<P, Q>, Q>>;
    fn and_intro<P, Q>() -> Self::Cert<Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>>;
}

type Iff<'l, L, P, Q> =
    <L as And<'l>>::And<<L as Imply<'l>>::Imply<P, Q>, <L as Imply<'l>>::Imply<Q, P>>;

pub trait Or<'l>: PropLogic<'l> {
    type Or<P, Q>: Clone;
    fn or_left<P, Q>() -> Self::Cert<Self::Imply<P, Self::Or<P, Q>>>;
    fn or_right<P, Q>() -> Self::Cert<Self::Imply<Q, Self::Or<P, Q>>>;
    fn or_elim<P, Q, R>() -> Self::Cert<
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    >;
}

pub trait Intuitionistic<'l>: PropLogic<'l> + And<'l> + Or<'l> {
    fn explosion<P>() -> Self::Cert<Self::Imply<Infallible, P>>;
}

pub trait ForAllProof<'l, Logic: Imply<'l>, P, Q: for<'x> View<'x> + ?Sized> {
    fn prove<'x>(self) -> Logic::Imply<P, <Q as View<'x>>::Output>;
}
pub trait ExistsProof<'l, Logic: Imply<'l>, P: for<'x> View<'x> + ?Sized, Q> {
    fn prove<'x>(self) -> Logic::Imply<<P as View<'x>>::Output, Q>;
}

pub trait FirstOrder<'l>: Imply<'l> + 'l {
    type ForAll<P: for<'x> View<'x> + ?Sized>: Clone;
    type Exists<P: for<'x> View<'x> + ?Sized>: Clone;
    fn forall_gen<P, Q: for<'x> View<'x> + ?Sized, S: ForAllProof<'l, Self, P, Q>>(
        proof: S,
    ) -> Self::Cert<Self::Imply<P, Self::ForAll<Q>>>;
    fn exists_gen<P: for<'x> View<'x> + ?Sized, Q, S: ExistsProof<'l, Self, P, Q>>(
        proof: S,
    ) -> Self::Cert<Self::Imply<Self::Exists<P>, Q>>;
    fn forall_elim<'t, P: for<'x> View<'x> + ?Sized>()
    -> Self::Cert<Self::Imply<Self::ForAll<P>, <P as View<'t>>::Output>>;
    fn exists_elim<'t, P: for<'x> View<'x> + ?Sized, Q>()
    -> Self::Cert<Self::Imply<<P as View<'t>>::Output, Self::Exists<P>>>;
}

pub trait ViewT {
    type Output<T>;
}

pub trait ForAllProofT<'l, Logic: Imply<'l>, P, Q: ViewT + ?Sized> {
    fn prove<T>(self) -> Logic::Imply<P, Q::Output<T>>;
}
pub trait ExistsProofT<'l, Logic: Imply<'l>, P: ViewT + ?Sized, Q> {
    fn prove<T>(self) -> Logic::Imply<P::Output<T>, Q>;
}

pub trait FirstOrderT<'l>: Imply<'l> + 'l {
    type ForAll<P: ViewT + ?Sized>: Clone;
    type Exists<P: ViewT + ?Sized>: Clone;
    fn forall_gen<P, Q: ViewT + ?Sized, S: ForAllProofT<'l, Self, P, Q>>(
        proof: S,
    ) -> Self::Cert<Self::Imply<P, Self::ForAll<Q>>>;
    fn exists_gen<P: ViewT + ?Sized, Q, S: ExistsProofT<'l, Self, P, Q>>(
        proof: S,
    ) -> Self::Cert<Self::Imply<Self::Exists<P>, Q>>;
}
