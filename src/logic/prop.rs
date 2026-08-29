#![forbid(unsafe_code)]

pub mod il;
pub mod neg;
mod thm;

pub use self::thm::*;

pub trait View<'x> {
    type Output;
}

pub trait PropLogic<'a>: Imply<'a> {
    /// Axiom L1: P → (Q → P)
    /// If P is true, then Q implies P
    fn l1<P: Clone + 'a, Q>() -> Cert<'a, Self, Self::Imply<P, Self::Imply<Q, P>>>;

    /// Axiom L2: (P → (Q → R)) → ((P → Q) → (P → R))
    /// Distribution of implication
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<
        'a,
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    >;
}

pub use self::sealed_cert::Cert;
mod sealed_cert {
    use super::Imply;
    pub struct Cert<'l, Logic: Imply<'l>, P: Clone + 'l>(Logic::Cert<P>);
    impl<'l, Logic: Imply<'l>, P: Clone + 'l> Clone for Cert<'l, Logic, P> {
        fn clone(&self) -> Self {
            Cert(self.0.clone())
        }
    }
    impl<'l, Logic: Imply<'l>, P: Clone + 'l> Cert<'l, Logic, P> {
        pub fn new(cert: Logic::Cert<P>) -> Self {
            Cert(cert)
        }
        pub fn into_inner(self) -> Logic::Cert<P> {
            self.0
        }
    }
}

pub trait Imply<'a>: Sized {
    /// Implication: P implies Q
    type Imply<P: 'a, Q: 'a>: Clone + 'a;
    type Cert<P: Clone + 'a>: Clone;

    /// Modus Ponens: Given (P → Q) and P, derive Q
    /// This is the only inference rule - all others are axioms
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Cert<'a, Self, Self::Imply<P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q>;

    fn def<P, Q>() -> Cert<'a, Self, Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a;
}

pub trait Negation<'l> {
    type Neg<P: 'l>: Clone + 'l;
}

/// Reductio ad absurdum: (P → ¬Q) → (Q → ¬P)
///
/// The negation-*introduction* rule. [`DoubleNegElim`], [`ExFalsoQuodlibet`]
/// and [`DoubleNegIntro`] all either consume a `Neg` or re-wrap an existing
/// one, so none of them can produce the `¬¬P` that [`Contraposition`] needs:
/// interpreting `Neg<_>` as a constant falsehood satisfies all three and
/// refutes contraposition. This rule closes that gap, and unlike
/// [`Contraposition`] it adds no classical strength -- it holds for the
/// intuitionistic reading `¬P := P → ⊥`.
///
/// [`DoubleNegElim`]: neg::DoubleNegElim
/// [`ExFalsoQuodlibet`]: neg::ExFalsoQuodlibet
/// [`DoubleNegIntro`]: neg::DoubleNegIntro
/// [`Contraposition`]: neg::Contraposition
pub trait Reductio<'a>: PropLogic<'a> + Negation<'a> {
    fn reductio<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>>;
}

pub trait And<'l>: PropLogic<'l> {
    type And<P: 'l, Q: 'l>: Clone;
    fn and_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, P>>;
    fn and_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>>;
    fn and_intro<P: Clone, Q: Clone>()
    -> Cert<'l, Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>>;
}

pub type Iff<'l, L, P, Q> =
    <L as And<'l>>::And<<L as Imply<'l>>::Imply<P, Q>, <L as Imply<'l>>::Imply<Q, P>>;

pub trait Or<'l>: PropLogic<'l> {
    type Or<P: 'l, Q: 'l>: Clone;
    fn or_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>>;
    fn or_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>>;
    fn or_elim<P: Clone, Q: Clone, R: Clone>() -> Cert<
        'l,
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    >;
}

pub trait Intuitionistic<'l>: PropLogic<'l> + And<'l> + Or<'l> + Negation<'l> {
    type False;
    fn explosion<P: Clone>() -> Cert<'l, Self, Self::Imply<Self::False, P>>;
    fn neg_def<P: Clone>()
    -> Cert<'l, Self, Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>>;
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
    ) -> Cert<'l, Self, Self::Imply<P, Self::ForAll<Q>>>;
    fn exists_gen<P: for<'x> View<'x> + ?Sized, Q, S: ExistsProof<'l, Self, P, Q>>(
        proof: S,
    ) -> Cert<'l, Self, Self::Imply<Self::Exists<P>, Q>>;
    fn forall_elim<'t, P: for<'x> View<'x> + ?Sized>()
    -> Cert<'l, Self, Self::Imply<Self::ForAll<P>, <P as View<'t>>::Output>>;
    fn exists_elim<'t, P: for<'x> View<'x> + ?Sized, Q>()
    -> Cert<'l, Self, Self::Imply<<P as View<'t>>::Output, Self::Exists<P>>>;
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
    ) -> Cert<'l, Self, Self::Imply<P, Self::ForAll<Q>>>;
    fn exists_gen<P: ViewT + ?Sized, Q, S: ExistsProofT<'l, Self, P, Q>>(
        proof: S,
    ) -> Cert<'l, Self, Self::Imply<Self::Exists<P>, Q>>;
}
