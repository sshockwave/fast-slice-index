pub mod il;
pub mod neg;
mod rust;
mod thm;

pub use self::thm::*;

pub trait View<'x> {
    type Output;
}

pub trait PropLogic: Imply {
    /// Axiom L1: P → (Q → P)
    /// If P is true, then Q implies P
    fn l1<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, P>>>;

    /// Axiom L2: (P → (Q → R)) → ((P → Q) → (P → R))
    /// Distribution of implication
    fn l2<P, Q, R>() -> Cert<
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
    pub struct Cert<Logic: Imply, P>(Logic::Cert<P>);
    impl<Logic: Imply, P> Clone for Cert<Logic, P> {
        fn clone(&self) -> Self {
            Cert(self.0.clone())
        }
    }
    impl<Logic: Imply, P> Cert<Logic, P> {
        pub fn new(cert: Logic::Cert<P>) -> Self {
            Cert(cert)
        }
        pub fn into_inner(self) -> Logic::Cert<P> {
            self.0
        }
    }
}

/// The most basic logic trait: implication.
///
/// The most fundamental reason to have a lifetime in the trait
/// is to allow using `dyn` in constructive proofs with Rust instances.
/// Enums cannot be used instead of `dyn` until [#2999] is resolved.
/// `dyn` require an explicit lifetime lower bound that the members of the object must satisfy,
/// while from the object's perspective, it's the upper bound of the object's lifetime.
/// We cannot use `'static` for this lower bound
/// because that would require the object to contain only `'static` lifetimes.
/// We want to use lifetimes for proofs because lifetimes are easier to express HRTB than types.
///
/// [#2999]: https://github.com/rust-lang/rfcs/issues/2999
pub trait Imply: Sized {
    /// Implication: P implies Q
    type Imply<P, Q>;
    type Cert<P>: Clone;

    /// Modus Ponens: Given (P → Q) and P, derive Q
    /// This is the only inference rule - all others are axioms
    fn mp<P, Q>(pq: Cert<Self, Self::Imply<P, Q>>, p: Cert<Self, P>) -> Cert<Self, Q>;
}

pub trait Negation {
    type Neg<P>;
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
pub trait Reductio: PropLogic + Negation {
    fn reductio<P, Q>()
    -> Cert<Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>>;
}

pub trait And: PropLogic {
    type And<P, Q>;
    fn and_left<P, Q>() -> Cert<Self, Self::Imply<Self::And<P, Q>, P>>;
    fn and_right<P, Q>() -> Cert<Self, Self::Imply<Self::And<P, Q>, Q>>;
    fn and_intro<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>>;
}

pub type Iff<L, P, Q> = <L as And>::And<<L as Imply>::Imply<P, Q>, <L as Imply>::Imply<Q, P>>;

pub trait Or: PropLogic {
    type Or<P, Q>;
    fn or_left<P, Q>() -> Cert<Self, Self::Imply<P, Self::Or<P, Q>>>;
    fn or_right<P, Q>() -> Cert<Self, Self::Imply<Q, Self::Or<P, Q>>>;
    fn or_elim<P, Q, R>() -> Cert<
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    >;
}

pub trait Intuitionistic: PropLogic + And + Or + Negation {
    type False;
    fn explosion<P>() -> Cert<Self, Self::Imply<Self::False, P>>;
    fn neg_def<P>() -> Cert<Self, Iff<Self, Self::Neg<P>, Self::Imply<P, Self::False>>>;
}

pub trait ForAllProof<Logic: Imply, P, Q: for<'x> View<'x> + ?Sized>: Clone {
    fn prove<'x>(self) -> Cert<Logic, Logic::Imply<P, <Q as View<'x>>::Output>>;
}
pub trait ExistsProof<Logic: Imply, P: for<'x> View<'x> + ?Sized, Q>: Clone {
    fn prove<'x>(self) -> Cert<Logic, Logic::Imply<<P as View<'x>>::Output, Q>>;
}

pub trait FirstOrder: Imply {
    type ForAll<P: for<'x> View<'x> + ?Sized>;
    type Exists<P: for<'x> View<'x> + ?Sized>;
    fn forall_gen<P, Q: for<'x> View<'x> + ?Sized, S: ForAllProof<Self, P, Q>>(
        proof: S,
    ) -> Cert<Self, Self::Imply<P, Self::ForAll<Q>>>;
    fn exists_gen<P: for<'x> View<'x> + ?Sized, Q, S: ExistsProof<Self, P, Q>>(
        proof: S,
    ) -> Cert<Self, Self::Imply<Self::Exists<P>, Q>>;
    fn forall_elim<'t, P: for<'x> View<'x> + ?Sized>()
    -> Cert<Self, Self::Imply<Self::ForAll<P>, <P as View<'t>>::Output>>;
    fn exists_elim<'t, P: for<'x> View<'x> + ?Sized, Q>()
    -> Cert<Self, Self::Imply<<P as View<'t>>::Output, Self::Exists<P>>>;
}

pub trait ViewT {
    type Output<T>;
}

pub trait ForAllProofT<Logic: Imply, P, Q: ViewT + ?Sized> {
    fn prove<T>(self) -> Logic::Imply<P, Q::Output<T>>;
}
pub trait ExistsProofT<Logic: Imply, P: ViewT + ?Sized, Q> {
    fn prove<T>(self) -> Logic::Imply<P::Output<T>, Q>;
}

pub trait FirstOrderT: Imply {
    type ForAll<P: ViewT + ?Sized>;
    type Exists<P: ViewT + ?Sized>;
    fn forall_gen<P, Q: ViewT + ?Sized, S: ForAllProofT<Self, P, Q>>(
        proof: S,
    ) -> Cert<Self, Self::Imply<P, Self::ForAll<Q>>>;
    fn exists_gen<P: ViewT + ?Sized, Q, S: ExistsProofT<Self, P, Q>>(
        proof: S,
    ) -> Cert<Self, Self::Imply<Self::Exists<P>, Q>>;
}
