use crate::logic::prop::{
    Chain, Deduction, Imply, Intuitionistic, Negation, PropLogic, reflexive, syllogism,
};
use ::core::marker::PhantomData;

pub trait Contraposition<'a>: Imply<'a> + Negation<'a> {
    fn l3<P, Q>()
    -> Self::Cert<Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>>;
}

pub trait DoubleNegation<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P>() -> Self::Cert<Self::Imply<Self::Neg<Self::Neg<P>>, P>>;
}

pub trait DoubleNegIntro<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P>() -> Self::Cert<Self::Imply<P, Self::Neg<Self::Neg<P>>>>;
}

/// Peirce's law: ((P → Q) → P) → P
///
/// The characteristic classical axiom: it is equivalent to [`Contraposition`]
/// over the intuitionistic base `L1`/`L2`, so it is derivable here.
pub trait PeirceLaw<'a>: PropLogic<'a> {
    fn peirce<P: Clone + 'a, Q: 'a>()
    -> Self::Cert<Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>>;
}

pub struct ProofRing<'a, Prop>(PhantomData<(&'a (), Prop)>);

impl<'a, Prop> PropLogic<'a> for ProofRing<'a, Prop>
where
    Prop: PropLogic<'a>,
{
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
}

impl<'a, Prop: Imply<'a>> Imply<'a> for ProofRing<'a, Prop> {
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Self::Cert<Self::Imply<P, Q>>,
        p: Self::Cert<P>,
    ) -> Self::Cert<Q> {
        Prop::mp(pq, p)
    }
    fn def<P, Q>() -> Self::Cert<Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a,
    {
        Prop::def()
    }
}

impl<'a, Prop: Negation<'a>> Negation<'a> for ProofRing<'a, Prop> {
    type Neg<P: 'a> = Prop::Neg<P>;
}

impl<'a, Prop> DoubleNegation<'a> for ProofRing<'a, Prop>
where
    Prop: Contraposition<'a> + PropLogic<'a>,
{
    fn l3<P>() -> Self::Cert<Self::Imply<Self::Neg<Self::Neg<P>>, P>>
    where
        P: 'a,
    {
        // https://math.stackexchange.com/questions/4634566/prove-that-contrapositive-rule-is-equivalent-to-the-rule-of-double-negation
        syllogism::<_, _, _, Prop>()
            .apply(Prop::l1())
            .apply(Prop::l3())
            .pipe(syllogism::<_, _, _, Prop>())
            .apply(Prop::l3())
            .pipe(Prop::l2())
            .apply(reflexive::<_, Prop>())
    }
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> DoubleNegIntro<'a> for ProofRing<'a, Prop> {
    fn l3<P>() -> Self::Cert<Self::Imply<P, Self::Neg<Self::Neg<P>>>> {
        Prop::l3().apply(<ProofRing<Prop> as DoubleNegation<'_>>::l3())
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> ExFalsoQuodlibet<'a> for ProofRing<'a, Prop> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>> {
        syllogism::<_, _, _, Prop>()
            .apply(Prop::l1())
            .apply(Prop::l3())
    }
}

pub fn simplification<'a, P, Q, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Neg<Prop::Imply<P, Q>>, P>> {
    syllogism::<_, _, _, Prop>()
        .apply(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3())
        .apply(<ProofRing<Prop> as DoubleNegIntro<'_>>::l3())
        .pipe(Prop::l3())
}

/// Transposition: (P → Q) → (¬Q → ¬P)
///
/// The converse of [`Contraposition`], obtained by wrapping both sides in a
/// double negation so that [`Contraposition::l3`] applies.
pub fn transposition<'a, P: Clone + 'a, Q: Clone + 'a, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Neg<Q>, Prop::Neg<P>>>> {
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

/// Consequentia mirabilis: (¬P → P) → P
///
/// If denying `P` proves `P`, then `P` holds outright. The self-implication
/// `P → P` stands in for "truth": deriving `¬(P → P)` from `¬P` lets
/// [`Contraposition::l3`] transpose it back into `(P → P) → P`.
pub fn consequentia_mirabilis<'a, P: Clone + 'a, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Prop::Cert<Prop::Imply<Prop::Imply<Prop::Neg<P>, P>, P>> {
    // ¬P → (P → ¬(P → P)), distributed over the assumption ¬P → P,
    // yields ¬P → ¬(P → P).
    let absurd = Prop::l2().apply(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3::<
        P,
        Prop::Neg<Prop::Imply<P, P>>,
    >());
    // Transposing gives (P → P) → P, and P → P is a theorem.
    Prop::l2()
        .apply(syllogism::<_, _, _, Prop>().apply(absurd).apply(Prop::l3()))
        .apply(Prop::l1().apply(reflexive::<_, Prop>()))
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> PeirceLaw<'a> for ProofRing<'a, Prop> {
    fn peirce<P: Clone + 'a, Q: 'a>()
    -> Self::Cert<Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>> {
        // ¬P → (P → Q) composed with the antecedent (P → Q) → P gives ¬P → P.
        let self_deny = syllogism::<_, _, _, Prop>()
            .apply(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3::<P, Q>());
        syllogism::<_, _, _, Prop>()
            .apply(self_deny)
            .apply(consequentia_mirabilis::<P, Prop>())
    }
}

impl<'l, Logic: PeirceLaw<'l> + Negation<'l>> Contraposition<'l> for ProofRing<'l, Logic> {
    fn l3<P, Q>()
    -> Self::Cert<Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        todo!()
    }
}

use self::sealed_connectives::Or;
mod sealed_connectives {
    use super::{Negation, PropLogic};
    pub struct Or<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + Negation<'a>>(
        pub(super) Prop::Cert<Prop::Imply<Prop::Neg<P>, Q>>,
    );
}

impl<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + Negation<'a>> Clone for Or<'a, P, Q, Prop> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::And<'l> for ProofRing<'l, Logic> {
    type And<P: 'l, Q: 'l> = Logic::Neg<Self::Imply<Q, Logic::Neg<P>>>;
    fn and_intro<P: Clone, Q: Clone>() -> Self::Cert<Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>>
    {
        pub fn intro<'l, P, Q, Prop: Contraposition<'l> + PropLogic<'l>>(
            p: Prop::Cert<P>,
            q: Prop::Cert<Q>,
        ) -> Prop::Cert<Prop::Neg<Prop::Imply<Q, Prop::Neg<P>>>>
        where
            P: Clone + 'l,
            Q: Clone + 'l,
        {
            // From Q, derive (Q → ¬P) → ¬P by modus ponens on the assumption.
            Prop::l2()
                .apply(reflexive::<_, Prop>())
                .apply(Prop::l1().apply(q))
                // Transposing gives ¬¬P → ¬(Q → ¬P), and ¬¬P follows from P.
                .pipe(transposition::<_, _, Prop>())
                .apply(<ProofRing<Prop> as DoubleNegIntro<'_>>::l3().apply(p))
        }
        Deduction::<_, Logic>::scope(|p| {
            Deduction::<_, Deduction<_, _>>::scope(|q| {
                intro::<_, _, Deduction<_, _>>(Deduction::upgrade(p), q)
            })
        })
    }
    /// Left elimination: P ∧ Q → P
    fn and_left<P: Clone, Q: Clone>() -> Self::Cert<Self::Imply<Self::And<P, Q>, P>> {
        // ¬P → (Q → ¬P) transposes to ¬(Q → ¬P) → ¬¬P, then double negation.
        Deduction::mp(
            Deduction::upgrade(<ProofRing<Logic> as DoubleNegation<'_>>::l3()),
            Deduction::mp(
                Deduction::upgrade(
                    transposition::<_, _, Logic>().apply(Logic::l1::<Logic::Neg<P>, Q>()),
                ),
                Deduction::<_, Logic>::assume(),
            ),
        )
        .finish()
    }
    /// Right elimination: P ∧ Q → Q
    fn and_right<P, Q: Clone>() -> Self::Cert<Self::Imply<Self::And<P, Q>, Q>> {
        Deduction::mp(
            Deduction::upgrade(simplification::<_, _, Logic>()),
            Deduction::<_, Logic>::assume(),
        )
        .finish()
    }
}

impl<'a, P: 'a, Q: 'a, Prop: Contraposition<'a> + PropLogic<'a>> Or<'a, P, Q, Prop> {
    pub fn intro_left(p: Prop::Cert<P>) -> Self
    where
        P: Clone,
    {
        Self(
            <ProofRing<Prop> as DoubleNegIntro<'_>>::l3()
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
            .apply(<ProofRing<Prop> as DoubleNegIntro<'_>>::l3())
            .pipe(Prop::l2())
            .apply(self.0)
            .pipe(Prop::l3())
    }
}

impl<'l, A: Clone + 'l, Logic: Contraposition<'l> + PropLogic<'l>> Contraposition<'l>
    for Deduction<A, Logic>
{
    fn l3<P, Q>()
    -> Self::Cert<Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        Self::upgrade(Logic::l3())
    }
}
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::Or<'l> for ProofRing<'l, Logic> {
    type Or<P: 'l, Q: 'l> = Or<'l, P, Q, Logic>;
    fn or_left<P, Q>() -> Self::Cert<Self::Imply<P, Self::Or<P, Q>>> {
        todo!()
    }
    fn or_right<P, Q>() -> Self::Cert<Self::Imply<Q, Self::Or<P, Q>>> {
        todo!()
    }
    fn or_elim<P, Q, R>() -> Self::Cert<
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        todo!()
    }
}
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> Intuitionistic<'l> for ProofRing<'l, Logic> {
    type False = Self::And<(), Self::Neg<()>>;
    fn explosion<P>() -> Self::Cert<Self::Imply<Self::False, P>> {
        todo!()
    }
    fn neg_def<P>() -> Self::Cert<super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        todo!()
    }
}
