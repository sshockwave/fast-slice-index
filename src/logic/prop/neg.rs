use crate::logic::prop::{
    Cert, Deduction, DeductionUpgrade, Imply, Intuitionistic, Negation, PropLogic, reflexive,
    syllogism,
};
use ::core::marker::PhantomData;

pub trait Contraposition<'a>: Imply<'a> + Negation<'a> {
    fn l3<P, Q>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>>;
}

pub trait DoubleNegation<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P>() -> Cert<'a, Self, Self::Imply<Self::Neg<Self::Neg<P>>, P>>;
}

pub trait DoubleNegIntro<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P>() -> Cert<'a, Self, Self::Imply<P, Self::Neg<Self::Neg<P>>>>;
}

/// Peirce's law: ((P → Q) → P) → P
///
/// The characteristic classical axiom: it is equivalent to [`Contraposition`]
/// over the intuitionistic base `L1`/`L2`, so it is derivable here.
pub trait PeirceLaw<'a>: PropLogic<'a> {
    fn peirce<P: Clone + 'a, Q: 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>>;
}

pub struct ProofRing<'a, Prop>(PhantomData<(&'a (), Prop)>);

impl<'a, Prop> PropLogic<'a> for ProofRing<'a, Prop>
where
    Prop: PropLogic<'a>,
{
    fn l1<P: Clone + 'a, Q>() -> Cert<'a, Self, Self::Imply<P, Self::Imply<Q, P>>> {
        Prop::l1().cast()
    }
    fn l2<P: Clone + 'a, Q: 'a, R: 'a>() -> Cert<
        'a,
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        Prop::l2().cast()
    }
}

impl<'a, Prop: Imply<'a>> Imply<'a> for ProofRing<'a, Prop> {
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Cert<'a, Self, Self::Imply<P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        Prop::mp(pq.cast(), p.cast()).cast()
    }
    fn def<P, Q>() -> Cert<'a, Self, Self::Imply<P, Q>>
    where
        P: Into<Q> + Clone + 'a,
        Q: Clone + 'a,
    {
        Prop::def().cast()
    }
}

impl<'a, Prop: Negation<'a>> Negation<'a> for ProofRing<'a, Prop> {
    type Neg<P: 'a> = Prop::Neg<P>;
}

impl<'a, Prop> DoubleNegation<'a> for ProofRing<'a, Prop>
where
    Prop: Contraposition<'a> + PropLogic<'a>,
{
    fn l3<P>() -> Cert<'a, Self, Self::Imply<Self::Neg<Self::Neg<P>>, P>>
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
            .cast()
    }
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> DoubleNegIntro<'a> for ProofRing<'a, Prop> {
    fn l3<P>() -> Cert<'a, Self, Self::Imply<P, Self::Neg<Self::Neg<P>>>> {
        Prop::l3()
            .apply(<ProofRing<Prop> as DoubleNegation<'_>>::l3().cast())
            .cast()
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P, Q>() -> Cert<'a, Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> ExFalsoQuodlibet<'a> for ProofRing<'a, Prop> {
    fn l3<P, Q>() -> Cert<'a, Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>> {
        syllogism::<_, _, _, Prop>()
            .apply(Prop::l1())
            .apply(Prop::l3())
            .cast()
    }
}

pub fn simplification<'a, P, Q, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Neg<Prop::Imply<P, Q>>, P>> {
    syllogism::<_, _, _, Prop>()
        .apply(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3().cast())
        .apply(<ProofRing<Prop> as DoubleNegIntro<'_>>::l3().cast())
        .pipe(Prop::l3())
}

/// Transposition: (P → Q) → (¬Q → ¬P)
///
/// The converse of [`Contraposition`], obtained by wrapping both sides in a
/// double negation so that [`Contraposition::l3`] applies.
pub fn transposition<'a, P: Clone + 'a, Q: Clone + 'a, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Neg<Q>, Prop::Neg<P>>>> {
    // (P → Q) → (¬¬P → Q)
    let pre = Prop::mp(
        syllogism::<_, _, _, Prop>(),
        <ProofRing<Prop> as DoubleNegation<'_>>::l3::<P>().cast(),
    );
    // (¬¬P → Q) → (¬¬P → ¬¬Q)
    let post = Prop::mp(
        Prop::l2(),
        Prop::mp(
            Prop::l1(),
            <ProofRing<Prop> as DoubleNegIntro<'_>>::l3::<Q>().cast(),
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
-> Cert<'a, Prop, Prop::Imply<Prop::Imply<Prop::Neg<P>, P>, P>> {
    // ¬P → (P → ¬(P → P)), distributed over the assumption ¬P → P,
    // yields ¬P → ¬(P → P).
    let absurd = Prop::l2().apply(
        <ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3::<P, Prop::Neg<Prop::Imply<P, P>>>().cast(),
    );
    // Transposing gives (P → P) → P, and P → P is a theorem.
    Prop::l2()
        .apply(syllogism().apply(absurd).apply(Prop::l3()))
        .apply(Prop::l1().apply(reflexive()))
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> PeirceLaw<'a> for ProofRing<'a, Prop> {
    fn peirce<P: Clone + 'a, Q: 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>> {
        // ¬P → (P → Q) composed with the antecedent (P → Q) → P gives ¬P → P.
        let self_deny = syllogism().apply(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3().cast());
        syllogism::<_, _, _, Prop>()
            .apply(self_deny)
            .apply(consequentia_mirabilis())
            .cast()
    }
}

impl<'l, Logic: PeirceLaw<'l> + Negation<'l>> Contraposition<'l> for ProofRing<'l, Logic> {
    fn l3<P, Q>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        todo!()
    }
}

use self::sealed_connectives::Or;
mod sealed_connectives {
    use super::{Cert, Negation, PropLogic};
    pub struct Or<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + Negation<'a>>(
        pub(super) Cert<'a, Prop, Prop::Imply<Prop::Neg<P>, Q>>,
    );
}

impl<'a, P: 'a, Q: 'a, Prop: PropLogic<'a> + Negation<'a>> Clone for Or<'a, P, Q, Prop> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::And<'l> for ProofRing<'l, Logic> {
    type And<P: 'l, Q: 'l> = Logic::Neg<Self::Imply<Q, Logic::Neg<P>>>;
    fn and_intro<P: Clone, Q: Clone>()
    -> Cert<'l, Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>> {
        pub fn intro<'l, P, Q, Prop: Contraposition<'l> + PropLogic<'l>>(
            p: Cert<'l, Prop, P>,
            q: Cert<'l, Prop, Q>,
        ) -> Cert<'l, Prop, Prop::Neg<Prop::Imply<Q, Prop::Neg<P>>>>
        where
            P: Clone + 'l,
            Q: Clone + 'l,
        {
            // From Q, derive (Q → ¬P) → ¬P by modus ponens on the assumption.
            Prop::l2()
                .apply(reflexive())
                .apply(Prop::l1().apply(q))
                // Transposing gives ¬¬P → ¬(Q → ¬P), and ¬¬P follows from P.
                .pipe(transposition::<_, _, Prop>())
                .apply(
                    <ProofRing<Prop> as DoubleNegIntro<'_>>::l3()
                        .apply(p.cast())
                        .cast(),
                )
        }
        intro(
            Deduction::<_, Logic>::assume().upgrade(),
            Deduction::assume(),
        )
        .cast()
    }
    /// Left elimination: P ∧ Q → P
    fn and_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, P>> {
        // ¬P → (Q → ¬P) transposes to ¬(Q → ¬P) → ¬¬P, then double negation.
        transposition()
            .apply(Logic::l1::<Logic::Neg<P>, Q>())
            .cast()
            .upgrade()
            .apply(Deduction::<_, Logic>::assume())
            .pipe(
                <ProofRing<Logic> as DoubleNegation<'_>>::l3()
                    .cast()
                    .upgrade(),
            )
            .cast()
    }
    /// Right elimination: P ∧ Q → Q
    fn and_right<P, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>> {
        simplification()
            .upgrade()
            .apply(Deduction::<_, Logic>::assume())
            .cast()
    }
}

impl<'a, P: 'a, Q: 'a, Prop: Contraposition<'a> + PropLogic<'a>> Or<'a, P, Q, Prop> {
    pub fn intro_left(p: Cert<'a, Prop, P>) -> Self
    where
        P: Clone,
    {
        Self(
            <ProofRing<Prop> as DoubleNegIntro<'_>>::l3()
                .cast()
                .apply(p)
                .pipe(Prop::l1())
                .pipe(Prop::l3())
                .cast(),
        )
    }
    pub fn intro_right(q: Cert<'a, Prop, Q>) -> Self
    where
        Q: Clone,
    {
        Self(Prop::l1().apply(q))
    }
    pub fn p_to_q(self) -> Cert<'a, Prop, Prop::Imply<Prop::Neg<P>, Q>> {
        self.0
    }
    pub fn q_to_p(self) -> Cert<'a, Prop, Prop::Imply<Prop::Neg<Q>, P>>
    where
        P: Clone,
    {
        <ProofRing<Prop> as DoubleNegIntro<'_>>::l3()
            .cast()
            .pipe(Prop::l1())
            .pipe(Prop::l2())
            .apply(self.0)
            .pipe(Prop::l3())
    }
}

impl<'l, A: Clone + 'l, Logic: Contraposition<'l> + PropLogic<'l>> Contraposition<'l>
    for Deduction<A, Logic>
{
    fn l3<P, Q>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        Self::upgrade(Logic::l3())
    }
}
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::Or<'l> for ProofRing<'l, Logic> {
    type Or<P: 'l, Q: 'l> = Or<'l, P, Q, Logic>;
    fn or_left<P, Q>() -> Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>> {
        todo!()
    }
    fn or_right<P, Q>() -> Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>> {
        todo!()
    }
    fn or_elim<P, Q, R>() -> Cert<
        'l,
        Self,
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
    fn explosion<P>() -> Cert<'l, Self, Self::Imply<Self::False, P>> {
        todo!()
    }
    fn neg_def<P>()
    -> Cert<'l, Self, super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        todo!()
    }
}
