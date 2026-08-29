use crate::logic::prop::{Chain, PropLogic, reflexive, syllogism};
use ::core::marker::PhantomData;

pub trait Negation<'l> {
    type Neg<P: 'l>: Clone + 'l;
}

pub trait Contraposition<'a>: PropLogic<'a> + Negation<'a> {
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

impl<'a, Prop: Negation<'a>> Negation<'a> for ProofRing<'a, Prop> {
    type Neg<P: 'a> = Prop::Neg<P>;
}

impl<'a, Prop> DoubleNegation<'a> for ProofRing<'a, Prop>
where
    Prop: Contraposition<'a>,
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

impl<'a, Prop: Contraposition<'a>> DoubleNegIntro<'a> for ProofRing<'a, Prop> {
    fn l3<P>() -> Self::Cert<Self::Imply<P, Self::Neg<Self::Neg<P>>>> {
        Prop::l3().apply(<ProofRing<Prop> as DoubleNegation<'_>>::l3())
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a>> ExFalsoQuodlibet<'a> for ProofRing<'a, Prop> {
    fn l3<P, Q>() -> Self::Cert<Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>> {
        syllogism::<_, _, _, Prop>()
            .apply(Prop::l1())
            .apply(Prop::l3())
    }
}

pub fn simplification<'a, P, Q, Prop: Contraposition<'a>>()
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
pub fn transposition<'a, P: Clone + 'a, Q: Clone + 'a, Prop: Contraposition<'a>>()
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
pub fn consequentia_mirabilis<'a, P: Clone + 'a, Prop: Contraposition<'a>>()
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

impl<'a, Prop: Contraposition<'a>> PeirceLaw<'a> for ProofRing<'a, Prop> {
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
