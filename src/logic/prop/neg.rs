use crate::logic::prop::{
    And, Cert, Deduction, DeductionUpgrade, Imply, Intuitionistic, Negation, PropLogic,
    il::Reductio, reflexive, syllogism,
};
use ::core::marker::PhantomData;

pub trait Contraposition<'a>: Imply<'a> + Negation<'a> {
    fn l3<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>>;
}

pub trait DoubleNegation<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<Self::Neg<Self::Neg<P>>, P>>;
}

pub trait DoubleNegIntro<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<P, Self::Neg<Self::Neg<P>>>>;
}

/// Peirce's law: ((P → Q) → P) → P
///
/// The characteristic classical axiom: it is equivalent to [`Contraposition`]
/// over the intuitionistic base `L1`/`L2`, so it is derivable here.
pub trait PeirceLaw<'a>: PropLogic<'a> {
    fn peirce<P: Clone + 'a, Q: Clone + 'a>()
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
    fn l3<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<Self::Neg<Self::Neg<P>>, P>> {
        // https://math.stackexchange.com/questions/4634566/prove-that-contrapositive-rule-is-equivalent-to-the-rule-of-double-negation
        syllogism::<_, _, _, Prop>()
            .mp(Prop::l1())
            .mp(Prop::l3())
            .pipe(syllogism::<_, _, _, Prop>())
            .mp(Prop::l3())
            .pipe(Prop::l2())
            .mp(reflexive::<_, Prop>())
            .cast()
    }
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> DoubleNegIntro<'a> for ProofRing<'a, Prop> {
    fn l3<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<P, Self::Neg<Self::Neg<P>>>> {
        Prop::l3()
            .mp(<ProofRing<Prop> as DoubleNegation<'_>>::l3().cast())
            .cast()
    }
}

/// [`Contraposition`] proves [`Reductio`], so requiring it costs nothing for
/// logics that already have the classical axiom: transposing `P → ¬Q` gives
/// `¬¬Q → ¬P`, and `Q → ¬¬Q` feeds it.
impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> Reductio<'a> for ProofRing<'a, Prop> {
    fn l3<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>> {
        // (¬¬Q → ¬P) → (Q → ¬P)
        let pre = Prop::mp(
            syllogism::<_, _, _, Prop>(),
            <ProofRing<Prop> as DoubleNegIntro<'_>>::l3::<Q>().cast(),
        );
        syllogism::<_, _, _, Prop>()
            .mp(transposition::<P, Prop::Neg<Q>, Prop>())
            .mp(pre)
            .cast()
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> + Negation<'a> {
    fn l3<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> ExFalsoQuodlibet<'a> for ProofRing<'a, Prop> {
    fn l3<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>> {
        syllogism::<_, _, _, Prop>()
            .mp(Prop::l1())
            .mp(Prop::l3())
            .cast()
    }
}

pub fn simplification<'a, P, Q, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Neg<Prop::Imply<P, Q>>, P>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
{
    syllogism::<_, _, _, Prop>()
        .mp(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3().cast())
        .mp(<ProofRing<Prop> as DoubleNegIntro<'_>>::l3().cast())
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
    let absurd = Prop::l2().mp(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3::<
        P,
        Prop::Neg<Prop::Imply<P, P>>,
    >()
    .cast());
    // Transposing gives (P → P) → P, and P → P is a theorem.
    Prop::l2()
        .mp(syllogism().mp(absurd).mp(Prop::l3()))
        .mp(Prop::l1().mp(reflexive()))
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> PeirceLaw<'a> for ProofRing<'a, Prop> {
    fn peirce<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>> {
        // ¬P → (P → Q) composed with the antecedent (P → Q) → P gives ¬P → P.
        let self_deny = syllogism().mp(<ProofRing<Prop> as ExFalsoQuodlibet<'_>>::l3().cast());
        syllogism::<_, _, _, Prop>()
            .mp(self_deny)
            .mp(consequentia_mirabilis())
            .cast()
    }
}

impl<'l, Logic: DoubleNegation<'l> + Reductio<'l>> Contraposition<'l> for ProofRing<'l, Logic> {
    fn l3<P: Clone + 'l, Q: Clone + 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        // Reductio at (¬P, Q) introduces the outer negation:
        // (¬P → ¬Q) → (Q → ¬¬P)
        let intro = <Logic as Reductio<'_>>::l3::<Logic::Neg<P>, Q>();
        // Double negation under `Q →`, by L2 on Q → (¬¬P → P):
        // (Q → ¬¬P) → (Q → P)
        let elim = Logic::l2().mp(Logic::l1().mp(<Logic as DoubleNegation<'_>>::l3::<P>()));
        // Chaining the two gives (¬P → ¬Q) → (Q → P).
        syllogism::<_, _, _, Logic>().mp(intro).mp(elim).cast()
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
                .mp(reflexive())
                .mp(Prop::l1().mp(q))
                // Transposing gives ¬¬P → ¬(Q → ¬P), and ¬¬P follows from P.
                .pipe(transposition::<_, _, Prop>())
                .mp(<ProofRing<Prop> as DoubleNegIntro<'_>>::l3()
                    .mp(p.cast())
                    .cast())
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
            .mp(Logic::l1::<Logic::Neg<P>, Q>())
            .cast()
            .upgrade()
            .mp(Deduction::<_, Logic>::assume())
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
            .mp(Deduction::<_, Logic>::assume())
            .cast()
    }
}

impl<'l, A: Clone + 'l, Logic: Contraposition<'l> + PropLogic<'l>> Contraposition<'l>
    for Deduction<A, Logic>
{
    fn l3<P: Clone + 'l, Q: Clone + 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        Self::upgrade(Logic::l3())
    }
}
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::Or<'l> for ProofRing<'l, Logic> {
    type Or<P: 'l, Q: 'l> = Logic::Imply<Logic::Neg<P>, Q>;
    fn or_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>> {
        <ProofRing<Logic> as DoubleNegIntro<'_>>::l3()
            .cast()
            .upgrade()
            .mp(Deduction::assume())
            .pipe(Logic::l1().upgrade())
            .pipe(Logic::l3().upgrade())
            .cast()
    }
    fn or_right<P, Q: Clone>() -> Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>> {
        Logic::l1().upgrade().mp(Deduction::assume()).cast()
    }
    fn or_elim<P: Clone, Q: Clone, R: Clone>() -> Cert<
        'l,
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        syllogism()
            .mp(Deduction::assume()) // ~P -> Q
            .mp(Deduction::assume().upgrade()) // Q -> R
            .pipe(
                // (~P -> R) -> (~R -> ~~P)
                transposition::<_, _, Logic>()
                    .cast()
                    .upgrade()
                    .upgrade()
                    .upgrade(),
            )
            .upgrade()
            .mp(Deduction::assume()) // Assume ~R, Got ~~P
            .pipe(
                // ~~P -> P
                <Self as DoubleNegation<'_>>::l3()
                    .upgrade()
                    .upgrade()
                    .upgrade()
                    .upgrade(),
            )
            .pipe(Deduction::assume().upgrade().upgrade().upgrade()) // P -> R
            .qed() // ~R -> R
            .pipe(
                consequentia_mirabilis::<_, Logic>()
                    .cast()
                    .upgrade()
                    .upgrade()
                    .upgrade(),
            )
            .cast()
    }
}
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> Intuitionistic<'l> for ProofRing<'l, Logic> {
    type False = Self::And<(), Self::Neg<()>>;
    fn explosion<P: Clone>() -> Cert<'l, Self, Self::Imply<Self::False, P>> {
        let absurd = Deduction::assume();
        <Self as ExFalsoQuodlibet<'l>>::l3()
            .upgrade()
            .mp(absurd.clone().pipe(Self::and_right().upgrade()))
            .mp(absurd.pipe(Self::and_left().upgrade()))
            .qed()
    }
    fn neg_def<P: Clone>()
    -> Cert<'l, Self, super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        let l2r: Cert<Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Self::False>>> =
            <Self as ExFalsoQuodlibet<'_>>::l3();
        let neg_false: Cert<Self, Self::Neg<Self::False>> =
            reflexive().pipe(<Self as DoubleNegIntro<'_>>::l3());
        let r2l = Self::l1()
            .mp(<Self as DoubleNegIntro<'_>>::l3())
            .pipe(Self::l2())
            .pipe(syllogism())
            .mp(
                syllogism()
                    .mp(<Self as DoubleNegation<'_>>::l3()) // ~~p -> p
                    .mp(Self::and_intro().mp(neg_false)) // p -> (~False & p) = ~(p -> ~~False)
                    .pipe(Logic::l3().cast()), // (p -> ~~False) -> ~p
            );
        Self::and_intro().mp(l2r).mp(r2l)
    }
}

/// Static witnesses: these compile only if the derivations above really apply
/// at the stated bounds. `cargo check` is the proof checker.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
const _: () = {
    const fn need_contraposition<'l, C: Contraposition<'l>>() {}
    const fn need_reductio<'l, R: Reductio<'l>>() {}

    /// `DoubleNegation + Reductio` alone yields `Contraposition`: the bound
    /// mentions neither the classical axiom nor any concrete logic, so nothing
    /// smuggles it in.
    const fn cp_from_dne_and_reductio<'l, L: DoubleNegation<'l> + Reductio<'l>>() {
        need_contraposition::<ProofRing<'l, L>>();
    }

    /// `Reductio` itself needs no classical axiom -- it holds for `¬P := P → ⊥`
    /// over plain L1/L2, so it is strictly weaker than `Contraposition`.
    const fn reductio_is_intuitionistic<'l, L: PropLogic<'l>>() {
        need_reductio::<crate::logic::prop::il::IntuitionisticImpl<'l, L>>();
    }

    // No in-crate instantiation is possible: no concrete logic asserts the
    // classical axiom yet. The generic bodies are themselves the proof -- they
    // typecheck exactly when the impls apply at the stated bounds.
    let _ = reductio_is_intuitionistic::<crate::logic::prop::PropLogicThm> as fn();
};
