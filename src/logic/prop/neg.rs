use crate::logic::prop::{
    And, Cert, Deduction, DeductionUpgrade, Imply, Intuitionistic, Negation, PropLogic, Reductio,
    reflexive, syllogism,
};
use ::core::marker::PhantomData;

pub trait Contraposition<'a>: Imply<'a> + Negation<'a> {
    fn l3<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>>;
}

pub trait DoubleNegElim<'a>: PropLogic<'a> + Negation<'a> {
    fn double_neg_elim<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<Self::Neg<Self::Neg<P>>, P>>;
}

pub trait DoubleNegIntro<'a>: PropLogic<'a> + Negation<'a> {
    fn double_neg_intro<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<P, Self::Neg<Self::Neg<P>>>>;
}

/// Peirce's law: ((P → Q) → P) → P
///
/// The characteristic classical axiom: it is equivalent to [`Contraposition`]
/// over the intuitionistic base `L1`/`L2`, so it is derivable here.
pub trait PeirceLaw<'a>: PropLogic<'a> {
    fn peirce<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>>;
}

pub struct ProofRing<Prop>(PhantomData<Prop>);

impl<'a, Prop> PropLogic<'a> for ProofRing<Prop>
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

impl<'a, Prop: Imply<'a>> Imply<'a> for ProofRing<Prop> {
    type Imply<P: 'a, Q: 'a> = Prop::Imply<P, Q>;
    type Cert<P: Clone + 'a> = Prop::Cert<P>;
    fn mp<P: Clone, Q: Clone + 'a>(
        pq: Cert<'a, Self, Self::Imply<P, Q>>,
        p: Cert<'a, Self, P>,
    ) -> Cert<'a, Self, Q> {
        Prop::mp(pq.cast(), p.cast()).cast()
    }
}

impl<'a, Prop: Negation<'a>> Negation<'a> for ProofRing<Prop> {
    type Neg<P: 'a> = Prop::Neg<P>;
}

impl<'a, Prop> DoubleNegElim<'a> for ProofRing<Prop>
where
    Prop: Contraposition<'a> + PropLogic<'a>,
{
    fn double_neg_elim<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<Self::Neg<Self::Neg<P>>, P>> {
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

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> DoubleNegIntro<'a> for ProofRing<Prop> {
    fn double_neg_intro<P: Clone + 'a>() -> Cert<'a, Self, Self::Imply<P, Self::Neg<Self::Neg<P>>>>
    {
        Prop::l3().cast().mp(Self::double_neg_elim())
    }
}

/// [`Contraposition`] proves [`Reductio`], so requiring it costs nothing for
/// logics that already have the classical axiom: transposing `P → ¬Q` gives
/// `¬¬Q → ¬P`, and `Q → ¬¬Q` feeds it.
impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> Reductio<'a> for ProofRing<Prop> {
    fn reductio<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<P, Self::Neg<Q>>, Self::Imply<Q, Self::Neg<P>>>> {
        // (¬¬Q → ¬P) → (Q → ¬P)
        let pre = Prop::mp(
            syllogism::<_, _, _, Prop>(),
            Self::double_neg_intro::<Q>().cast(),
        );
        syllogism::<_, _, _, Prop>()
            .mp(transposition::<P, Prop::Neg<Q>, Prop>())
            .mp(pre)
            .cast()
    }
}

pub trait ExFalsoQuodlibet<'a>: PropLogic<'a> + Negation<'a> {
    fn ex_falso_quodlibet<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>>;
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> ExFalsoQuodlibet<'a> for ProofRing<Prop> {
    fn ex_falso_quodlibet<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Q>>> {
        syllogism().mp(Prop::l1()).mp(Prop::l3()).cast()
    }
}

pub fn simplification<'a, P, Q, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Neg<Prop::Imply<P, Q>>, P>>
where
    P: Clone + 'a,
    Q: Clone + 'a,
{
    syllogism::<_, _, _, Prop>()
        .mp(ProofRing::<Prop>::ex_falso_quodlibet().cast())
        .mp(ProofRing::<Prop>::double_neg_intro().cast())
        .pipe(Prop::l3())
}

/// Transposition: (P → Q) → (¬Q → ¬P)
///
/// The converse of [`Contraposition`], obtained by wrapping both sides in a
/// double negation so that [`Contraposition::l3`] applies.
pub fn transposition<'a, P: Clone + 'a, Q: Clone + 'a, Prop: Contraposition<'a> + PropLogic<'a>>()
-> Cert<'a, Prop, Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Neg<Q>, Prop::Neg<P>>>> {
    // (P → Q) → (¬¬P → Q)
    let pre = syllogism().mp(ProofRing::<Prop>::double_neg_elim().cast());
    // (¬¬P → Q) → (¬¬P → ¬¬Q)
    let post = ProofRing::<Prop>::double_neg_intro()
        .cast()
        .pipe(Prop::l1())
        .pipe(Prop::l2());
    // (P → Q) → (¬¬P → ¬¬Q)
    syllogism()
        .mp(pre)
        .mp(post)
        .pipe(syllogism())
        .mp(Prop::l3())
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
    let absurd = Prop::l2().mp(
        <ProofRing<Prop> as ExFalsoQuodlibet<'_>>::ex_falso_quodlibet::<
            P,
            Prop::Neg<Prop::Imply<P, P>>,
        >()
        .cast(),
    );
    // Transposing gives (P → P) → P, and P → P is a theorem.
    Prop::l2()
        .mp(syllogism().mp(absurd).mp(Prop::l3()))
        .mp(Prop::l1().mp(reflexive()))
}

impl<'a, Prop: Contraposition<'a> + PropLogic<'a>> PeirceLaw<'a> for ProofRing<Prop> {
    fn peirce<P: Clone + 'a, Q: Clone + 'a>()
    -> Cert<'a, Self, Self::Imply<Self::Imply<Self::Imply<P, Q>, P>, P>> {
        // ¬P → (P → Q) composed with the antecedent (P → Q) → P gives ¬P → P.
        syllogism()
            .mp(<Self as ExFalsoQuodlibet<'_>>::ex_falso_quodlibet())
            .pipe(syllogism())
            .mp(consequentia_mirabilis::<_, Prop>().cast())
    }
}

impl<'l, Logic: DoubleNegElim<'l> + Reductio<'l>> Contraposition<'l> for ProofRing<Logic> {
    fn l3<P: Clone + 'l, Q: Clone + 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        // Reductio at (¬P, Q) introduces the outer negation:
        // (¬P → ¬Q) → (Q → ¬¬P)
        let intro = <Logic as Reductio<'_>>::reductio::<Logic::Neg<P>, Q>();
        // Double negation under `Q →`, by L2 on Q → (¬¬P → P):
        // (Q → ¬¬P) → (Q → P)
        let elim =
            Logic::l2().mp(Logic::l1().mp(<Logic as DoubleNegElim<'_>>::double_neg_elim::<P>()));
        // Chaining the two gives (¬P → ¬Q) → (Q → P).
        syllogism::<_, _, _, Logic>().mp(intro).mp(elim).cast()
    }
}

impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::And<'l> for ProofRing<Logic> {
    type And<P: Clone + 'l, Q: Clone + 'l> = Logic::Neg<Self::Imply<Q, Logic::Neg<P>>>;
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
                .mp(<ProofRing<Prop> as DoubleNegIntro<'_>>::double_neg_intro()
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
            .upgrade()
            .mp(Deduction::<_, Logic>::assume())
            .pipe(Self::double_neg_elim().cast().upgrade())
            .cast()
    }
    /// Right elimination: P ∧ Q → Q
    fn and_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Self::And<P, Q>, Q>> {
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
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> super::Or<'l> for ProofRing<Logic> {
    type Or<P: Clone + 'l, Q: Clone + 'l> = Logic::Imply<Logic::Neg<P>, Q>;
    fn or_left<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<P, Self::Or<P, Q>>> {
        Self::double_neg_intro()
            .cast()
            .upgrade()
            .mp(Deduction::assume())
            .pipe(Logic::l1().upgrade())
            .pipe(Logic::l3().upgrade())
            .cast()
    }
    fn or_right<P: Clone, Q: Clone>() -> Cert<'l, Self, Self::Imply<Q, Self::Or<P, Q>>> {
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
                Self::double_neg_elim()
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
impl<'l, Logic: Contraposition<'l> + PropLogic<'l>> Intuitionistic<'l> for ProofRing<Logic> {
    type False = Self::And<(), Self::Neg<()>>;
    fn explosion<P: Clone>() -> Cert<'l, Self, Self::Imply<Self::False, P>> {
        let absurd = Deduction::assume();
        Self::ex_falso_quodlibet()
            .upgrade()
            .mp(absurd.clone().pipe(Self::and_right().upgrade()))
            .mp(absurd.pipe(Self::and_left().upgrade()))
            .qed()
    }
    fn neg_def<P: Clone>()
    -> Cert<'l, Self, super::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        let l2r: Cert<Self, Self::Imply<Self::Neg<P>, Self::Imply<P, Self::False>>> =
            Self::ex_falso_quodlibet();
        let neg_false: Cert<Self, Self::Neg<Self::False>> =
            reflexive().pipe(Self::double_neg_intro());
        let r2l = Self::l1()
            .mp(Self::double_neg_intro())
            .pipe(Self::l2())
            .pipe(syllogism())
            .mp(
                syllogism()
                    .mp(Self::double_neg_elim()) // ~~p -> p
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

    /// `DoubleNegElim + Reductio` alone yields `Contraposition`: the bound
    /// mentions neither the classical axiom nor any concrete logic, so nothing
    /// smuggles it in.
    const fn cp_from_dne_and_reductio<'l, L: DoubleNegElim<'l> + Reductio<'l>>() {
        need_contraposition::<ProofRing<L>>();
    }

    /// `Reductio` itself needs no classical axiom -- it holds for `¬P := P → ⊥`
    /// over plain L1/L2, so it is strictly weaker than `Contraposition`.
    const fn reductio_is_intuitionistic<'l, L: PropLogic<'l>>() {
        need_reductio::<crate::logic::prop::il::IntuitionisticImpl<L>>();
    }

    // No in-crate instantiation is possible: no concrete logic asserts the
    // classical axiom yet. The generic bodies are themselves the proof -- they
    // typecheck exactly when the impls apply at the stated bounds.
    let _ = reductio_is_intuitionistic::<crate::logic::prop::il::PropLogicThm> as fn();
};
