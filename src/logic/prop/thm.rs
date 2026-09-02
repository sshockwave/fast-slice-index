use super::{
    And, Cert, ExistsProof, FirstOrder, ForAllProof, Iff, Imply, Negation, Or, PropLogic, View,
};
use ::core::marker::PhantomData;

impl<PQ, Prop: Imply + ?Sized> Cert<Prop, PQ> {
    pub fn mp<P, Q>(self, p: Cert<Prop, P>) -> Cert<Prop, Q>
    where
        Self: Into<Cert<Prop, Prop::Imply<P, Q>>>,
    {
        Prop::mp(self.into(), p)
    }
    pub fn pipe<Q>(self, pq: Cert<Prop, Prop::Imply<PQ, Q>>) -> Cert<Prop, Q> {
        pq.mp(self)
    }
    pub fn cast<Logic, R>(self) -> Cert<Logic, R>
    where
        Logic: Imply<Cert<R> = Prop::Cert<PQ>>,
    {
        Cert::new(self.into_inner())
    }
}

pub fn reflexive<P, Prop: PropLogic>() -> Cert<Prop, Prop::Imply<P, P>> {
    Prop::l2().mp(Prop::l1()).mp(Prop::l1::<_, P>())
}

mod sealed_deduction {
    use super::{Cert, Imply, PropLogic, reflexive};
    use ::core::marker::PhantomData;

    /// Deduction theorem: If we can derive Q from P, then we can derive P → Q.
    pub struct Deduction<A, Prop>(PhantomData<(A, Prop)>);

    impl<A, Prop: PropLogic> Deduction<A, Prop> {
        pub fn assume() -> Cert<Self, A> {
            reflexive::<_, Prop>().cast()
        }
        pub fn upgrade<P>(value: Cert<Prop, P>) -> Cert<Self, P> {
            Prop::l1().mp(value).cast()
        }
        pub fn scope<R>(
            f: impl FnOnce(Cert<Self, A>) -> Cert<Self, R>,
        ) -> Cert<Prop, Prop::Imply<A, R>> {
            f(Self::assume()).cast()
        }
    }

    impl<A, Prop: PropLogic> Imply for Deduction<A, Prop> {
        type Imply<P, Q> = Prop::Imply<P, Q>;
        type Cert<P> = Prop::Cert<Prop::Imply<A, P>>;
        fn mp<P, Q>(pq: Cert<Self, Self::Imply<P, Q>>, p: Cert<Self, P>) -> Cert<Self, Q> {
            Prop::l2().mp(pq.cast()).mp(p.cast()).cast()
        }
    }
    impl<A, Prop: PropLogic> PropLogic for Deduction<A, Prop> {
        fn l1<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, P>>> {
            Self::upgrade(Prop::l1())
        }
        fn l2<P, Q, R>() -> Cert<
            Self,
            Self::Imply<
                Self::Imply<P, Self::Imply<Q, R>>,
                Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
            >,
        > {
            Self::upgrade(Prop::l2())
        }
    }
}
pub use sealed_deduction::Deduction;

pub trait DeductionUpgrade<A, P, Prop: PropLogic> {
    fn upgrade(self) -> Cert<Deduction<A, Prop>, P>;
    fn qed<Prop2: PropLogic>(self) -> Cert<Prop2, Prop2::Imply<A, P>>
    where
        Cert<Prop, P>: Into<Cert<Deduction<A, Prop2>, P>>;
}
impl<A, P, Prop: PropLogic> DeductionUpgrade<A, P, Prop> for Cert<Prop, P> {
    fn upgrade(self) -> Cert<Deduction<A, Prop>, P> {
        Deduction::upgrade(self)
    }
    fn qed<Prop2: PropLogic>(self) -> Cert<Prop2, Prop2::Imply<A, P>>
    where
        Cert<Prop, P>: Into<Cert<Deduction<A, Prop2>, P>>,
    {
        self.into().cast()
    }
}

impl<A, Logic: Negation> Negation for Deduction<A, Logic> {
    type Neg<P> = Logic::Neg<P>;
}

pub fn syllogism<P, Q, R, Prop: PropLogic>()
-> Cert<Prop, Prop::Imply<Prop::Imply<P, Q>, Prop::Imply<Prop::Imply<Q, R>, Prop::Imply<P, R>>>> {
    Deduction::assume()
        .pipe(Deduction::assume().upgrade().upgrade())
        .pipe(Deduction::assume().upgrade())
        .qed()
        .qed()
        .qed()
}

/// Exchange of antecedents: (P → (Q → R)) → (Q → (P → R))
pub fn exchange<P, Q, R, Prop: PropLogic>()
-> Cert<Prop, Prop::Imply<Prop::Imply<P, Prop::Imply<Q, R>>, Prop::Imply<Q, Prop::Imply<P, R>>>> {
    Deduction::assume()
        .pipe(Deduction::assume().upgrade().upgrade())
        .mp(Deduction::assume().upgrade())
        .qed()
        .qed()
        .qed()
}

/// Currying: `((A ∧ B) → C) → (A → (B → C))`
pub fn curry<A, B, C, Prop: And>()
-> Cert<Prop, Prop::Imply<Prop::Imply<Prop::And<A, B>, C>, Prop::Imply<A, Prop::Imply<B, C>>>> {
    // Three nested scopes: the outer assumes `(A ∧ B) → C`, then `A`, then `B`.
    let g = Deduction::<Prop::Imply<Prop::And<A, B>, C>, Prop>::assume();
    let a = Deduction::<A, Deduction<Prop::Imply<Prop::And<A, B>, C>, Prop>>::assume();
    let b =
        Deduction::<B, Deduction<A, Deduction<Prop::Imply<Prop::And<A, B>, C>, Prop>>>::assume();
    let pair = Prop::and_intro::<A, B>()
        .upgrade()
        .upgrade()
        .upgrade()
        .mp(a.upgrade())
        .mp(b);
    g.upgrade().upgrade().mp(pair).cast()
}

/// Uncurrying: `(A → (B → C)) → ((A ∧ B) → C)`
///
/// The direction that lets an extra hypothesis be folded into a single
/// antecedent, which is what [`FirstOrder::forall_gen`] needs in order to
/// generalise underneath a [`Deduction`] assumption.
pub fn uncurry<A, B, C, Prop: And>()
-> Cert<Prop, Prop::Imply<Prop::Imply<A, Prop::Imply<B, C>>, Prop::Imply<Prop::And<A, B>, C>>> {
    let f = Deduction::<Prop::Imply<A, Prop::Imply<B, C>>, Prop>::assume();
    let ab =
        Deduction::<Prop::And<A, B>, Deduction<Prop::Imply<A, Prop::Imply<B, C>>, Prop>>::assume();
    f.upgrade()
        .mp(ab.clone().pipe(Prop::and_left().upgrade().upgrade()))
        .mp(ab.pipe(Prop::and_right().upgrade().upgrade()))
        .cast()
}

/// Commutativity of conjunction: `(A ∧ B) → (B ∧ A)`
pub fn and_comm<A, B, Prop: And>() -> Cert<Prop, Prop::Imply<Prop::And<A, B>, Prop::And<B, A>>> {
    let h = Deduction::<Prop::And<A, B>, Prop>::assume();
    Prop::and_intro()
        .upgrade()
        .mp(h.clone().pipe(Prop::and_right().upgrade()))
        .mp(h.pipe(Prop::and_left().upgrade()))
        .cast()
}

/// Conjunction is a functor: `(A → A') → (B → B') → ((A ∧ B) → (A' ∧ B'))`
pub fn and_map<A, B, A2, B2, Prop: And>(
    f: Cert<Prop, Prop::Imply<A, A2>>,
    g: Cert<Prop, Prop::Imply<B, B2>>,
) -> Cert<Prop, Prop::Imply<Prop::And<A, B>, Prop::And<A2, B2>>> {
    let h = Deduction::<Prop::And<A, B>, Prop>::assume();
    Prop::and_intro()
        .upgrade()
        .mp(h.clone().pipe(Prop::and_left().upgrade()).pipe(f.upgrade()))
        .mp(h.pipe(Prop::and_right().upgrade()).pipe(g.upgrade()))
        .cast()
}

/// Transitivity of the biconditional: `((A ↔ B) ∧ (B ↔ C)) → (A ↔ C)`
pub fn iff_trans<A, B, C, Prop: And>()
-> Cert<Prop, Prop::Imply<Prop::And<Iff<Prop, A, B>, Iff<Prop, B, C>>, Iff<Prop, A, C>>> {
    let h = Deduction::<Prop::And<Iff<Prop, A, B>, Iff<Prop, B, C>>, Prop>::assume();
    let left = h.clone().pipe(Prop::and_left().upgrade());
    let right = h.pipe(Prop::and_right().upgrade());
    let ab = left.clone().pipe(Prop::and_left().upgrade());
    let ba = left.pipe(Prop::and_right().upgrade());
    let bc = right.clone().pipe(Prop::and_left().upgrade());
    let cb = right.pipe(Prop::and_right().upgrade());
    Prop::and_intro()
        .upgrade()
        .mp(syllogism().mp(ab).mp(bc))
        .mp(syllogism().mp(cb).mp(ba))
        .cast()
}

/// `(B ↔ C) → ((A ↔ B) → (A ↔ C))`
///
/// [`iff_trans`] with the right-hand biconditional already in hand, which is
/// the shape needed to rewrite one side of a biconditional under a quantifier.
pub fn iff_extend<A, B, C, Prop: And>(
    bc: Cert<Prop, Iff<Prop, B, C>>,
) -> Cert<Prop, Prop::Imply<Iff<Prop, A, B>, Iff<Prop, A, C>>> {
    let h = Deduction::<Iff<Prop, A, B>, Prop>::assume();
    iff_trans::<A, B, C, Prop>()
        .upgrade()
        .mp(Prop::and_intro().upgrade().mp(h).mp(bc.upgrade()))
        .cast()
}

/// `P ↔ (P ∨ P)`, at any logic with conjunction and disjunction.
pub fn or_idem<P, Prop: And + Or>() -> Cert<Prop, Iff<Prop, P, Prop::Or<P, P>>> {
    Prop::and_intro()
        .mp(Prop::or_left())
        .mp(Prop::or_elim().mp(reflexive()).mp(reflexive()))
}

/// Conjunction survives an assumption: every axiom is closed, so `upgrade`
/// carries each one in unchanged.
impl<A, Logic: And> And for Deduction<A, Logic> {
    type And<P, Q> = Logic::And<P, Q>;
    fn and_left<P, Q>() -> Cert<Self, Self::Imply<Self::And<P, Q>, P>> {
        Self::upgrade(Logic::and_left())
    }
    fn and_right<P, Q>() -> Cert<Self, Self::Imply<Self::And<P, Q>, Q>> {
        Self::upgrade(Logic::and_right())
    }
    fn and_intro<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>> {
        Self::upgrade(Logic::and_intro())
    }
}

use self::sealed_deduction_fol::{Exchanged, Uncurried};
mod sealed_deduction_fol {
    use super::{
        And, Cert, Deduction, ExistsProof, FirstOrder, ForAllProof, PhantomData, View, exchange,
        uncurry,
    };

    /// Repackages a [`ForAllProof`] written under the assumption `A` as one
    /// whose single antecedent is `A ∧ P`.
    pub struct Uncurried<A, Logic, P, S>(pub S, pub PhantomData<(A, Logic, P)>);

    impl<A, Logic, P, S: Clone> Clone for Uncurried<A, Logic, P, S> {
        fn clone(&self) -> Self {
            Uncurried(self.0.clone(), PhantomData)
        }
    }

    impl<A, Logic, P, Q, S> ForAllProof<Logic, Logic::And<A, P>, Q> for Uncurried<A, Logic, P, S>
    where
        Logic: FirstOrder + And,
        Q: for<'x> View<'x> + ?Sized,
        S: ForAllProof<Deduction<A, Logic>, P, Q>,
    {
        fn prove<'x>(self) -> Cert<Logic, Logic::Imply<Logic::And<A, P>, <Q as View<'x>>::Output>> {
            uncurry::<A, P, <Q as View<'x>>::Output, Logic>().mp(self.0.prove::<'x>().cast())
        }
    }

    /// Repackages an [`ExistsProof`] written under the assumption `A` by
    /// swapping `A` past the witness antecedent. Unlike [`Uncurried`] this
    /// needs no conjunction — the assumption can simply move into the
    /// consequent.
    pub struct Exchanged<A, Logic, P: ?Sized, Q, S>(
        pub S,
        pub PhantomData<(A, Logic, Q)>,
        pub PhantomData<P>,
    );

    impl<A, Logic, P: ?Sized, Q, S: Clone> Clone for Exchanged<A, Logic, P, Q, S> {
        fn clone(&self) -> Self {
            Exchanged(self.0.clone(), PhantomData, PhantomData)
        }
    }

    impl<A, Logic, P, Q, S> ExistsProof<Logic, P, Logic::Imply<A, Q>> for Exchanged<A, Logic, P, Q, S>
    where
        Logic: FirstOrder + super::PropLogic,
        P: for<'x> View<'x> + ?Sized,
        S: ExistsProof<Deduction<A, Logic>, P, Q>,
    {
        fn prove<'x>(
            self,
        ) -> Cert<Logic, Logic::Imply<<P as View<'x>>::Output, Logic::Imply<A, Q>>> {
            exchange::<A, <P as View<'x>>::Output, Q, Logic>().mp(self.0.prove::<'x>().cast())
        }
    }
}

/// Quantifiers survive an assumption.
///
/// The two elimination rules are closed axioms, so they just `upgrade`. The
/// two generalisation rules have to move the assumption `A` out of the way
/// first, because `∀x. (A → Q x)` is not the same proposition as
/// `A → ∀x. Q x`: `forall_gen` folds `A` into the antecedent with
/// [`uncurry`] and unfolds the result with [`curry`], while `exists_gen`
/// only has to [`exchange`] `A` past the witness.
impl<A, Logic: FirstOrder + And> FirstOrder for Deduction<A, Logic> {
    type ForAll<P: for<'x> View<'x> + ?Sized> = Logic::ForAll<P>;
    type Exists<P: for<'x> View<'x> + ?Sized> = Logic::Exists<P>;

    fn forall_elim<'t, P: for<'x> View<'x> + ?Sized>()
    -> Cert<Self, Self::Imply<Self::ForAll<P>, <P as View<'t>>::Output>> {
        Self::upgrade(Logic::forall_elim::<'t, P>())
    }

    fn exists_elim<'t, P: for<'x> View<'x> + ?Sized, Q>()
    -> Cert<Self, Self::Imply<<P as View<'t>>::Output, Self::Exists<P>>> {
        Self::upgrade(Logic::exists_elim::<'t, P, Q>())
    }

    fn forall_gen<P, Q: for<'x> View<'x> + ?Sized, S: ForAllProof<Self, P, Q>>(
        proof: S,
    ) -> Cert<Self, Self::Imply<P, Self::ForAll<Q>>> {
        curry::<A, P, Logic::ForAll<Q>, Logic>()
            .mp(Logic::forall_gen(Uncurried::<A, Logic, P, S>(
                proof,
                PhantomData,
            )))
            .cast()
    }

    fn exists_gen<P: for<'x> View<'x> + ?Sized, Q, S: ExistsProof<Self, P, Q>>(
        proof: S,
    ) -> Cert<Self, Self::Imply<Self::Exists<P>, Q>> {
        exchange::<Logic::Exists<P>, A, Q, Logic>()
            .mp(Logic::exists_gen(Exchanged::<A, Logic, P, Q, S>(
                proof,
                PhantomData,
                PhantomData,
            )))
            .cast()
    }
}

/// A proof of `Q<'x>` that is uniform in `'x`, with no antecedent.
///
/// [`FirstOrder::forall_gen`] always produces an implication `P → ∀x. Q x`,
/// because that is the shape universal generalisation takes in a Hilbert
/// system. When the theorem being generalised is closed there is nothing for
/// `P` to be, and threading a dummy antecedent through by hand at every use
/// obscures the proof. [`forall_intro`] does it once.
pub trait Generalise<Logic: Imply, Q: for<'x> View<'x> + ?Sized>: Clone {
    fn prove<'x>(self) -> Cert<Logic, <Q as View<'x>>::Output>;
}

use self::sealed_generalise::Generalised;
mod sealed_generalise {
    use super::{Cert, ForAllProof, Generalise, PhantomData, PropLogic, View};

    pub struct Generalised<Logic, Q: ?Sized, S>(pub S, pub PhantomData<Logic>, pub PhantomData<Q>);

    impl<Logic, Q: ?Sized, S: Clone> Clone for Generalised<Logic, Q, S> {
        fn clone(&self) -> Self {
            Generalised(self.0.clone(), PhantomData, PhantomData)
        }
    }

    impl<Logic, Q, S> ForAllProof<Logic, Logic::Imply<(), ()>, Q> for Generalised<Logic, Q, S>
    where
        Logic: PropLogic,
        Q: for<'x> View<'x> + ?Sized,
        S: Generalise<Logic, Q>,
    {
        fn prove<'x>(
            self,
        ) -> Cert<Logic, Logic::Imply<Logic::Imply<(), ()>, <Q as View<'x>>::Output>> {
            Logic::l1().mp(self.0.prove::<'x>())
        }
    }
}

/// Universal generalisation of a closed theorem: from a proof of `Q<'x>`
/// uniform in `'x`, conclude `∀x. Q x`.
pub fn forall_intro<Logic, Q, S>(proof: S) -> Cert<Logic, Logic::ForAll<Q>>
where
    Logic: FirstOrder + PropLogic,
    Q: for<'x> View<'x> + ?Sized,
    S: Generalise<Logic, Q>,
{
    Logic::forall_gen(Generalised::<Logic, Q, S>(proof, PhantomData, PhantomData))
        .mp(reflexive::<(), Logic>())
}
