//! **Pilot.** Set-theoretic vocabulary as opaque associated types.
//!
//! Everything here is generic over the logic `L`, and every defined notion is a
//! GAT rather than a `pub type` alias. `<L as Vocab>::Applies<'f,'a,'b>` with
//! `L` a type parameter is a *rigid* projection: rustc has no impl to look up,
//! so it never expands, and region renumbering sees one node instead of the
//! ~10^4-node tree the concrete aliases unfold into.
//!
//! One trait here rather than one per definition — the split is orthogonal to
//! what this pilot measures.
#![forbid(unsafe_code)]

use crate::logic::prop::{And, Cert, FirstOrder, Iff, Imply, PropLogic, View, syllogism};

/// The vocabulary, opaque. Each `*_iff` unfolds **exactly one level**, stated
/// against the next opaque layer down — that is what keeps the cost additive
/// over definitions instead of multiplicative through the proof tree.
pub trait Vocab: PropLogic + And + FirstOrder + 'static {
    type In<'a, 'b>;
    type Eq<'x, 'y>;
    type Applies<'f, 'a, 'b>;
    type IsRelation<'f>;
    type IsSingleValued<'f>;
    type IsFunction<'f>;

    /// `IsFunction(f) ↔ IsRelation(f) ∧ IsSingleValued(f)`
    fn function_iff<'f>() -> Cert<
        Self,
        Iff<Self, Self::IsFunction<'f>, Self::And<Self::IsRelation<'f>, Self::IsSingleValued<'f>>>,
    >;

    /// `IsSingleValued(f) ↔ ∀a ∀b ∀c. f(a)=b ∧ f(a)=c → b = c`
    fn single_valued_iff<'f>()
    -> Cert<Self, Iff<Self, Self::IsSingleValued<'f>, Self::ForAll<SvView<'f, Self>>>>;
}

/// `λc. f(a)=b ∧ f(a)=c → b = c`
pub type SvView2<'f, 'a, 'b, L> = dyn for<'c> View<
        'c,
        Output = <L as Imply>::Imply<
            <L as And>::And<<L as Vocab>::Applies<'f, 'a, 'b>, <L as Vocab>::Applies<'f, 'a, 'c>>,
            <L as Vocab>::Eq<'b, 'c>,
        >,
    > + 'static;

/// `λb. ∀c. …`
pub type SvView1<'f, 'a, L> =
    dyn for<'b> View<'b, Output = <L as FirstOrder>::ForAll<SvView2<'f, 'a, 'b, L>>> + 'static;

/// `λa. ∀b ∀c. …` — the body of [`Vocab::IsSingleValued`].
pub type SvView<'f, L> =
    dyn for<'a> View<'a, Output = <L as FirstOrder>::ForAll<SvView1<'f, 'a, L>>> + 'static;

/// `IsFunction(f) → (f(a)=b ∧ f(a)=c → b = c)`
///
/// The generic twin of `concrete::theorems::func_apply_unique_at`. Same proof,
/// same number of locals; the only difference is that every proposition in it
/// is a rigid projection.
pub fn func_apply_unique_at<'f, 'a, 'b, 'c, L>() -> Cert<
    L,
    L::Imply<
        L::IsFunction<'f>,
        L::Imply<L::And<L::Applies<'f, 'a, 'b>, L::Applies<'f, 'a, 'c>>, L::Eq<'b, 'c>>,
    >,
>
where
    L: Vocab,
{
    let unpack = <L as And>::and_left().mp(L::function_iff::<'f>());
    let single = syllogism().mp(unpack).mp(<L as And>::and_right());
    let unfold = <L as And>::and_left().mp(L::single_valued_iff::<'f>());
    syllogism()
        .mp(syllogism().mp(single).mp(unfold))
        .mp(syllogism()
            .mp(<L as FirstOrder>::forall_elim::<'a, SvView<'f, L>>())
            .mp(syllogism()
                .mp(<L as FirstOrder>::forall_elim::<'b, SvView1<'f, 'a, L>>())
                .mp(<L as FirstOrder>::forall_elim::<'c, SvView2<'f, 'a, 'b, L>>())))
}
