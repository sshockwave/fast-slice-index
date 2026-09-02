//! The language of set theory: the vocabulary the axioms are stated in.
//!
//! This sits *below* [`super::axioms`] because the nine assumptions have to be
//! written in some language, and that language cannot in turn depend on them.
//! Nothing here proves anything — every item is a definition, so the module has
//! no `fn` at all. The derivations live one layer up, in [`super::theorems`].
//!
//! [`In`] is the sole primitive. Equality is *defined* ([`Eq`]) as having the
//! same members, which is why [`super::axioms::ext`] only has to assume the
//! converse congruence.
#![forbid(unsafe_code)]
#![expect(
    unused_parens,
    reason = "`pred!` parses its body as an expression, so operands are \
              parenthesised for grouping; the parens survive into the type"
)]

use ::core::marker::PhantomData;

use super::Axiomize;
use crate::logic::prop::{And, FirstOrder, Iff, Imply, Negation, View};
use crate::macros::pred;

/// A binary relation as a type-level schema parameter, for [`super::axioms::replacement`].
///
/// [`View`] carries one lifetime and replacement needs two, so this is its
/// two-argument counterpart. Like every schema here it is instantiated per
/// relation rather than quantified over, which keeps the development
/// predicative.
pub trait Rel2 {
    type At<'x, 'y>;
}

/// `'a ∈ 'b`. The one primitive relation.
pub struct In<'a, 'b>(PhantomData<(&'a (), &'b ())>);

/// `∀z. (z ∈ x ↔ z ∈ y)` — the body of [`Eq`], with `'z` still to bind.
pub type EqView<'x, 'y> =
    dyn for<'z> View<'z, Output = Iff<Axiomize, In<'z, 'x>, In<'z, 'y>>> + 'static;

/// `'x = 'y`, *defined* as having the same members.
pub type Eq<'x, 'y> = <Axiomize as FirstOrder>::ForAll<EqView<'x, 'y>>;

/// `∀z. (z ∈ x → z ∈ y)` — the body of [`Subset`].
pub type SubsetView<'x, 'y> =
    dyn for<'z> View<'z, Output = <Axiomize as Imply>::Imply<In<'z, 'x>, In<'z, 'y>>> + 'static;

/// `'x ⊆ 'y`.
pub type Subset<'x, 'y> = <Axiomize as FirstOrder>::ForAll<SubsetView<'x, 'y>>;

/// `λw. x ∈ w ↔ y ∈ w` — the congruence [`super::axioms::ext`] hands back.
pub type ExtCongrView<'x, 'y> =
    dyn for<'w> View<'w, Output = Iff<Axiomize, In<'x, 'w>, In<'y, 'w>>> + 'static;

/// `λy. x = y → ∀w. (x ∈ w ↔ y ∈ w)`
pub type ExtView1<'x> = dyn for<'y> View<
        'y,
        Output = <Axiomize as Imply>::Imply<
            Eq<'x, 'y>,
            <Axiomize as FirstOrder>::ForAll<ExtCongrView<'x, 'y>>,
        >,
    > + 'static;

/// `λx. ∀y. x = y → ∀w. (x ∈ w ↔ y ∈ w)` — the body of extensionality.
///
/// Named here rather than left anonymous inside the axiom so that the axiom's
/// quantifiers can actually be eliminated: [`FirstOrder::forall_elim`] needs
/// the view as a type argument, and a `pred!` body gives it no name.
pub type ExtView =
    dyn for<'x> View<'x, Output = <Axiomize as FirstOrder>::ForAll<ExtView1<'x>>> + 'static;

// ---------------------------------------------------------------------------
// Defined notions
// ---------------------------------------------------------------------------

/// `λz. z ∉ e` — the body of [`IsEmpty`], named so it can be eliminated.
pub type EmptyView<'e> =
    dyn for<'z> View<'z, Output = <Axiomize as Negation>::Neg<In<'z, 'e>>> + 'static;

/// `IsEmpty(e) := ∀z. z ∉ e`
pub type IsEmpty<'e> = <Axiomize as FirstOrder>::ForAll<EmptyView<'e>>;

/// `λz. z ∈ s ↔ z = a` — the body of [`IsSingleton`].
///
/// Named for the same reason as [`PairView`]: a proof about singletons has to
/// pin this view in an impl header.
pub type SingletonView<'s, 'a> =
    dyn for<'z> View<'z, Output = Iff<Axiomize, In<'z, 's>, Eq<'z, 'a>>> + 'static;

/// `IsSingleton(s, a) := ∀z. (z ∈ s ↔ z = a)`, i.e. `s = {a}`.
pub type IsSingleton<'s, 'a> = <Axiomize as FirstOrder>::ForAll<SingletonView<'s, 'a>>;

/// `λz. z ∈ p ↔ (z = a ∨ z = b)` — the body of [`IsPair`].
///
/// Named separately because a proof about pairs has to pin this view in an
/// impl header, and the `pred!` form gives it no name.
pub type PairView<'p, 'a, 'b> = dyn for<'z> View<'z, Output = pred!({ Axiomize }, In::<'z, 'p>.iff(Eq::<'z, 'a> || Eq::<'z, 'b>))>
    + 'static;

/// `IsPair(p, a, b) := ∀z. (z ∈ p ↔ (z = a ∨ z = b))`, i.e. `p = {a, b}`.
pub type IsPair<'p, 'a, 'b> = <Axiomize as FirstOrder>::ForAll<PairView<'p, 'a, 'b>>;

/// `IsSuccOf(s, y) := ∀w. (w ∈ s ↔ (w ∈ y ∨ w = y))`, i.e. `s = y ∪ {y}`.
///
/// The von Neumann successor, used only to state [`super::axioms::infinity`].
/// `λw. w ∈ s ↔ (w ∈ y ∨ w = y)` — the body of [`IsSuccOf`].
pub type SuccView<'s, 'y> = dyn for<'w> View<
        'w,
        Output = pred!(
            { Axiomize },
            (In::<'w, 's>).iff((In::<'w, 'y>) || (Eq::<'w, 'y>))
        ),
    > + 'static;

pub type IsSuccOf<'s, 'y> = <Axiomize as FirstOrder>::ForAll<SuccView<'s, 'y>>;

/// `λz. z ∈ s ↔ (z ∈ a ∧ Q(z))` — the body of [`IsSeparated`].
pub type SeparatedView<'s, 'a, Q> = dyn for<'z> View<
        'z,
        Output = Iff<
            Axiomize,
            In<'z, 's>,
            <Axiomize as And>::And<In<'z, 'a>, <Q as View<'z>>::Output>,
        >,
    > + 'static;

/// `IsSeparated(s, a, Q) := ∀z. (z ∈ s ↔ (z ∈ a ∧ Q(z)))`
///
/// "`s` is the subset of `a` carved out by `Q`" — what
/// [`super::axioms::separation`] promises to exist.
pub type IsSeparated<'s, 'a, Q> = <Axiomize as FirstOrder>::ForAll<SeparatedView<'s, 'a, Q>>;

/// `λs. IsSeparated(s, a, Q)`
pub type SeparationInnerView<'a, Q> =
    dyn for<'s> View<'s, Output = IsSeparated<'s, 'a, Q>> + 'static;
/// `λa. ∃s. IsSeparated(s, a, Q)` — the body of [`super::axioms::separation`].
pub type SeparationView<Q> = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::Exists<SeparationInnerView<'a, Q>>>
    + 'static;

/// `λe. e ∈ i ∧ IsEmpty(e)` — the body of [`HasEmpty`].
pub type HasEmptyView<'i> =
    dyn for<'e> View<'e, Output = pred!({ Axiomize }, (In::<'e, 'i>) && (IsEmpty::<'e>))> + 'static;

/// `HasEmpty(i) := ∃e. e ∈ i ∧ IsEmpty(e)`
pub type HasEmpty<'i> = <Axiomize as FirstOrder>::Exists<HasEmptyView<'i>>;

/// `λs. s ∈ i ∧ IsSuccOf(s, y)` — the witness [`ClosedUnderSucc`] demands.
pub type SuccStepView<'i, 'y> = dyn for<'s> View<'s, Output = pred!({ Axiomize }, (In::<'s, 'i>) && (IsSuccOf::<'s, 'y>))>
    + 'static;

/// `λy. y ∈ i → ∃s. s ∈ i ∧ IsSuccOf(s, y)` — the body of [`ClosedUnderSucc`].
pub type ClosedUnderSuccView<'i> = dyn for<'y> View<
        'y,
        Output = <Axiomize as Imply>::Imply<
            In<'y, 'i>,
            <Axiomize as FirstOrder>::Exists<SuccStepView<'i, 'y>>,
        >,
    > + 'static;

/// `ClosedUnderSucc(i) := ∀y. y ∈ i → ∃s. s ∈ i ∧ IsSuccOf(s, y)`
pub type ClosedUnderSucc<'i> = <Axiomize as FirstOrder>::ForAll<ClosedUnderSuccView<'i>>;

/// `IsInductive(i) := HasEmpty(i) ∧ ClosedUnderSucc(i)`
///
/// Exactly what [`super::axioms::infinity`] asserts of some set. Naming it
/// is what lets that existential be eliminated at a use site.
pub type IsInductive<'i> = <Axiomize as And>::And<HasEmpty<'i>, ClosedUnderSucc<'i>>;

/// `λi. IsInductive(i)` — the body of [`super::axioms::infinity`].
pub type InductiveView = dyn for<'i> View<'i, Output = IsInductive<'i>> + 'static;

/// `λi. IsInductive(i) → n ∈ i` — the body of [`IsNat`].
pub type IsNatView<'n> = dyn for<'i> View<'i, Output = <Axiomize as Imply>::Imply<IsInductive<'i>, In<'n, 'i>>>
    + 'static;

/// `IsNat(n) := ∀i. IsInductive(i) → n ∈ i`
///
/// A natural number is what every inductive set is obliged to contain. This is
/// first-order here — `i` ranges over sets, which are ordinary elements — so no
/// second-order quantification sneaks in, and ω need not exist yet for the
/// predicate to be stated.
pub type IsNat<'n> = <Axiomize as FirstOrder>::ForAll<IsNatView<'n>>;

/// `IsOrderedPair(p, a, b) := p = {{a}, {a, b}}` — the Kuratowski pair.
///
/// Stated as an existential over the two layers because this logic has no term
/// formers: `u` is `{a}`, `v` is `{a, b}`, `p` is `{u, v}`. [`super::axioms::pairing`] is what
/// makes all three exist. This is the construction
/// [`crate::algebra::group`]'s module docs call unavailable at the level of
/// lifetimes alone — it becomes available once sets are the elements.
pub type IsOrderedPair<'p, 'a, 'b> = pred!(
    { Axiomize },
    Exists::<'u, 'v>((IsSingleton::<'u, 'a>) && ((IsPair::<'v, 'a, 'b>) && (IsPair::<'p, 'u, 'v>)))
);

/// `Applies(f, a, b) := ⟨a, b⟩ ∈ f` — "f maps a to b".
///
/// A function *is* its graph, so application is membership of an ordered pair.
/// This is the reified counterpart of
/// [`crate::logic::function::Function`]'s type-level `F<'x, 'y>`: here `'f` is
/// an ordinary element, so it can be quantified over — which is what makes a
/// recursion theorem statable at all.
pub type Applies<'f, 'a, 'b> = pred!(
    { Axiomize },
    Exists::<'p>((IsOrderedPair::<'p, 'a, 'b>) && (In::<'p, 'f>))
);

/// `IsRelation(r) := every member of r is an ordered pair`
pub type IsRelation<'r> = pred!(
    { Axiomize },
    ForAll::<'z>((In::<'z, 'r>).imply(Exists::<'a, 'b>(IsOrderedPair::<'z, 'a, 'b>)))
);

/// `λc. (f(a)=b ∧ f(a)=c) → b = c`
pub type SingleValuedView2<'f, 'a, 'b> = dyn for<'c> View<
        'c,
        Output = pred!(
            { Axiomize },
            ((Applies::<'f, 'a, 'b>) && (Applies::<'f, 'a, 'c>)) >>= Eq::<'b, 'c>
        ),
    > + 'static;
/// `λb. ∀c. (f(a)=b ∧ f(a)=c) → b = c`
pub type SingleValuedView1<'f, 'a> = dyn for<'b> View<'b, Output = <Axiomize as FirstOrder>::ForAll<SingleValuedView2<'f, 'a, 'b>>>
    + 'static;
/// `λa. ∀b ∀c. (f(a)=b ∧ f(a)=c) → b = c`
pub type SingleValuedView<'f> = dyn for<'a> View<'a, Output = <Axiomize as FirstOrder>::ForAll<SingleValuedView1<'f, 'a>>>
    + 'static;

/// `IsSingleValued(f) := ∀a ∀b ∀c. (f(a)=b ∧ f(a)=c) → b = c`
///
/// Split out of [`IsFunction`] and named so its quantifiers can be eliminated;
/// [`func_apply_unique`] is what that buys.
pub type IsSingleValued<'f> = <Axiomize as FirstOrder>::ForAll<SingleValuedView<'f>>;

/// `IsFunction(f) := IsRelation(f) ∧ f is single-valued`
pub type IsFunction<'f> = pred!({ Axiomize }, (IsRelation::<'f>) && (IsSingleValued::<'f>));

/// `λb. f(a) = b` — the body of [`InDomain`].
pub type InDomainView<'f, 'a> = dyn for<'b> View<'b, Output = Applies<'f, 'a, 'b>> + 'static;

/// `InDomain(f, a) := ∃b. f(a) = b`
pub type InDomain<'f, 'a> = <Axiomize as FirstOrder>::Exists<InDomainView<'f, 'a>>;
