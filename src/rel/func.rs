//! Functions as elements: application, and what makes it single-valued.
//!
//! A function here is not a type-level mapping but an ordinary object of the
//! domain — its graph. That is what makes "there exists a function such that …"
//! a first-order statement rather than a schema, and it is why the notions
//! below are worth stating abstractly at all.
//!
//! Every notion is an **opaque** associated type paired with an `…_iff`
//! unfolding it *exactly one level*, against the next opaque layer down. With
//! `A` a type parameter, `A::App<'f,'a,'b>` is a rigid projection: rustc has no
//! impl to look up, so region renumbering sees one node where the concrete
//! spelling unfolds into a ~10⁴-node tree — a Kuratowski pair inside an
//! existential inside three quantifiers. Unfolding one level at a time is what
//! keeps the cost additive over the definitions instead of multiplicative
//! through the proof tree.
#![forbid(unsafe_code)]

use ::core::marker::PhantomData;

use crate::logic::prop::{
    And, Cert, FirstOrder, Generalise, Iff, Imply, PropLogic, View, forall_intro, syllogism,
};
use crate::rel::ext::{ExtEq, Membership};

/// Application as a relation: `App(f, a, b)` is "`f` maps `a` to `b`".
///
/// The `Is…` notions are opaque rather than defined here because the ambient
/// theory owns their spelling — being a relation, in particular, means being a
/// set of ordered pairs, which this module has no vocabulary for. What it does
/// own is the shape they have to fit: a function is a relation that is single
/// valued, and single valued means agreeing up to [`Membership`]'s equality.
pub trait Application<Logic>: 'static
where
    Logic: PropLogic + And + FirstOrder,
{
    /// The membership relation whose induced equality values are compared by.
    type Mem: Membership<Logic> + ?Sized;

    /// `f(a) = b`
    type App<'f, 'a, 'b>;
    /// `IsRelation(f)` — whatever the theory requires beyond single-valuedness.
    type IsRel<'f>;
    /// `IsSingleValued(f)`
    type IsSingleValued<'f>;
    /// `IsFunction(f)`
    type IsFunction<'f>;
    /// `InDomain(f, a)`
    type InDomain<'f, 'a>;

    /// `IsFunction(f) ↔ IsRelation(f) ∧ IsSingleValued(f)`
    fn function_iff<'f>() -> Cert<
        Logic,
        Iff<
            Logic,
            Self::IsFunction<'f>,
            <Logic as And>::And<Self::IsRel<'f>, Self::IsSingleValued<'f>>,
        >,
    >;

    /// `IsSingleValued(f) ↔ ∀a ∀b ∀c. (f(a)=b ∧ f(a)=c) → b = c`
    fn single_valued_iff<'f>() -> Cert<
        Logic,
        Iff<
            Logic,
            Self::IsSingleValued<'f>,
            <Logic as FirstOrder>::ForAll<SvView<'f, Logic, Self>>,
        >,
    >;

    /// `InDomain(f, a) ↔ ∃b. f(a) = b`
    fn in_domain_iff<'f, 'a>() -> Cert<
        Logic,
        Iff<
            Logic,
            Self::InDomain<'f, 'a>,
            <Logic as FirstOrder>::Exists<DomainView<'f, 'a, Logic, Self>>,
        >,
    >;
}

/// `λc. (f(a)=b ∧ f(a)=c) → b = c`
pub type SvView2<'f, 'a, 'b, Logic, A> = dyn for<'c> View<
        'c,
        Output = <Logic as Imply>::Imply<
            <Logic as And>::And<
                <A as Application<Logic>>::App<'f, 'a, 'b>,
                <A as Application<Logic>>::App<'f, 'a, 'c>,
            >,
            ExtEq<'b, 'c, Logic, <A as Application<Logic>>::Mem>,
        >,
    > + 'static;
/// `λb. ∀c. …`
pub type SvView1<'f, 'a, Logic, A> = dyn for<'b> View<
        'b,
        Output = <Logic as FirstOrder>::ForAll<SvView2<'f, 'a, 'b, Logic, A>>,
    > + 'static;
/// `λa. ∀b ∀c. …` — the body [`Application::single_valued_iff`] unfolds to.
pub type SvView<'f, Logic, A> = dyn for<'a> View<
        'a,
        Output = <Logic as FirstOrder>::ForAll<SvView1<'f, 'a, Logic, A>>,
    > + 'static;

/// `λb. f(a) = b` — the body [`Application::in_domain_iff`] unfolds to.
pub type DomainView<'f, 'a, Logic, A> =
    dyn for<'b> View<'b, Output = <A as Application<Logic>>::App<'f, 'a, 'b>> + 'static;

// ---------------------------------------------------------------------------
// Elimination rules, at fixed points
// ---------------------------------------------------------------------------
//
// These unpack `IsFunction` and say nothing about which functions exist; that
// needs axioms and belongs to whatever theory supplies them.

/// `IsFunction(f) → IsRelation(f)`, at a fixed `'f`.
pub fn is_rel_at<'f, Logic, A>()
-> Cert<Logic, Logic::Imply<A::IsFunction<'f>, A::IsRel<'f>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    syllogism()
        .mp(Logic::and_left().mp(A::function_iff::<'f>()))
        .mp(Logic::and_left())
}

/// `IsFunction(f) → IsSingleValued(f)`, at a fixed `'f`.
pub fn single_valued_at<'f, Logic, A>()
-> Cert<Logic, Logic::Imply<A::IsFunction<'f>, A::IsSingleValued<'f>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    syllogism()
        .mp(Logic::and_left().mp(A::function_iff::<'f>()))
        .mp(Logic::and_right())
}

/// `IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`, at fixed points.
///
/// Two unfoldings and three quantifier eliminations, and no other content: the
/// property *is* the definition, read at a point.
pub fn apply_unique_at<'f, 'a, 'b, 'c, Logic, A>() -> Cert<
    Logic,
    Logic::Imply<
        A::IsFunction<'f>,
        Logic::Imply<
            Logic::And<A::App<'f, 'a, 'b>, A::App<'f, 'a, 'c>>,
            ExtEq<'b, 'c, Logic, A::Mem>,
        >,
    >,
>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    let unfold = Logic::and_left().mp(A::single_valued_iff::<'f>());
    syllogism()
        .mp(syllogism().mp(single_valued_at::<'f, Logic, A>()).mp(unfold))
        .mp(syllogism()
            .mp(Logic::forall_elim::<'a, SvView<'f, Logic, A>>())
            .mp(syllogism()
                .mp(Logic::forall_elim::<'b, SvView1<'f, 'a, Logic, A>>())
                .mp(Logic::forall_elim::<'c, SvView2<'f, 'a, 'b, Logic, A>>())))
}

/// `f(a) = b → a ∈ dom f`, at fixed points.
///
/// The witness for the existential is the value itself, so this is
/// [`FirstOrder::exists_elim`] against one unfolding and nothing more.
pub fn in_domain_at<'f, 'a, 'b, Logic, A>()
-> Cert<Logic, Logic::Imply<A::App<'f, 'a, 'b>, A::InDomain<'f, 'a>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    syllogism()
        .mp(Logic::exists_elim::<
            'b,
            DomainView<'f, 'a, Logic, A>,
            A::InDomain<'f, 'a>,
        >())
        .mp(Logic::and_right().mp(A::in_domain_iff::<'f, 'a>()))
}

// ---------------------------------------------------------------------------
// The same rules with their quantifiers put back
// ---------------------------------------------------------------------------

/// `PhantomData<*const A>` is not `Clone`-derivable and every prover here is a
/// unit, so the impls are written out rather than derived.
macro_rules! unit_clone {
    ($name:ident<$($lt:lifetime),*>) => {
        impl<$($lt,)* Logic, A: ?Sized> Clone for $name<$($lt,)* Logic, A> {
            fn clone(&self) -> Self {
                $name(PhantomData)
            }
        }
    };
}

/// `λf. IsFunction(f) → IsRelation(f)`
pub type IsRelView<Logic, A> = dyn for<'f> View<
        'f,
        Output = <Logic as Imply>::Imply<
            <A as Application<Logic>>::IsFunction<'f>,
            <A as Application<Logic>>::IsRel<'f>,
        >,
    > + 'static;

/// `∀f. IsFunction(f) → IsRelation(f)` — **proved**.
///
/// Every function is a relation, so anything proved about relations applies to
/// it.
pub fn is_rel<Logic, A>() -> Cert<Logic, Logic::ForAll<IsRelView<Logic, A>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    forall_intro(IsRel::<Logic, A>(PhantomData))
}

struct IsRel<Logic, A: ?Sized>(PhantomData<(Logic, *const A)>);
unit_clone!(IsRel<>);

impl<Logic, A, Q> Generalise<Logic, Q> for IsRel<Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'f> View<'f, Output = Logic::Imply<A::IsFunction<'f>, A::IsRel<'f>>> + ?Sized,
{
    fn prove<'f>(self) -> Cert<Logic, <Q as View<'f>>::Output> {
        is_rel_at::<'f, Logic, A>()
    }
}

/// `λf. IsFunction(f) → IsSingleValued(f)`
pub type SingleValuedRuleView<Logic, A> = dyn for<'f> View<
        'f,
        Output = <Logic as Imply>::Imply<
            <A as Application<Logic>>::IsFunction<'f>,
            <A as Application<Logic>>::IsSingleValued<'f>,
        >,
    > + 'static;

/// `∀f. IsFunction(f) → IsSingleValued(f)` — **proved**.
pub fn single_valued<Logic, A>() -> Cert<Logic, Logic::ForAll<SingleValuedRuleView<Logic, A>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    forall_intro(SingleValued::<Logic, A>(PhantomData))
}

struct SingleValued<Logic, A: ?Sized>(PhantomData<(Logic, *const A)>);
unit_clone!(SingleValued<>);

impl<Logic, A, Q> Generalise<Logic, Q> for SingleValued<Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'f> View<'f, Output = Logic::Imply<A::IsFunction<'f>, A::IsSingleValued<'f>>> + ?Sized,
{
    fn prove<'f>(self) -> Cert<Logic, <Q as View<'f>>::Output> {
        single_valued_at::<'f, Logic, A>()
    }
}

/// `λc. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c`
pub type ApplyUniqueView3<'f, 'a, 'b, Logic, A> = dyn for<'c> View<
        'c,
        Output = <Logic as Imply>::Imply<
            <A as Application<Logic>>::IsFunction<'f>,
            <Logic as Imply>::Imply<
                <Logic as And>::And<
                    <A as Application<Logic>>::App<'f, 'a, 'b>,
                    <A as Application<Logic>>::App<'f, 'a, 'c>,
                >,
                ExtEq<'b, 'c, Logic, <A as Application<Logic>>::Mem>,
            >,
        >,
    > + 'static;
/// `λb. ∀c. …`
pub type ApplyUniqueView2<'f, 'a, Logic, A> = dyn for<'b> View<
        'b,
        Output = <Logic as FirstOrder>::ForAll<ApplyUniqueView3<'f, 'a, 'b, Logic, A>>,
    > + 'static;
/// `λa. ∀b ∀c. …`
pub type ApplyUniqueView1<'f, Logic, A> = dyn for<'a> View<
        'a,
        Output = <Logic as FirstOrder>::ForAll<ApplyUniqueView2<'f, 'a, Logic, A>>,
    > + 'static;
/// `λf. ∀a ∀b ∀c. …`
pub type ApplyUniqueView<Logic, A> = dyn for<'f> View<
        'f,
        Output = <Logic as FirstOrder>::ForAll<ApplyUniqueView1<'f, Logic, A>>,
    > + 'static;

/// `∀f ∀a ∀b ∀c. IsFunction(f) → (f(a)=b ∧ f(a)=c) → b = c` — **proved**.
///
/// A function has at most one value at each argument: the defining property,
/// unpacked from behind its quantifiers into usable form.
pub fn apply_unique<Logic, A>() -> Cert<Logic, Logic::ForAll<ApplyUniqueView<Logic, A>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    forall_intro(ApplyUnique::<Logic, A>(PhantomData))
}

struct ApplyUnique<Logic, A: ?Sized>(PhantomData<(Logic, *const A)>);
unit_clone!(ApplyUnique<>);

impl<Logic, A, Q> Generalise<Logic, Q> for ApplyUnique<Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'f> View<'f, Output = Logic::ForAll<ApplyUniqueView1<'f, Logic, A>>> + ?Sized,
{
    fn prove<'f>(self) -> Cert<Logic, <Q as View<'f>>::Output> {
        forall_intro::<Logic, ApplyUniqueView1<'f, Logic, A>, _>(ApplyUnique1::<'f, Logic, A>(
            PhantomData,
        ))
    }
}

struct ApplyUnique1<'f, Logic, A: ?Sized>(PhantomData<(&'f (), Logic, *const A)>);
unit_clone!(ApplyUnique1<'f>);

impl<'f, Logic, A, Q> Generalise<Logic, Q> for ApplyUnique1<'f, Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = Logic::ForAll<ApplyUniqueView2<'f, 'a, Logic, A>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro::<Logic, ApplyUniqueView2<'f, 'a, Logic, A>, _>(ApplyUnique2::<
            'f,
            'a,
            Logic,
            A,
        >(PhantomData))
    }
}

struct ApplyUnique2<'f, 'a, Logic, A: ?Sized>(PhantomData<(&'f (), &'a (), Logic, *const A)>);
unit_clone!(ApplyUnique2<'f, 'a>);

impl<'f, 'a, Logic, A, Q> Generalise<Logic, Q> for ApplyUnique2<'f, 'a, Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = Logic::ForAll<ApplyUniqueView3<'f, 'a, 'b, Logic, A>>> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, <Q as View<'b>>::Output> {
        forall_intro::<Logic, ApplyUniqueView3<'f, 'a, 'b, Logic, A>, _>(ApplyUnique3::<
            'f,
            'a,
            'b,
            Logic,
            A,
        >(PhantomData))
    }
}

struct ApplyUnique3<'f, 'a, 'b, Logic, A: ?Sized>(
    PhantomData<(&'f (), &'a (), &'b (), Logic, *const A)>,
);
unit_clone!(ApplyUnique3<'f, 'a, 'b>);

impl<'f, 'a, 'b, Logic, A, Q> Generalise<Logic, Q> for ApplyUnique3<'f, 'a, 'b, Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'c> View<
            'c,
            Output = Logic::Imply<
                A::IsFunction<'f>,
                Logic::Imply<
                    Logic::And<A::App<'f, 'a, 'b>, A::App<'f, 'a, 'c>>,
                    ExtEq<'b, 'c, Logic, A::Mem>,
                >,
            >,
        > + ?Sized,
{
    fn prove<'c>(self) -> Cert<Logic, <Q as View<'c>>::Output> {
        apply_unique_at::<'f, 'a, 'b, 'c, Logic, A>()
    }
}

/// `λb. f(a) = b → a ∈ dom f`
pub type InDomainView2<'f, 'a, Logic, A> = dyn for<'b> View<
        'b,
        Output = <Logic as Imply>::Imply<
            <A as Application<Logic>>::App<'f, 'a, 'b>,
            <A as Application<Logic>>::InDomain<'f, 'a>,
        >,
    > + 'static;
/// `λa. ∀b. f(a) = b → a ∈ dom f`
pub type InDomainView1<'f, Logic, A> = dyn for<'a> View<
        'a,
        Output = <Logic as FirstOrder>::ForAll<InDomainView2<'f, 'a, Logic, A>>,
    > + 'static;
/// `λf. ∀a ∀b. f(a) = b → a ∈ dom f`
pub type InDomainView<Logic, A> = dyn for<'f> View<
        'f,
        Output = <Logic as FirstOrder>::ForAll<InDomainView1<'f, Logic, A>>,
    > + 'static;

/// `∀f ∀a ∀b. f(a) = b → a ∈ dom f` — **proved**.
///
/// Anything a function maps somewhere is in its domain.
pub fn in_domain<Logic, A>() -> Cert<Logic, Logic::ForAll<InDomainView<Logic, A>>>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
{
    forall_intro(InDomain::<Logic, A>(PhantomData))
}

struct InDomain<Logic, A: ?Sized>(PhantomData<(Logic, *const A)>);
unit_clone!(InDomain<>);

impl<Logic, A, Q> Generalise<Logic, Q> for InDomain<Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'f> View<'f, Output = Logic::ForAll<InDomainView1<'f, Logic, A>>> + ?Sized,
{
    fn prove<'f>(self) -> Cert<Logic, <Q as View<'f>>::Output> {
        forall_intro::<Logic, InDomainView1<'f, Logic, A>, _>(InDomain1::<'f, Logic, A>(
            PhantomData,
        ))
    }
}

struct InDomain1<'f, Logic, A: ?Sized>(PhantomData<(&'f (), Logic, *const A)>);
unit_clone!(InDomain1<'f>);

impl<'f, Logic, A, Q> Generalise<Logic, Q> for InDomain1<'f, Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'a> View<'a, Output = Logic::ForAll<InDomainView2<'f, 'a, Logic, A>>> + ?Sized,
{
    fn prove<'a>(self) -> Cert<Logic, <Q as View<'a>>::Output> {
        forall_intro::<Logic, InDomainView2<'f, 'a, Logic, A>, _>(InDomain2::<'f, 'a, Logic, A>(
            PhantomData,
        ))
    }
}

struct InDomain2<'f, 'a, Logic, A: ?Sized>(PhantomData<(&'f (), &'a (), Logic, *const A)>);
unit_clone!(InDomain2<'f, 'a>);

impl<'f, 'a, Logic, A, Q> Generalise<Logic, Q> for InDomain2<'f, 'a, Logic, A>
where
    Logic: PropLogic + And + FirstOrder,
    A: Application<Logic> + ?Sized,
    Q: for<'b> View<'b, Output = Logic::Imply<A::App<'f, 'a, 'b>, A::InDomain<'f, 'a>>> + ?Sized,
{
    fn prove<'b>(self) -> Cert<Logic, <Q as View<'b>>::Output> {
        in_domain_at::<'f, 'a, 'b, Logic, A>()
    }
}
