//! [`Axiomize`]'s functions, packaged as a structure.
//!
//! The companion to [`super::equality`], and the same division of labour: the
//! mathematics — that a function has at most one value, that a value witnesses
//! membership of the domain — is in [`crate::rel::func`], generic over the
//! application relation. All this module does is say which relation
//! [`Axiomize`] means by `f(a) = b`, and discharge the three unfoldings that
//! connect the opaque notions to their spellings in [`super::lang`].
//!
//! Each unfolding is [`reflexive`] in both directions, because at `Axiomize`
//! every notion *is* its definition. That triviality is exactly what is not
//! available generically: a proof written against the concrete aliases would
//! mention the whole Kuratowski expansion at every occurrence, and
//! `mir_borrowck` cost scales with that.
#![forbid(unsafe_code)]

use super::Axiomize;
use super::lang::{
    Applies, Eq, InDomain, InDomainView, IsFunction, IsRelation, IsSingleValued, SingleValuedView,
};
use crate::logic::prop::{And, Cert, FirstOrder, Iff, Imply, reflexive};
use crate::rel::func::{Application, DomainView, SvView};

/// Application on the universe of sets: `⟨a, b⟩ ∈ f`.
pub struct SetApp;

impl Application<Axiomize> for SetApp {
    type Mem = super::equality::SetIn;

    type App<'f, 'a, 'b> = Applies<'f, 'a, 'b>;
    type IsRel<'f> = IsRelation<'f>;
    type IsSingleValued<'f> = IsSingleValued<'f>;
    type IsFunction<'f> = IsFunction<'f>;
    type InDomain<'f, 'a> = InDomain<'f, 'a>;

    fn function_iff<'f>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            IsFunction<'f>,
            <Axiomize as And>::And<IsRelation<'f>, IsSingleValued<'f>>,
        >,
    > {
        <Axiomize as And>::and_intro().mp(reflexive()).mp(reflexive())
    }

    fn single_valued_iff<'f>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            IsSingleValued<'f>,
            <Axiomize as FirstOrder>::ForAll<SvView<'f, Axiomize, Self>>,
        >,
    > {
        <Axiomize as And>::and_intro().mp(reflexive()).mp(reflexive())
    }

    fn in_domain_iff<'f, 'a>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            InDomain<'f, 'a>,
            <Axiomize as FirstOrder>::Exists<DomainView<'f, 'a, Axiomize, Self>>,
        >,
    > {
        <Axiomize as And>::and_intro().mp(reflexive()).mp(reflexive())
    }
}

/// The three unfoldings above are `reflexive` in both directions only because
/// each opaque notion is spelled the same way [`super::lang`] spells it. If one
/// ever drifts, `reflexive` stops typechecking — but these say *which*
/// identification broke, rather than leaving it to be read off a trait impl.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
fn notions_match_the_language<'f, 'a, 'b, 'c>(
    s: Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SvView<'f, Axiomize, SetApp>>>,
    d: Cert<Axiomize, <Axiomize as FirstOrder>::Exists<DomainView<'f, 'a, Axiomize, SetApp>>>,
    e: Cert<Axiomize, <Axiomize as Imply>::Imply<Applies<'f, 'a, 'b>, Eq<'b, 'c>>>,
) -> (
    Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SingleValuedView<'f>>>,
    Cert<Axiomize, <Axiomize as FirstOrder>::Exists<InDomainView<'f, 'a>>>,
    Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <SetApp as Application<Axiomize>>::App<'f, 'a, 'b>,
            crate::rel::ext::ExtEq<'b, 'c, Axiomize, <SetApp as Application<Axiomize>>::Mem>,
        >,
    >,
) {
    (s, d, e)
}
