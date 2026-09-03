//! [`Axiomize`]'s functions, packaged as a structure.
//!
//! The companion to [`super::equality`], and the same division of labour: the
//! mathematics — that a function has at most one value, that a value witnesses
//! membership of the domain — is in [`crate::rel::func`], generic over the
//! application relation. All this module does is say which relation
//! [`Axiomize`] means by `f(a) = b`, and discharge the three unfoldings that
//! connect the associated notions to their generic spellings.
//!
//! Each unfolding is [`reflexive`] in both directions, because at `Axiomize`
//! every notion *is* its definition. That triviality is exactly what is not
//! available generically: a proof written against the concrete aliases would
//! mention the whole Kuratowski expansion at every occurrence, and
//! `mir_borrowck` cost scales with that.
#![forbid(unsafe_code)]

use super::Axiomize;
use crate::logic::prop::{And, Cert, FirstOrder, Iff, Imply, reflexive};
use crate::macros::pred;
use crate::rel::func::{Application, DomainView, SvView};
use crate::rel::pair::Pairing;

/// Application on the universe of sets: `⟨a, b⟩ ∈ f`.
impl Application<Axiomize> for Axiomize {
    type Mem = Axiomize;

    type App<'f, 'a, 'b> = pred!(
        { Axiomize },
        Exists::<'p, 'u, 'v>(
            <Axiomize as Pairing<Axiomize>>::Singleton::<'u, 'a>
                && (<Axiomize as Pairing<Axiomize>>::Pair::<'v, 'a, 'b>
                    && (<Axiomize as Pairing<Axiomize>>::Pair::<'p, 'u, 'v>
                        && <Axiomize as crate::rel::ext::Membership<Axiomize>>::In::<'p, 'f>))
        )
    );
    type IsRel<'f> = pred!(
        { Axiomize },
        ForAll::<'z>(<Axiomize as crate::rel::ext::Membership<Axiomize>>::In::<'z, 'f>
            >>= Exists::<'a, 'b>(<Axiomize as Application<Axiomize>>::App::<'z, 'a, 'b>))
    );
    type IsSingleValued<'f> = <Axiomize as FirstOrder>::ForAll<SvView<'f, Axiomize, Axiomize>>;
    type IsFunction<'f> = <Axiomize as And>::And<
        <Axiomize as Application<Axiomize>>::IsRel<'f>,
        <Axiomize as Application<Axiomize>>::IsSingleValued<'f>,
    >;
    type InDomain<'f, 'a> = <Axiomize as FirstOrder>::Exists<DomainView<'f, 'a, Axiomize, Axiomize>>;

    fn function_iff<'f>() -> Cert<
        Axiomize,
        Iff<Axiomize, Self::IsFunction<'f>, <Axiomize as And>::And<Self::IsRel<'f>, Self::IsSingleValued<'f>>>,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }

    fn single_valued_iff<'f>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            Self::IsSingleValued<'f>,
            <Axiomize as FirstOrder>::ForAll<SvView<'f, Axiomize, Axiomize>>,
        >,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }

    fn in_domain_iff<'f, 'a>() -> Cert<
        Axiomize,
        Iff<
            Axiomize,
            Self::InDomain<'f, 'a>,
            <Axiomize as FirstOrder>::Exists<DomainView<'f, 'a, Axiomize, Self>>,
        >,
    > {
        <Axiomize as And>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }
}

/// The three unfoldings above are `reflexive` in both directions only because
/// each associated notion is spelled directly by its generic definition.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
fn notions_match_the_language<'f, 'a, 'b, 'c>(
    s: Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SvView<'f, Axiomize, Axiomize>>>,
    d: Cert<Axiomize, <Axiomize as FirstOrder>::Exists<DomainView<'f, 'a, Axiomize, Axiomize>>>,
    e: Cert<Axiomize, <Axiomize as Imply>::Imply<<Axiomize as Application<Axiomize>>::App<'f, 'a, 'b>, crate::rel::ext::ExtEq<'b, 'c, Axiomize, Axiomize>>>,
) -> (
    Cert<Axiomize, <Axiomize as FirstOrder>::ForAll<SvView<'f, Axiomize, Axiomize>>>,
    Cert<Axiomize, <Axiomize as FirstOrder>::Exists<DomainView<'f, 'a, Axiomize, Axiomize>>>,
    Cert<
        Axiomize,
        <Axiomize as Imply>::Imply<
            <Axiomize as Application<Axiomize>>::App<'f, 'a, 'b>,
            crate::rel::ext::ExtEq<'b, 'c, Axiomize, <Axiomize as Application<Axiomize>>::Mem>,
        >,
    >,
) {
    (s, d, e)
}
