//! One concrete proof system, standing on assumptions we chose to make.
//!
//! This sits beside [`crate::logic`] rather than inside it because the two
//! answer different questions. `logic` is generic: its derivations are
//! parameterised over a `Logic` and hold in *any* system meeting the stated
//! bounds. [`Axiomize`] instead commits — it picks the classical connectives,
//! and [`axioms`] asserts nine set-theoretic axioms outright.
//!
//! The plan is to migrate proofs in the other direction over time: generalise a
//! theorem into `logic` where it only needs bounds, then have the axiomatised
//! version call the general proof rather than restate it. Keeping the concrete
//! system in its own module makes the remaining distance visible.
//!
//! All `unsafe` in the development is confined here, and `base::sealed_cert` is
//! private to this module, so no certificate can be minted anywhere else.

use crate::logic::prop::{And, Cert, Imply, Intuitionistic, Negation, Or, neg::ProofRing};

pub mod axioms;
mod base;
pub mod equality;
pub mod function;
pub mod lang;
pub mod pair;
pub mod succ;
pub mod theorems;

pub struct Axiomize;

impl Negation for Axiomize {
    type Neg<P> = <Self as Imply>::Imply<P, <Self as Intuitionistic>::False>;
}

impl And for Axiomize {
    type And<P, Q> = <ProofRing<Self> as And>::And<P, Q>;
    fn and_intro<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, Self::And<P, Q>>>> {
        <ProofRing<Self> as And>::and_intro().cast()
    }
    fn and_left<P, Q>() -> Cert<Self, Self::Imply<Self::And<P, Q>, P>> {
        <ProofRing<Self> as And>::and_left().cast()
    }
    fn and_right<P, Q>() -> Cert<Self, Self::Imply<Self::And<P, Q>, Q>> {
        <ProofRing<Self> as And>::and_right().cast()
    }
}

impl Or for Axiomize {
    type Or<P, Q> = <ProofRing<Self> as Or>::Or<P, Q>;
    fn or_elim<P, Q, R>() -> Cert<
        Self,
        Self::Imply<
            Self::Imply<P, R>,
            Self::Imply<Self::Imply<Q, R>, Self::Imply<Self::Or<P, Q>, R>>,
        >,
    > {
        <ProofRing<Self> as Or>::or_elim().cast()
    }
    fn or_left<P, Q>() -> Cert<Self, Self::Imply<P, Self::Or<P, Q>>> {
        <ProofRing<Self> as Or>::or_left().cast()
    }
    fn or_right<P, Q>() -> Cert<Self, Self::Imply<Q, Self::Or<P, Q>>> {
        <ProofRing<Self> as Or>::or_right().cast()
    }
}
