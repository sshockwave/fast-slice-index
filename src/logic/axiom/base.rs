//! A selected set of axioms
//!
//! Rules: always use new wrapper types for certs
//! to prevent custom construction when the associated types are leaked.
#![expect(unsafe_code)]

use super::Axiomize;
use crate::logic::prop::{
    And, Cert, FirstOrder, Imply, Intuitionistic, PropLogic, View, neg::Contraposition, reflexive,
};
use std::convert::Infallible;

use self::sealed_cert::{PhantomCert, cert};
mod sealed_cert {
    use super::{Axiomize, Cert};
    use ::core::marker::PhantomData;

    /// A new wrapper type to prevent custom construction.
    pub struct PhantomCert<T>(PhantomData<T>);

    impl<T> Clone for PhantomCert<T> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<T> Copy for PhantomCert<T> {}

    pub unsafe fn cert<T>() -> Cert<Axiomize, T> {
        Cert::new(PhantomCert(PhantomData))
    }
}

impl Imply for Axiomize {
    type Imply<P, Q> = Infer<P, Q>;
    type Cert<P> = PhantomCert<P>;
    fn mp<P, Q>(pq: Cert<Self, Self::Imply<P, Q>>, p: Cert<Self, P>) -> Cert<Self, Q> {
        Cert::new(pq.into_inner().mp(p.into_inner()))
    }
}

use self::sealed_infer::Infer;
mod sealed_infer {
    use ::core::marker::PhantomData;

    pub struct Infer<P, Q>(PhantomData<(P, Q)>);
}

impl<P, Q> Infer<P, Q> {
    /// Feels like introducing many assumptions from Rust,
    /// But we need to admit the axioms anyway,
    /// so why not let the compiler do another round of sanity check?
    /// Set to private so that we don't expose anything other than the axioms.
    fn new<F>(proof: F) -> PhantomCert<Self>
    where
        F: FnOnce(PhantomCert<P>) -> PhantomCert<Q>,
    {
        // Actually run once to make sure the proof terminates
        proof(unsafe { cert() }.into_inner());
        unsafe { cert() }.into_inner()
    }
}
impl<P, Q> PhantomCert<Infer<P, Q>> {
    fn mp(self, _: PhantomCert<P>) -> PhantomCert<Q> {
        // The proof is assumed to be correct and we don't check it a second time.
        unsafe { cert() }.into_inner()
    }
}

impl PropLogic for Axiomize {
    fn l1<P, Q>() -> Cert<Self, Self::Imply<P, Self::Imply<Q, P>>> {
        Cert::new(Infer::new(|p| Infer::new(|_| p)))
    }
    fn l2<P, Q, R>() -> Cert<
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        Cert::new(Infer::new(|pqr| {
            Infer::new(|pq| Infer::new(|p| pqr.mp(p).mp(pq.mp(p))))
        }))
    }
}

impl Contraposition for Axiomize {
    fn l3<P, Q>()
    -> Cert<Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        unsafe { cert() }
    }
}

impl Intuitionistic for Axiomize {
    type False = Infallible;
    fn explosion<P>() -> Cert<Self, Self::Imply<Self::False, P>> {
        unsafe { cert() }
    }
    fn neg_def<P>()
    -> Cert<Self, crate::logic::prop::Iff<Self, Self::Neg<P>, Self::Imply<P, Self::False>>> {
        <Self as And>::and_intro().mp(reflexive()).mp(reflexive())
    }
}

use sealed_fol::{Exists, ForAll};
mod sealed_fol {
    use ::core::marker::PhantomData;

    pub struct ForAll<P: ?Sized>(PhantomData<P>);
    impl<P: ?Sized> Clone for ForAll<P> {
        fn clone(&self) -> Self {
            ForAll(PhantomData)
        }
    }

    pub struct Exists<P: ?Sized>(PhantomData<P>);
    impl<P: ?Sized> Clone for Exists<P> {
        fn clone(&self) -> Self {
            Exists(PhantomData)
        }
    }
}

impl FirstOrder for Axiomize {
    type ForAll<P: for<'x> View<'x> + ?Sized> = ForAll<P>;
    type Exists<P: for<'x> View<'x> + ?Sized> = Exists<P>;
    fn exists_elim<'t, P: for<'x> crate::logic::prop::View<'x> + ?Sized, Q>()
    -> Cert<Self, Self::Imply<<P as crate::logic::prop::View<'t>>::Output, Self::Exists<P>>> {
        unsafe { cert() }
    }
    fn exists_gen<
        P: for<'x> crate::logic::prop::View<'x> + ?Sized,
        Q,
        S: crate::logic::prop::ExistsProof<Self, P, Q>,
    >(
        _: S,
    ) -> Cert<Self, Self::Imply<Self::Exists<P>, Q>> {
        unsafe { cert() }
    }
    fn forall_elim<'t, P: for<'x> crate::logic::prop::View<'x> + ?Sized>()
    -> Cert<Self, Self::Imply<Self::ForAll<P>, <P as crate::logic::prop::View<'t>>::Output>> {
        unsafe { cert() }
    }
    fn forall_gen<
        P,
        Q: for<'x> crate::logic::prop::View<'x> + ?Sized,
        S: crate::logic::prop::ForAllProof<Self, P, Q>,
    >(
        _: S,
    ) -> Cert<Self, Self::Imply<P, Self::ForAll<Q>>> {
        unsafe { cert() }
    }
}
