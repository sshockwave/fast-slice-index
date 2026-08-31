//! A selected set of axioms
//!
//! Rules: always use new wrapper types for certs
//! to prevent custom construction when the associated types are leaked.
#![expect(unsafe_code)]

use super::Axiomize;
use crate::logic::prop::{
    And, Cert, Imply, Intuitionistic, PropLogic, neg::Contraposition, reflexive,
};
use std::convert::Infallible;

use self::sealed_cert::cert;
mod sealed_cert {
    use super::{Axiomize, Cert, Imply};
    use ::core::marker::PhantomData;

    /// A new wrapper type to prevent custom construction.
    pub struct PhantomCert<T>(PhantomData<T>);

    impl<T> Clone for PhantomCert<T> {
        fn clone(&self) -> Self {
            PhantomCert(PhantomData)
        }
    }

    pub unsafe fn cert<'l, T: Clone>() -> Cert<'l, Axiomize, T> {
        Cert::new(PhantomCert(PhantomData))
    }

    pub struct Infer<P, Q>(PhantomData<(P, Q)>);

    impl<P, Q> Clone for Infer<P, Q> {
        fn clone(&self) -> Self {
            Infer(PhantomData)
        }
    }

    impl<'l> Imply<'l> for Axiomize {
        type Imply<P: 'l, Q: 'l> = Infer<P, Q>;
        type Cert<P: Clone + 'l> = PhantomCert<P>;
        fn mp<P: Clone, Q: Clone + 'l>(
            _pq: Cert<'l, Self, Self::Imply<P, Q>>,
            _p: Cert<'l, Self, P>,
        ) -> Cert<'l, Self, Q> {
            unsafe { cert() }
        }
    }
}

impl<'l> PropLogic<'l> for Axiomize {
    fn l1<P: Clone + 'l, Q>() -> Cert<'l, Self, Self::Imply<P, Self::Imply<Q, P>>> {
        unsafe { cert() }
    }
    fn l2<P: Clone + 'l, Q: 'l, R: 'l>() -> Cert<
        'l,
        Self,
        Self::Imply<
            Self::Imply<P, Self::Imply<Q, R>>,
            Self::Imply<Self::Imply<P, Q>, Self::Imply<P, R>>,
        >,
    > {
        unsafe { cert() }
    }
}

impl<'l> Contraposition<'l> for Axiomize {
    fn l3<P: Clone + 'l, Q: Clone + 'l>()
    -> Cert<'l, Self, Self::Imply<Self::Imply<Self::Neg<P>, Self::Neg<Q>>, Self::Imply<Q, P>>> {
        unsafe { cert() }
    }
}

impl<'l> Intuitionistic<'l> for Axiomize {
    type False = Infallible;
    fn explosion<P: Clone>() -> Cert<'l, Self, Self::Imply<Self::False, P>> {
        unsafe { cert() }
    }
    fn neg_def<P: Clone>()
    -> Cert<'l, Self, crate::logic::prop::Iff<'l, Self, Self::Neg<P>, Self::Imply<P, Self::False>>>
    {
        <Self as And<'l>>::and_intro()
            .mp(reflexive())
            .mp(reflexive())
    }
}

mod sealed_fol {
    use super::{Axiomize, cert};
    use crate::logic::prop::{Cert, FirstOrder, View};
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

    impl<'l> FirstOrder<'l> for Axiomize {
        type ForAll<P: for<'x> View<'x> + ?Sized + 'l> = ForAll<P>;
        type Exists<P: for<'x> View<'x> + ?Sized> = Exists<P>;
        fn exists_elim<'t: 'l, P: for<'x> crate::logic::prop::View<'x> + ?Sized, Q>()
        -> Cert<'l, Self, Self::Imply<<P as crate::logic::prop::View<'t>>::Output, Self::Exists<P>>>
        where
            <P as crate::logic::prop::View<'t>>::Output: Clone,
        {
            unsafe { cert() }
        }
        fn exists_gen<
            P: for<'x> crate::logic::prop::View<'x> + ?Sized + 'l,
            Q,
            S: crate::logic::prop::ExistsProof<'l, Self, P, Q>,
        >(
            _: S,
        ) -> Cert<'l, Self, Self::Imply<Self::Exists<P>, Q>> {
            unsafe { cert() }
        }
        fn forall_elim<'t: 'l, P: for<'x> crate::logic::prop::View<'x> + ?Sized>()
        -> Cert<'l, Self, Self::Imply<Self::ForAll<P>, <P as crate::logic::prop::View<'t>>::Output>>
        where
            <P as crate::logic::prop::View<'t>>::Output: Clone,
        {
            unsafe { cert() }
        }
        fn forall_gen<
            P: Clone,
            Q: for<'x> crate::logic::prop::View<'x, Output: Clone> + ?Sized,
            S: crate::logic::prop::ForAllProof<'l, Self, P, Q>,
        >(
            _: S,
        ) -> Cert<'l, Self, Self::Imply<P, Self::ForAll<Q>>> {
            unsafe { cert() }
        }
    }
}
