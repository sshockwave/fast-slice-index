#![expect(unsafe_code)]

use crate::logic::{Sealed, prop::Infer};
use ::core::{marker::PhantomData, mem};

#[derive(Clone, Copy)]
pub struct FastInfer<P, Q>(PhantomData<(P, Q)>);

impl<P, Q> FastInfer<P, Q> {
    pub fn new(_: impl Infer<P, Q> + Copy) -> Self {
        Self(PhantomData)
    }
}
impl<P, Q> Sealed for FastInfer<P, Q> {}
impl<P, Q: Copy> Infer<P, Q> for FastInfer<P, Q> {
    type Cert = P;
    fn mp(self, _: P) -> Q {
        const { assert!(mem::size_of::<Q>() == 0) };
        // SAFETY: All implementations of `Infer` (a sealed trait)
        // only do move or copy when creating `Q` from `P`.
        // Let's proceed as if we have run the `Infer` implementation
        // and got an instance of `Q` from `P`.
        // We can claim that `()` is a copy of the instance
        // because `Q` is zero-sized.
        // Then we can claim that we have destructed the original `Q` instance
        // because [E0184] requires that the destructor to be no-op.
        //
        // [E0184]: https://doc.rust-lang.org/error_codes/E0184.html
        unsafe { mem::transmute_copy(&()) }
    }
}
