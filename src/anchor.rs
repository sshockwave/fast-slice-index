use std::marker::PhantomData;

/// A numeric token with a branded lifetime 'id
#[derive(Copy, Clone)]
pub struct Anchor<'id, I = usize> {
    value: I,
    _marker: PhantomData<&'id ()>,
}

impl<'id, I> Anchor<'id, I> {
    /// Get the raw value
    #[inline]
    pub fn get(&self) -> I
    where
        I: Copy,
    {
        self.value
    }

    /// Create a scope with a numeric token
    pub fn scope<R>(value: I, f: impl FnOnce(Anchor<'id, I>) -> R) -> R {
        f(Anchor {
            value,
            _marker: PhantomData,
        })
    }
}
