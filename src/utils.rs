#![expect(unsafe_code)]
use ::core::marker::PhantomData;

pub struct TrustedOption<'a, T>(&'a mut Option<T>);
pub struct IsSome<'a>(PhantomData<&'a ()>);

impl<'a, T> TrustedOption<'a, T> {
    pub fn set(&mut self, value: T) -> IsSome<'a> {
        *self.0 = Some(value);
        IsSome(PhantomData)
    }
    pub fn take(&mut self, _proof: IsSome<'a>) -> T {
        let value = self.0.take();
        unsafe { value.unwrap_unchecked() }
    }
}

pub fn option_scope<T, R>(f: impl for<'x> FnOnce(TrustedOption<'x, T>) -> R) -> R {
    let mut option = None;
    f(TrustedOption(&mut option))
}
