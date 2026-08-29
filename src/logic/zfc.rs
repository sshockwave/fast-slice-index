use crate::logic::prop::{And, Cert, Iff, Imply, Negation, View};

pub trait Spec<'x, 'w, 'z> {
    type Output;
}

pub type Empty<'l, 'x, P> =
    dyn for<'y> View<'y, Output = <P as Negation<'l>>::Neg<<P as ZF<'l>>::In<'y, 'x>>> + 'l;

pub type Disjoint<'l, 'x, 'y, P> = dyn for<'z> View<
        'z,
        Output = <P as Imply<'l>>::Imply<
            <P as ZF<'l>>::In<'z, 'x>,
            <P as Negation<'l>>::Neg<<P as ZF<'l>>::In<'z, 'y>>,
        >,
    > + 'l;

pub type Subset<'l, 'x, 'y, P> = dyn for<'z> View<
        'z,
        Output = <P as Imply<'l>>::Imply<<P as ZF<'l>>::In<'z, 'x>, <P as ZF<'l>>::In<'z, 'y>>,
    > + 'l;

pub trait ZF<'l>: Negation<'l> + And<'l> + 'l {
    type In<'b: 'l, 'c: 'l>;

    // First-order Logic
    fn instantiate<'x, V: for<'y> View<'y, Output: Clone>>()
    -> Cert<'l, Self, <V as View<'x>>::Output>;

    fn extensionality() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = Self::Imply<
                    &'l dyn for<'z> View<
                        'z,
                        Output = Iff<'l, Self, Self::In<'z, 'x>, Self::In<'z, 'y>>,
                    >,
                    &'l dyn for<'w> View<
                        'w,
                        Output = Iff<'l, Self, Self::In<'w, 'x>, Self::In<'w, 'y>>,
                    >,
                >,
            >,
        >,
    >;

    fn regularity() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = Self::Imply<
                dyn for<'y> View<
                        'y,
                        Output = Self::Neg<
                            Self::Imply<Disjoint<'y, 'x, 'y, Self>, Self::Neg<Self::In<'y, 'x>>>,
                        >,
                    > + 'l,
                // We can't find a disjoint member, the set must be empty.
                Empty<'l, 'x, Self>,
            >,
        >,
    >;

    fn specification<S: for<'x, 'w, 'z> Spec<'x, 'w, 'z>>() -> dyn for<'z> View<
            'z,
            Output = dyn for<'w> View<
                'w,
                Output = Self::Neg<
                    dyn for<'y> View<
                            'y,
                            Output = Self::Neg<
                                dyn for<'x> View<
                                        'x,
                                        Output = Iff<
                                            'l,
                                            Self,
                                            Self::In<'x, 'z>,
                                            <S as Spec<'x, 'w, 'z>>::Output,
                                        >,
                                    > + 'l,
                            >,
                        > + 'l,
                >,
            > + 'l,
        >;

    fn pairing() -> dyn for<'x> View<
            'x,
            Output = dyn for<'y> View<
                'y,
                Output = Self::Neg<
                    dyn for<'z> View<
                            'z,
                            Output = Self::Imply<Self::In<'x, 'z>, Self::Neg<Self::In<'y, 'z>>>,
                        > + 'l,
                >,
            > + 'l,
        > + 'l;

    fn union() -> dyn for<'f> View<
            'f,
            Output = Self::Neg<
                dyn for<'a> View<
                        'a,
                        Output = Self::Neg<
                            dyn for<'y> View<
                                    'y,
                                    Output = dyn for<'x> View<
                                        'x,
                                        Output = Self::Imply<
                                            Self::And<Self::In<'x, 'y>, Self::In<'y, 'f>>,
                                            Self::In<'x, 'a>,
                                        >,
                                    > + 'l,
                                > + 'l,
                        >,
                    > + 'l,
            >,
        >;

    // TODO: replacement
    // TODO: infinity

    fn power_set() -> dyn for<'x> View<
            'x,
            Output = Self::Neg<
                dyn for<'y> View<
                        'y,
                        Output = Self::Neg<
                            dyn for<'z> View<
                                    'z,
                                    Output = Self::Imply<
                                        Subset<'l, 'z, 'x, Self>,
                                        Self::In<'z, 'y>,
                                    >,
                                > + 'l,
                        >,
                    > + 'l,
            >,
        >;
}
