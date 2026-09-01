use crate::logic::prop::{And, Cert, Iff, Imply, Negation, View};

pub trait Spec<'x, 'w, 'z> {
    type Output;
}

pub type Empty<'x, P> = dyn for<'y> View<'y, Output = <P as Negation>::Neg<<P as ZF>::In<'y, 'x>>>;

pub type Disjoint<'x, 'y, P> = dyn for<'z> View<
        'z,
        Output = <P as Imply>::Imply<
            <P as ZF>::In<'z, 'x>,
            <P as Negation>::Neg<<P as ZF>::In<'z, 'y>>,
        >,
    >;

pub type Subset<'x, 'y, P> = dyn for<'z> View<'z, Output = <P as Imply>::Imply<<P as ZF>::In<'z, 'x>, <P as ZF>::In<'z, 'y>>>;

pub trait ZF: Negation + And
where
    Self: 'static,
{
    type In<'b, 'c>;

    fn extensionality() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = Self::Imply<
                    &'static dyn for<'z> View<
                        'z,
                        Output = Iff<Self, Self::In<'z, 'x>, Self::In<'z, 'y>>,
                    >,
                    &'static dyn for<'w> View<
                        'w,
                        Output = Iff<Self, Self::In<'w, 'x>, Self::In<'w, 'y>>,
                    >,
                >,
            >,
        >,
    >;

    fn regularity() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = Self::Imply<
                dyn for<'y> View<
                        'y,
                        Output = Self::Neg<
                            Self::Imply<Disjoint<'y, 'x, Self>, Self::Neg<Self::In<'y, 'x>>>,
                        >,
                    > + 'static,
                // We can't find a disjoint member, the set must be empty.
                Empty<'x, Self>,
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
                                            Self,
                                            Self::In<'x, 'z>,
                                            <S as Spec<'x, 'w, 'z>>::Output,
                                        >,
                                    > + 'static,
                            >,
                        > + 'static,
                >,
            > + 'static,
        >;

    fn pairing() -> dyn for<'x> View<
            'x,
            Output = dyn for<'y> View<
                'y,
                Output = Self::Neg<
                    dyn for<'z> View<
                            'z,
                            Output = Self::Imply<Self::In<'x, 'z>, Self::Neg<Self::In<'y, 'z>>>,
                        > + 'static,
                >,
            > + 'static,
        >;

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
                                    > + 'static,
                                > + 'static,
                        >,
                    > + 'static,
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
                                    Output = Self::Imply<Subset<'z, 'x, Self>, Self::In<'z, 'y>>,
                                > + 'static,
                        >,
                    > + 'static,
            >,
        >;
}
