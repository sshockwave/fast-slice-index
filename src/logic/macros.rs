macro_rules! pred {
    ($l:lifetime, ForAll::<$x:lifetime, $($y:lifetime),+$(,)?>( $($P:tt)+ )) => {
        <Self as $crate::logic::prop::FirstOrder<$l>>::ForAll<
            dyn for<$x> $crate::logic::prop::View<
                $x,
                Output = $crate::logic::macros::pred!(
                    $l,
                    ForAll::<$($y),+>( $($P)+ )
                )
            > + $l,
        >
    };
    ($l:lifetime, ForAll::<$x:lifetime$(,)?>( $($P:tt)+ )) => {
        <Self as $crate::logic::prop::FirstOrder<$l>>::ForAll<
            dyn for<$x> $crate::logic::prop::View<
                $x,
                Output = $crate::logic::macros::pred!($l, $($P)+)
            > + $l,
        >
    };
    ($l:lifetime, ($($P:tt)*).iff($($Q:tt)*)) => {
        $crate::logic::prop::Iff<$l, Self, $crate::logic::macros::pred!($l, $($P)*), $crate::logic::macros::pred!($l, $($Q)*)>
    };
    ($l:lifetime, ($($P:tt)*).imply($($Q:tt)*)) => {
        <Self as $crate::logic::prop::Imply<$l>>::Imply<
            $crate::logic::macros::pred!($l, $($P)*),
            $crate::logic::macros::pred!($l, $($Q)*),
        >
    };
    ($l:lifetime, !$($P:tt)*) => {
        <Self as $crate::logic::prop::Negation<$l>>::Neg<$crate::logic::macros::pred!($l, $($P)*)>
    };
    ($l:lifetime, ($($P:tt)*)) => {
        $crate::logic::macros::pred!($l, $($P)*)
    };
    ($l:lifetime, $P:ty$(,)?) => {
        $P
    };
}

macro_rules! thm {
    ($l:lifetime: {}, $($P:tt)+) => {
        $crate::logic::prop::Cert<$l, Self, $crate::logic::macros::pred!($l, $($P)+)>
    };
}

pub(crate) use {pred, thm};
