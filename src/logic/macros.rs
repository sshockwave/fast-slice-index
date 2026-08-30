// Re-export pred procedural macro from the logic-macros crate
pub(crate) use ::logic_macros::{parenthesize, pred};

// Keep thm as a declarative macro that calls pred
macro_rules! thm {
    ($l:lifetime: {}, $($P:tt)+) => {
        $crate::logic::prop::Cert<$l, Self, $crate::logic::macros::pred!($l, $($P)+)>
    };
}

pub(crate) use thm;
