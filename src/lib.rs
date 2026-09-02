pub mod algebra;
pub mod concrete;
pub mod logic;
pub mod rel;

mod macros {
    // Re-export pred procedural macro from the logic-macros crate
    pub(crate) use ::logic_macros::{pred, thm};
}
