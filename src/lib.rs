pub mod algebra;
pub mod logic;
pub mod utils;

mod macros {
    // Re-export pred procedural macro from the logic-macros crate
    pub(crate) use ::logic_macros::{pred, thm};
}
