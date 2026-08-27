#![forbid(unsafe_code)]

mod imply;

pub use self::imply::{PropLogic, PropLogicThm};
use ::core::marker::PhantomData;
