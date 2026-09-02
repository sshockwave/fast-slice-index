pub mod desc;
pub mod empty;
pub mod eq;
pub mod ext;
pub mod poset;
pub mod set;

pub trait Set {
    /// `'a` is in this set iff the predicate `El<'a>` holds
    type El<'a>;
}
