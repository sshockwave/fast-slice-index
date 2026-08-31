pub mod poset;

pub trait Set<'l> {
    /// `'a` is in this set iff the predicate `El<'a>` holds
    type El<'a: 'l>;
}
