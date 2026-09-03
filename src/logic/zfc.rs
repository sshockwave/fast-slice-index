/// A binary relation schema used by replacement.
///
/// Unlike a unary predicate view, replacement needs two independently
/// quantified terms, so its parameter exposes both lifetimes through an
/// associated family.
pub trait Rel2 {
    type At<'x, 'y>;
}
