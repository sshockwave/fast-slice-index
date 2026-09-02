use crate::logic::prop::{And, FirstOrder, Imply, View};
use crate::macros::thm;
use crate::rel::poset::{BinRel, Equivalence};

/// The equality symbol of the logic `L`.
///
/// Equality is `L`'s own [`BinRel::Rel`]: the logic is the universe, and its
/// distinguished relation on that universe is equality. Writing it through
/// this alias keeps the reading unambiguous where a *structure*'s relation is
/// also in scope -- `Self::Rel` is the structure's, `Eq<'a, 'b, Logic>` is the
/// logic's.
///
/// The alias is one step deep and lands on a rigid projection, so at a type
/// parameter `L` it stays a four-node term rather than expanding into a
/// definition. That is what keeps proof terms small; see [`crate::rel::set`].
pub type Eq<'a, 'b, L> = <L as BinRel>::Rel<'a, 'b>;

/// Equality: an equivalence relation on the logic's objects that additionally
/// satisfies Leibniz's law.
///
/// Unlike [`crate::rel::poset`]'s relations this takes no `Logic` parameter --
/// `Self` *is* the logic. Equality is used too often and sits too deep to be
/// one structure among many: in a set theory it applies to every object,
/// because every object is a set. So the logic carries the universe
/// ([`crate::rel::Set::El`], "is an object") and equality on it ([`BinRel::Rel`]).
///
/// Reflexivity, symmetry and transitivity are deliberately *not* restated
/// here. They are [`Equivalence<Self>`], so the definition lives in one place
/// and anything proved generically about equivalence relations applies to
/// equality for free. Because the bound's subject is `Self` it elaborates like
/// a supertrait, so a plain `L: Equality` bound carries all three with no
/// repetition at the use site.
pub trait Equality: Imply + FirstOrder + Equivalence<Self> {
    /// Substitution (Leibniz's law): forall x y. x = y -> (P(x) -> P(y)),
    /// as a schema in the predicate `P`. This is the whole difference between
    /// equality and an arbitrary equivalence relation.
    fn eq_subst<P>() -> thm!(
        { Self },
        ForAll::<'x, 'y>(
            Eq::<'x, 'y, Self> >>= <P as View<'x>>::Output >>= <P as View<'y>>::Output
        )
    )
    where
        P: for<'a> View<'a> + 'static;
}

/// Function trait: A binary relation F that is total and functional
///
/// Generic over `Logic`: the logic whose equality is used in the codomain
///
/// WARNING: We do NOT quantify over all possible F generically.
/// Instead, each specific function (like Succ) is a concrete associated type.
/// This avoids impredicativity issues.
pub trait Function<Logic>
where
    Logic: Equality + FirstOrder + And,
{
    /// The function's graph: F<'x, 'y> means "F maps x to y"
    /// This is an associated type, not a quantified predicate
    type F<'x, 'y>;

    /// Domain predicate: what x values are in the domain
    type Dom<'x>;

    /// Codomain predicate: what y values are in the codomain
    type Codom<'y>;

    /// Total: ∀x. Dom(x) → ∃y. Codom(y) ∧ F(x, y)
    /// Every element in domain has an image
    fn total() -> thm!(
        { Logic },
        'x: { Self::Dom::<'x> },
        Exists::<'y>(Self::Codom::<'y> && Self::F::<'x, 'y>)
    );

    /// Functional (single-valued): ∀x ∀y ∀z. F(x,y) ∧ F(x,z) → y = z
    /// Each input maps to at most one output
    fn functional() -> thm!(
        { Logic },
        'x: { Self::Dom::<'x> },
        'y: { Self::F::<'x, 'y> },
        'z: { Self::F::<'x, 'z> },
        Eq::<'y, 'z, Logic>
    );
}

/// Injection trait: A function that is injective
pub trait Injection<Logic>: Function<Logic>
where
    Logic: Equality + FirstOrder + And,
{
    /// Injective: ∀x ∀y ∀z. F(x,z) ∧ F(y,z) → x = y
    /// Different inputs map to different outputs
    fn injective() -> thm!(
        { Logic },
        ForAll::<'x, 'y, 'z>((Self::F::<'x, 'z> && Self::F::<'y, 'z>).imply(Eq::<'x, 'y, Logic>))
    );
}

// SAFETY NOTE: Consistency Analysis
//
// Q: Does quantifying over predicates cause impredicativity/Russell's paradox?
// A: No, because:
//
// 1. F is an ASSOCIATED TYPE, not a quantified variable
//    - Each function is a concrete type declared in the trait
//    - Not quantifying "∀F. F is a function → ..."
//    - Each F instantiation is resolved at compile time
//
// 2. Domain predicates are SPECIFIC associated types
//    - Dom<'x>, Codom<'y> are concrete associated types
//    - Not quantifying over all possible predicates
//
// 3. The universe is the DOMAIN, not the logic
//    - Lifetimes 'x, 'y range over domain elements (first-order)
//    - Predicates are type-level (metalanguage)
//    - No "set of all sets that don't contain themselves"
//
// 4. Logic is a GENERIC PARAMETER
//    - Allows different equality relations
//    - More composable and flexible
//    - Still resolved at compile time
//
// This is predicative and consistent.

/// Static witnesses: `cargo check` is the proof checker.
#[expect(dead_code, reason = "typecheck-only proof assertions")]
const _: () = {
    const fn need_equivalence<Logic, R>()
    where
        R: Equivalence<Logic>,
        Logic: Imply + FirstOrder,
    {
    }

    /// A bare `L: Equality` bound carries reflexivity, symmetry and
    /// transitivity of [`Eq`] with no repetition at the use site. This is the
    /// whole reason the bound's subject is `Self` rather than a wrapper type:
    /// only then does rustc elaborate it like a supertrait.
    const fn equality_is_an_equivalence<L: Equality>() {
        need_equivalence::<L, L>();
    }
};
