use crate::logic::prop::{And, FirstOrder, Imply};
use crate::macros::thm;
use crate::rel::Set;
use crate::rel::poset::{BinRel, Equivalence, Reflexive, Symmetric, Transitive};

/// The definitional half of equality: name the equivalence relation that
/// serves as this logic's `=`.
///
/// This is the only trait a logic implements by hand. It carries no `Logic`
/// parameter -- `Self` *is* the logic. Equality is used too often and sits too
/// deep to be one structure among many: in a set theory it applies to every
/// object, because every object is a set.
///
/// Reflexivity, symmetry and transitivity are deliberately *not* stated here.
/// They come from [`EqRel`](EqualityDef::EqRel) being an [`Equivalence`], so
/// the definition of an equivalence relation lives in exactly one place and
/// anything proved generically about equivalence relations applies to equality
/// for free.
pub trait EqualityDef: Imply + FirstOrder {
    /// The relation that serves as equality, as a structure. Its domain
    /// ([`Set::El`]) is what counts as an object of this logic.
    ///
    /// Nothing here distinguishes equality from any other equivalence
    /// relation. What does is substitution, and that is deliberately not a
    /// method: as a schema over every `P: View` it would assert that *set*
    /// equality buys the total congruence rustc gives *definitional* equality,
    /// over all type-level constructions rather than over formulas of the
    /// language. It is proved per-predicate instead, by induction on how the
    /// predicate is built.
    type EqRel: Equivalence<Self>;
}

/// Equality spelled directly on the logic.
///
/// Pure convenience: every method proxies to [`EqualityDef::EqRel`]'s
/// [`Equivalence`] impl, and the blanket impl below is the only one there will
/// ever be. It exists so that call sites write `Logic::Eq<'a, 'b>` rather than
/// `<Logic::EqRel as BinRel>::Rel<'a, 'b>`, and so that `Self::Rel` never
/// leaks onto the logic itself.
///
/// [`Eq`](Equality::Eq) is an *associated type*, never a type alias, so
/// `<L as Equality>::Eq<'a, 'b>` at a type parameter `L` is a rigid projection
/// rustc cannot normalise. That is what keeps proof terms small; see
/// [`crate::rel::set`] for the measurement.
pub trait Equality: EqualityDef {
    /// `'a` is an object of this logic -- what equality ranges over.
    type El<'a>;

    /// Equality relation between two terms at lifetimes `'a` and `'b`
    type Eq<'a, 'b>;

    /// Reflexivity: forall x. x = x
    fn eq_refl() -> thm!({ Self }, 'x: { Self::El::<'x> }, Self::Eq::<'x, 'x>);

    /// Symmetry: forall x y. x = y -> y = x
    fn eq_symm() -> thm!(
        { Self },
        'x: { Self::El::<'x> },
        'y: { Self::El::<'y> },
        Self::Eq::<'x, 'y> >>= Self::Eq::<'y, 'x>
    );

    /// Transitivity: forall x y z. x = y -> y = z -> x = z
    fn eq_trans() -> thm!(
        { Self },
        'x: { Self::El::<'x> },
        'y: { Self::El::<'y> },
        'z: { Self::El::<'z> },
        Self::Eq::<'x, 'y> >>= Self::Eq::<'y, 'z> >>= Self::Eq::<'x, 'z>
    );
}

impl<L: EqualityDef> Equality for L {
    type El<'a> = <L::EqRel as Set>::El<'a>;
    type Eq<'a, 'b> = <L::EqRel as BinRel>::Rel<'a, 'b>;

    fn eq_refl() -> thm!({ Self }, 'x: { Self::El::<'x> }, Self::Eq::<'x, 'x>) {
        <L::EqRel as Reflexive<L>>::refl()
    }

    fn eq_symm() -> thm!(
        { Self },
        'x: { Self::El::<'x> },
        'y: { Self::El::<'y> },
        Self::Eq::<'x, 'y> >>= Self::Eq::<'y, 'x>
    ) {
        <L::EqRel as Symmetric<L>>::sym()
    }

    fn eq_trans() -> thm!(
        { Self },
        'x: { Self::El::<'x> },
        'y: { Self::El::<'y> },
        'z: { Self::El::<'z> },
        Self::Eq::<'x, 'y> >>= Self::Eq::<'y, 'z> >>= Self::Eq::<'x, 'z>
    ) {
        <L::EqRel as Transitive<L>>::transitive()
    }
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
        Logic::Eq::<'y, 'z>
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
        ForAll::<'x, 'y, 'z>((Self::F::<'x, 'z> && Self::F::<'y, 'z>).imply(Logic::Eq::<'x, 'y>))
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
    const fn need_equality<L: Equality>() {}

    /// Defining the relation is all a logic has to do: the four `eq_*`
    /// theorems and `El`/`Eq` follow with no further obligation.
    const fn def_gives_equality<L: EqualityDef>() {
        need_equality::<L>();
    }
};
