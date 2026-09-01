use crate::logic::prop::{And, Cert, FirstOrder, Imply, View};
use crate::macros::thm;

/// Equality trait - axiomatizes equality relation
pub trait Equality: Imply {
    /// Equality relation between two terms at lifetimes 'a and 'b
    type Eq<'a, 'b>;

    /// Reflexivity: ∀x. x = x
    fn eq_refl() -> Cert<Self, &'static dyn for<'x> View<'x, Output = Self::Eq<'x, 'x>>>
    where
        Self: 'static;

    /// Symmetry: ∀x ∀y. x = y → y = x
    fn eq_symm() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = Self::Imply<Self::Eq<'x, 'y>, Self::Eq<'y, 'x>>,
            >,
        >,
    >
    where
        Self: 'static;

    /// Transitivity: ∀x ∀y ∀z. x = y → y = z → x = z
    fn eq_trans() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = &'static dyn for<'z> View<
                    'z,
                    Output = Self::Imply<
                        Self::Eq<'x, 'y>,
                        Self::Imply<Self::Eq<'y, 'z>, Self::Eq<'x, 'z>>,
                    >,
                >,
            >,
        >,
    >
    where
        Self: 'static;

    /// Substitution (Leibniz's law): ∀x ∀y. x = y → (P(x) → P(y))
    /// For any predicate P
    fn eq_subst<P>() -> Cert<
        Self,
        &'static dyn for<'x> View<
            'x,
            Output = &'static dyn for<'y> View<
                'y,
                Output = Self::Imply<
                    Self::Eq<'x, 'y>,
                    Self::Imply<<P as View<'x>>::Output, <P as View<'y>>::Output>,
                >,
            >,
        >,
    >
    where
        P: for<'a> View<'a> + 'static,
        Self: 'static;
}

/// Function trait: A binary relation F that is total and functional
///
/// Generic over Eq: the equality relation used in the codomain
///
/// WARNING: We do NOT quantify over all possible F generically.
/// Instead, each specific function (like Succ) is a concrete associated type.
/// This avoids impredicativity issues.
pub trait Function<Eq>
where
    Eq: Equality + FirstOrder + And,
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
        { Eq },
        'x: { Self::Dom::<'x> },
        Exists::<'y>(Self::Codom::<'y> && Self::F::<'x, 'y>)
    );

    /// Functional (single-valued): ∀x ∀y ∀z. F(x,y) ∧ F(x,z) → y = z
    /// Each input maps to at most one output
    fn functional() -> thm!(
        { Eq },
        'x: { Self::Dom::<'x> },
        'y: { Self::F::<'x, 'y> },
        'z: { Self::F::<'x, 'z> },
        Eq::Eq::<'y, 'z>
    );
}

/// Injection trait: A function that is injective
pub trait Injection<Eq>: Function<Eq>
where
    Eq: Equality + FirstOrder + And,
{
    /// Injective: ∀x ∀y ∀z. F(x,z) ∧ F(y,z) → x = y
    /// Different inputs map to different outputs
    fn injective() -> thm!(
        { Eq },
        ForAll::<'x, 'y, 'z>((Self::F::<'x, 'z> && Self::F::<'y, 'z>).imply(Eq::Eq::<'x, 'y>))
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
// 4. Eq is a GENERIC PARAMETER
//    - Allows different equality relations
//    - More composable and flexible
//    - Still resolved at compile time
//
// This is predicative and consistent.
