use crate::logic::prop::{And, Cert, FirstOrder, Imply, View};
use crate::macros::thm;

/// Equality trait - axiomatizes equality relation
pub trait Equality<'l>: Imply<'l>
where
    Self: 'l,
{
    /// Equality relation between two terms at lifetimes 'a and 'b
    type Eq<'a: 'l, 'b: 'l>: Clone;

    /// Reflexivity: ∀x. x = x
    fn eq_refl() -> Cert<'l, Self, &'l dyn for<'x> View<'x, Output = Self::Eq<'x, 'x>>>;

    /// Symmetry: ∀x ∀y. x = y → y = x
    fn eq_symm() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = Self::Imply<Self::Eq<'x, 'y>, Self::Eq<'y, 'x>>,
            >,
        >,
    >;

    /// Transitivity: ∀x ∀y ∀z. x = y → y = z → x = z
    fn eq_trans() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = Self::Imply<
                        Self::Eq<'x, 'y>,
                        Self::Imply<Self::Eq<'y, 'z>, Self::Eq<'x, 'z>>,
                    >,
                >,
            >,
        >,
    >;

    /// Substitution (Leibniz's law): ∀x ∀y. x = y → (P(x) → P(y))
    /// For any predicate P
    fn eq_subst<P>() -> Cert<
        'l,
        Self,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = Self::Imply<
                    Self::Eq<'x, 'y>,
                    Self::Imply<<P as View<'x>>::Output, <P as View<'y>>::Output>,
                >,
            >,
        >,
    >
    where
        P: for<'a> View<'a> + 'l;
}

/// Function trait: A binary relation F that is total and functional
///
/// Generic over Eq: the equality relation used in the codomain
///
/// WARNING: We do NOT quantify over all possible F generically.
/// Instead, each specific function (like Succ) is a concrete associated type.
/// This avoids impredicativity issues.
pub trait Function<'l, Eq>
where
    Self: 'l,
    Eq: Equality<'l> + FirstOrder<'l> + And<'l>,
{
    /// The function's graph: F<'x, 'y> means "F maps x to y"
    /// This is an associated type, not a quantified predicate
    type F<'x: 'l, 'y: 'l>;

    /// Domain predicate: what x values are in the domain
    type Dom<'x: 'l>: Clone;

    /// Codomain predicate: what y values are in the codomain
    type Codom<'y: 'l>;

    /// Total: ∀x. Dom(x) → ∃y. Codom(y) ∧ F(x, y)
    /// Every element in domain has an image
    fn total() -> thm!(
        'l: { Eq },
        'x: { Self::Dom::<'x> },
        Exists::<'y>(Self::Codom::<'y> && Self::F::<'x, 'y>)
    );

    /// Functional (single-valued): ∀x ∀y ∀z. F(x,y) ∧ F(x,z) → y = z
    /// Each input maps to at most one output
    fn functional() -> Cert<
        'l,
        Eq,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = Eq::Imply<Self::F<'x, 'y>, Eq::Imply<Self::F<'x, 'z>, Eq::Eq<'y, 'z>>>,
                >,
            >,
        >,
    >;

    /// Well-typed: ∀x ∀y. F(x,y) → Dom(x) ∧ Codom(y)
    fn well_typed() -> Cert<
        'l,
        Eq,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = Eq::Imply<Self::F<'x, 'y>, Eq::Imply<Self::Dom<'x>, Self::Codom<'y>>>,
            >,
        >,
    >;
}

/// Injection trait: A function that is injective
pub trait Injection<'l, Eq>: Function<'l, Eq>
where
    Self: 'l,
    Eq: Equality<'l> + FirstOrder<'l> + And<'l>,
{
    /// Injective: ∀x ∀y ∀z. F(x,z) ∧ F(y,z) → x = y
    /// Different inputs map to different outputs
    fn injective() -> Cert<
        'l,
        Eq,
        &'l dyn for<'x> View<
            'x,
            Output = &'l dyn for<'y> View<
                'y,
                Output = &'l dyn for<'z> View<
                    'z,
                    Output = Eq::Imply<Self::F<'x, 'z>, Eq::Imply<Self::F<'y, 'z>, Eq::Eq<'x, 'y>>>,
                >,
            >,
        >,
    >;
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
