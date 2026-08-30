#![forbid(unsafe_code)]

use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Expr, ExprAssign, ExprCall, ExprMethodCall, ExprParen, ExprTuple, ExprUnary, Lifetime, Token,
    Type, UnOp,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
};

/// Parse the `pred!` macro syntax: `pred!('l, pattern)`
struct PredInput {
    expr: Type,
}

impl Parse for PredInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lifetime = input.parse()?;
        input.parse::<Token![,]>()?;
        let expr = input.parse()?;
        Ok(PredInput {
            expr: expand_pred_expr(&lifetime, &expr)?,
        })
    }
}

fn expand_pred_expr(lifetime: &Lifetime, expr: &Expr) -> syn::Result<Type> {
    Ok(expand_pred_expr2(lifetime, expr)?.unwrap_or_else(|| parse_quote!(#expr)))
}

trait IterOnly: Iterator {
    fn only(self) -> Option<Self::Item>;
}

impl<T: Iterator> IterOnly for T {
    fn only(mut self) -> Option<Self::Item> {
        let first = self.next()?;
        if self.next().is_some() {
            None
        } else {
            Some(first)
        }
    }
}

/// Try to parse the special (Call::<'x> = Path::<'y,'z>, Body) syntax
/// Returns Some(expanded_type) if it matches the pattern, None otherwise
fn try_parse_call_syntax(
    lifetime: &Lifetime,
    elems: &syn::punctuated::Punctuated<Expr, syn::token::Comma>,
) -> syn::Result<Option<Type>> {
    // Need at least 2 elements: the assignment and the body
    if elems.len() < 2 {
        return Ok(None);
    }

    // First element must be an assignment
    let Expr::Assign(ExprAssign { left, right, .. }) = &elems[0] else {
        return Ok(None);
    };

    // Left side must be a path (Call::<'x>)
    let Expr::Path(left_path) = &**left else {
        return Ok(None);
    };

    // Must be a single-segment path (just "Call", not "foo::Call")
    if left_path.path.segments.len() != 1 {
        return Ok(None);
    }

    // Get the segment and verify it's "Call"
    let left_segment = &left_path.path.segments[0];

    if left_segment.ident != "Call" {
        return Ok(None);
    }

    // Must have turbofish generics
    let syn::PathArguments::AngleBracketed(left_generics) = &left_segment.arguments else {
        return Ok(None);
    };

    // Extract lifetimes from Call::<'x> and verify they're ALL lifetimes
    let mut call_lifetimes = Vec::new();
    for arg in &left_generics.args {
        match arg {
            syn::GenericArgument::Lifetime(lt) => call_lifetimes.push(lt),
            _ => return Ok(None), // Non-lifetime argument, not our syntax
        }
    }

    if call_lifetimes.is_empty() {
        return Ok(None);
    }

    // Right side must be a path with generics (Path::<'y,'z>)
    let Expr::Path(right_path) = &**right else {
        return Ok(None);
    };

    // Clone the full ExprPath and append call lifetimes to the last segment's generics
    let mut path_expr = right_path.clone();

    // Get mutable reference to the last segment
    let last_segment = path_expr.path.segments.last_mut().unwrap();

    // Build new generic arguments: existing + call lifetimes
    let mut all_generics = syn::punctuated::Punctuated::new();

    // Copy existing generics if present
    if let syn::PathArguments::AngleBracketed(ref existing_generics) = last_segment.arguments {
        for arg in &existing_generics.args {
            all_generics.push(arg.clone());
        }
    }

    // Append the call lifetimes
    for lt in &call_lifetimes {
        all_generics.push(syn::GenericArgument::Lifetime((*lt).clone()));
    }

    // Update the last segment with new generics
    last_segment.arguments =
        syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
            colon2_token: None,
            lt_token: Default::default(),
            args: all_generics,
            gt_token: Default::default(),
        });

    // Build the consequent from remaining tuple elements
    let rest_elems: Vec<_> = elems.iter().skip(1).cloned().collect();

    let consequent = expand_pred_expr(
        lifetime,
        &Expr::Tuple(ExprTuple {
            attrs: vec![],
            paren_token: Default::default(),
            elems: rest_elems.into_iter().collect(),
        }),
    )?;

    // Build the path expression with all generics
    let path_with_call: Type = parse_quote! { #path_expr };

    // Build implication: path_with_call.imply(consequent)
    let implication: Type = parse_quote! {
        <Self as crate::logic::prop::Imply<#lifetime>>::Imply<
            #path_with_call,
            #consequent,
        >
    };

    // Wrap in ForAll for each call lifetime
    let mut result = implication;
    for lt in call_lifetimes.iter().rev() {
        result = parse_quote! {
            <Self as crate::logic::prop::FirstOrder<#lifetime>>::ForAll<
                dyn for<#lt> crate::logic::prop::View<
                    #lt,
                    Output = #result
                > + #lifetime,
            >
        };
    }

    Ok(Some(result))
}

/// Recursively process the pattern expression
fn expand_pred_expr2(lifetime: &Lifetime, expr: &Expr) -> syn::Result<Option<Type>> {
    match expr {
        // (Call::<'x> = Path::<'y,'z>, rest)
        // translates to ForAll::<'x>(Path::<'y,'z,'x>.imply(rest))
        Expr::Tuple(ExprTuple { elems, .. }) => {
            if let Some(result) = try_parse_call_syntax(lifetime, elems)? {
                return Ok(Some(result));
            }
            // Not the special syntax, treat as regular tuple
            Ok(None)
        }

        // ForAll::<'x, 'y, ...>(inner) - turbofish call
        Expr::Call(ExprCall { func, args, .. }) => {
            // Check if func is a path with turbofish (ForAll::<lifetimes>)
            if let Expr::Path(path_expr) = &**func {
                if let Some(segment) = path_expr.path.segments.last() {
                    let quantifier = &segment.ident;
                    if quantifier == "ForAll" || quantifier == "Exists" {
                        // Extract lifetimes from turbofish
                        if let syn::PathArguments::AngleBracketed(ref generic_args) =
                            segment.arguments
                        {
                            let lifetimes: Vec<_> = generic_args
                                .args
                                .iter()
                                .map(|arg| {
                                    if let syn::GenericArgument::Lifetime(lt) = arg {
                                        Ok(lt)
                                    } else {
                                        Err(syn::Error::new_spanned(
                                            arg,
                                            "ForAll/Exists expects only lifetimes",
                                        ))
                                    }
                                })
                                .collect::<Result<_, _>>()?;

                            if lifetimes.is_empty() {
                                return Err(syn::Error::new_spanned(
                                    segment,
                                    "ForAll requires at least one lifetime",
                                ));
                            }

                            let inner = expand_pred_expr(lifetime, &parse_quote!((#args)))?;

                            // Recursively build the nested structure
                            // ForAll::<'x, 'y, 'z>(inner) becomes
                            // ForAll::<'x>(ForAll::<'y>(ForAll::<'z>(inner)))

                            let mut result = inner;
                            for lt in lifetimes.iter().rev() {
                                result = parse_quote! {
                                    <Self as crate::logic::prop::FirstOrder<#lifetime>>::#quantifier<
                                        dyn for<#lt> crate::logic::prop::View<
                                            #lt,
                                            Output = #result
                                        > + #lifetime,
                                    >
                                };
                            }

                            return Ok(Some(result));
                        }
                    }
                }
            }
            Ok(None)
        }

        // (pattern).iff(pattern) or (pattern).imply(pattern)
        Expr::MethodCall(ExprMethodCall {
            receiver,
            method,
            args,
            ..
        }) => {
            let method_name = method.to_string();

            if method_name == "iff" {
                let Some(arg) = args.into_iter().only() else {
                    return Err(syn::Error::new_spanned(
                        args,
                        "imply requires exactly one argument",
                    ));
                };

                let left = expand_pred_expr(lifetime, receiver)?;
                let right = expand_pred_expr(lifetime, arg)?;

                Ok(Some(parse_quote! {
                    crate::logic::prop::Iff<#lifetime, Self, #left, #right>
                }))
            } else if method_name == "imply" {
                let Some(arg) = args.into_iter().only() else {
                    return Err(syn::Error::new_spanned(
                        args,
                        "imply requires exactly one argument",
                    ));
                };

                let left = expand_pred_expr(lifetime, receiver)?;
                let right = expand_pred_expr(lifetime, arg)?;

                Ok(Some(parse_quote! {
                    <Self as crate::logic::prop::Imply<#lifetime>>::Imply<
                        #left,
                        #right,
                    >
                }))
            } else {
                // Unknown method - treat as type
                Ok(None)
            }
        }

        // !pattern - negation
        Expr::Unary(ExprUnary {
            op: UnOp::Not(_),
            expr: inner,
            ..
        }) => {
            let inner_expanded = expand_pred_expr(lifetime, inner)?;
            Ok(Some(parse_quote! {
                <Self as crate::logic::prop::Negation<#lifetime>>::Neg<#inner_expanded>
            }))
        }

        // (pattern) - strip parens and recurse
        Expr::Paren(ExprParen { expr: inner, .. }) => expand_pred_expr2(lifetime, inner),
        // Otherwise, treat as a type expression
        _ => Ok(None),
    }
}

/// The `pred!` macro: expands predicate patterns into type expressions
#[proc_macro]
pub fn pred(input: TokenStream) -> TokenStream {
    let PredInput { expr } = syn::parse_macro_input!(input as PredInput);
    TokenStream::from(quote! { #expr })
}

fn paren(expr: Expr) -> Expr {
    Expr::Paren(ExprParen {
        expr: Box::new(expr),
        attrs: Default::default(),
        paren_token: Default::default(),
    })
}

fn punctuated_paren<P>(punctuated: Punctuated<Expr, P>) -> Punctuated<Expr, P> {
    let mut result = Punctuated::new();
    for pair in punctuated.into_pairs() {
        use syn::punctuated::Pair;
        match pair {
            Pair::Punctuated(token, delim) => {
                result.push_value(paren(token));
                result.push_punct(delim);
            }
            Pair::End(token) => {
                result.push_value(paren(token));
            }
        }
    }
    result
}

fn recur_paren(expr: Expr) -> Expr {
    use syn::*;
    match expr {
        Expr::MethodCall(ExprMethodCall {
            attrs,
            receiver,
            dot_token,
            method,
            turbofish,
            paren_token,
            args,
        }) => paren(Expr::MethodCall(ExprMethodCall {
            attrs,
            receiver: Box::new(recur_paren(*receiver)),
            dot_token,
            method,
            turbofish,
            paren_token,
            args: punctuated_paren(args),
        })),
        Expr::Binary(ExprBinary {
            attrs,
            op,
            left,
            right,
        }) => paren(Expr::Binary(ExprBinary {
            attrs,
            op,
            left: Box::new(recur_paren(*left)),
            right: Box::new(recur_paren(*right)),
        })),
        _ => parse_quote!((#expr)),
    }
}

#[proc_macro]
pub fn parenthesize(intput: TokenStream) -> TokenStream {
    let expr = syn::parse_macro_input!(intput as Expr);
    let expr = recur_paren(expr);
    TokenStream::from(quote! { #expr })
}
