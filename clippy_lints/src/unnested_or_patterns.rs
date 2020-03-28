use crate::utils::ast_utils::{eq_field_pat, eq_id, eq_pat, eq_path};
use crate::utils::{over, span_lint_and_then};
use rustc_ast::ast::{Arm, Pat, PatKind, PatKind::*, DUMMY_NODE_ID};
use rustc_ast::mut_visit::*;
use rustc_ast::ptr::P;
use rustc_ast_pretty::pprust;
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::DUMMY_SP;

use std::cell::Cell;
use std::mem;

declare_clippy_lint! {
    /// **What it does:**
    ///
    /// Checks for unnested or-patterns, e.g., `Some(0) | Some(2)` and
    /// suggests replacing the pattern with a nested one, `Some(0 | 2)`.
    ///
    /// Another way to think of this is that it rewrites patterns in
    /// *disjunctive normal form (DNF)* into *conjunctive normal form (CNF)*.
    ///
    /// **Why is this bad?**
    ///
    /// In the example above, `Some` is repeated, which unncessarily complicates the pattern.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    ///
    /// ```rust
    /// fn main() {
    ///     if let Some(0) | Some(2) = Some(0) {}
    /// }
    /// ```
    /// Use instead:
    /// ```rust
    /// fn main() {
    ///     if let Some(0 | 2) = Some(0) {}
    /// }
    /// ```
    pub UNNESTED_OR_PATTERNS,
    complexity,
    "unnested or-patterns, e.g., `Foo(Bar) | Foo(Baz) instead of `Foo(Bar | Baz)`"
}

declare_lint_pass!(UnnestedOrPatterns => [UNNESTED_OR_PATTERNS]);

impl EarlyLintPass for UnnestedOrPatterns {
    fn check_arm(&mut self, cx: &EarlyContext<'_>, arm: &Arm) {
        if !cx.sess.opts.unstable_features.is_nightly_build() {
            // User cannot do `#![feature(or_patterns)]`, so bail.
            return;
        }

        // Transform all unnested or-patterns into nested ones.
        let mut pat = P(arm.pat.clone());
        if !unnest_or_patterns(&mut pat) {
            // There were none, so quit.
            return;
        }
        span_lint_and_then(cx, UNNESTED_OR_PATTERNS, pat.span, "unnested or-patterns", |db| {
            db.span_suggestion_verbose(
                pat.span,
                "nest the patterns",
                pprust::pat_to_string(&pat),
                Applicability::MachineApplicable,
            );
        });
    }
}

/// Unnest or-patterns `p0 | ... | p1` in the pattern `pat`.
/// For example, this would transform `Some(0) | FOO | Some(2)` into `Some(0 | 2) | FOO`.
fn unnest_or_patterns(pat: &mut P<Pat>) -> bool {
    struct Visitor {
        changed: bool,
    }
    impl MutVisitor for Visitor {
        fn visit_pat(&mut self, p: &mut P<Pat>) {
            // This is a bottom up transformation, so recurse first.
            noop_visit_pat(p, self);

            // Don't have an or-pattern? Just quit early on.
            let alternatives = match &mut p.kind {
                Or(ps) => ps,
                _ => return,
            };

            // Focus on `p_n` and then try to transform all `p_i` where `i > n`.
            let mut focus_idx = 0;
            while focus_idx < alternatives.len() {
                self.changed |= transform_with_focus_on_idx(alternatives, focus_idx);
                focus_idx += 1;
            }
        }
    }

    let mut visitor = Visitor { changed: false };
    visitor.visit_pat(pat);
    visitor.changed
}

/// Match `$scrutinee` against `$pat` and extract `$then` from it.
/// Panics if there is no match.
macro_rules! always_pat {
    ($scrutinee:expr, $pat:pat => $then:expr) => {
        match $scrutinee {
            $pat => $then,
            _ => unreachable!(),
        }
    };
}

/// Focus on `focus_idx` in `alternatives`,
/// attempting to extend it with elements of the same constructor `C`
/// in `alternatives[focus_idx + 1..]`.
fn transform_with_focus_on_idx(alternatives: &mut Vec<P<Pat>>, focus_idx: usize) -> bool {
    // Extract the kind; we'll need to make some changes in it.
    let mut focus_kind = mem::replace(&mut alternatives[focus_idx].kind, PatKind::Wild);
    // We'll focus on `alternatives[focus_idx]`,
    // so we're draining from `alternatives[focus_idx + 1..]`.
    let start = focus_idx + 1;
    // Record whether we altered `focus_kind` or not.
    let mut changed = false;

    // We're trying to find whatever kind (~"constructor") we found in `alternatives[start..]`.
    match &mut focus_kind {
        // These pattern forms do not have sub-patterns.
        // Therefore they are not some form of constructor `C`,
        // with which a pattern `C(P0)` may be formed,
        // which we would want to join with other `C(Pj)`s.
        Ident(_, _, None) | Lit(_) | Wild | Path(_, _) | Range(_, _, _) | Rest | MacCall(_) | Or(_) | Paren(_) => {},
        // Transform `box x | ... | box y` into `box (x | y)`.
        //
        // The cases below until `Slice(...)` deal *singleton* products.
        // These patterns have the shape `C(p)`, and not e.g., `C(p0, ..., pn)`.
        Box(target) => {
            changed |= extend_with_matching(
                target,
                start,
                alternatives,
                true,
                |k| matches!(k, Box(_)),
                |k| always_pat!(k, Box(p) => p),
            );
        },
        // Transform `&m x | ... | &m y` into `&m (x, y)`.
        Ref(target, m1) => {
            changed |= extend_with_matching(
                target,
                start,
                alternatives,
                true,
                |k| matches!(k, Ref(_, m2) if m1 == m2), // Mutabilities must match.
                |k| always_pat!(k, Ref(p, _) => p),
            );
        },
        // Transform `b @ p0 | ... b @ p1` into `b @ (p0 | p1)`.
        Ident(b1, i1, Some(target)) => {
            changed |= extend_with_matching(
                target,
                start,
                alternatives,
                true,
                // Binding names must match.
                |k| matches!(k, Ident(b2, i2, Some(_)) if b1 == b2 && eq_id(*i1, *i2)),
                |k| always_pat!(k, Ident(_, _, Some(p)) => p),
            );
        },
        // Transform `[pre, x, post] | ... | [pre, y, post]` into `[pre, x | y, post]`.
        //
        // These cases below are more tricky, as they look like `C(p_0, ..., p_n)`.
        // Here, the idea is that we fixate on some `p_k` in `C`,
        // allowing it to vary between two `ps1` and `ps2`,
        // while also requiring `ps1[..n] ~ ps2[..n]` (pre) and `ps1[n + 1..] ~ ps2[n + 1..]` (post),
        // where `~` denotes semantic equality.
        Slice(ps1) => {
            for idx in 0..ps1.len() {
                let tail_or = drain_matching(
                    start,
                    alternatives,
                    |k| matches!(k, Slice(ps2) if eq_pre_post(ps1, ps2, idx)),
                    |k| always_pat!(k, Slice(mut ps) => ps.swap_remove(idx)),
                );
                changed |= extend_with_tail_or(&mut ps1[idx], tail_or, false);
            }
        },
        // Transform `(pre, x, post) | ... | (pre, y, post)` into `(pre, x | y, post]`.
        Tuple(ps1) => {
            for idx in 0..ps1.len() {
                let tail_or = drain_matching(
                    start,
                    alternatives,
                    |k| matches!(k, Tuple(ps2) if eq_pre_post(ps1, ps2, idx)),
                    |k| always_pat!(k, Tuple(mut ps) => ps.swap_remove(idx)),
                );
                changed |= extend_with_tail_or(&mut ps1[idx], tail_or, false);
            }
        },
        // Transform `S(pre, x, post) | ... | S(pre, y, post)` into `S(pre, x | y, post]`.
        TupleStruct(path1, ps1) => {
            for idx in 0..ps1.len() {
                let tail_or = drain_matching(
                    start,
                    alternatives,
                    |k| {
                        matches!(k, TupleStruct(path2, ps2)
                        if eq_path(path1, path2) && eq_pre_post(ps1, ps2, idx))
                    },
                    |k| always_pat!(k, TupleStruct(_, mut ps) => ps.swap_remove(idx)),
                );
                changed |= extend_with_tail_or(&mut ps1[idx], tail_or, false);
            }
        },
        // Here we focusing on a record pattern `S { fp_0, ..., fp_n }`.
        // In particular, for a record pattern, the order in which the field patterns is irrelevant.
        // So when we fixate on some `ident_k: pat_k`, we try to find `ident_k` in the other pattern
        // and check that all `fp_i` where `i ∈ ((0...n) \ k)` between two patterns are equal.
        Struct(path1, fps1, rest1) => {
            for idx in 0..fps1.len() {
                let pos_in_2 = Cell::new(None); // The element `k`.
                let tail_or = drain_matching(
                    start,
                    alternatives,
                    |k| {
                        matches!(k, Struct(path2, fps2, rest2)
                        if rest1 == rest2 // If one struct pattern has `..` so must the other.
                        && eq_path(path1, path2)
                        && fps1.len() == fps2.len()
                        && fps1.iter().enumerate().all(|(idx_1, fp1)| {
                            if idx_1 == idx {
                                // In the case of `k`, we merely require identical field names
                                // so that we will transform into `ident_k: p1_k | p2_k`.
                                let pos = fps2.iter().position(|fp2| eq_id(fp1.ident, fp2.ident));
                                pos_in_2.set(pos);
                                pos.is_some()
                            } else {
                                fps2.iter().any(|fp2| eq_field_pat(fp1, fp2))
                            }
                        }))
                    },
                    // Extract `p2_k`.
                    |k| {
                        always_pat!(k, Struct(_, mut fps, _)
                            => fps.swap_remove(pos_in_2.take().unwrap()).pat
                        )
                    },
                );
                changed |= extend_with_tail_or(&mut fps1[idx].pat, tail_or, false);
            }
        },
    }

    alternatives[focus_idx].kind = focus_kind;
    changed
}

/// Extract the pattern from the given one and replace it with `Wild`.
/// This is meant for temporarily swapping out the pattern for manipulation.
fn take_pat(from: &mut Pat) -> Pat {
    let dummy = Pat {
        id: DUMMY_NODE_ID,
        kind: Wild,
        span: DUMMY_SP,
    };
    mem::replace(from, dummy)
}

/// Flatten all immediately nested parenthesis in `pat`.
fn flatten_paren_in(pat: &mut Pat) {
    let mut curr = take_pat(pat);
    while let Pat { kind: Paren(pat), .. } = curr {
        curr = pat.into_inner();
    }
    *pat = curr;
}

/// Peel through all immediately nested parenthesis in `pat` returning a reference to the inner one.
fn peel_paren(mut curr: &Pat) -> &Pat {
    while let Paren(p) = &curr.kind {
        curr = &p;
    }
    curr
}

/// Extend `target` as an or-pattern with the alternatives
/// in `tail_or` if there are any and return if there were.
fn extend_with_tail_or(target: &mut Pat, tail_or: Vec<P<Pat>>, needs_paren: bool) -> bool {
    fn extend(target: &mut Pat, mut tail_or: Vec<P<Pat>>) {
        match target {
            // On an existing or-pattern in the target, append to it.
            Pat { kind: Or(ps), .. } => ps.append(&mut tail_or),
            // Otherwise convert the target to an or-pattern.
            target => {
                let mut init_or = vec![P(take_pat(target))];
                init_or.append(&mut tail_or);
                target.kind = Or(init_or);
            },
        }
    }

    let changed = !tail_or.is_empty();
    if changed {
        // Unwrap all parens in target first.
        flatten_paren_in(target);
        // Extend the target.
        extend(target, tail_or);
        if needs_paren {
            // e.g., `box 0 | 1` needs to become `box (0 | 1)`.
            target.kind = Paren(P(take_pat(target)));
        }
    }
    changed
}

// Extract all inner patterns in `alternatives` matching our `predicate`.
// Only elements beginning with `start` are considered for extraction.
fn drain_matching(
    start: usize,
    alternatives: &mut Vec<P<Pat>>,
    predicate: impl Fn(&PatKind) -> bool,
    extract: impl Fn(PatKind) -> P<Pat>,
) -> Vec<P<Pat>> {
    let mut tail_or = vec![];
    let mut idx = 0;
    for mut pat in alternatives.drain_filter(|p| {
        // Check if we should extract, but only if `idx >= start`.
        idx += 1;
        idx > start && predicate(&peel_paren(p).kind)
    }) {
        flatten_paren_in(&mut pat);
        let mut pat = extract(pat.into_inner().kind); // Do the extraction.
        flatten_paren_in(&mut pat);
        tail_or.push(pat);
    }
    tail_or
}

fn extend_with_matching(
    target: &mut Pat,
    start: usize,
    alternatives: &mut Vec<P<Pat>>,
    needs_paren: bool,
    predicate: impl Fn(&PatKind) -> bool,
    extract: impl Fn(PatKind) -> P<Pat>,
) -> bool {
    extend_with_tail_or(
        target,
        drain_matching(start, alternatives, predicate, extract),
        needs_paren,
    )
}

/// Are the patterns in `ps1` and `ps2` equal save for `ps1[idx]` compared to `ps2[idx]`?
fn eq_pre_post(ps1: &[P<Pat>], ps2: &[P<Pat>], idx: usize) -> bool {
    ps1.len() == ps2.len()
        && over(&ps1[..idx], &ps2[..idx], |l, r| eq_pat(l, r))
        && over(&ps1[idx + 1..], &ps2[idx + 1..], |l, r| eq_pat(l, r))
}
