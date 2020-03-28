use crate::utils::ast_utils::{eq_field_pat, eq_id, eq_pat, eq_path};
use crate::utils::{self, over};
use rustc_ast::ast::{Arm, Pat, PatKind, PatKind::*, DUMMY_NODE_ID};
use rustc_ast::mut_visit::*;
use rustc_ast::ptr::P;
use rustc_ast_pretty::pprust;
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass, LintContext};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::DUMMY_SP;

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
        let mut pat = P(arm.pat.clone());
        let mut visitor = Vis { changed: false };
        visitor.visit_pat(&mut pat);
        if !visitor.changed {
            return;
        }

        cx.struct_span_lint(UNNESTED_OR_PATTERNS, pat.span, |db| {
            let mut db = db.build("unnested or-patterns");
            utils::docs_link(&mut db, UNNESTED_OR_PATTERNS);
            db.span_suggestion_verbose(
                pat.span,
                "nest the patterns",
                pprust::pat_to_string(&pat),
                Applicability::MachineApplicable,
            );
            db.emit();
        });
    }
}

struct Vis {
    changed: bool,
}

fn take_pat(from: &mut Pat) -> Pat {
    let dummy = Pat {
        id: DUMMY_NODE_ID,
        kind: Wild,
        span: DUMMY_SP,
    };
    mem::replace(from, dummy)
}

fn flatten_paren_in(pat: &mut Pat) {
    let mut curr = take_pat(pat);
    while let Pat { kind: Paren(pat), .. } = curr {
        curr = pat.into_inner();
    }
    *pat = curr;
}

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
fn drain_matching(
    start: usize,
    alternatives: &mut Vec<P<Pat>>,
    predicate: impl Fn(&PatKind) -> bool,
    extract: impl Fn(PatKind) -> P<Pat>,
) -> Vec<P<Pat>> {
    let mut tail_or = vec![];
    let mut idx = 0;
    for mut pat in alternatives.drain_filter(|p| {
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

macro_rules! always_pat {
    ($scrutinee:expr, $pat:pat => $then:expr) => {
        match $scrutinee {
            $pat => $then,
            _ => unreachable!(),
        }
    };
}

fn focus_on_idx(alternatives: &mut Vec<P<Pat>>, focus_idx: usize) -> bool {
    let mut focus_kind = mem::replace(&mut alternatives[focus_idx].kind, PatKind::Wild);

    let start = focus_idx + 1;

    let mut changed = false;
    match &mut focus_kind {
        // These pattern forms do not have sub-patterns.
        // Therefore they are not some form of constructor `C`,
        // with which a pattern `C(P0)` may be formed,
        // which we would want to join with other `C(Pj)`s.
        Ident(_, _, None) | Lit(_) | Wild | Path(_, _) | Range(_, _, _) | Rest | MacCall(_) | Or(_) | Paren(_) => {},
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
        Ref(target, m1) => {
            changed |= extend_with_matching(
                target,
                start,
                alternatives,
                true,
                |k| matches!(k, Ref(_, m2) if m1 == m2),
                |k| always_pat!(k, Ref(p, _) => p),
            );
        },
        Ident(b1, i1, Some(target)) => {
            changed |= extend_with_matching(
                target,
                start,
                alternatives,
                true,
                |k| matches!(k, Ident(b2, i2, Some(_)) if b1 == b2 && eq_id(*i1, *i2)),
                |k| always_pat!(k, Ident(_, _, Some(p)) => p),
            );
        },
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
        Struct(path1, fps1, rest1) => {
            for idx in 0..fps1.len() {
                let pos_in_2 = std::cell::Cell::new(None);
                let tail_or = drain_matching(
                    start,
                    alternatives,
                    |k| {
                        matches!(k, Struct(path2, fps2, rest2)
                        if rest1 == rest2
                        && eq_path(path1, path2)
                        && fps1.len() == fps2.len()
                        && fps1.iter().enumerate().all(|(idx_1, fp1)| {
                            if idx_1 == idx {
                                let pos = fps2.iter().position(|fp2| eq_id(fp1.ident, fp2.ident));
                                pos_in_2.set(pos);
                                pos.is_some()
                            } else {
                                fps2.iter().any(|fp2| eq_field_pat(fp1, fp2))
                            }
                        }))
                    },
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

impl MutVisitor for Vis {
    fn visit_pat(&mut self, p: &mut P<Pat>) {
        noop_visit_pat(p, self);

        let alternatives = match &mut p.kind {
            Or(ps) => ps,
            _ => return,
        };

        let mut focus_idx = 0;
        while focus_idx < alternatives.len() {
            self.changed |= focus_on_idx(alternatives, focus_idx);
            focus_idx += 1;
        }
    }
}

fn eq_pre_post(ps1: &[P<Pat>], ps2: &[P<Pat>], idx: usize) -> bool {
    ps1.len() == ps2.len()
        && over(&ps1[..idx], &ps2[..idx], |l, r| eq_pat(l, r))
        && over(&ps1[idx + 1..], &ps2[idx + 1..], |l, r| eq_pat(l, r))
}
