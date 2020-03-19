use crate::utils::{self, both, over};
use rustc_ast::ast::{self, *};
use rustc_ast::mut_visit::*;
use rustc_ast::ptr::P;
use rustc_ast_pretty::pprust;
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass, LintContext};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::{Span, DUMMY_SP};

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

fn dummy_pat() -> Pat {
    Pat {
        id: DUMMY_NODE_ID,
        kind: PatKind::Wild,
        span: DUMMY_SP,
    }
}

fn take_pat(from: &mut Pat) -> Pat {
    mem::replace(from, dummy_pat())
}

fn flatten_paren_in(pat: &mut Pat) {
    let mut curr = take_pat(pat);
    while let Pat {
        kind: PatKind::Paren(pat),
        ..
    } = curr
    {
        curr = pat.into_inner();
    }
    *pat = curr;
}

fn peel_paren(mut curr: &Pat) -> &Pat {
    while let PatKind::Paren(p) = &curr.kind {
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
            Pat {
                kind: PatKind::Or(ps), ..
            } => ps.append(&mut tail_or),
            // Otherwise convert the target to an or-pattern.
            target => {
                let mut init_or = vec![P(take_pat(target))];
                init_or.append(&mut tail_or);
                target.kind = PatKind::Or(init_or);
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
            target.kind = PatKind::Paren(P(take_pat(target)));
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

    let changed = match &mut focus_kind {
        PatKind::Ident(_, _, None)
        | PatKind::Lit(_)
        | PatKind::Wild
        | PatKind::Path(_, _)
        | PatKind::Range(_, _, _)
        | PatKind::Rest
        | PatKind::MacCall(_)
        | PatKind::Or(_)
        | PatKind::Paren(_) => false,
        PatKind::Box(target) => extend_with_matching(
            target,
            start,
            alternatives,
            true,
            |k| matches!(k, PatKind::Box(_)),
            |k| always_pat!(k, PatKind::Box(p) => p),
        ),
        PatKind::Ref(target, m1) => extend_with_matching(
            target,
            start,
            alternatives,
            true,
            |k| matches!(k, PatKind::Ref(_, m2) if m1 == m2),
            |k| always_pat!(k, PatKind::Ref(p, _) => p),
        ),
        PatKind::Ident(b1, i1, Some(target)) => extend_with_matching(
            target,
            start,
            alternatives,
            true,
            |k| matches!(k, PatKind::Ident(b2, i2, Some(_)) if b1 == b2 && eq_id(*i1, *i2)),
            |k| always_pat!(k, PatKind::Ident(_, _, Some(p)) => p),
        ),
        PatKind::Slice(ps1) => (0..ps1.len()).any(|idx| {
            let tail_or = drain_matching(
                start,
                alternatives,
                |k| matches!(k, PatKind::Slice(ps2) if eq_pre_post(ps1, ps2, idx)),
                |k| always_pat!(k, PatKind::Slice(mut ps) => ps.swap_remove(idx)),
            );
            extend_with_tail_or(&mut ps1[idx], tail_or, false)
        }),
        PatKind::Tuple(ps1) => (0..ps1.len()).any(|idx| {
            let tail_or = drain_matching(
                start,
                alternatives,
                |k| matches!(k, PatKind::Tuple(ps2) if eq_pre_post(ps1, ps2, idx)),
                |k| always_pat!(k, PatKind::Tuple(mut ps) => ps.swap_remove(idx)),
            );
            extend_with_tail_or(&mut ps1[idx], tail_or, false)
        }),
        PatKind::TupleStruct(path1, ps1) => (0..ps1.len()).any(|idx| {
            let tail_or = drain_matching(
                start,
                alternatives,
                |k| {
                    matches!(k, PatKind::TupleStruct(path2, ps2)
                        if eq_path(path1, path2) && eq_pre_post(ps1, ps2, idx))
                },
                |k| always_pat!(k, PatKind::TupleStruct(_, mut ps) => ps.swap_remove(idx)),
            );
            extend_with_tail_or(&mut ps1[idx], tail_or, false)
        }),
        PatKind::Struct(path1, fps1, rest1) => (0..fps1.len()).any(|idx| {
            let pos_in_2 = std::cell::Cell::new(None);
            let tail_or = drain_matching(
                start,
                alternatives,
                |k| {
                    matches!(k, PatKind::Struct(path2, fps2, rest2)
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
                    always_pat!(k, PatKind::Struct(_, mut fps, _)
                        => fps.swap_remove(pos_in_2.take().unwrap()).pat
                    )
                },
            );
            extend_with_tail_or(&mut fps1[idx].pat, tail_or, false)
        }),
    };

    alternatives[focus_idx].kind = focus_kind;
    changed
}

impl MutVisitor for Vis {
    fn visit_pat(&mut self, p: &mut P<Pat>) {
        noop_visit_pat(p, self);

        let alternatives = match &mut p.kind {
            PatKind::Or(ps) => ps,
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

fn eq_id(l: Ident, r: Ident) -> bool {
    l.name == r.name
}

fn eq_pat(l: &Pat, r: &Pat) -> bool {
    use PatKind::*;
    match (&l.kind, &r.kind) {
        (Paren(l), _) => eq_pat(l, r),
        (_, Paren(r)) => eq_pat(l, r),
        (Wild, Wild) | (Rest, Rest) => true,
        (Lit(l), Lit(r)) => eq_expr(l, r),
        (Ident(b1, i1, s1), Ident(b2, i2, s2)) => b1 == b2 && eq_id(*i1, *i2) && both(s1, s2, |l, r| eq_pat(l, r)),
        (Range(lf, lt, le), Range(rf, rt, re)) => {
            eq_expr_opt(lf, rf)
                && eq_expr_opt(lt, rt)
                && match (&le.node, &re.node) {
                    (RangeEnd::Excluded, RangeEnd::Excluded) => true,
                    (RangeEnd::Included(l), RangeEnd::Included(r)) => {
                        matches!(l, RangeSyntax::DotDotEq) == matches!(r, RangeSyntax::DotDotEq)
                    },
                    _ => false,
                }
        },
        (Box(l), Box(r))
        | (Ref(l, Mutability::Not), Ref(r, Mutability::Not))
        | (Ref(l, Mutability::Mut), Ref(r, Mutability::Mut)) => eq_pat(l, r),
        (Tuple(l), Tuple(r)) | (Slice(l), Slice(r)) => over(l, r, |l, r| eq_pat(l, r)),
        (Path(lq, lp), Path(rq, rp)) => both(lq, rq, |l, r| eq_qself(l, r)) && eq_path(lp, rp),
        (TupleStruct(lp, lfs), TupleStruct(rp, rfs)) => eq_path(lp, rp) && over(lfs, rfs, |l, r| eq_pat(l, r)),
        (Struct(lp, lfs, lr), Struct(rp, rfs, rr)) => {
            lr == rr
                && eq_path(lp, rp)
                && lfs.len() == rfs.len()
                && lfs.iter().all(|lf| rfs.iter().any(|rf| eq_field_pat(lf, rf)))
        },
        (Or(ls), Or(rs)) => ls.len() == rs.len() && ls.iter().all(|l| rs.iter().any(|r| eq_pat(l, r))),
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_field_pat(l: &FieldPat, r: &FieldPat) -> bool {
    l.is_placeholder == r.is_placeholder
        && eq_id(l.ident, r.ident)
        && eq_pat(&l.pat, &r.pat)
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
}

fn eq_qself(l: &QSelf, r: &QSelf) -> bool {
    l.position == r.position && eq_ty(&l.ty, &r.ty)
}

fn eq_path(l: &Path, r: &Path) -> bool {
    over(&l.segments, &r.segments, |l, r| eq_path_seg(l, r))
}

fn eq_path_seg(l: &PathSegment, r: &PathSegment) -> bool {
    eq_id(l.ident, r.ident) && both(&l.args, &r.args, |l, r| eq_generic_args(l, r))
}

fn eq_generic_args(l: &GenericArgs, r: &GenericArgs) -> bool {
    match (l, r) {
        (GenericArgs::AngleBracketed(l), GenericArgs::AngleBracketed(r)) => {
            over(&l.args, &r.args, |l, r| eq_generic_arg(l, r))
                && over(&l.constraints, &r.constraints, |l, r| eq_assoc_constraint(l, r))
        },
        (GenericArgs::Parenthesized(l), GenericArgs::Parenthesized(r)) => {
            over(&l.inputs, &r.inputs, |l, r| eq_ty(l, r)) && eq_fn_ret_ty(&l.output, &r.output)
        },
        _ => false,
    }
}

fn eq_generic_arg(l: &GenericArg, r: &GenericArg) -> bool {
    match (l, r) {
        (GenericArg::Lifetime(l), GenericArg::Lifetime(r)) => eq_id(l.ident, r.ident),
        (GenericArg::Type(l), GenericArg::Type(r)) => eq_ty(l, r),
        (GenericArg::Const(l), GenericArg::Const(r)) => eq_expr(&l.value, &r.value),
        _ => false,
    }
}

fn eq_expr_opt(l: &Option<P<Expr>>, r: &Option<P<Expr>>) -> bool {
    both(l, r, |l, r| eq_expr(l, r))
}

fn eq_expr(l: &Expr, r: &Expr) -> bool {
    use ExprKind::*;
    if !over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r)) {
        return false;
    }
    match (&l.kind, &r.kind) {
        (Paren(l), _) => eq_expr(l, r),
        (_, Paren(r)) => eq_expr(l, r),
        (Err, Err) => true,
        (Box(l), Box(r)) | (Try(l), Try(r)) | (Await(l), Await(r)) => eq_expr(l, r),
        (Array(l), Array(r)) | (Tup(l), Tup(r)) => over(l, r, |l, r| eq_expr(l, r)),
        (Repeat(le, ls), Repeat(re, rs)) => eq_expr(le, re) && eq_expr(&ls.value, &rs.value),
        (Call(lc, la), Call(rc, ra)) => eq_expr(lc, rc) && over(la, ra, |l, r| eq_expr(l, r)),
        (MethodCall(lc, la), MethodCall(rc, ra)) => eq_path_seg(lc, rc) && over(la, ra, |l, r| eq_expr(l, r)),
        (Binary(lo, ll, lr), Binary(ro, rl, rr)) => lo.node == ro.node && eq_expr(ll, rl) && eq_expr(lr, rr),
        (Unary(lo, l), Unary(ro, r)) => mem::discriminant(lo) == mem::discriminant(ro) && eq_expr(l, r),
        (Lit(l), Lit(r)) => l.kind == r.kind,
        (Cast(l, lt), Cast(r, rt)) | (Type(l, lt), Type(r, rt)) => eq_expr(l, r) && eq_ty(lt, rt),
        (Let(lp, le), Let(rp, re)) => eq_pat(lp, rp) && eq_expr(le, re),
        (If(lc, lt, le), If(rc, rt, re)) => eq_expr(lc, rc) && eq_block(lt, rt) && eq_expr_opt(le, re),
        (While(lc, lt, ll), While(rc, rt, rl)) => eq_label(ll, rl) && eq_expr(lc, rc) && eq_block(lt, rt),
        (ForLoop(lp, li, lt, ll), ForLoop(rp, ri, rt, rl)) => {
            eq_label(ll, rl) && eq_pat(lp, rp) && eq_expr(li, ri) && eq_block(lt, rt)
        },
        (Loop(lt, ll), Loop(rt, rl)) => eq_label(ll, rl) && eq_block(lt, rt),
        (Block(lb, ll), Block(rb, rl)) => eq_label(ll, rl) && eq_block(lb, rb),
        (TryBlock(l), TryBlock(r)) => eq_block(l, r),
        (Yield(l), Yield(r)) | (Ret(l), Ret(r)) => eq_expr_opt(l, r),
        (Break(ll, le), Break(rl, re)) => eq_label(ll, rl) && eq_expr_opt(le, re),
        (Continue(ll), Continue(rl)) => eq_label(ll, rl),
        (Assign(l1, l2, _), Assign(r1, r2, _)) | (Index(l1, l2), Index(r1, r2)) => eq_expr(l1, r1) && eq_expr(l2, r2),
        (AssignOp(lo, lp, lv), AssignOp(ro, rp, rv)) => lo.node == ro.node && eq_expr(lp, rp) && eq_expr(lv, rv),
        (Field(lp, lf), Field(rp, rf)) => eq_id(*lf, *rf) && eq_expr(lp, rp),
        (Match(ls, la), Match(rs, ra)) => eq_expr(ls, rs) && over(la, ra, |l, r| eq_arm(l, r)),
        (Closure(lc, la, lm, lf, lb, _), Closure(rc, ra, rm, rf, rb, _)) => {
            lc == rc && la.is_async() == ra.is_async() && lm == rm && eq_fn_decl(lf, rf) && eq_expr(lb, rb)
        },
        (Async(lc, _, lb), Async(rc, _, rb)) => lc == rc && eq_block(lb, rb),
        (Range(lf, lt, ll), Range(rf, rt, rl)) => ll == rl && eq_expr_opt(lf, rf) && eq_expr_opt(lt, rt),
        (AddrOf(lbk, lm, le), AddrOf(rbk, rm, re)) => lbk == rbk && lm == rm && eq_expr(le, re),
        (Path(lq, lp), Path(rq, rp)) => both(lq, rq, |l, r| eq_qself(l, r)) && eq_path(lp, rp),
        (InlineAsm(_), InlineAsm(_)) => false, // Cutting some corners...
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        (Struct(lp, lfs, lb), Struct(rp, rfs, rb)) => {
            eq_path(lp, rp)
                && eq_expr_opt(lb, rb)
                && lfs.len() == rfs.len()
                && lfs.iter().all(|lf| rfs.iter().any(|rf| eq_field(lf, rf)))
        },
        _ => false,
    }
}

fn eq_field(l: &Field, r: &Field) -> bool {
    l.is_placeholder == r.is_placeholder
        && eq_id(l.ident, r.ident)
        && eq_expr(&l.expr, &r.expr)
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
}

fn eq_arm(l: &Arm, r: &Arm) -> bool {
    l.is_placeholder == r.is_placeholder
        && eq_pat(&l.pat, &r.pat)
        && eq_expr(&l.body, &r.body)
        && eq_expr_opt(&l.guard, &r.guard)
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
}

fn eq_label(l: &Option<Label>, r: &Option<Label>) -> bool {
    both(l, r, |l, r| eq_id(l.ident, r.ident))
}

fn eq_block(l: &Block, r: &Block) -> bool {
    l.rules == r.rules && over(&l.stmts, &r.stmts, |l, r| eq_stmt(l, r))
}

fn eq_stmt(l: &Stmt, r: &Stmt) -> bool {
    use StmtKind::*;
    match (&l.kind, &r.kind) {
        (Local(l), Local(r)) => {
            eq_pat(&l.pat, &r.pat)
                && both(&l.ty, &r.ty, |l, r| eq_ty(l, r))
                && eq_expr_opt(&l.init, &r.init)
                && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
        },
        (Item(l), Item(r)) => eq_item(l, r, eq_item_kind),
        (Expr(l), Expr(r)) | (Semi(l), Semi(r)) => eq_expr(l, r),
        (Empty, Empty) => true,
        (MacCall(l), MacCall(r)) => l.1 == r.1 && eq_mac_call(&l.0, &r.0) && over(&l.2, &r.2, |l, r| eq_attr(l, r)),
        _ => false,
    }
}

fn eq_item<K>(l: &Item<K>, r: &Item<K>, mut eq_kind: impl FnMut(&K, &K) -> bool) -> bool {
    eq_id(l.ident, r.ident)
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
        && eq_vis(&l.vis, &r.vis)
        && eq_kind(&l.kind, &r.kind)
}

fn eq_item_kind(l: &ItemKind, r: &ItemKind) -> bool {
    use ItemKind::*;
    match (l, r) {
        (ExternCrate(l), ExternCrate(r)) => l == r,
        (Use(l), Use(r)) => eq_use_tree(l, r),
        (Static(lt, lm, le), Static(rt, rm, re)) => lm == rm && eq_ty(lt, rt) && eq_expr_opt(le, re),
        (Const(ld, lt, le), Const(rd, rt, re)) => eq_defaultness(*ld, *rd) && eq_ty(lt, rt) && eq_expr_opt(le, re),
        (Fn(ld, lf, lg, lb), Fn(rd, rf, rg, rb)) => {
            eq_defaultness(*ld, *rd) && eq_fn_sig(lf, rf) && eq_generics(lg, rg) && both(lb, rb, |l, r| eq_block(l, r))
        },
        (Mod(l), Mod(r)) => l.inline == r.inline && over(&l.items, &r.items, |l, r| eq_item(l, r, eq_item_kind)),
        (ForeignMod(l), ForeignMod(r)) => {
            both(&l.abi, &r.abi, |l, r| eq_str_lit(l, r))
                && over(&l.items, &r.items, |l, r| eq_item(l, r, eq_foreign_item_kind))
        },
        (GlobalAsm(_), GlobalAsm(_)) => false, // Cutting corners..
        (TyAlias(ld, lg, lb, lt), TyAlias(rd, rg, rb, rt)) => {
            eq_defaultness(*ld, *rd)
                && eq_generics(lg, rg)
                && over(lb, rb, |l, r| eq_generic_bound(l, r))
                && both(lt, rt, |l, r| eq_ty(l, r))
        },
        (Enum(le, lg), Enum(re, rg)) => {
            over(&le.variants, &re.variants, |l, r| eq_variant(l, r)) && eq_generics(lg, rg)
        },
        (Struct(lv, lg), Struct(rv, rg)) | (Union(lv, lg), Union(rv, rg)) => {
            eq_variant_data(lv, rv) && eq_generics(lg, rg)
        },
        (Trait(la, lu, lg, lb, li), Trait(ra, ru, rg, rb, ri)) => {
            la == ra
                && matches!(lu, Unsafe::No) == matches!(ru, Unsafe::No)
                && eq_generics(lg, rg)
                && over(lb, rb, |l, r| eq_generic_bound(l, r))
                && over(li, ri, |l, r| eq_item(l, r, eq_assoc_item_kind))
        },
        (TraitAlias(lg, lb), TraitAlias(rg, rb)) => eq_generics(lg, rg) && over(lb, rb, |l, r| eq_generic_bound(l, r)),
        (
            Impl {
                unsafety: lu,
                polarity: lp,
                defaultness: ld,
                constness: lc,
                generics: lg,
                of_trait: lot,
                self_ty: lst,
                items: li,
            },
            Impl {
                unsafety: ru,
                polarity: rp,
                defaultness: rd,
                constness: rc,
                generics: rg,
                of_trait: rot,
                self_ty: rst,
                items: ri,
            },
        ) => {
            matches!(lu, Unsafe::No) == matches!(ru, Unsafe::No)
                && matches!(lp, ImplPolarity::Positive) == matches!(rp, ImplPolarity::Positive)
                && eq_defaultness(*ld, *rd)
                && matches!(lc, ast::Const::No) == matches!(rc, ast::Const::No)
                && eq_generics(lg, rg)
                && both(lot, rot, |l, r| eq_path(&l.path, &r.path))
                && eq_ty(lst, rst)
                && over(li, ri, |l, r| eq_item(l, r, eq_assoc_item_kind))
        },
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        (MacroDef(l), MacroDef(r)) => l.macro_rules == r.macro_rules && eq_mac_args(&l.body, &r.body),
        _ => false,
    }
}

fn eq_foreign_item_kind(l: &ForeignItemKind, r: &ForeignItemKind) -> bool {
    use ForeignItemKind::*;
    match (l, r) {
        (Static(lt, lm, le), Static(rt, rm, re)) => lm == rm && eq_ty(lt, rt) && eq_expr_opt(le, re),
        (Fn(ld, lf, lg, lb), Fn(rd, rf, rg, rb)) => {
            eq_defaultness(*ld, *rd) && eq_fn_sig(lf, rf) && eq_generics(lg, rg) && both(lb, rb, |l, r| eq_block(l, r))
        },
        (TyAlias(ld, lg, lb, lt), TyAlias(rd, rg, rb, rt)) => {
            eq_defaultness(*ld, *rd)
                && eq_generics(lg, rg)
                && over(lb, rb, |l, r| eq_generic_bound(l, r))
                && both(lt, rt, |l, r| eq_ty(l, r))
        },
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_assoc_item_kind(l: &AssocItemKind, r: &AssocItemKind) -> bool {
    use AssocItemKind::*;
    match (l, r) {
        (Const(ld, lt, le), Const(rd, rt, re)) => eq_defaultness(*ld, *rd) && eq_ty(lt, rt) && eq_expr_opt(le, re),
        (Fn(ld, lf, lg, lb), Fn(rd, rf, rg, rb)) => {
            eq_defaultness(*ld, *rd) && eq_fn_sig(lf, rf) && eq_generics(lg, rg) && both(lb, rb, |l, r| eq_block(l, r))
        },
        (TyAlias(ld, lg, lb, lt), TyAlias(rd, rg, rb, rt)) => {
            eq_defaultness(*ld, *rd)
                && eq_generics(lg, rg)
                && over(lb, rb, |l, r| eq_generic_bound(l, r))
                && both(lt, rt, |l, r| eq_ty(l, r))
        },
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_variant(l: &Variant, r: &Variant) -> bool {
    l.is_placeholder == r.is_placeholder
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
        && eq_vis(&l.vis, &r.vis)
        && eq_id(l.ident, r.ident)
        && eq_variant_data(&l.data, &r.data)
        && both(&l.disr_expr, &r.disr_expr, |l, r| eq_expr(&l.value, &r.value))
}

fn eq_variant_data(l: &VariantData, r: &VariantData) -> bool {
    use VariantData::*;
    match (l, r) {
        (Unit(_), Unit(_)) => true,
        (Struct(l, _), Struct(r, _)) | (Tuple(l, _), Tuple(r, _)) => over(l, r, |l, r| eq_struct_field(l, r)),
        _ => false,
    }
}

fn eq_struct_field(l: &StructField, r: &StructField) -> bool {
    l.is_placeholder == r.is_placeholder
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
        && eq_vis(&l.vis, &r.vis)
        && both(&l.ident, &r.ident, |l, r| eq_id(*l, *r))
        && eq_ty(&l.ty, &r.ty)
}

fn eq_fn_sig(l: &FnSig, r: &FnSig) -> bool {
    eq_fn_decl(&l.decl, &r.decl) && eq_fn_header(&l.header, &r.header)
}

fn eq_fn_header(l: &FnHeader, r: &FnHeader) -> bool {
    matches!(l.unsafety, Unsafe::No) == matches!(r.unsafety, Unsafe::No)
        && l.asyncness.is_async() == r.asyncness.is_async()
        && matches!(l.constness, Const::No) == matches!(r.constness, Const::No)
        && eq_ext(&l.ext, &r.ext)
}

fn eq_generics(l: &Generics, r: &Generics) -> bool {
    over(&l.params, &r.params, |l, r| eq_generic_param(l, r))
        && over(&l.where_clause.predicates, &r.where_clause.predicates, |l, r| {
            eq_where_predicate(l, r)
        })
}

fn eq_where_predicate(l: &WherePredicate, r: &WherePredicate) -> bool {
    use WherePredicate::*;
    match (l, r) {
        (BoundPredicate(l), BoundPredicate(r)) => {
            over(&l.bound_generic_params, &r.bound_generic_params, |l, r| {
                eq_generic_param(l, r)
            }) && eq_ty(&l.bounded_ty, &r.bounded_ty)
                && over(&l.bounds, &r.bounds, |l, r| eq_generic_bound(l, r))
        },
        (RegionPredicate(l), RegionPredicate(r)) => {
            eq_id(l.lifetime.ident, r.lifetime.ident) && over(&l.bounds, &r.bounds, |l, r| eq_generic_bound(l, r))
        },
        (EqPredicate(l), EqPredicate(r)) => eq_ty(&l.lhs_ty, &r.lhs_ty) && eq_ty(&l.rhs_ty, &r.rhs_ty),
        _ => false,
    }
}

fn eq_use_tree(l: &UseTree, r: &UseTree) -> bool {
    eq_path(&l.prefix, &r.prefix) && eq_use_tree_kind(&l.kind, &r.kind)
}

fn eq_use_tree_kind(l: &UseTreeKind, r: &UseTreeKind) -> bool {
    use UseTreeKind::*;
    match (l, r) {
        (Glob, Glob) => true,
        (Simple(l, _, _), Simple(r, _, _)) => both(l, r, |l, r| eq_id(*l, *r)),
        (Nested(l), Nested(r)) => over(l, r, |(l, _), (r, _)| eq_use_tree(l, r)),
        _ => false,
    }
}

fn eq_defaultness(l: Defaultness, r: Defaultness) -> bool {
    match (l, r) {
        (Defaultness::Final, Defaultness::Final) | (Defaultness::Default(_), Defaultness::Default(_)) => true,
        _ => false,
    }
}

fn eq_vis(l: &Visibility, r: &Visibility) -> bool {
    use VisibilityKind::*;
    match (&l.node, &r.node) {
        (Public, Public) | (Inherited, Inherited) | (Crate(_), Crate(_)) => true,
        (Restricted { path: l, .. }, Restricted { path: r, .. }) => eq_path(l, r),
        _ => false,
    }
}

fn eq_fn_decl(l: &FnDecl, r: &FnDecl) -> bool {
    eq_fn_ret_ty(&l.output, &r.output)
        && over(&l.inputs, &r.inputs, |l, r| {
            l.is_placeholder == r.is_placeholder
                && eq_pat(&l.pat, &r.pat)
                && eq_ty(&l.ty, &r.ty)
                && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
        })
}

fn eq_fn_ret_ty(l: &FnRetTy, r: &FnRetTy) -> bool {
    match (l, r) {
        (FnRetTy::Default(_), FnRetTy::Default(_)) => true,
        (FnRetTy::Ty(l), FnRetTy::Ty(r)) => eq_ty(l, r),
        _ => false,
    }
}

fn eq_ty(l: &Ty, r: &Ty) -> bool {
    use TyKind::*;
    match (&l.kind, &r.kind) {
        (Paren(l), _) => eq_ty(l, r),
        (_, Paren(r)) => eq_ty(l, r),
        (Never, Never) | (Infer, Infer) | (ImplicitSelf, ImplicitSelf) | (Err, Err) | (CVarArgs, CVarArgs) => true,
        (Slice(l), Slice(r)) => eq_ty(l, r),
        (Array(le, ls), Array(re, rs)) => eq_ty(le, re) && eq_expr(&ls.value, &rs.value),
        (Ptr(l), Ptr(r)) => l.mutbl == r.mutbl && eq_ty(&l.ty, &r.ty),
        (Rptr(ll, l), Rptr(rl, r)) => {
            both(ll, rl, |l, r| eq_id(l.ident, r.ident)) && l.mutbl == r.mutbl && eq_ty(&l.ty, &r.ty)
        },
        (BareFn(l), BareFn(r)) => {
            l.unsafety == r.unsafety
                && eq_ext(&l.ext, &r.ext)
                && over(&l.generic_params, &r.generic_params, |l, r| eq_generic_param(l, r))
                && eq_fn_decl(&l.decl, &r.decl)
        },
        (Tup(l), Tup(r)) => over(l, r, |l, r| eq_ty(l, r)),
        (Path(lq, lp), Path(rq, rp)) => both(lq, rq, |l, r| eq_qself(l, r)) && eq_path(lp, rp),
        (TraitObject(lg, ls), TraitObject(rg, rs)) => ls == rs && over(lg, rg, |l, r| eq_generic_bound(l, r)),
        (ImplTrait(_, lg), ImplTrait(_, rg)) => over(lg, rg, |l, r| eq_generic_bound(l, r)),
        (Typeof(l), Typeof(r)) => eq_expr(&l.value, &r.value),
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_ext(l: &Extern, r: &Extern) -> bool {
    use Extern::*;
    match (l, r) {
        (None, None) | (Implicit, Implicit) => true,
        (Explicit(l), Explicit(r)) => eq_str_lit(l, r),
        _ => false,
    }
}

fn eq_str_lit(l: &StrLit, r: &StrLit) -> bool {
    l.style == r.style && l.symbol == r.symbol && l.suffix == r.suffix
}

fn eq_poly_ref_trait(l: &PolyTraitRef, r: &PolyTraitRef) -> bool {
    eq_path(&l.trait_ref.path, &r.trait_ref.path)
        && over(&l.bound_generic_params, &r.bound_generic_params, |l, r| {
            eq_generic_param(l, r)
        })
}

fn eq_generic_param(l: &GenericParam, r: &GenericParam) -> bool {
    use GenericParamKind::*;
    l.is_placeholder == r.is_placeholder
        && eq_id(l.ident, r.ident)
        && over(&l.bounds, &r.bounds, |l, r| eq_generic_bound(l, r))
        && match (&l.kind, &r.kind) {
            (Lifetime, Lifetime) => true,
            (Type { default: l }, Type { default: r }) => both(l, r, |l, r| eq_ty(l, r)),
            (Const { ty: l }, Const { ty: r }) => eq_ty(l, r),
            _ => false,
        }
        && over(&l.attrs, &r.attrs, |l, r| eq_attr(l, r))
}

fn eq_generic_bound(l: &GenericBound, r: &GenericBound) -> bool {
    use GenericBound::*;
    match (l, r) {
        (Trait(ptr1, tbm1), Trait(ptr2, tbm2)) => tbm1 == tbm2 && eq_poly_ref_trait(ptr1, ptr2),
        (Outlives(l), Outlives(r)) => eq_id(l.ident, r.ident),
        _ => false,
    }
}

fn eq_assoc_constraint(l: &AssocTyConstraint, r: &AssocTyConstraint) -> bool {
    use AssocTyConstraintKind::*;
    eq_id(l.ident, r.ident)
        && match (&l.kind, &r.kind) {
            (Equality { ty: l }, Equality { ty: r }) => eq_ty(l, r),
            (Bound { bounds: l }, Bound { bounds: r }) => over(l, r, |l, r| eq_generic_bound(l, r)),
            _ => false,
        }
}

fn eq_mac_call(l: &MacCall, r: &MacCall) -> bool {
    eq_path(&l.path, &r.path) && eq_mac_args(&l.args, &r.args)
}

fn eq_attr(l: &Attribute, r: &Attribute) -> bool {
    use AttrKind::*;
    l.style == r.style
        && match (&l.kind, &r.kind) {
            (DocComment(l), DocComment(r)) => l == r,
            (Normal(l), Normal(r)) => eq_path(&l.path, &r.path) && eq_mac_args(&l.args, &r.args),
            _ => false,
        }
}

fn eq_mac_args(l: &MacArgs, r: &MacArgs) -> bool {
    use MacArgs::*;
    match (l, r) {
        (Empty, Empty) => true,
        (Delimited(_, ld, lts), Delimited(_, rd, rts)) => ld == rd && lts.eq_unspanned(rts),
        (Eq(_, lts), Eq(_, rts)) => lts.eq_unspanned(rts),
        _ => false,
    }
}
