//! Single-contact step certificate (phys-05d; SPEC §7 subset: one contact
//! row, no gravity, no snaps, no position integration, single-part shapes).
//! The full multi-row StepCert with ledgers and joints is phys-06.
//!
//! D8: the engine's claims rest on this checker, not on the solver — it
//! re-computes the impulse application (C1), the λ bounds (C2), the post
//! relative velocity (C3), and re-runs exact SAT on world polys it
//! transforms itself (C4). Each check is EXACT (ok == its spec), so a
//! weaker solver can only cause Reject, never a wrong accept — and scenes
//! prove ok == true from the spec side.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::body::Body;
use crate::broadphase::{world_verts, world_verts_exec};
use crate::narrowphase::{axis_separates, classify_side, no_axis_separates};
use crate::proofs::rational_raw::{lemma_unit_norm_raw, unit_norm_raw};
use crate::proofs::world::lemma_convex_poly_inv_world;
use crate::row::{
    apply_impulse_exec, lambda_in_bounds, row_vel_exec, row_vel_spec, vel_after_impulse, BoundQ,
    Row,
};
use crate::shape::{convex_poly_inv, edge_normal, min_sep, ConvexPoly};
use crate::types::{SVec2, Scalar};

verus! {

/// C1 (single row, impulse-only): post velocities/omegas are the
/// impulse-applied pre values and positions are unchanged (eqv per
/// component — the checker compares with exact rational equality).
pub open spec fn c1_single_contact(
    pre_a: Body,
    pre_b: Body,
    post_a: Body,
    post_b: Body,
    row: Row,
) -> bool {
    let app_a = vel_after_impulse(
        pre_a.inv_mass@, pre_a.inv_inertia@, row.jla.model@, row.jaa@, row.lambda@,
        pre_a.vel.model@, pre_a.omega@);
    let app_b = vel_after_impulse(
        pre_b.inv_mass@, pre_b.inv_inertia@, row.jlb.model@, row.jab@, row.lambda@,
        pre_b.vel.model@, pre_b.omega@);
    &&& post_a.vel.model@.x.eqv_spec(app_a.0.x)
    &&& post_a.vel.model@.y.eqv_spec(app_a.0.y)
    &&& post_a.omega@.eqv_spec(app_a.1)
    &&& post_b.vel.model@.x.eqv_spec(app_b.0.x)
    &&& post_b.vel.model@.y.eqv_spec(app_b.0.y)
    &&& post_b.omega@.eqv_spec(app_b.1)
    &&& post_a.pos.model@.x.eqv_spec(pre_a.pos.model@.x)
    &&& post_a.pos.model@.y.eqv_spec(pre_a.pos.model@.y)
    &&& post_b.pos.model@.x.eqv_spec(pre_b.pos.model@.x)
    &&& post_b.pos.model@.y.eqv_spec(pre_b.pos.model@.y)
}

/// One touching-witness for C4: edge (fa, e) has min_sep ≥ −tol_p.
pub open spec fn c4_touch_witness(
    wa: Seq<Vec2<Rational>>,
    wb: Seq<Vec2<Rational>>,
    tol_p: Rational,
    fa: bool,
    e: int,
) -> bool {
    let owner = if fa { wa } else { wb };
    let other = if fa { wb } else { wa };
    &&& 0 <= e < owner.len()
    &&& tol_p.neg_spec().le_spec(min_sep(
            edge_normal(owner[e], owner[(e + 1) % (owner.len() as int)]),
            owner[e], other, 0))
}

/// C4 (SPEC §7): the checker re-runs exact SAT on the post world polys
/// itself. Either a strict separating witness exists (either side), or no
/// axis separates and some edge's min separation is at least −tol_p (the
/// penetration-depth bound: the max over edges is the least-separating
/// axis, so ONE edge ≥ −tol_p is the depth statement).
pub open spec fn c4_single_contact(
    wa: Seq<Vec2<Rational>>,
    wb: Seq<Vec2<Rational>>,
    tol_p: Rational,
) -> bool {
    ||| exists|e: int| axis_separates(wa, wb, e)
    ||| exists|e: int| axis_separates(wb, wa, e)
    ||| (no_axis_separates(wa, wb) && exists|fa: bool, e: int| c4_touch_witness(
            wa, wb, tol_p, fa, e))
}

/// The world poly of a single-part body (spec view the checker computes).
pub open spec fn body_world_verts(b: Body) -> Seq<Vec2<Rational>>
    recommends b.shape.parts@.len() == 1
{
    world_verts(b.pos.model@, b.rot.c@, b.rot.s@, b.shape.model_parts()[0])
}

/// What the checker checks (exact: ok == this).
pub open spec fn contact_checks_pass(
    pre_a: Body,
    pre_b: Body,
    post_a: Body,
    post_b: Body,
    row: Row,
    tol_v: Rational,
    tol_p: Rational,
) -> bool {
    &&& c1_single_contact(pre_a, pre_b, post_a, post_b, row)
    &&& lambda_in_bounds(row.lo.val(), row.hi.val(), row.lambda@)
    &&& tol_v.neg_spec().le_spec(row_vel_spec(
            row.jla.model@, row.jaa@, row.jlb.model@, row.jab@,
            post_a.vel.model@, post_a.omega@, post_b.vel.model@, post_b.omega@))
    &&& convex_poly_inv(body_world_verts(post_a))
    &&& convex_poly_inv(body_world_verts(post_b))
    &&& c4_single_contact(body_world_verts(post_a), body_world_verts(post_b), tol_p)
}

/// The certificate claim (C1–C4; C5 joints and C6 ledgers are N/A for an
/// impulse-only step — phys-06).
pub open spec fn contact_step_certified(
    pre_a: Body,
    pre_b: Body,
    post_a: Body,
    post_b: Body,
    row: Row,
    tol_v: Rational,
    tol_p: Rational,
) -> bool {
    &&& c1_single_contact(pre_a, pre_b, post_a, post_b, row)
    &&& lambda_in_bounds(row.lo.val(), row.hi.val(), row.lambda@)
    &&& tol_v.neg_spec().le_spec(row_vel_spec(
            row.jla.model@, row.jaa@, row.jlb.model@, row.jab@,
            post_a.vel.model@, post_a.omega@, post_b.vel.model@, post_b.omega@))
    &&& c4_single_contact(body_world_verts(post_a), body_world_verts(post_b), tol_p)
}

// ── per-check exec functions (each exact: ok == spec) ─────────────────

/// C1: re-compute the impulse application and compare exactly.
pub fn check_c1(pre_a: &Body, pre_b: &Body, post_a: &Body, post_b: &Body, row: &Row) -> (ok: bool)
    requires
        pre_a.wf_spec(),
        pre_b.wf_spec(),
        post_a.wf_spec(),
        post_b.wf_spec(),
        row.wf_spec(),
    ensures
        ok == c1_single_contact(*pre_a, *pre_b, *post_a, *post_b, *row),
{
    let app_a = apply_impulse_exec(pre_a, &row.jla, &row.jaa, &row.lambda);
    let app_b = apply_impulse_exec(pre_b, &row.jlb, &row.jab, &row.lambda);
    let ok = app_a.vel.x.eq(&post_a.vel.x) && app_a.vel.y.eq(&post_a.vel.y)
        && app_a.omega.eq(&post_a.omega)
        && app_b.vel.x.eq(&post_b.vel.x) && app_b.vel.y.eq(&post_b.vel.y)
        && app_b.omega.eq(&post_b.omega)
        && post_a.pos.x.eq(&pre_a.pos.x) && post_a.pos.y.eq(&pre_a.pos.y)
        && post_b.pos.x.eq(&pre_b.pos.x) && post_b.pos.y.eq(&pre_b.pos.y);
    proof {
        // eq is eqv in one direction per component; c1 wants eqv(post, app)
        Rational::lemma_eqv_symmetric(app_a.vel.x@, post_a.vel.x@);
        Rational::lemma_eqv_symmetric(app_a.vel.y@, post_a.vel.y@);
        Rational::lemma_eqv_symmetric(app_a.omega@, post_a.omega@);
        Rational::lemma_eqv_symmetric(app_b.vel.x@, post_b.vel.x@);
        Rational::lemma_eqv_symmetric(app_b.vel.y@, post_b.vel.y@);
        Rational::lemma_eqv_symmetric(app_b.omega@, post_b.omega@);
    }
    ok
}

/// C2: λ within [lo, hi].
pub fn check_c2(row: &Row) -> (ok: bool)
    requires
        row.wf_spec(),
    ensures
        ok == lambda_in_bounds(row.lo.val(), row.hi.val(), row.lambda@),
{
    let lo_ok = match &row.lo {
        BoundQ::Finite(l) => l.le(&row.lambda),
        BoundQ::Inf => true,
    };
    let hi_ok = match &row.hi {
        BoundQ::Finite(h) => row.lambda.le(h),
        BoundQ::Inf => true,
    };
    lo_ok && hi_ok
}

/// C3: post relative normal velocity ≥ −tol_v.
pub fn check_c3(row: &Row, post_a: &Body, post_b: &Body, tol_v: &Scalar) -> (ok: bool)
    requires
        row.wf_spec(),
        post_a.wf_spec(),
        post_b.wf_spec(),
        tol_v.wf_spec(),
    ensures
        ok == tol_v@.neg_spec().le_spec(row_vel_spec(
            row.jla.model@, row.jaa@, row.jlb.model@, row.jab@,
            post_a.vel.model@, post_a.omega@, post_b.vel.model@, post_b.omega@)),
{
    let rv = row_vel_exec(row, post_a, post_b);
    let ntol_v = tol_v.neg();
    ntol_v.le(&rv)
}

/// C4: transform world polys, verify convexity, re-run SAT, depth-check.
pub fn check_c4(post_a: &Body, post_b: &Body, tol_p: &Scalar) -> (ok: bool)
    requires
        post_a.wf_spec(),
        post_b.wf_spec(),
        tol_p.wf_spec(),
        post_a.shape.parts@.len() == 1,
        post_b.shape.parts@.len() == 1,
    ensures
        ok == (convex_poly_inv(body_world_verts(*post_a))
            && convex_poly_inv(body_world_verts(*post_b))
            && c4_single_contact(body_world_verts(*post_a), body_world_verts(*post_b), tol_p@)),
{
    proof {
        assert(post_a.shape.parts@[0].wf_spec());
        assert(post_b.shape.parts@[0].wf_spec());
    }
    let wa_v = world_verts_exec(&post_a.pos, &post_a.rot, &post_a.shape.parts[0]);
    let wb_v = world_verts_exec(&post_b.pos, &post_b.rot, &post_b.shape.parts[0]);
    proof {
        assert(wa_v@.map(|_i: int, v: SVec2| v.model@) == body_world_verts(*post_a));
        assert(wb_v@.map(|_i: int, v: SVec2| v.model@) == body_world_verts(*post_b));
    }
    let wa_o = ConvexPoly::new_checked(wa_v);
    let wb_o = ConvexPoly::new_checked(wb_v);
    if wa_o.is_none() || wb_o.is_none() {
        proof {
            assert(!convex_poly_inv(body_world_verts(*post_a))
                || !convex_poly_inv(body_world_verts(*post_b)));
        }
        return false;
    }
    proof {
        // both world polys are convex (rigid motion preserves the invariant)
        lemma_unit_norm_raw(post_a.rot.c@, post_a.rot.s@);
        lemma_unit_norm_raw(post_b.rot.c@, post_b.rot.s@);
        lemma_convex_poly_inv_world(
            post_a.pos.model@, post_a.rot.c@, post_a.rot.s@, body_world_verts(*post_a));
        lemma_convex_poly_inv_world(
            post_b.pos.model@, post_b.rot.c@, post_b.rot.s@, body_world_verts(*post_b));
    }
    let wa = wa_o.unwrap();
    let wb = wb_o.unwrap();
    let (sep_a, e_a, ms_a) = classify_side(&wa, &wb);
    if sep_a.is_some() {
        proof {
            let e = sep_a->Some_0;
            assert(axis_separates(wa.model_verts(), wb.model_verts(), e as int));
            assert(wa.model_verts() == body_world_verts(*post_a));
            assert(wb.model_verts() == body_world_verts(*post_b));
            assert(c4_single_contact(body_world_verts(*post_a), body_world_verts(*post_b), tol_p@));
        }
        return true;
    }
    let (sep_b, e_b, ms_b) = classify_side(&wb, &wa);
    if sep_b.is_some() {
        proof {
            let e = sep_b->Some_0;
            assert(axis_separates(wb.model_verts(), wa.model_verts(), e as int));
            assert(c4_single_contact(body_world_verts(*post_a), body_world_verts(*post_b), tol_p@));
        }
        return true;
    }
    // touching: depth check on the global max(ms_a, ms_b)
    let ntol_p = tol_p.neg();
    let a_ge_b = ms_a.ge(&ms_b);
    let depth_ok = if a_ge_b {
        ntol_p.le(&ms_a)
    } else {
        ntol_p.le(&ms_b)
    };
    proof {
        let wva = wa.model_verts();
        let wvb = wb.model_verts();
        assert(no_axis_separates(wva, wvb));
        assert(wva.len() >= 3);
        assert(wvb.len() >= 3);
        if depth_ok {
            crate::proofs::cert::lemma_c4_witness_of_depth(
                wva, wvb, ms_a@, ms_b@, e_a as int, e_b as int, tol_p@, a_ge_b);
            assert(c4_single_contact(wva, wvb, tol_p@));
        } else {
            crate::proofs::cert::lemma_no_sep_witness_of_all_nonpos(wva, wvb);
            crate::proofs::cert::lemma_no_sep_witness_of_all_nonpos(wvb, wva);
            crate::proofs::cert::lemma_c4_no_witness_of_shallow(
                wva, wvb, ms_a@, ms_b@, tol_p@, a_ge_b);
            assert(!c4_single_contact(wva, wvb, tol_p@));
        }
    }
    depth_ok
}

/// The proven checker (SPEC §7 shape): ok == the checks pass, and
/// ok ⟹ the step is certified.
pub fn check_contact_step(
    pre_a: &Body,
    pre_b: &Body,
    post_a: &Body,
    post_b: &Body,
    row: &Row,
    tol_v: &Scalar,
    tol_p: &Scalar,
) -> (ok: bool)
    requires
        pre_a.wf_spec(),
        pre_b.wf_spec(),
        post_a.wf_spec(),
        post_b.wf_spec(),
        row.wf_spec(),
        tol_v.wf_spec(),
        tol_p.wf_spec(),
        post_a.shape.parts@.len() == 1,
        post_b.shape.parts@.len() == 1,
    ensures
        ok == contact_checks_pass(*pre_a, *pre_b, *post_a, *post_b, *row, tol_v@, tol_p@),
        ok ==> contact_step_certified(*pre_a, *pre_b, *post_a, *post_b, *row, tol_v@, tol_p@),
{
    let c1 = check_c1(pre_a, pre_b, post_a, post_b, row);
    let c2 = check_c2(row);
    let c3 = check_c3(row, post_a, post_b, tol_v);
    let c4 = check_c4(post_a, post_b, tol_p);
    c1 && c2 && c3 && c4
}

} // verus!
