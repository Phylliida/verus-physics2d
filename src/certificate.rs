//! Single-contact step certificate (phys-05d; SPEC §7 subset: one contact
//! row, no gravity, no snaps, no position integration, single-part shapes).
//! The full multi-row checker (C1–C7) is phys-06; the StepCert/SnapEntry
//! datatypes (SPEC §7) already live here.
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
use crate::joints::Joint;
use crate::massprops::{vdot, vscale, vzero};
use crate::narrowphase::{axis_separates, classify_side, no_axis_separates};
use crate::proofs::rational_raw::{lemma_unit_norm_raw, unit_norm_raw};
use crate::proofs::world::lemma_convex_poly_inv_world;
use crate::row::{
    apply_impulse_exec, lambda_in_bounds, row_vel_exec, row_vel_spec, vel_after_impulse, BoundQ,
    Row,
};
use crate::shape::{convex_poly_inv, edge_normal, min_sep, vadd, vsub, ConvexPoly};
use crate::step::body_dynamic;
use crate::types::{SVec2, Scalar};
use crate::world::World;

verus! {

/// Which field a snap entry applies to (SPEC §7, D3/E5).
pub enum SnapKind {
    VelX,
    VelY,
    Omega,
    PosX,
    PosY,
}

/// One declared snap: the value-changing rounding of a single component
/// (SPEC §7). The checker (C6a) recomputes the actual signed delta from
/// pre/post fields and requires |actual| ≤ bound.
pub struct SnapEntry {
    pub body: usize,
    pub kind: SnapKind,
    /// The actual signed delta applied.
    pub delta: Scalar,
    /// The declared bound: |delta| ≤ bound.
    pub bound: Scalar,
}

impl SnapEntry {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.delta.wf_spec()
        &&& self.bound.wf_spec()
    }
}

/// The full step certificate (SPEC §7): the untrusted witness the checker
/// re-verifies. rows carries the final λ per row; tan_halfs and
/// angle_entries are per body; snaps is vacuous until 06c.
pub struct StepCert {
    pub rows: Vec<Row>,
    pub tan_halfs: Vec<Scalar>,
    pub snaps: Vec<SnapEntry>,
    pub angle_entries: Vec<Scalar>,
}

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

verus! {

// ── phys-06 step certificate: folds + C1/C2/C3/C5 ─────────────────────
// Structural discipline: spec folds are left-nested and exec folds build
// SVec2 via ::new over per-component RuntimeRational ops (raw models), so
// exec results match the spec folds with structural equality — no
// canonical bridges needed.

/// Vec2 component-wise equivalence.
pub open spec fn veqv(a: Vec2<Rational>, b: Vec2<Rational>) -> bool {
    &&& a.x.eqv_spec(b.x)
    &&& a.y.eqv_spec(b.y)
}

/// Linear impulse applied to body i by the first k rows (λ·jl per row).
pub open spec fn impulse_sum_lin(rows: Seq<Row>, i: int, k: int) -> Vec2<Rational>
    decreases k
{
    if k <= 0 {
        vzero()
    } else {
        let prev = impulse_sum_lin(rows, i, (k - 1) as int);
        let r = rows[k - 1];
        if r.a as int == i {
            vadd(prev, vscale(r.lambda@, r.jla.model@))
        } else if r.b as int == i {
            vadd(prev, vscale(r.lambda@, r.jlb.model@))
        } else {
            prev
        }
    }
}

/// Angular impulse applied to body i by the first k rows (λ·ja per row).
pub open spec fn impulse_sum_ang(rows: Seq<Row>, i: int, k: int) -> Rational
    decreases k
{
    if k <= 0 {
        Rational::from_int_spec(0)
    } else {
        let prev = impulse_sum_ang(rows, i, (k - 1) as int);
        let r = rows[k - 1];
        if r.a as int == i {
            prev.add_spec(r.lambda@.mul_spec(r.jaa@))
        } else if r.b as int == i {
            prev.add_spec(r.lambda@.mul_spec(r.jab@))
        } else {
            prev
        }
    }
}

/// Velocity snap deltas applied to body i by the first k snap entries.
pub open spec fn snap_delta_lin(snaps: Seq<SnapEntry>, i: int, k: int) -> Vec2<Rational>
    decreases k
{
    if k <= 0 {
        vzero()
    } else {
        let prev = snap_delta_lin(snaps, i, (k - 1) as int);
        let s = snaps[k - 1];
        if s.body as int == i && s.kind is VelX {
            vadd(prev, Vec2 { x: s.delta@, y: Rational::from_int_spec(0) })
        } else if s.body as int == i && s.kind is VelY {
            vadd(prev, Vec2 { x: Rational::from_int_spec(0), y: s.delta@ })
        } else {
            prev
        }
    }
}

/// Omega snap deltas applied to body i by the first k snap entries.
pub open spec fn snap_delta_ang(snaps: Seq<SnapEntry>, i: int, k: int) -> Rational
    decreases k
{
    if k <= 0 {
        Rational::from_int_spec(0)
    } else {
        let prev = snap_delta_ang(snaps, i, (k - 1) as int);
        let s = snaps[k - 1];
        if s.body as int == i && s.kind is Omega {
            prev.add_spec(s.delta@)
        } else {
            prev
        }
    }
}

/// C1 per body (exact velocity bookkeeping, SPEC §7): post velocities are
/// pre + gravity (dynamic only) + the impulses of every row touching the
/// body (computed from the cert's final λ) + declared snap deltas.
pub open spec fn c1_body_step(pre: World, post: World, cert: StepCert, i: int) -> bool
    recommends 0 <= i < pre.bodies@.len()
{
    let pb = pre.bodies@[i];
    let qb = post.bodies@[i];
    let gdv = if body_dynamic(pb) {
        vscale(pre.dt@, pre.gravity.model@)
    } else {
        vzero()
    };
    let rn = cert.rows@.len();
    let sn = cert.snaps@.len();
    &&& veqv(
        qb.vel.model@,
        vadd(
            vadd(vadd(pb.vel.model@, gdv), vscale(pb.inv_mass@, impulse_sum_lin(cert.rows@, i, rn as int))),
            snap_delta_lin(cert.snaps@, i, sn as int)))
    &&& qb.omega@.eqv_spec(
        pb.omega@.add_spec(
            pb.inv_inertia@.mul_spec(impulse_sum_ang(cert.rows@, i, rn as int))).add_spec(
                snap_delta_ang(cert.snaps@, i, sn as int)))
    // static bodies are frozen (the pipeline never integrates them) —
    // this is what makes C4's static-static pair skip sound
    &&& (!body_dynamic(pb) ==> {
        &&& veqv(qb.pos.model@, pb.pos.model@)
        &&& qb.rot.c@.eqv_spec(pb.rot.c@)
        &&& qb.rot.s@.eqv_spec(pb.rot.s@)
    })
}

/// C1 over all bodies.
pub open spec fn c1_step_bookkeeping(pre: World, post: World, cert: StepCert) -> bool {
    &&& post.bodies@.len() == pre.bodies@.len()
    &&& forall|i: int| 0 <= i < pre.bodies@.len() ==> c1_body_step(pre, post, cert, i)
}

/// C1 exec: fold rows/snaps per body, recompute expected velocities,
/// compare components exactly (ok == its spec).
pub fn check_c1_body(pre: &World, post: &World, cert: &StepCert, i: usize) -> (ok: bool)
    requires
        pre.wf_spec(),
        post.wf_spec(),
        i < pre.bodies@.len(),
        post.bodies@.len() == pre.bodies@.len(),
        forall|k: int| 0 <= k < cert.rows@.len() ==> (#[trigger] cert.rows@[k]).wf_spec(),
        forall|k: int| 0 <= k < cert.snaps@.len() ==> (#[trigger] cert.snaps@[k]).wf_spec(),
    ensures
        ok == c1_body_step(*pre, *post, *cert, i as int),
{
    let mut sum_lin = SVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0));
    let mut sum_ang = RuntimeRational::from_int(0);
    let mut k: usize = 0;
    while k < cert.rows.len()
        invariant
            k <= cert.rows@.len(),
            i < pre.bodies@.len(),
            sum_lin.wf_spec(),
            sum_ang.wf_spec(),
            sum_lin.model@ == impulse_sum_lin(cert.rows@, i as int, k as int),
            sum_ang@ == impulse_sum_ang(cert.rows@, i as int, k as int),
            forall|k2: int| 0 <= k2 < cert.rows@.len() ==> (#[trigger] cert.rows@[k2]).wf_spec(),
        decreases cert.rows.len() - k,
    {
        let r = &cert.rows[k];
        if r.a == i {
            let cx = r.jla.x.mul(&r.lambda);
            let cy = r.jla.y.mul(&r.lambda);
            sum_lin = SVec2::new(sum_lin.x.add(&cx), sum_lin.y.add(&cy));
            sum_ang = sum_ang.add(&r.lambda.mul(&r.jaa));
            proof {
                assert(sum_lin.model@ == impulse_sum_lin(cert.rows@, i as int, (k + 1) as int)) by {
                    reveal_with_fuel(impulse_sum_lin, 2);
                };
                assert(sum_ang@ == impulse_sum_ang(cert.rows@, i as int, (k + 1) as int)) by {
                    reveal_with_fuel(impulse_sum_ang, 2);
                };
            }
        } else if r.b == i {
            let cx = r.jlb.x.mul(&r.lambda);
            let cy = r.jlb.y.mul(&r.lambda);
            sum_lin = SVec2::new(sum_lin.x.add(&cx), sum_lin.y.add(&cy));
            sum_ang = sum_ang.add(&r.lambda.mul(&r.jab));
            proof {
                assert(sum_lin.model@ == impulse_sum_lin(cert.rows@, i as int, (k + 1) as int)) by {
                    reveal_with_fuel(impulse_sum_lin, 2);
                };
                assert(sum_ang@ == impulse_sum_ang(cert.rows@, i as int, (k + 1) as int)) by {
                    reveal_with_fuel(impulse_sum_ang, 2);
                };
            }
        }
        k = k + 1;
    }
    let mut snap_lin = SVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0));
    let mut snap_ang = RuntimeRational::from_int(0);
    let mut sk: usize = 0;
    while sk < cert.snaps.len()
        invariant
            sk <= cert.snaps@.len(),
            i < pre.bodies@.len(),
            snap_lin.wf_spec(),
            snap_ang.wf_spec(),
            snap_lin.model@ == snap_delta_lin(cert.snaps@, i as int, sk as int),
            snap_ang@ == snap_delta_ang(cert.snaps@, i as int, sk as int),
            forall|k2: int| 0 <= k2 < cert.snaps@.len() ==> (#[trigger] cert.snaps@[k2]).wf_spec(),
        decreases cert.snaps.len() - sk,
    {
        let s = &cert.snaps[sk];
        if s.body == i {
            match s.kind {
                SnapKind::VelX => {
                    let nx = snap_lin.x.add(&s.delta);
                    snap_lin = SVec2::new(nx, verus_rational::runtime_rational::copy_rational(
                        &snap_lin.y));
                    proof {
                        assert(snap_lin.model@ == snap_delta_lin(
                            cert.snaps@, i as int, (sk + 1) as int)) by {
                            reveal_with_fuel(snap_delta_lin, 2);
                        };
                    }
                },
                SnapKind::VelY => {
                    let ny = snap_lin.y.add(&s.delta);
                    snap_lin = SVec2::new(verus_rational::runtime_rational::copy_rational(
                        &snap_lin.x), ny);
                    proof {
                        assert(snap_lin.model@ == snap_delta_lin(
                            cert.snaps@, i as int, (sk + 1) as int)) by {
                            reveal_with_fuel(snap_delta_lin, 2);
                        };
                    }
                },
                SnapKind::Omega => {
                    snap_ang = snap_ang.add(&s.delta);
                    proof {
                        assert(snap_ang@ == snap_delta_ang(
                            cert.snaps@, i as int, (sk + 1) as int)) by {
                            reveal_with_fuel(snap_delta_ang, 2);
                        };
                    }
                },
                SnapKind::PosX => {},
                SnapKind::PosY => {},
            }
        }
        sk = sk + 1;
    }
    let pb = &pre.bodies[i];
    let qb = &post.bodies[i];
    let zero = RuntimeRational::from_int(0);
    let is_static = pb.inv_mass.eq(&zero);
    proof {
        assert(is_static == (pb.inv_mass@.num == 0));
        assert(is_static == !body_dynamic(*pb));
    }
    let (evx, evy) = if is_static {
        (RuntimeRational::from_int(0), RuntimeRational::from_int(0))
    } else {
        (pre.gravity.x.mul(&pre.dt), pre.gravity.y.mul(&pre.dt))
    };
    let ex = pb.vel.x.add(&evx).add(&pb.inv_mass.mul(&sum_lin.x)).add(&snap_lin.x);
    let ey = pb.vel.y.add(&evy).add(&pb.inv_mass.mul(&sum_lin.y)).add(&snap_lin.y);
    let eom = pb.omega.add(&pb.inv_inertia.mul(&sum_ang)).add(&snap_ang);
    let okx = ex.eq(&qb.vel.x);
    let oky = ey.eq(&qb.vel.y);
    let okom = eom.eq(&qb.omega);
    let okpos = if is_static {
        qb.pos.x.eq(&pb.pos.x) && qb.pos.y.eq(&pb.pos.y)
            && qb.rot.c.eq(&pb.rot.c) && qb.rot.s.eq(&pb.rot.s)
    } else {
        true
    };
    proof {
        // static branch: the expected components match vzero() form
        if is_static {
            assert(evx@ == Rational::from_int_spec(0));
            assert(evy@ == Rational::from_int_spec(0));
        }
    }
    okx && oky && okom && okpos
}

/// C1 over all bodies (ok == its spec).
pub fn check_c1_rows(pre: &World, post: &World, cert: &StepCert) -> (ok: bool)
    requires
        pre.wf_spec(),
        post.wf_spec(),
        post.bodies@.len() == pre.bodies@.len(),
        forall|k: int| 0 <= k < cert.rows@.len() ==> (#[trigger] cert.rows@[k]).wf_spec(),
        forall|k: int| 0 <= k < cert.snaps@.len() ==> (#[trigger] cert.snaps@[k]).wf_spec(),
    ensures
        ok == c1_step_bookkeeping(*pre, *post, *cert),
{
    let mut i: usize = 0;
    let mut ok = true;
    while i < pre.bodies.len()
        invariant
            i <= pre.bodies@.len(),
            pre.wf_spec(),
            post.wf_spec(),
            post.bodies@.len() == pre.bodies@.len(),
            forall|k: int| 0 <= k < cert.rows@.len() ==> (#[trigger] cert.rows@[k]).wf_spec(),
            forall|k: int| 0 <= k < cert.snaps@.len() ==> (#[trigger] cert.snaps@[k]).wf_spec(),
            ok == forall|j: int| 0 <= j < i as int ==> c1_body_step(*pre, *post, *cert, j),
        decreases pre.bodies.len() - i,
    {
        let ok_i = check_c1_body(pre, post, cert, i);
        ok = ok && ok_i;
        proof {
            assert(ok_i == c1_body_step(*pre, *post, *cert, i as int));
        }
        i = i + 1;
    }
    ok
}

/// C2 (bounds): every row's final λ within [lo, hi].
pub open spec fn c2_step_bounds(rows: Seq<Row>) -> bool {
    forall|k: int|
        0 <= k < rows.len() ==> lambda_in_bounds(
            #[trigger] rows[k].lo.val(), rows[k].hi.val(), rows[k].lambda@)
}

/// C2 exec (ok == its spec).
pub fn check_c2_rows(cert: &StepCert) -> (ok: bool)
    requires
        forall|k: int| 0 <= k < cert.rows@.len() ==> (#[trigger] cert.rows@[k]).wf_spec(),
    ensures
        ok == c2_step_bounds(cert.rows@),
{
    let mut k: usize = 0;
    let mut ok = true;
    while k < cert.rows.len()
        invariant
            k <= cert.rows@.len(),
            forall|k2: int| 0 <= k2 < cert.rows@.len() ==> (#[trigger] cert.rows@[k2]).wf_spec(),
            ok == forall|k2: int|
                0 <= k2 < k as int ==> lambda_in_bounds(
                    #[trigger] cert.rows@[k2].lo.val(), cert.rows@[k2].hi.val(),
                    cert.rows@[k2].lambda@),
        decreases cert.rows.len() - k,
    {
        let ok_k = check_c2(&cert.rows[k]);
        ok = ok && ok_k;
        k = k + 1;
    }
    ok
}

/// C3 (restitution, e = 0): every contact row's post relative normal
/// velocity ≥ −tol_v.
pub open spec fn c3_step_restitution(post: World, rows: Seq<Row>, tol_v: Rational) -> bool
    recommends
        forall|k: int|
            0 <= k < rows.len() ==> {
                &&& (#[trigger] rows[k]).a < post.bodies@.len()
                &&& rows[k].b < post.bodies@.len()
            },
{
    forall|k: int|
        0 <= k < rows.len() ==> tol_v.neg_spec().le_spec(row_vel_spec(
            #[trigger] rows[k].jla.model@, rows[k].jaa@, rows[k].jlb.model@, rows[k].jab@,
            post.bodies@[rows[k].a as int].vel.model@, post.bodies@[rows[k].a as int].omega@,
            post.bodies@[rows[k].b as int].vel.model@, post.bodies@[rows[k].b as int].omega@))
}

/// C3 exec (ok == its spec).
pub fn check_c3_rows(post: &World, cert: &StepCert, tol_v: &Scalar) -> (ok: bool)
    requires
        post.wf_spec(),
        tol_v.wf_spec(),
        forall|k: int| 0 <= k < cert.rows@.len() ==> (#[trigger] cert.rows@[k]).wf_spec(),
        forall|k: int|
            0 <= k < cert.rows@.len() ==> {
                &&& (#[trigger] cert.rows@[k]).a < post.bodies@.len()
                &&& cert.rows@[k].b < post.bodies@.len()
            },
    ensures
        ok == c3_step_restitution(*post, cert.rows@, tol_v@),
{
    let mut k: usize = 0;
    let mut ok = true;
    while k < cert.rows.len()
        invariant
            k <= cert.rows@.len(),
            post.wf_spec(),
            tol_v.wf_spec(),
            forall|k2: int| 0 <= k2 < cert.rows@.len() ==> (#[trigger] cert.rows@[k2]).wf_spec(),
            forall|k2: int|
                0 <= k2 < cert.rows@.len() ==> {
                    &&& (#[trigger] cert.rows@[k2]).a < post.bodies@.len()
                    &&& cert.rows@[k2].b < post.bodies@.len()
                },
            ok == forall|k2: int|
                0 <= k2 < k as int ==> tol_v@.neg_spec().le_spec(row_vel_spec(
                    #[trigger] cert.rows@[k2].jla.model@, cert.rows@[k2].jaa@,
                    cert.rows@[k2].jlb.model@, cert.rows@[k2].jab@,
                    post.bodies@[cert.rows@[k2].a as int].vel.model@,
                    post.bodies@[cert.rows@[k2].a as int].omega@,
                    post.bodies@[cert.rows@[k2].b as int].vel.model@,
                    post.bodies@[cert.rows@[k2].b as int].omega@)),
        decreases cert.rows.len() - k,
    {
        let r = &cert.rows[k];
        let ok_k = check_c3(r, &post.bodies[r.a], &post.bodies[r.b], tol_v);
        ok = ok && ok_k;
        k = k + 1;
    }
    ok
}

/// World anchor of a joint attachment point (pos + rot·anchor).
pub open spec fn joint_world_anchor(b: Body, anchor: Vec2<Rational>) -> Vec2<Rational> {
    vadd(
        b.pos.model@,
        Vec2 {
            x: b.rot.c@.mul_spec(anchor.x).sub_spec(b.rot.s@.mul_spec(anchor.y)),
            y: b.rot.s@.mul_spec(anchor.x).add_spec(b.rot.c@.mul_spec(anchor.y)),
        },
    )
}

/// C5 per joint: squared anchor drift (no sqrt, standing rule).
pub open spec fn joint_anchor_drift(post: World, j: Joint) -> Rational
    recommends (j.a as int) < post.bodies@.len(), (j.b as int) < post.bodies@.len()
{
    let wa = joint_world_anchor(post.bodies@[j.a as int], j.anchor_a.model@);
    let wb = joint_world_anchor(post.bodies@[j.b as int], j.anchor_b.model@);
    vdot(vsub(wa, wb), vsub(wa, wb))
}

/// C5 (joint drift): every joint's squared anchor drift ≤ tol_j.
/// Vacuous over empty joints (phys-06; full content phys-07).
pub open spec fn c5_step_joints(post: World, tol_j: Rational) -> bool {
    forall|j: int|
        0 <= j < post.joints@.len() ==> joint_anchor_drift(
            post, #[trigger] post.joints@[j]).le_spec(tol_j)
}

/// C5 exec (ok == its spec).
pub fn check_c5_joints(post: &World, tol_j: &Scalar) -> (ok: bool)
    requires
        post.wf_spec(),
        tol_j.wf_spec(),
    ensures
        ok == c5_step_joints(*post, tol_j@),
{
    let mut j: usize = 0;
    let mut ok = true;
    while j < post.joints.len()
        invariant
            j <= post.joints@.len(),
            post.wf_spec(),
            tol_j.wf_spec(),
            ok == forall|j2: int|
                0 <= j2 < j as int ==> joint_anchor_drift(
                    *post, #[trigger] post.joints@[j2]).le_spec(tol_j@),
        decreases post.joints.len() - j,
    {
        let jj = &post.joints[j];
        let wa_rot = post.bodies[jj.a].rot.apply(&jj.anchor_a);
        let wb_rot = post.bodies[jj.b].rot.apply(&jj.anchor_b);
        let wax = post.bodies[jj.a].pos.x.add(&wa_rot.x);
        let way = post.bodies[jj.a].pos.y.add(&wa_rot.y);
        let wbx = post.bodies[jj.b].pos.x.add(&wb_rot.x);
        let wby = post.bodies[jj.b].pos.y.add(&wb_rot.y);
        let dx = wax.sub(&wbx);
        let dy = way.sub(&wby);
        let drift = dx.mul(&dx).add(&dy.mul(&dy));
        let ok_j = drift.le(&tol_j);
        proof {
            assert(drift@ == joint_anchor_drift(*post, *jj));
        }
        ok = ok && ok_j;
        j = j + 1;
    }
    ok
}

} // verus!

verus! {

// ── phys-06 C4: non-penetration over the whole post world ─────────────

/// C4 for one part pair: the 05d per-pair claim (convexity of both world
/// polys + strict separation or bounded penetration, exists-EDGE-witness).
pub closed spec fn c4_parts_pair(
    post: World,
    i: int,
    j: int,
    pi: int,
    pj: int,
    tol_p: Rational,
) -> bool
    recommends
        0 <= i < post.bodies@.len(),
        0 <= j < post.bodies@.len(),
        0 <= pi < post.bodies@[i].shape.parts@.len(),
        0 <= pj < post.bodies@[j].shape.parts@.len(),
{
    let bi = post.bodies@[i];
    let bj = post.bodies@[j];
    let wa = world_verts(
        bi.pos.model@, bi.rot.c@, bi.rot.s@, bi.shape.model_parts()[pi]);
    let wb = world_verts(
        bj.pos.model@, bj.rot.c@, bj.rot.s@, bj.shape.model_parts()[pj]);
    &&& convex_poly_inv(wa)
    &&& convex_poly_inv(wb)
    &&& c4_single_contact(wa, wb, tol_p)
}

/// C4 for one body pair: all part pairs, unless both bodies are static
/// (frozen by C1, so no relative motion is possible — documented skip).
pub closed spec fn c4_body_pair(post: World, i: int, j: int, tol_p: Rational) -> bool
    recommends 0 <= i < j < post.bodies@.len()
{
    (body_dynamic(post.bodies@[i]) || body_dynamic(post.bodies@[j])) ==> {
        forall|pi: int, pj: int|
            (0 <= pi < post.bodies@[i].shape.parts@.len()
                && 0 <= pj < post.bodies@[j].shape.parts@.len())
                ==> c4_parts_pair(post, i, j, pi, pj, tol_p)
    }
}

/// C4 (non-penetration, re-derived, SPEC §7): the checker runs its own
/// broadphase over the post world; every candidate pair is separated or
/// penetrating at most tol_p.
pub open spec fn c4_step_world(post: World, tol_p: Rational) -> bool {
    forall|i: int, j: int|
        (0 <= i < j < post.bodies@.len()) ==> c4_body_pair(post, i, j, tol_p)
}

/// The 05d poly-pair check, generalized: strict separating witness on
/// either side, or touching with max-sep ≥ −tol_p (ok == its spec).
pub fn check_c4_polys(wa: &ConvexPoly, wb: &ConvexPoly, tol_p: &Scalar) -> (ok: bool)
    requires
        wa.wf_spec(),
        wb.wf_spec(),
        tol_p.wf_spec(),
    ensures
        ok == c4_single_contact(wa.model_verts(), wb.model_verts(), tol_p@),
{
    let (sep_a, e_a, ms_a) = classify_side(wa, wb);
    if sep_a.is_some() {
        proof {
            let e = sep_a->Some_0;
            assert(axis_separates(wa.model_verts(), wb.model_verts(), e as int));
            assert(c4_single_contact(wa.model_verts(), wb.model_verts(), tol_p@));
        }
        return true;
    }
    let (sep_b, e_b, ms_b) = classify_side(wb, wa);
    if sep_b.is_some() {
        proof {
            let e = sep_b->Some_0;
            assert(axis_separates(wb.model_verts(), wa.model_verts(), e as int));
            assert(c4_single_contact(wa.model_verts(), wb.model_verts(), tol_p@));
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

} // verus!

verus! {

/// C4 for one row of the parts grid: body i's part pi against every part
/// of body j (ok == its spec).
pub fn check_c4_parts_row(
    post: &World,
    i: usize,
    j: usize,
    pi: usize,
    tol_p: &Scalar,
) -> (ok: bool)
    requires
        post.wf_spec(),
        tol_p.wf_spec(),
        i < j < post.bodies@.len(),
        pi < post.bodies@[i as int].shape.parts@.len(),
    ensures
        ok == forall|p2: int|
            0 <= p2 < post.bodies@[j as int].shape.parts@.len()
                ==> c4_parts_pair(*post, i as int, j as int, pi as int, p2, tol_p@),
{
    let mut ok = true;
    let mut pj: usize = 0;
    while pj < post.bodies[j].shape.parts.len()
        invariant
            pi < post.bodies@[i as int].shape.parts@.len(),
            pj <= post.bodies@[j as int].shape.parts@.len(),
            i < j < post.bodies@.len(),
            post.wf_spec(),
            tol_p.wf_spec(),
            ok == forall|p2: int|
                0 <= p2 < pj as int
                    ==> c4_parts_pair(*post, i as int, j as int, pi as int, p2, tol_p@),
        decreases post.bodies@[j as int].shape.parts@.len() - pj as int,
    {
        let bi = &post.bodies[i];
        let bj = &post.bodies[j];
        let wvi = world_verts_exec(&bi.pos, &bi.rot, &bi.shape.parts[pi]);
        let wvj = world_verts_exec(&bj.pos, &bj.rot, &bj.shape.parts[pj]);
        proof {
            assert(wvi@.map(|_k: int, v: SVec2| v.model@) == world_verts(
                bi.pos.model@, bi.rot.c@, bi.rot.s@,
                bi.shape.model_parts()[pi as int]));
            assert(wvj@.map(|_k: int, v: SVec2| v.model@) == world_verts(
                bj.pos.model@, bj.rot.c@, bj.rot.s@,
                bj.shape.model_parts()[pj as int]));
        }
        let gi = ConvexPoly::new_checked(wvi);
        let gj = ConvexPoly::new_checked(wvj);
        if gi.is_none() || gj.is_none() {
            proof {
                reveal(c4_parts_pair);
                assert(!c4_parts_pair(*post, i as int, j as int, pi as int, pj as int, tol_p@));
            }
            return false;
        }
        let wa = gi.unwrap();
        let wb = gj.unwrap();
        proof {
            lemma_unit_norm_raw(bi.rot.c@, bi.rot.s@);
            lemma_unit_norm_raw(bj.rot.c@, bj.rot.s@);
            lemma_convex_poly_inv_world(
                bi.pos.model@, bi.rot.c@, bi.rot.s@, bi.shape.model_parts()[pi as int]);
            lemma_convex_poly_inv_world(
                bj.pos.model@, bj.rot.c@, bj.rot.s@, bj.shape.model_parts()[pj as int]);
        }
        let ok_p = check_c4_polys(&wa, &wb, tol_p);
        ok = ok && ok_p;
        proof {
            reveal(c4_parts_pair);
            assert(wa.model_verts() == world_verts(
                bi.pos.model@, bi.rot.c@, bi.rot.s@,
                bi.shape.model_parts()[pi as int]));
            assert(wb.model_verts() == world_verts(
                bj.pos.model@, bj.rot.c@, bj.rot.s@,
                bj.shape.model_parts()[pj as int]));
            assert(ok_p == c4_parts_pair(*post, i as int, j as int, pi as int, pj as int, tol_p@));
        }
        pj = pj + 1;
    }
    ok
}

/// C4 for one body pair (ok == its spec).
pub fn check_c4_body_pair(post: &World, i: usize, j: usize, tol_p: &Scalar) -> (ok: bool)
    requires
        post.wf_spec(),
        tol_p.wf_spec(),
        i < j < post.bodies@.len(),
    ensures
        ok == c4_body_pair(*post, i as int, j as int, tol_p@),
{
    let zero = RuntimeRational::from_int(0);
    let si = post.bodies[i].inv_mass.eq(&zero);
    let sj = post.bodies[j].inv_mass.eq(&zero);
    proof {
        assert(si == !body_dynamic(post.bodies@[i as int]));
        assert(sj == !body_dynamic(post.bodies@[j as int]));
    }
    if si && sj {
        proof {
            reveal(c4_body_pair);
        }
        return true;
    }
    let mut ok = true;
    let mut pi: usize = 0;
    while pi < post.bodies[i].shape.parts.len()
        invariant
            pi <= post.bodies@[i as int].shape.parts@.len(),
            i < j < post.bodies@.len(),
            post.wf_spec(),
            tol_p.wf_spec(),
            body_dynamic(post.bodies@[i as int]) || body_dynamic(post.bodies@[j as int]),
            ok == forall|p1: int, p2: int|
                (0 <= p1 < pi as int && 0 <= p2 < post.bodies@[j as int].shape.parts@.len())
                    ==> c4_parts_pair(*post, i as int, j as int, p1, p2, tol_p@),
        decreases post.bodies@[i as int].shape.parts@.len() - pi as int,
    {
        let ok_r = check_c4_parts_row(post, i, j, pi, tol_p);
        ok = ok && ok_r;
        proof {
            assert(ok_r == forall|p2: int|
                0 <= p2 < post.bodies@[j as int].shape.parts@.len()
                    ==> c4_parts_pair(*post, i as int, j as int, pi as int, p2, tol_p@));
        }
        pi = pi + 1;
    }
    proof {
        reveal(c4_body_pair);
        assert(body_dynamic(post.bodies@[i as int]) || body_dynamic(post.bodies@[j as int]));
    }
    ok
}

/// C4 for one row of the pair grid: body i against every j > i
/// (ok == its spec).
pub fn check_c4_row(post: &World, i: usize, tol_p: &Scalar) -> (ok: bool)
    requires
        post.wf_spec(),
        tol_p.wf_spec(),
        i < post.bodies@.len(),
    ensures
        ok == forall|j2: int|
            i as int + 1 <= j2 < post.bodies@.len()
                ==> c4_body_pair(*post, i as int, j2, tol_p@),
{
    let mut ok = true;
    let mut j: usize = 0;
    while j < post.bodies.len()
        invariant
            i < post.bodies@.len(),
            j <= post.bodies@.len(),
            post.wf_spec(),
            tol_p.wf_spec(),
            ok == forall|j2: int|
                i as int + 1 <= j2 < j as int
                    ==> c4_body_pair(*post, i as int, j2, tol_p@),
        decreases post.bodies.len() - j,
    {
        if j > i {
            let ok_p = check_c4_body_pair(post, i, j, tol_p);
            ok = ok && ok_p;
            proof {
                assert(ok_p == c4_body_pair(*post, i as int, j as int, tol_p@));
            }
        }
        proof {
            assert(ok == forall|j2: int|
                i as int + 1 <= j2 < j as int + 1
                    ==> c4_body_pair(*post, i as int, j2, tol_p@));
        }
        j = j + 1;
    }
    ok
}

/// C4 over all body pairs (ok == its spec).
pub fn check_c4_world(post: &World, tol_p: &Scalar) -> (ok: bool)
    requires
        post.wf_spec(),
        tol_p.wf_spec(),
    ensures
        ok == c4_step_world(*post, tol_p@),
{
    let mut ok = true;
    let mut i: usize = 0;
    while i < post.bodies.len()
        invariant
            i <= post.bodies@.len(),
            post.wf_spec(),
            tol_p.wf_spec(),
            ok == forall|i2: int, j2: int|
                (0 <= i2 < i as int && i2 < j2 < post.bodies@.len())
                    ==> c4_body_pair(*post, i2, j2, tol_p@),
        decreases post.bodies.len() - i,
    {
        let ok_r = check_c4_row(post, i, tol_p);
        ok = ok && ok_r;
        proof {
            assert(ok_r == forall|j2: int|
                i as int + 1 <= j2 < post.bodies@.len()
                    ==> c4_body_pair(*post, i as int, j2, tol_p@));
        }
        i = i + 1;
    }
    ok
}

} // verus!

verus! {

// ── phys-06 C7: exact energy ledger ───────────────────────────────────
// KE = Σ_dynamic (1/inv_m)·|v|²/2 + (1/inv_I)·ω²/2,
// PE = −Σ_dynamic (1/inv_m)·dot(g, pos),
// W_drift = −Σ_dynamic (1/inv_m)·|g|²·dt²/2  (the exact symplectic-Euler
// drift — accounted, not an error). Dissipation is nonnegative and
// exactly computed: E(post) ≤ E(pre) + W_drift + W_proj + W_snaps.
// No tolerance anywhere (D13 candidate; W_proj/W_snaps vacuous in 06a).

/// KE of the first k bodies (dynamic only).
pub open spec fn ke_sum(bodies: Seq<Body>, k: int) -> Rational
    decreases k
{
    if k <= 0 {
        Rational::from_int_spec(0)
    } else {
        let prev = ke_sum(bodies, (k - 1) as int);
        let b = bodies[k - 1];
        if body_dynamic(b) {
            let ke1 = Rational::from_int_spec(1).div_spec(b.inv_mass@).mul_spec(
                vdot(b.vel.model@, b.vel.model@)).div_spec(Rational::from_int_spec(2));
            // inv_I ≡ 0 (infinite inertia) pins ω ≡ 0 — the angular term
            // is genuinely zero, so skip the (undefined) 1/inv_I form
            let ke2 = if b.inv_inertia@.eqv_spec(Rational::from_int_spec(0)) {
                Rational::from_int_spec(0)
            } else {
                Rational::from_int_spec(1).div_spec(b.inv_inertia@).mul_spec(
                    b.omega@.mul_spec(b.omega@)).div_spec(Rational::from_int_spec(2))
            };
            prev.add_spec(ke1.add_spec(ke2))
        } else {
            prev
        }
    }
}

/// PE of the first k bodies under gravity g (dynamic only).
pub open spec fn pe_sum(bodies: Seq<Body>, g: Vec2<Rational>, k: int) -> Rational
    decreases k
{
    if k <= 0 {
        Rational::from_int_spec(0)
    } else {
        let prev = pe_sum(bodies, g, (k - 1) as int);
        let b = bodies[k - 1];
        if body_dynamic(b) {
            let pe = Rational::from_int_spec(1).div_spec(b.inv_mass@).mul_spec(
                vdot(g, b.pos.model@)).neg_spec();
            prev.add_spec(pe)
        } else {
            prev
        }
    }
}

/// The exact symplectic drift allowance of the first k bodies.
pub open spec fn w_drift_sum(
    bodies: Seq<Body>,
    g: Vec2<Rational>,
    dt: Rational,
    k: int,
) -> Rational
    decreases k
{
    if k <= 0 {
        Rational::from_int_spec(0)
    } else {
        let prev = w_drift_sum(bodies, g, dt, (k - 1) as int);
        let b = bodies[k - 1];
        if body_dynamic(b) {
            let wd = Rational::from_int_spec(1).div_spec(b.inv_mass@).mul_spec(
                vdot(g, g)).mul_spec(dt).mul_spec(dt).div_spec(
                Rational::from_int_spec(2)).neg_spec();
            prev.add_spec(wd)
        } else {
            prev
        }
    }
}

/// Total energy of a world (KE + PE over all bodies).
pub open spec fn world_energy(bodies: Seq<Body>, g: Vec2<Rational>) -> Rational {
    ke_sum(bodies, bodies.len() as int).add_spec(pe_sum(bodies, g, bodies.len() as int))
}

/// C7 (exact energy ledger, SPEC §7 as resolved — D13): dissipation is
/// nonnegative and exactly computed: D = E(pre) + W_proj + W_snaps −
/// E(post) ≥ 0. NO drift allowance: the symplectic drift is itself
/// dissipative (free flight: D = g²dt²/2·(1/inv_m) > 0), and the
/// SPEC's negative W_drift term would forbid the honest ΔE = 0 of a
/// resting contact (measured: C7 rejected rest). 06a: W_proj = W_snaps
/// = 0 (no projection yet, no snaps yet).
pub open spec fn c7_energy_ledger(
    pre: World,
    post: World,
    w_proj: Rational,
    w_snaps: Rational,
) -> bool
    recommends post.bodies@.len() == pre.bodies@.len()
{
    let e_pre = world_energy(pre.bodies@, pre.gravity.model@);
    let e_post = world_energy(post.bodies@, post.gravity.model@);
    e_post.le_spec(e_pre.add_spec(w_proj).add_spec(w_snaps))
}

/// C7 exec: fold KE/PE/drift, compare (ok == its spec).
pub fn check_c7_energy(pre: &World, post: &World) -> (ok: bool)
    requires
        pre.wf_spec(),
        post.wf_spec(),
        post.bodies@.len() == pre.bodies@.len(),
    ensures
        ok == c7_energy_ledger(*pre, *post, Rational::from_int_spec(0), Rational::from_int_spec(0)),
{
    let one = RuntimeRational::from_int(1);
    let two = RuntimeRational::from_int(2);
    let mut ke = RuntimeRational::from_int(0);
    let mut pe = RuntimeRational::from_int(0);
    let mut ke_post = RuntimeRational::from_int(0);
    let mut pe_post = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < pre.bodies.len()
        invariant
            i <= pre.bodies@.len(),
            pre.wf_spec(),
            post.wf_spec(),
            post.bodies@.len() == pre.bodies@.len(),
            one.wf_spec(),
            two.wf_spec(),
            one@ == Rational::from_int_spec(1),
            two@ == Rational::from_int_spec(2),
            ke.wf_spec(),
            pe.wf_spec(),
            ke_post.wf_spec(),
            pe_post.wf_spec(),
            ke@ == ke_sum(pre.bodies@, i as int),
            pe@ == pe_sum(pre.bodies@, pre.gravity.model@, i as int),
            ke_post@ == ke_sum(post.bodies@, i as int),
            pe_post@ == pe_sum(post.bodies@, post.gravity.model@, i as int),
        decreases pre.bodies.len() - i,
    {
        let zero = RuntimeRational::from_int(0);
        let is_static = pre.bodies[i].inv_mass.eq(&zero);
        proof {
            assert(is_static == !body_dynamic(pre.bodies@[i as int]));
        }
        if !is_static {
            let pb = &pre.bodies[i];
            proof {
                Rational::lemma_eqv_zero_iff_num_zero(pb.inv_mass@);
                Rational::lemma_eqv_zero_iff_num_zero(pb.inv_inertia@);
            }
            let vv = pb.vel.x.mul(&pb.vel.x).add(&pb.vel.y.mul(&pb.vel.y));
            let ke1 = one.div(&pb.inv_mass).mul(&vv).div(&two);
            let om2 = pb.omega.mul(&pb.omega);
            let no_i = pb.inv_inertia.eq(&zero);
            let ke2 = if no_i {
                proof {
                    assert(pb.inv_inertia@.eqv_spec(Rational::from_int_spec(0)));
                }
                RuntimeRational::from_int(0)
            } else {
                one.div(&pb.inv_inertia).mul(&om2).div(&two)
            };
            ke = ke.add(&ke1.add(&ke2));
            let gd = pre.gravity.x.mul(&pb.pos.x).add(&pre.gravity.y.mul(&pb.pos.y));
            pe = pe.add(&one.div(&pb.inv_mass).mul(&gd).neg());
            proof {
                assert(ke@ == ke_sum(pre.bodies@, (i + 1) as int)) by {
                    reveal_with_fuel(ke_sum, 2);
                };
                assert(pe@ == pe_sum(pre.bodies@, pre.gravity.model@, (i + 1) as int)) by {
                    reveal_with_fuel(pe_sum, 2);
                };
            }
        } else {
            proof {
                assert(ke@ == ke_sum(pre.bodies@, (i + 1) as int)) by {
                    reveal_with_fuel(ke_sum, 2);
                };
                assert(pe@ == pe_sum(pre.bodies@, pre.gravity.model@, (i + 1) as int)) by {
                    reveal_with_fuel(pe_sum, 2);
                };
            }
        }
        let qb = &post.bodies[i];
        let is_static_q = qb.inv_mass.eq(&zero);
        proof {
            assert(is_static_q == !body_dynamic(post.bodies@[i as int]));
        }
        if !is_static_q {
            proof {
                Rational::lemma_eqv_zero_iff_num_zero(qb.inv_mass@);
                Rational::lemma_eqv_zero_iff_num_zero(qb.inv_inertia@);
            }
            let vv = qb.vel.x.mul(&qb.vel.x).add(&qb.vel.y.mul(&qb.vel.y));
            let ke1 = one.div(&qb.inv_mass).mul(&vv).div(&two);
            let om2 = qb.omega.mul(&qb.omega);
            let no_i = qb.inv_inertia.eq(&zero);
            let ke2 = if no_i {
                proof {
                    assert(qb.inv_inertia@.eqv_spec(Rational::from_int_spec(0)));
                }
                RuntimeRational::from_int(0)
            } else {
                one.div(&qb.inv_inertia).mul(&om2).div(&two)
            };
            ke_post = ke_post.add(&ke1.add(&ke2));
            let gd = post.gravity.x.mul(&qb.pos.x).add(&post.gravity.y.mul(&qb.pos.y));
            pe_post = pe_post.add(&one.div(&qb.inv_mass).mul(&gd).neg());
            proof {
                assert(ke_post@ == ke_sum(post.bodies@, (i + 1) as int)) by {
                    reveal_with_fuel(ke_sum, 2);
                };
                assert(pe_post@ == pe_sum(
                    post.bodies@, post.gravity.model@, (i + 1) as int)) by {
                    reveal_with_fuel(pe_sum, 2);
                };
            }
        } else {
            proof {
                assert(ke_post@ == ke_sum(post.bodies@, (i + 1) as int)) by {
                    reveal_with_fuel(ke_sum, 2);
                };
                assert(pe_post@ == pe_sum(
                    post.bodies@, post.gravity.model@, (i + 1) as int)) by {
                    reveal_with_fuel(pe_sum, 2);
                };
            }
        }
        i = i + 1;
    }
    let e_pre = ke.add(&pe);
    let e_post = ke_post.add(&pe_post);
    let zero = RuntimeRational::from_int(0);
    let allowance = e_pre.add(&zero).add(&zero);
    proof {
        assert(e_pre@ == world_energy(pre.bodies@, pre.gravity.model@));
        assert(e_post@ == world_energy(post.bodies@, post.gravity.model@));
        assert(zero@ == Rational::from_int_spec(0));
        Rational::lemma_add_zero_identity(e_pre@);
        Rational::lemma_add_zero_identity(e_pre@.add_spec(zero@));
    }
    e_post.le(&allowance)
}

// ── phys-06: the full step checker ─────────────────────────────────────

/// All step checks (SPEC §7): C1 velocity bookkeeping, C2 bounds, C3
/// restitution, C4 non-penetration, C5 joint drift, C7 energy ledger.
/// (C6 ledgers lands in 06c.)
pub open spec fn step_checks_pass(
    pre: World,
    post: World,
    cert: StepCert,
    tol_v: Rational,
    tol_p: Rational,
    tol_j: Rational,
) -> bool
    recommends
        post.bodies@.len() == pre.bodies@.len(),
        forall|k: int|
            0 <= k < cert.rows@.len() ==> {
                &&& (#[trigger] cert.rows@[k]).a < post.bodies@.len()
                &&& cert.rows@[k].b < post.bodies@.len()
            },
{
    &&& c1_step_bookkeeping(pre, post, cert)
    &&& c2_step_bounds(cert.rows@)
    &&& c3_step_restitution(post, cert.rows@, tol_v)
    &&& c4_step_world(post, tol_p)
    &&& c5_step_joints(post, tol_j)
    &&& c7_energy_ledger(pre, post, Rational::from_int_spec(0), Rational::from_int_spec(0))
}

/// The semantic claim (ok ⟹ this). C4's semantic content is the
/// separation/depth claim; the convexity conjuncts are checker-side
/// gates needed for the bidirectional direction (mirror of 05d).
pub open spec fn step_certified(
    pre: World,
    post: World,
    cert: StepCert,
    tol_v: Rational,
    tol_p: Rational,
    tol_j: Rational,
) -> bool
    recommends
        post.bodies@.len() == pre.bodies@.len(),
        forall|k: int|
            0 <= k < cert.rows@.len() ==> {
                &&& (#[trigger] cert.rows@[k]).a < post.bodies@.len()
                &&& cert.rows@[k].b < post.bodies@.len()
            },
{
    &&& c1_step_bookkeeping(pre, post, cert)
    &&& c2_step_bounds(cert.rows@)
    &&& c3_step_restitution(post, cert.rows@, tol_v)
    &&& c4_step_world(post, tol_p)
    &&& c5_step_joints(post, tol_j)
    &&& c7_energy_ledger(pre, post, Rational::from_int_spec(0), Rational::from_int_spec(0))
}

/// The proven checker (SPEC §7, D8): ok == the checks pass, and ok ⟹ the
/// step is certified. This is the ONLY thing the engine's headline claims
/// rest on.
pub fn check_step(
    pre: &World,
    post: &World,
    cert: &StepCert,
    tol_v: &Scalar,
    tol_p: &Scalar,
    tol_j: &Scalar,
) -> (ok: bool)
    requires
        pre.wf_spec(),
        post.wf_spec(),
        tol_v.wf_spec(),
        tol_p.wf_spec(),
        tol_j.wf_spec(),
        post.bodies@.len() == pre.bodies@.len(),
        forall|k: int| 0 <= k < cert.rows@.len() ==> (#[trigger] cert.rows@[k]).wf_spec(),
        forall|k: int| 0 <= k < cert.snaps@.len() ==> (#[trigger] cert.snaps@[k]).wf_spec(),
        forall|k: int|
            0 <= k < cert.rows@.len() ==> {
                &&& (#[trigger] cert.rows@[k]).a < post.bodies@.len()
                &&& cert.rows@[k].b < post.bodies@.len()
            },
    ensures
        ok == step_checks_pass(*pre, *post, *cert, tol_v@, tol_p@, tol_j@),
        ok ==> step_certified(*pre, *post, *cert, tol_v@, tol_p@, tol_j@),
{
    let c1 = check_c1_rows(pre, post, cert);
    let c2 = check_c2_rows(cert);
    let c3 = check_c3_rows(post, cert, tol_v);
    let c4 = check_c4_world(post, tol_p);
    let c5 = check_c5_joints(post, tol_j);
    let c7 = check_c7_energy(pre, post);
    c1 && c2 && c3 && c4 && c5 && c7
}

} // verus!
