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
    proof {
        // static branch: the expected components match vzero() form
        if is_static {
            assert(evx@ == Rational::from_int_spec(0));
            assert(evy@ == Rational::from_int_spec(0));
        }
    }
    okx && oky && okom
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
