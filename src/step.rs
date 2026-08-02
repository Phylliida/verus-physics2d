//! Free-flight symplectic Euler step (phys-03; SPEC §6 pipeline steps 1+4).
//!
//! Pure: World -> StepResult, Reject = tan-half parameter outside [−1,1]
//! (driver policy is to halve dt, SPEC §1/§3). StepResult replaces the
//! old Option form (DESIGN §3.7(a)); Ok carries the StepCert witness
//! (SPEC §7 — rows/snaps empty for free flight, tan_halfs and
//! angle_entries per body).
//! Rotation integrates through the untrusted tan_half_series chooser; the
//! per-body ledger accumulates 2·|term_{k+1}(t)| (E2 angle ledger, phys-02b).

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::scale;
use verus_rational::{Rational, RuntimeRational};

use crate::angle_ledger::{
    arctan_term, arctan_term_exec, t_in_symmetric_unit_interval, t_in_unit_interval, two_x,
};
use crate::body::Body;
use crate::certificate::{veqv, StepCert};
use crate::joints::Joint;
use crate::massprops::vscale;
use crate::shape::vadd;
use crate::proofs::rational_raw::{
    compose_c, compose_s, lemma_raw_add_nonneg, lemma_raw_add_zero_right, lemma_raw_abs_nonneg,
    lemma_raw_neg_mul_left, lemma_raw_neg_mul_neg, lemma_raw_neg_mul_right, lemma_raw_two_nonneg,
};
use crate::proofs::rpow::{ipow, lemma_ipow_congruence, lemma_ipow_zero_base};
use crate::rotq::RotQ;
use crate::types::{copy_svec2, q_nonneg, q_pos, SVec2, Scalar};
use crate::world::World;

verus! {

/// A body is dynamic iff its inverse mass numerator is nonzero.
pub open spec fn body_dynamic(b: Body) -> bool {
    b.inv_mass@.num != 0
}

/// tan-half-angle coordinates (spec forms matching RotQ::from_tan_half).
pub open spec fn tan_half_c(t: Rational) -> Rational {
    Rational::from_int_spec(1).sub_spec(t.mul_spec(t)).div_spec(
        Rational::from_int_spec(1).add_spec(t.mul_spec(t)))
}

pub open spec fn tan_half_s(t: Rational) -> Rational {
    Rational::from_int_spec(2).mul_spec(t).div_spec(
        Rational::from_int_spec(1).add_spec(t.mul_spec(t)))
}

/// The untrusted series chooser model (matches RotQ::tan_half_series).
pub open spec fn tan_half_series_model(h: Rational) -> Rational {
    h.add_spec(
        h.mul_spec(h).mul_spec(h).mul_spec(Rational::from_frac_spec(1, 3)),
    ).add_spec(
        Rational::from_int_spec(2).mul_spec(
            h.mul_spec(h).mul_spec(h).mul_spec(h).mul_spec(h),
        ).mul_spec(Rational::from_frac_spec(1, 15)),
    )
}

/// h = ω·dt/2 (matches the exec computation order).
pub open spec fn half_angle_model(omega: Rational, dt: Rational) -> Rational {
    omega.mul_spec(dt).div_spec(Rational::from_int_spec(2))
}

/// Relational spec of one body's free-flight step (symplectic Euler +
/// tan-half rotation). The exec step ensures this for every body.
pub open spec fn body_step_rel(
    pre: Body,
    post: Body,
    g: Vec2<Rational>,
    dt: Rational,
    t: Rational,
) -> bool {
    if body_dynamic(pre) {
        let vel1 = pre.vel.model@.add(scale(dt, g));
        &&& t == tan_half_series_model(half_angle_model(pre.omega@, dt))
        &&& post.vel.model@ == vel1
        &&& post.pos.model@ == pre.pos.model@.add(scale(dt, vel1))
        &&& post.omega@ == pre.omega@
        &&& post.rot.c@ == compose_c(pre.rot.c@, pre.rot.s@, tan_half_c(t), tan_half_s(t))
        &&& post.rot.s@ == compose_s(pre.rot.c@, pre.rot.s@, tan_half_c(t), tan_half_s(t))
        &&& post.inv_mass@ == pre.inv_mass@
        &&& post.inv_inertia@ == pre.inv_inertia@
        &&& post.shape.model_parts() == pre.shape.model_parts()
    } else {
        &&& post.pos.model@ == pre.pos.model@
        &&& post.vel.model@ == pre.vel.model@
        &&& post.rot.c@ == pre.rot.c@
        &&& post.rot.s@ == pre.rot.s@
        &&& post.omega@ == pre.omega@
        &&& post.inv_mass@ == pre.inv_mass@
        &&& post.inv_inertia@ == pre.inv_inertia@
        &&& post.shape.model_parts() == pre.shape.model_parts()
    }
}

/// The per-body per-step ledger increment: 2·|term_{k+1}(t)|.
pub open spec fn ledger_increment(t: Rational, series_k: nat) -> Rational {
    two_x(arctan_term(t, series_k + 1).abs_spec())
}

/// |term_j| ≥ 0 (abs of anything is nonneg — re-export shape for callers).
pub proof fn lemma_ledger_increment_nonneg(t: Rational, series_k: nat)
    ensures
        Rational::from_int_spec(0).le_spec(ledger_increment(t, series_k)),
{
    lemma_raw_abs_nonneg(arctan_term(t, series_k + 1));
    lemma_raw_two_nonneg(arctan_term(t, series_k + 1).abs_spec());
}

/// 0 ≤ h ≤ 1/2 ⇒ the untrusted series stays in [0, 1] (so the step
/// never rejects for such h). Bounds: t ≤ h + h/12 + h/120 < 1.
pub proof fn lemma_series_unit_interval(h: Rational)
    requires
        Rational::from_int_spec(0).le_spec(h),
        h.le_spec(Rational::from_frac_spec(1, 2)),
    ensures
        t_in_unit_interval(tan_half_series_model(h)),
{
    let z = Rational::from_int_spec(0);
    let half = Rational::from_frac_spec(1, 2);
    let t = tan_half_series_model(h);
    // pieces
    let h2 = h.mul_spec(h);
    let h3 = h2.mul_spec(h);
    let h4 = h3.mul_spec(h);
    let h5 = h4.mul_spec(h);
    let third = Rational::from_frac_spec(1, 3);
    let t1 = h3.mul_spec(third);
    let h5x2 = Rational::from_int_spec(2).mul_spec(h5);
    let t2 = h5x2.mul_spec(Rational::from_frac_spec(1, 15));
    let s1 = h.add_spec(t1);
    // nonnegatives
    Rational::lemma_eqv_implies_le(z, z);
    Rational::lemma_le_mul_nonneg_both(z, h, z, h);
    Rational::lemma_mul_zero(z);
    Rational::lemma_eqv_implies_le(z.mul_spec(z), z);
    Rational::lemma_le_transitive(z, z.mul_spec(z), z.mul_spec(h));
    assert(z.le_spec(h2));
    Rational::lemma_le_mul_nonneg_both(z, h2, z, h);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h2.mul_spec(h));
    assert(z.le_spec(h3));
    Rational::lemma_le_mul_nonneg_both(z, h3, z, h);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h3.mul_spec(h));
    assert(z.le_spec(h4));
    Rational::lemma_le_mul_nonneg_both(z, h4, z, h);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h4.mul_spec(h));
    assert(z.le_spec(h5));
    assert(z.le_spec(third));
    Rational::lemma_le_mul_nonneg_both(z, h3, z, third);
    Rational::lemma_le_transitive(z, z.mul_spec(z), t1);
    assert(z.le_spec(t1));
    assert(z.le_spec(Rational::from_int_spec(2)));
    Rational::lemma_le_mul_nonneg_both(z, Rational::from_int_spec(2), z, h5);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h5x2);
    assert(z.le_spec(h5x2));
    assert(z.le_spec(Rational::from_frac_spec(1, 15)));
    Rational::lemma_le_mul_nonneg_both(z, h5x2, z, Rational::from_frac_spec(1, 15));
    Rational::lemma_le_transitive(z, z.mul_spec(z), t2);
    assert(z.le_spec(t2));
    Rational::lemma_le_add_both(z, h, z, t1);
    assert(z.add_spec(z) == z);
    Rational::lemma_le_transitive(z, z.add_spec(z), s1);
    Rational::lemma_le_add_both(z, s1, z, t2);
    Rational::lemma_le_transitive(z, z.add_spec(z), t);
    assert(z.le_spec(t));
    // upper bounds: h ≤ 1/2 ⇒ h^p ≤ (1/2)^p
    Rational::lemma_le_mul_nonneg_both(h, half, h, half);
    assert(half.mul_spec(half) == Rational::from_frac_spec(1, 4));
    Rational::lemma_le_mul_nonneg_both(h2, Rational::from_frac_spec(1, 4), h, half);
    assert(Rational::from_frac_spec(1, 4).mul_spec(half) == Rational::from_frac_spec(1, 8));
    Rational::lemma_le_mul_nonneg_both(h3, Rational::from_frac_spec(1, 8), h, half);
    assert(Rational::from_frac_spec(1, 8).mul_spec(half) == Rational::from_frac_spec(1, 16));
    Rational::lemma_le_mul_nonneg_both(h4, Rational::from_frac_spec(1, 16), h, half);
    assert(Rational::from_frac_spec(1, 16).mul_spec(half) == Rational::from_frac_spec(1, 32));
    // t1 ≤ 1/8 · 1/3 = 1/24 ; 2h⁵ ≤ 2/32 = 1/16 ; t2 ≤ 1/16 · 1/15 = 1/240
    Rational::lemma_eqv_implies_le(third, third);
    Rational::lemma_le_mul_nonneg_both(h3, Rational::from_frac_spec(1, 8), third, third);
    assert(Rational::from_frac_spec(1, 8).mul_spec(third) == Rational::from_frac_spec(1, 24));
    assert(t1.le_spec(Rational::from_frac_spec(1, 24)));
    Rational::lemma_eqv_implies_le(Rational::from_int_spec(2), Rational::from_int_spec(2));
    Rational::lemma_le_mul_nonneg_both(
        Rational::from_int_spec(2), Rational::from_int_spec(2),
        h5, Rational::from_frac_spec(1, 32));
    assert(Rational::from_int_spec(2).mul_spec(Rational::from_frac_spec(1, 32))
        .eqv_spec(Rational::from_frac_spec(1, 16)));
    Rational::lemma_eqv_implies_le(
        Rational::from_int_spec(2).mul_spec(Rational::from_frac_spec(1, 32)),
        Rational::from_frac_spec(1, 16));
    Rational::lemma_le_transitive(
        h5x2,
        Rational::from_int_spec(2).mul_spec(Rational::from_frac_spec(1, 32)),
        Rational::from_frac_spec(1, 16));
    assert(h5x2.le_spec(Rational::from_frac_spec(1, 16)));
    Rational::lemma_eqv_implies_le(Rational::from_frac_spec(1, 15), Rational::from_frac_spec(1, 15));
    Rational::lemma_le_mul_nonneg_both(
        h5x2, Rational::from_frac_spec(1, 16),
        Rational::from_frac_spec(1, 15), Rational::from_frac_spec(1, 15));
    assert(Rational::from_frac_spec(1, 16).mul_spec(Rational::from_frac_spec(1, 15))
        == Rational::from_frac_spec(1, 240));
    assert(t2.le_spec(Rational::from_frac_spec(1, 240)));
    // s1 ≤ 1/2 + 1/24 ≡ 13/24 ; t ≤ 13/24 + 1/240 ≤ 1
    Rational::lemma_le_add_both(h, half, t1, Rational::from_frac_spec(1, 24));
    let s1b = half.add_spec(Rational::from_frac_spec(1, 24));
    let f1324 = Rational::from_frac_spec(13, 24);
    assert(s1b.num == 26);
    assert(s1b.denom() == 48);
    assert(f1324.num == 13);
    assert(f1324.denom() == 24);
    assert(s1b.eqv_spec(f1324));
    Rational::lemma_eqv_implies_le(s1b, f1324);
    Rational::lemma_le_transitive(s1, s1b, f1324);
    Rational::lemma_le_add_both(s1, f1324, t2, Rational::from_frac_spec(1, 240));
    let s2b = f1324.add_spec(Rational::from_frac_spec(1, 240));
    let onei = Rational::from_int_spec(1);
    assert(s2b.num == 3144);
    assert(s2b.denom() == 5760);
    assert(onei.num == 1);
    assert(onei.denom() == 1);
    assert(s2b.le_spec(onei));
    Rational::lemma_le_transitive(t, s2b, onei);
    assert(t.le_spec(Rational::from_int_spec(1)));
}

/// The untrusted chooser is odd: series(−h) == −series(h) (structural).
pub proof fn lemma_series_model_neg(h: Rational)
    ensures
        tan_half_series_model(h.neg_spec()) == tan_half_series_model(h).neg_spec(),
{
    let nh = h.neg_spec();
    let third = Rational::from_frac_spec(1, 3);
    let f115 = Rational::from_frac_spec(1, 15);
    let two = Rational::from_int_spec(2);
    let h2 = h.mul_spec(h);
    let h3 = h2.mul_spec(h);
    let h4 = h3.mul_spec(h);
    let h5 = h4.mul_spec(h);
    let t1 = h3.mul_spec(third);
    let t2 = two.mul_spec(h5).mul_spec(f115);
    let s1 = h.add_spec(t1);
    // model unfolds (exact body form)
    assert(tan_half_series_model(h) == s1.add_spec(t2));
    assert(tan_half_series_model(nh) == nh.add_spec(
        nh.mul_spec(nh).mul_spec(nh).mul_spec(third),
    ).add_spec(
        two.mul_spec(nh.mul_spec(nh).mul_spec(nh).mul_spec(nh).mul_spec(nh))
            .mul_spec(f115),
    ));
    // power mirrors: nh² == h², nh³ == −h³, nh⁴ == h⁴, nh⁵ == −h⁵
    lemma_raw_neg_mul_neg(h, h);
    lemma_raw_neg_mul_right(h2, h);
    lemma_raw_neg_mul_neg(h3, h);
    lemma_raw_neg_mul_right(h4, h);
    assert(nh.mul_spec(nh) == h2);
    assert(nh.mul_spec(nh).mul_spec(nh) == h3.neg_spec());
    assert(nh.mul_spec(nh).mul_spec(nh).mul_spec(nh) == h4);
    assert(nh.mul_spec(nh).mul_spec(nh).mul_spec(nh).mul_spec(nh) == h5.neg_spec());
    // term mirrors
    lemma_raw_neg_mul_left(h3, third);
    lemma_raw_neg_mul_right(two, h5);
    lemma_raw_neg_mul_left(two.mul_spec(h5), f115);
    assert(nh.mul_spec(nh).mul_spec(nh).mul_spec(third) == t1.neg_spec());
    assert(two.mul_spec(h5.neg_spec()) == two.mul_spec(h5).neg_spec());
    assert(two.mul_spec(h5.neg_spec()).mul_spec(f115) == t2.neg_spec());
    // sum mirrors
    Rational::lemma_neg_add(h, t1);
    Rational::lemma_neg_add(s1, t2);
    assert(nh.add_spec(t1.neg_spec()) == s1.neg_spec());
    assert(tan_half_series_model(nh) == s1.neg_spec().add_spec(t2.neg_spec()));
    assert(tan_half_series_model(nh) == s1.add_spec(t2).neg_spec());
}

/// −1/2 ≤ h ≤ 0 ⇒ the untrusted series lands in [−1, 1] (odd mirror of
/// lemma_series_unit_interval — discharges the Some-guarantee for
/// negative spin).
pub proof fn lemma_series_neg_unit_interval(h: Rational)
    requires
        Rational::from_frac_spec(-1, 2).le_spec(h),
        h.le_spec(Rational::from_int_spec(0)),
    ensures
        t_in_symmetric_unit_interval(tan_half_series_model(h)),
{
    let nh = h.neg_spec();
    let z = Rational::from_int_spec(0);
    let half = Rational::from_frac_spec(1, 2);
    let mhalf = Rational::from_frac_spec(-1, 2);
    let one = Rational::from_int_spec(1);
    let mone = Rational::from_int_spec(-1);
    // 0 ≤ −h ≤ 1/2
    Rational::lemma_neg_reverses_le(mhalf, h);
    Rational::lemma_neg_reverses_le(h, z);
    assert(mhalf.num == -1);
    assert(mhalf.denom() == 2);
    assert(half.num == 1);
    assert(half.denom() == 2);
    assert(mhalf.neg_spec() == half);
    assert(z.neg_spec() == z);
    assert(z.le_spec(nh));
    assert(nh.le_spec(half));
    // series(−h) ∈ [0,1] and series(h) == −series(−h)
    lemma_series_unit_interval(nh);
    lemma_series_model_neg(h);
    Rational::lemma_neg_reverses_le(z, tan_half_series_model(nh));
    Rational::lemma_neg_reverses_le(tan_half_series_model(nh), one);
    Rational::lemma_neg_involution(tan_half_series_model(nh));
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(mone.num == -1);
    assert(mone.denom() == 1);
    assert(one.neg_spec() == mone);
    assert(tan_half_series_model(nh).neg_spec() == tan_half_series_model(h));
    assert(mone.le_spec(tan_half_series_model(h)));
    assert(tan_half_series_model(h).le_spec(z));
    assert(z.le_spec(one) == (z.num * one.denom() <= one.num * z.denom()));
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(one));
    Rational::lemma_le_transitive(tan_half_series_model(h), z, one);
}

/// t ≡ 0 ⇒ the ledger increment is ≡ 0.
pub proof fn lemma_ledger_increment_zero(t: Rational, series_k: nat)
    requires
        t.num == 0,
    ensures
        ledger_increment(t, series_k).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    crate::proofs::angle_ledger::lemma_arctan_term_zero(t, series_k + 1);
    crate::proofs::angle_ledger::lemma_arctan_term_num_denom(t, series_k + 1);
    lemma_ipow_congruence(t.num, 0, 2 * (series_k + 1) + 1);
    lemma_ipow_zero_base(2 * (series_k + 1) + 1);
    let term = arctan_term(t, series_k + 1);
    assert(term.num == 0);
    assert(term.abs_spec() == term);
    Rational::lemma_eqv_reflexive(Rational::from_int_spec(2));
    Rational::lemma_eqv_mul_congruence(
        Rational::from_int_spec(2), Rational::from_int_spec(2), term, z);
    let tz = two_x(z);
    Rational::lemma_mul_denom_product_int(Rational::from_int_spec(2), z);
    assert(tz.num == 0);
    assert(tz.denom() == 1);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(tz.eqv_spec(z));
    Rational::lemma_eqv_transitive(two_x(term), tz, z);
    assert(ledger_increment(t, series_k) == two_x(term.abs_spec()));
}

/// Why a step was rejected (SPEC §1: StepResult = Ok | Reject(Reason)).
pub enum RejectReason {
    /// A body's tan-half series parameter escaped [−1, 1] (SPEC §3).
    AngleOutOfRange(usize),
    /// The certificate checker rejected the step (D8: never wrong-accept).
    CertFailed,
    /// A snap/canonicalize failed a denominator bound (SPEC §7, 06c).
    DenomOverflow,
    /// Degenerate contact (zero-length normal etc., SPEC §5).
    ManifoldFailed,
}

/// The step contract (SPEC §1, DESIGN §3.7(a)): Ok carries the post-step
/// world and the StepCert witness (SPEC §7) — rows and snaps are empty
/// for free flight; Reject carries the reason. Rollback is free because
/// step is pure (E3).
pub enum StepResult {
    Ok(World, StepCert),
    Reject(RejectReason),
}

/// Free-flight step: gravity to velocities, symplectic position update,
/// tan-half rotation compose, ledger accumulation. Reject = angle reject.
/// Accept range is the full symmetric interval |t| ≤ 1 (SPEC §3); the
/// signed enclosure mirror (proofs/angle_ledger.rs) covers negative t.
pub fn step_free_flight(w: &World) -> (out: StepResult)
    requires
        w.wf_spec(),
    ensures
        // the step only rejects when some body's tan-half parameter
        // escapes [−1, 1] (SPEC §3 phase-1 restriction)
        (forall|i: int|
            0 <= i < w.bodies@.len() ==> t_in_symmetric_unit_interval(
                tan_half_series_model(half_angle_model(
                    #[trigger] w.bodies@[i].omega@, w.dt@))))
            ==> out is Ok,
        out is Ok ==> {
            let w2 = out->Ok_0;
            let cert = out->Ok_1;
            &&& w2.wf_spec()
            &&& w2.bodies@.len() == w.bodies@.len()
            &&& cert.tan_halfs@.len() == w.bodies@.len()
            &&& cert.rows@.len() == 0
            &&& cert.snaps@.len() == 0
            &&& cert.angle_entries@.len() == w.bodies@.len()
            &&& w2.gravity.model@ == w.gravity.model@
            &&& w2.dt@ == w.dt@
            &&& w2.series_k == w.series_k
            &&& forall|i: int|
                0 <= i < w.bodies@.len() ==> {
                    let ti = #[trigger] cert.tan_halfs@[i];
                    &&& ti.wf_spec()
                    &&& t_in_symmetric_unit_interval(ti@)
                    &&& body_step_rel(
                        w.bodies@[i], w2.bodies@[i], w.gravity.model@, w.dt@, ti@)
                    &&& w2.angle_err@[i]@.eqv_spec(
                        w.angle_err@[i as int]@.add_spec(ledger_increment(ti@, w.series_k as nat)))
                    &&& cert.angle_entries@[i]@.eqv_spec(
                        ledger_increment(ti@, w.series_k as nat))
                }
        },
{
    let mut new_bodies: Vec<Body> = Vec::new();
    let mut new_errs: Vec<Scalar> = Vec::new();
    let mut ts: Vec<Scalar> = Vec::new();
    let mut angle_entries: Vec<Scalar> = Vec::new();
    let mut i: usize = 0;
    while i < w.bodies.len()
        invariant
            i <= w.bodies@.len(),
            w.wf_spec(),
            new_bodies@.len() == i as int,
            new_errs@.len() == i as int,
            ts@.len() == i as int,
            angle_entries@.len() == i as int,
            forall|j: int|
                0 <= j < i as int ==> {
                    let tj = #[trigger] ts@[j];
                    &&& tj.wf_spec()
                    &&& t_in_symmetric_unit_interval(tj@)
                    &&& new_bodies@[j].wf_spec()
                    &&& body_step_rel(
                        w.bodies@[j], new_bodies@[j], w.gravity.model@, w.dt@, tj@)
                    &&& new_errs@[j].wf_spec()
                    &&& q_nonneg(new_errs@[j]@)
                    &&& new_errs@[j]@.eqv_spec(
                        w.angle_err@[j]@.add_spec(ledger_increment(tj@, w.series_k as nat)))
                    &&& angle_entries@[j]@.eqv_spec(
                        ledger_increment(tj@, w.series_k as nat))
                },
        decreases w.bodies.len() - i,
    {
        let zero = RuntimeRational::from_int(0);
        let is_static = w.bodies[i].inv_mass.eq(&zero);
        proof {
            // eq ⟺ num == 0 (bridge to body_dynamic)
            assert(w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0))
                == (w.bodies@[i as int].inv_mass@.num == 0));
            assert(is_static == (w.bodies@[i as int].inv_mass@.num == 0));
        }
        if is_static {
            let b2 = w.bodies[i].copy_body();
            let e2 = verus_rational::runtime_rational::copy_rational(&w.angle_err[i]);
            let t2 = RuntimeRational::from_int(0);
            proof {
                let ghost old_e = w.angle_err@[i as int]@;
                let ghost inc = ledger_increment(t2@, w.series_k as nat);
                let ghost z = Rational::from_int_spec(0);
                assert(t2@ == z);
                assert(t2@.num == 0);
                lemma_ledger_increment_zero(t2@, w.series_k as nat);
                // old + inc ≡ old + 0 ≡ old, so e2@ == old ≡ old + inc
                Rational::lemma_eqv_reflexive(old_e);
                Rational::lemma_eqv_add_congruence(old_e, old_e, inc, z);
                lemma_raw_add_zero_right(old_e);
                Rational::lemma_eqv_symmetric(old_e.add_spec(z), old_e);
                Rational::lemma_eqv_transitive(old_e.add_spec(inc), old_e.add_spec(z), old_e);
                Rational::lemma_eqv_symmetric(old_e.add_spec(inc), old_e);
                // t_in_symmetric_unit_interval(0): −1 ≤ 0 ≤ 1
                assert(Rational::from_int_spec(-1).le_spec(t2@));
                assert(t2@.le_spec(Rational::from_int_spec(1)));
            }
            new_bodies.push(b2);
            new_errs.push(e2);
            ts.push(t2);
            let e_inc = RuntimeRational::from_int(0);
            proof {
                // entry ≡ 0 ≡ ledger_increment(0, k) (increment of a static
                // body is exactly zero — lemma_ledger_increment_zero above)
                let ghost inc = ledger_increment(t2@, w.series_k as nat);
                let ghost z = Rational::from_int_spec(0);
                lemma_ledger_increment_zero(t2@, w.series_k as nat);
                Rational::lemma_eqv_reflexive(z);
                Rational::lemma_eqv_symmetric(inc, z);
                Rational::lemma_eqv_transitive(e_inc@, z, inc);
            }
            angle_entries.push(e_inc);
        } else {
            let gdt = w.gravity.scaled(&w.dt);
            let vel1 = w.bodies[i].vel.add(&gdt);
            let dp = vel1.scaled(&w.dt);
            let pos1 = w.bodies[i].pos.add(&dp);
            let h = w.bodies[i].omega.mul(&w.dt);
            let two = RuntimeRational::from_int(2);
            proof {
                assert(!two@.eqv_spec(Rational::from_int_spec(0)));
            }
            let half = h.div(&two);
            let t = RotQ::tan_half_series(&half);
            let one = RuntimeRational::from_int(1);
            let minus_one = RuntimeRational::from_int(-1);
            let t_ok = minus_one.le(&t) && t.le(&one);
            if !t_ok {
                proof {
                    // reject witness: this body's t is outside [−1, 1]
                    assert(!t_in_symmetric_unit_interval(t@));
                    assert(t@ == tan_half_series_model(half_angle_model(
                        w.bodies@[i as int].omega@, w.dt@)));
                }
                return StepResult::Reject(RejectReason::AngleOutOfRange(i));
            }
            let dr = RotQ::from_tan_half(&t);
            let rot1 = w.bodies[i].rot.compose(&dr);
            proof {
                assert(half@ == w.bodies@[i as int].omega@.mul_spec(w.dt@).div_spec(
                    Rational::from_int_spec(2)));
                assert(half@ == half_angle_model(w.bodies@[i as int].omega@, w.dt@));
                assert(t@ == tan_half_series_model(half@));
                assert(t@ == tan_half_series_model(half_angle_model(
                    w.bodies@[i as int].omega@, w.dt@)));
            }
            let omega1 = verus_rational::runtime_rational::copy_rational(&w.bodies[i].omega);
            let im1 = verus_rational::runtime_rational::copy_rational(&w.bodies[i].inv_mass);
            let ii1 = verus_rational::runtime_rational::copy_rational(&w.bodies[i].inv_inertia);
            let shape1 = w.bodies[i].shape.copy_compound();
            let b2 = Body {
                pos: pos1,
                rot: rot1,
                vel: vel1,
                omega: omega1,
                inv_mass: im1,
                inv_inertia: ii1,
                shape: shape1,
            };
            // ledger: 2·|term_{k+1}(t)|
            let term = arctan_term_exec(&t, w.series_k + 1);
            let sgn = term.signum();
            let abs_term = if sgn < 0i8 {
                term.neg()
            } else {
                term
            };
            let width = two.mul(&abs_term);
            let e2 = w.angle_err[i].add(&width);
            proof {
                Rational::lemma_signum_negative_iff(term@);
                Rational::lemma_signum_zero_iff(term@);
                Rational::lemma_signum_positive_iff(term@);
                if sgn < 0i8 {
                    assert(term@.signum() == -1);
                    assert(term@.num < 0);
                    assert(term@.abs_spec() == term@.neg_spec());
                } else {
                    assert(term@.signum() == 0 || term@.signum() == 1);
                    assert(term@.num >= 0);
                    assert(term@.abs_spec() == term@);
                }
                assert(abs_term@ == term@.abs_spec());
                assert(width@ == ledger_increment(t@, w.series_k as nat));
                lemma_ledger_increment_nonneg(t@, w.series_k as nat);
                lemma_raw_add_nonneg(w.angle_err@[i as int]@, ledger_increment(t@, w.series_k as nat));
            }
            new_bodies.push(b2);
            new_errs.push(e2);
            ts.push(t);
            proof {
                // width@ == ledger_increment(t@, k) (asserted above); the
                // cert entry is exactly the increment used.
                Rational::lemma_eqv_reflexive(ledger_increment(t@, w.series_k as nat));
            }
            angle_entries.push(width);
        }
        i = i + 1;
    }
    let gravity2 = copy_svec2(&w.gravity);
    let dt2 = verus_rational::runtime_rational::copy_rational(&w.dt);
    let mut joints2: Vec<Joint> = Vec::new();
    let mut j: usize = 0;
    while j < w.joints.len()
        invariant
            j <= w.joints@.len(),
            w.wf_spec(),
            joints2@.len() == j as int,
            forall|k: int|
                0 <= k < j as int ==> {
                    let jj = #[trigger] joints2@[k];
                    &&& jj.wf_spec()
                    &&& jj.a == w.joints@[k].a
                    &&& jj.b == w.joints@[k].b
                    &&& jj.anchor_a.model@ == w.joints@[k].anchor_a.model@
                    &&& jj.anchor_b.model@ == w.joints@[k].anchor_b.model@
                },
        decreases w.joints.len() - j,
    {
        joints2.push(w.joints[j].copy_joint());
        j = j + 1;
    }
    let w2 = World {
        bodies: new_bodies,
        joints: joints2,
        gravity: gravity2,
        dt: dt2,
        series_k: w.series_k,
        angle_err: new_errs,
    };
    proof {
        assert(q_pos(w2.dt@));
        assert forall|k: int|
            0 <= k < w2.joints@.len() implies {
                let jj = #[trigger] w2.joints@[k];
                &&& jj.wf_spec()
                &&& (jj.a as int) < w2.bodies@.len()
                &&& (jj.b as int) < w2.bodies@.len()
            }
        by {
            let jj = w2.joints@[k];
            assert(jj.wf_spec());
            assert((jj.a as int) < w.bodies@.len());
        }
        assert forall|j: int|
            0 <= j < w2.bodies@.len() implies (#[trigger] w2.bodies@[j]).wf_spec()
        by {
            let tj = ts@[j];
            assert(new_bodies@[j].wf_spec());
        }
        assert forall|j: int|
            0 <= j < w2.angle_err@.len() implies {
                let e = #[trigger] w2.angle_err@[j];
                e.wf_spec() && q_nonneg(e@)
            }
        by {
            let tj = ts@[j];
            assert(new_errs@[j].wf_spec());
            assert(q_nonneg(new_errs@[j]@));
        }
        assert(w2.wf_spec());
        assert forall|i: int|
            0 <= i < w.bodies@.len() implies {
                let ti = #[trigger] ts@[i];
                &&& ti.wf_spec()
                &&& t_in_symmetric_unit_interval(ti@)
                &&& body_step_rel(w.bodies@[i], w2.bodies@[i], w.gravity.model@, w.dt@, ti@)
                &&& w2.angle_err@[i]@.eqv_spec(
                    w.angle_err@[i]@.add_spec(ledger_increment(ti@, w.series_k as nat)))
                &&& angle_entries@[i]@.eqv_spec(
                    ledger_increment(ti@, w.series_k as nat))
            }
        by {
            let ti = ts@[i];
            assert(ti.wf_spec());
            assert(t_in_symmetric_unit_interval(ti@));
            assert(body_step_rel(w.bodies@[i], w2.bodies@[i], w.gravity.model@, w.dt@, ti@));
            assert(w2.angle_err@[i]@.eqv_spec(
                w.angle_err@[i]@.add_spec(ledger_increment(ti@, w.series_k as nat))));
            assert(angle_entries@[i]@.eqv_spec(
                ledger_increment(ti@, w.series_k as nat)));
        }
    }
    let cert = StepCert {
        rows: Vec::new(),
        tan_halfs: ts,
        snaps: Vec::new(),
        angle_entries,
    };
    StepResult::Ok(w2, cert)
}

} // verus!

verus! {

// ── phys-06: the full step pipeline (SPEC §6) ─────────────────────────
// Untrusted except ensures (D8): gravity → rows → PGS → canonicalize →
// integrate → canonicalize → certify. The checker is the claim.

/// Gravity pass (pipeline step 1): v += g·dt per dynamic body; statics
/// untouched. Everything else preserved (positions, rotations, shapes).
pub fn apply_gravity_exec(w: &World) -> (out: Vec<Body>)
    requires
        w.wf_spec(),
    ensures
        out@.len() == w.bodies@.len(),
        forall|i: int|
            0 <= i < w.bodies@.len() ==> {
                let b = #[trigger] out@[i];
                &&& b.wf_spec()
                &&& b.pos.model@ == w.bodies@[i].pos.model@
                &&& b.rot.c@ == w.bodies@[i].rot.c@
                &&& b.rot.s@ == w.bodies@[i].rot.s@
                &&& b.omega@ == w.bodies@[i].omega@
                &&& b.inv_mass@ == w.bodies@[i].inv_mass@
                &&& b.inv_inertia@ == w.bodies@[i].inv_inertia@
                &&& b.shape.model_parts() == w.bodies@[i].shape.model_parts()
                &&& (body_dynamic(w.bodies@[i]) ==> veqv(
                        b.vel.model@,
                        vadd(w.bodies@[i].vel.model@,
                            vscale(w.dt@, w.gravity.model@))))
                &&& (!body_dynamic(w.bodies@[i]) ==> veqv(
                        b.vel.model@, w.bodies@[i].vel.model@))
            },
{
    let mut out: Vec<Body> = Vec::new();
    let mut i: usize = 0;
    while i < w.bodies.len()
        invariant
            i <= w.bodies@.len(),
            w.wf_spec(),
            out@.len() == i as int,
            forall|j: int|
                0 <= j < i as int ==> {
                    let b = #[trigger] out@[j];
                    &&& b.wf_spec()
                    &&& b.pos.model@ == w.bodies@[j].pos.model@
                    &&& b.rot.c@ == w.bodies@[j].rot.c@
                    &&& b.rot.s@ == w.bodies@[j].rot.s@
                    &&& b.omega@ == w.bodies@[j].omega@
                    &&& b.inv_mass@ == w.bodies@[j].inv_mass@
                    &&& b.inv_inertia@ == w.bodies@[j].inv_inertia@
                    &&& b.shape.model_parts() == w.bodies@[j].shape.model_parts()
                    &&& (body_dynamic(w.bodies@[j]) ==> veqv(
                            b.vel.model@,
                            vadd(w.bodies@[j].vel.model@,
                                vscale(w.dt@, w.gravity.model@))))
                    &&& (!body_dynamic(w.bodies@[j]) ==> veqv(
                            b.vel.model@, w.bodies@[j].vel.model@))
                },
        decreases w.bodies.len() - i,
    {
        let zero = RuntimeRational::from_int(0);
        let is_static = w.bodies[i].inv_mass.eq(&zero);
        proof {
            assert(w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0))
                == (w.bodies@[i as int].inv_mass@.num == 0));
            assert(is_static == !body_dynamic(w.bodies@[i as int]));
        }
        if is_static {
            out.push(w.bodies[i].copy_body());
        } else {
            let nvx = w.bodies[i].vel.x.add(&w.gravity.x.mul(&w.dt));
            let nvy = w.bodies[i].vel.y.add(&w.gravity.y.mul(&w.dt));
            let b2 = Body {
                pos: copy_svec2(&w.bodies[i].pos),
                rot: w.bodies[i].rot.copy(),
                vel: SVec2::new(nvx, nvy),
                omega: verus_rational::runtime_rational::copy_rational(&w.bodies[i].omega),
                inv_mass: verus_rational::runtime_rational::copy_rational(&w.bodies[i].inv_mass),
                inv_inertia: verus_rational::runtime_rational::copy_rational(
                    &w.bodies[i].inv_inertia),
                shape: w.bodies[i].shape.copy_compound(),
            };
            proof {
                assert(b2.vel.model@ == vadd(
                    w.bodies@[i as int].vel.model@,
                    vscale(w.dt@, w.gravity.model@)));
                Rational::lemma_eqv_reflexive(b2.vel.model@.x);
                Rational::lemma_eqv_reflexive(b2.vel.model@.y);
            }
            out.push(b2);
        }
        i = i + 1;
    }
    out
}

/// Canonicalize pass (D10, exec feasibility — see memory/exec-feasibility):
/// normalize every body's velocity/position/rotation/omega witnesses in
/// place. Value-preserving (eqv), no ledger entry.
pub fn canonicalize_bodies_exec(bodies: &mut Vec<Body>)
    requires
        forall|i: int| 0 <= i < old(bodies)@.len() ==> (#[trigger] old(bodies)@[i]).wf_spec(),
    ensures
        bodies@.len() == old(bodies)@.len(),
        forall|i: int|
            0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
{
    let mut i: usize = 0;
    while i < bodies.len()
        invariant
            i <= bodies@.len(),
            bodies@.len() == old(bodies)@.len(),
            forall|j: int| 0 <= j < bodies@.len() ==> (#[trigger] bodies@[j]).wf_spec(),
        decreases bodies.len() - i,
    {
        let b = &bodies[i];
        let b2 = Body {
            pos: SVec2::new(b.pos.x.normalize(), b.pos.y.normalize()),
            rot: RotQ {
                c: b.rot.c.normalize(),
                s: b.rot.s.normalize(),
            },
            vel: SVec2::new(b.vel.x.normalize(), b.vel.y.normalize()),
            omega: b.omega.normalize(),
            inv_mass: verus_rational::runtime_rational::copy_rational(&b.inv_mass),
            inv_inertia: verus_rational::runtime_rational::copy_rational(&b.inv_inertia),
            shape: b.shape.copy_compound(),
        };
        proof {
            // normalize is value-preserving (eqv), and every body wf
            // predicate is eqv-respecting
            let ghost ob = bodies@[i as int];
            assert(b2.pos.model@.x.eqv_spec(ob.pos.model@.x));
            assert(b2.pos.model@.y.eqv_spec(ob.pos.model@.y));
            assert(b2.rot.c@.eqv_spec(ob.rot.c@));
            assert(b2.rot.s@.eqv_spec(ob.rot.s@));
            assert(b2.vel.model@.x.eqv_spec(ob.vel.model@.x));
            assert(b2.vel.model@.y.eqv_spec(ob.vel.model@.y));
            assert(b2.omega@.eqv_spec(ob.omega@));
            assert(b2.inv_mass@ == ob.inv_mass@);
            assert(b2.inv_inertia@ == ob.inv_inertia@);
            // unit_norm is eqv-respecting (q_eqv form), bridged by
            // lemma_unit_norm_raw (unit_norm == unit_norm_raw)
            crate::proofs::rational_raw::lemma_unit_norm_raw(ob.rot.c@, ob.rot.s@);
            assert(b2.rot.c@.mul_spec(b2.rot.c@).add_spec(b2.rot.s@.mul_spec(b2.rot.s@))
                .eqv_spec(Rational::from_int_spec(1))) by {
                Rational::lemma_eqv_reflexive(b2.rot.c@);
                Rational::lemma_eqv_reflexive(b2.rot.s@);
                Rational::lemma_eqv_mul_congruence(b2.rot.c@, ob.rot.c@, b2.rot.c@, ob.rot.c@);
                Rational::lemma_eqv_mul_congruence(b2.rot.s@, ob.rot.s@, b2.rot.s@, ob.rot.s@);
                Rational::lemma_eqv_add_congruence(
                    b2.rot.c@.mul_spec(b2.rot.c@), ob.rot.c@.mul_spec(ob.rot.c@),
                    b2.rot.s@.mul_spec(b2.rot.s@), ob.rot.s@.mul_spec(ob.rot.s@));
                Rational::lemma_eqv_transitive(
                    b2.rot.c@.mul_spec(b2.rot.c@).add_spec(b2.rot.s@.mul_spec(b2.rot.s@)),
                    ob.rot.c@.mul_spec(ob.rot.c@).add_spec(ob.rot.s@.mul_spec(ob.rot.s@)),
                    Rational::from_int_spec(1));
            };
            crate::proofs::rational_raw::lemma_unit_norm_raw(b2.rot.c@, b2.rot.s@);
            assert(b2.wf_spec());
        }
        bodies.set(i, b2);
        i = i + 1;
    }
}

} // verus!

verus! {

/// Integration pass (pipeline step 6): symplectic position update +
/// tan-half rotation compose + ledger accumulation over pre-computed
/// (gravity-applied, contact-solved) bodies. Reject = tan-half parameter
/// outside [−1, 1]. Thin ensures (D8): wf, lengths, per-body tan
/// interval, ledger-entry equivalence — the certificate is the claim.
pub fn integrate_exec(
    w: &World,
    bodies: Vec<Body>,
) -> (out: Result<(Vec<Body>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), usize>)
    requires
        w.wf_spec(),
        bodies@.len() == w.bodies@.len(),
        forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
    ensures
        out is Ok ==> {
            let (nb, errs, ts, entries) = out->Ok_0;
            &&& nb@.len() == w.bodies@.len()
            &&& errs@.len() == w.bodies@.len()
            &&& ts@.len() == w.bodies@.len()
            &&& entries@.len() == w.bodies@.len()
            &&& forall|i: int|
                0 <= i < w.bodies@.len() ==> {
                    let ti = #[trigger] ts@[i];
                    &&& ti.wf_spec()
                    &&& t_in_symmetric_unit_interval(ti@)
                    &&& nb@[i].wf_spec()
                    &&& errs@[i].wf_spec()
                    &&& q_nonneg(errs@[i]@)
                    &&& errs@[i]@.eqv_spec(
                        w.angle_err@[i]@.add_spec(ledger_increment(ti@, w.series_k as nat)))
                    &&& entries@[i].wf_spec()
                    &&& entries@[i]@.eqv_spec(ledger_increment(ti@, w.series_k as nat))
                }
        },
{
    let mut new_bodies: Vec<Body> = Vec::new();
    let mut new_errs: Vec<Scalar> = Vec::new();
    let mut ts: Vec<Scalar> = Vec::new();
    let mut angle_entries: Vec<Scalar> = Vec::new();
    let mut i: usize = 0;
    while i < bodies.len()
        invariant
            i <= bodies@.len(),
            w.wf_spec(),
            bodies@.len() == w.bodies@.len(),
            forall|bi: int| 0 <= bi < bodies@.len() ==> (#[trigger] bodies@[bi]).wf_spec(),
            new_bodies@.len() == i as int,
            new_errs@.len() == i as int,
            ts@.len() == i as int,
            angle_entries@.len() == i as int,
            forall|j: int|
                0 <= j < i as int ==> {
                    let tj = #[trigger] ts@[j];
                    &&& tj.wf_spec()
                    &&& t_in_symmetric_unit_interval(tj@)
                    &&& new_bodies@[j].wf_spec()
                    &&& new_errs@[j].wf_spec()
                    &&& q_nonneg(new_errs@[j]@)
                    &&& new_errs@[j]@.eqv_spec(
                        w.angle_err@[j]@.add_spec(ledger_increment(tj@, w.series_k as nat)))
                    &&& angle_entries@[j].wf_spec()
                    &&& angle_entries@[j]@.eqv_spec(ledger_increment(tj@, w.series_k as nat))
                },
        decreases bodies.len() - i,
    {
        let zero = RuntimeRational::from_int(0);
        let is_static = bodies[i].inv_mass.eq(&zero);
        proof {
            assert(bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0))
                == (bodies@[i as int].inv_mass@.num == 0));
            assert(is_static == (bodies@[i as int].inv_mass@.num == 0));
        }
        if is_static {
            let b2 = bodies[i].copy_body();
            let e2 = verus_rational::runtime_rational::copy_rational(&w.angle_err[i]);
            let t2 = RuntimeRational::from_int(0);
            proof {
                let ghost old_e = w.angle_err@[i as int]@;
                let ghost inc = ledger_increment(t2@, w.series_k as nat);
                let ghost z = Rational::from_int_spec(0);
                assert(t2@ == z);
                assert(t2@.num == 0);
                lemma_ledger_increment_zero(t2@, w.series_k as nat);
                Rational::lemma_eqv_reflexive(old_e);
                Rational::lemma_eqv_add_congruence(old_e, old_e, inc, z);
                lemma_raw_add_zero_right(old_e);
                Rational::lemma_eqv_symmetric(old_e.add_spec(z), old_e);
                Rational::lemma_eqv_transitive(old_e.add_spec(inc), old_e.add_spec(z), old_e);
                Rational::lemma_eqv_symmetric(old_e.add_spec(inc), old_e);
                assert(Rational::from_int_spec(-1).le_spec(t2@));
                assert(t2@.le_spec(Rational::from_int_spec(1)));
            }
            new_bodies.push(b2);
            new_errs.push(e2);
            ts.push(t2);
            let e_inc = RuntimeRational::from_int(0);
            proof {
                let ghost inc = ledger_increment(t2@, w.series_k as nat);
                let ghost z = Rational::from_int_spec(0);
                lemma_ledger_increment_zero(t2@, w.series_k as nat);
                Rational::lemma_eqv_reflexive(z);
                Rational::lemma_eqv_symmetric(inc, z);
                Rational::lemma_eqv_transitive(e_inc@, z, inc);
            }
            angle_entries.push(e_inc);
        } else {
            let dp = bodies[i].vel.scaled(&w.dt);
            let pos1 = bodies[i].pos.add(&dp);
            let vel1 = copy_svec2(&bodies[i].vel);
            let h = bodies[i].omega.mul(&w.dt);
            let two = RuntimeRational::from_int(2);
            proof {
                assert(!two@.eqv_spec(Rational::from_int_spec(0)));
            }
            let half = h.div(&two);
            let t = RotQ::tan_half_series(&half);
            let one = RuntimeRational::from_int(1);
            let minus_one = RuntimeRational::from_int(-1);
            let t_ok = minus_one.le(&t) && t.le(&one);
            if !t_ok {
                return Result::Err(i);
            }
            let dr = RotQ::from_tan_half(&t);
            let rot1 = bodies[i].rot.compose(&dr);
            let omega1 = verus_rational::runtime_rational::copy_rational(&bodies[i].omega);
            let im1 = verus_rational::runtime_rational::copy_rational(&bodies[i].inv_mass);
            let ii1 = verus_rational::runtime_rational::copy_rational(&bodies[i].inv_inertia);
            let shape1 = bodies[i].shape.copy_compound();
            let b2 = Body {
                pos: pos1,
                rot: rot1,
                vel: vel1,
                omega: omega1,
                inv_mass: im1,
                inv_inertia: ii1,
                shape: shape1,
            };
            // ledger: 2·|term_{k+1}(t)|
            let term = arctan_term_exec(&t, w.series_k + 1);
            let sgn = term.signum();
            let abs_term = if sgn < 0i8 {
                term.neg()
            } else {
                term
            };
            let width = two.mul(&abs_term);
            let e2 = w.angle_err[i].add(&width).normalize();
            proof {
                Rational::lemma_signum_negative_iff(term@);
                Rational::lemma_signum_zero_iff(term@);
                Rational::lemma_signum_positive_iff(term@);
                if sgn < 0i8 {
                    assert(term@.signum() == -1);
                    assert(term@.num < 0);
                    assert(term@.abs_spec() == term@.neg_spec());
                } else {
                    assert(term@.signum() == 0 || term@.signum() == 1);
                    assert(term@.num >= 0);
                    assert(term@.abs_spec() == term@);
                }
                assert(abs_term@ == term@.abs_spec());
                assert(width@ == ledger_increment(t@, w.series_k as nat));
                lemma_ledger_increment_nonneg(t@, w.series_k as nat);
                lemma_raw_add_nonneg(
                    w.angle_err@[i as int]@, ledger_increment(t@, w.series_k as nat));
                // e2 ≡ old + width (normalize is value-preserving)
                assert(e2@.eqv_spec(
                    w.angle_err@[i as int]@.add_spec(ledger_increment(t@, w.series_k as nat))));
                // e2 ≥ 0 (eqv to a nonneg value)
                crate::proofs::shape::lemma_le_eqv_subst_right(
                    Rational::from_int_spec(0),
                    w.angle_err@[i as int]@.add_spec(ledger_increment(t@, w.series_k as nat)),
                    e2@);
            }
            new_bodies.push(b2);
            new_errs.push(e2);
            ts.push(t);
            proof {
                Rational::lemma_eqv_reflexive(ledger_increment(t@, w.series_k as nat));
            }
            angle_entries.push(width);
        }
        i = i + 1;
    }
    Result::Ok((new_bodies, new_errs, ts, angle_entries))
}

/// The full engine step (SPEC §6): gravity → joint rows (none, phys-07)
/// → rows → PGS → canonicalize → integrate → canonicalize → certify.
/// Ok carries the post world and the StepCert the checker accepted;
/// Reject = angle out of range or certificate failure (D8: never a
/// wrong accept).
pub fn step(w: &World, tol_v: &Scalar, tol_p: &Scalar, tol_j: &Scalar) -> (r: StepResult)
    requires
        w.wf_spec(),
        tol_v.wf_spec(),
        tol_p.wf_spec(),
        tol_j.wf_spec(),
        forall|i: int| 0 <= i < w.bodies@.len() ==> (#[trigger] w.bodies@[i]).shape.parts@.len()
            >= 1,
    ensures
        r is Ok ==> {
            &&& r->Ok_0.wf_spec()
            &&& crate::certificate::step_checks_pass(*w, r->Ok_0, r->Ok_1, tol_v@, tol_p@, tol_j@)
            &&& crate::certificate::step_certified(*w, r->Ok_0, r->Ok_1, tol_v@, tol_p@, tol_j@)
        },
{
    // 1. gravity
    let gb = apply_gravity_exec(w);
    proof {
        // parts-len bridge: model_parts() == parts@.map(...) preserves len
        assert forall|bi: int|
            0 <= bi < gb@.len() implies (#[trigger] gb@[bi]).shape.parts@.len() >= 1
        by {
            assert(gb@[bi].shape.model_parts() == w.bodies@[bi].shape.model_parts());
            assert(gb@[bi].shape.model_parts().len() == gb@[bi].shape.parts@.len());
        }
    }
    // 2. joint rows — none in phys-06 (w.joints iterated but empty of rows)
    // 3. broadphase → narrowphase → manifolds → rows
    let mut aabbs: Vec<crate::broadphase::Aabb> = Vec::new();
    let mut ai: usize = 0;
    while ai < gb.len()
        invariant
            ai <= gb@.len(),
            aabbs@.len() == ai as int,
            forall|bi: int| 0 <= bi < gb@.len() ==> (#[trigger] gb@[bi]).wf_spec(),
            forall|bi: int| 0 <= bi < gb@.len() ==> (#[trigger] gb@[bi]).shape.parts@.len() >= 1,
            forall|k: int| 0 <= k < aabbs@.len() ==> (#[trigger] aabbs@[k]).wf_spec(),
        decreases gb.len() - ai,
    {
        aabbs.push(crate::solver::body_aabb_exec(&gb[ai]));
        ai = ai + 1;
    }
    let (rows, meffs) = crate::solver::build_rows_exec(&gb, &aabbs);
    proof {
        // meffs-wf trigger bridge (build_rows states it inside the rows-forall)
        assert forall|k: int| 0 <= k < meffs@.len() implies (#[trigger] meffs@[k]).wf_spec()
        by {
            let r = rows@[k];
        }
    }
    // 4. PGS velocity solve
    let (pb, prows) = crate::solver::pgs_sweep_exec(&gb, &rows, &meffs, 16);
    // 5. canonicalize (D10, exec feasibility)
    let mut pb2 = pb;
    canonicalize_bodies_exec(&mut pb2);
    // 6. integrate
    let integ = integrate_exec(w, pb2);
    match integ {
        Result::Err(idx) => StepResult::Reject(RejectReason::AngleOutOfRange(idx)),
        Result::Ok((nb, errs, ts, entries)) => {
            let mut nb2 = nb;
            proof {
                assert forall|bi: int| 0 <= bi < nb2@.len() implies (#[trigger] nb2@[bi]).wf_spec()
                by {
                    let tj = ts@[bi];
                }
            }
            canonicalize_bodies_exec(&mut nb2);
            // 7./8. projection + position snap are 06b/06c
            let gravity2 = copy_svec2(&w.gravity);
            let dt2 = verus_rational::runtime_rational::copy_rational(&w.dt);
            let mut joints2: Vec<Joint> = Vec::new();
            let mut j: usize = 0;
            while j < w.joints.len()
                invariant
                    j <= w.joints@.len(),
                    w.wf_spec(),
                    joints2@.len() == j as int,
                    forall|k: int|
                        0 <= k < j as int ==> {
                            let jj = #[trigger] joints2@[k];
                            &&& jj.wf_spec()
                            &&& jj.a == w.joints@[k].a
                            &&& jj.b == w.joints@[k].b
                            &&& jj.anchor_a.model@ == w.joints@[k].anchor_a.model@
                            &&& jj.anchor_b.model@ == w.joints@[k].anchor_b.model@
                        },
                decreases w.joints.len() - j,
            {
                joints2.push(w.joints[j].copy_joint());
                j = j + 1;
            }
            let post = World {
                bodies: nb2,
                joints: joints2,
                gravity: gravity2,
                dt: dt2,
                series_k: w.series_k,
                angle_err: errs,
            };
            proof {
                assert(q_pos(post.dt@));
                assert forall|k: int|
                    0 <= k < post.joints@.len() implies {
                        let jj = #[trigger] post.joints@[k];
                        &&& jj.wf_spec()
                        &&& (jj.a as int) < post.bodies@.len()
                        &&& (jj.b as int) < post.bodies@.len()
                    }
                by {
                    let jj = post.joints@[k];
                    assert(jj.wf_spec());
                    assert((jj.a as int) < w.bodies@.len());
                }
                assert forall|k: int|
                    0 <= k < post.angle_err@.len() implies {
                        let e = #[trigger] post.angle_err@[k];
                        e.wf_spec() && q_nonneg(e@)
                    }
                by {
                    let tj = ts@[k];
                }
                assert(post.wf_spec());
            }
            let cert = StepCert {
                rows: prows,
                tan_halfs: ts,
                snaps: Vec::new(),
                angle_entries: entries,
            };
            // 9. certify
            let ok = crate::certificate::check_step(w, &post, &cert, tol_v, tol_p, tol_j);
            if ok {
                StepResult::Ok(post, cert)
            } else {
                StepResult::Reject(RejectReason::CertFailed)
            }
        },
    }
}

} // verus!
