//! Acceptance scenes (SPEC §8), as verified exec functions: each scene's
//! claim is proven statically, so `ensures out == true` is the green flag.
//!
//! S1 (phys-03): two bodies, zero gravity, initial velocities; 1000 steps;
//!   total linear and angular momentum EXACTLY (eqv) equal to initial.
//! S2 (phys-02): one body spinning at ω = 3, dt = 1/240, 240 steps;
//!   accumulated angle-enclosure width ≤ 240 · (2/(2k+3)) with k = 8.
//! S2-mirror: same with ω = −3 — negative rotation through the signed
//!   enclosure mirror (extended |t| ≤ 1 accept range).

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::narrowphase::{sat_classify, SatResult};
use crate::shape::{convex_poly_inv, orient, vadd, vcross2, Compound, ConvexPoly};
use crate::massprops::{
    centroid_exec, centroid_num, centroid_num_chain, centroid_spec, chain_cross_sum, cross_sum,
    inertia0_exec, inertia0_spec, inertia_edge_term, inertia_num, inertia_num_chain,
    poly_area2_exec, vdot, vscale, vzero,
};
use crate::angle_ledger::{arctan_term, t_in_symmetric_unit_interval, two_x};
use crate::body::Body;
use crate::momentum::{ang_mom, ang_mom_exec, lin_mom_x, lin_mom_y, lin_mom_exec};
use crate::proofs::angle_ledger::{
    lemma_arctan_term_abs_bound, lemma_two_mul_monotone, lemma_unit_implies_symmetric,
};
use crate::proofs::momentum::{grav_zero, lemma_step_preserves_momentum};
use crate::rotq::RotQ;
use crate::step::{
    body_step_rel, half_angle_model, ledger_increment, lemma_series_neg_unit_interval,
    lemma_series_unit_interval, step_free_flight, tan_half_series_model, StepResult,
};
use crate::types::{q_nonneg, SVec2, Scalar};
use crate::world::World;

verus! {

/// 0 ≤ x for a closed nonneg from_int/from_frac value (helper).
proof fn lemma_closed_nonneg_one()
    ensures
        q_nonneg(Rational::from_int_spec(1)),
{
    let z = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(z.le_spec(one));
    assert(q_nonneg(one));
}

proof fn lemma_closed_nonneg_half()
    ensures
        q_nonneg(Rational::from_frac_spec(1, 2)),
{
    let z = Rational::from_int_spec(0);
    let h = Rational::from_frac_spec(1, 2);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(h.num == 1);
    assert(h.denom() == 2);
    assert(z.le_spec(h));
    assert(q_nonneg(h));
}

/// h = 0·dt/2 ≡ 0 — so any body's zero-spin tan-half is in [0,1].
proof fn lemma_half_angle_zero(dt: Rational)
    ensures
        half_angle_model(Rational::from_int_spec(0), dt).eqv_spec(
            Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    let h = half_angle_model(z, dt);
    Rational::lemma_mul_zero(dt);
    let num0 = z.mul_spec(dt);
    assert(Rational::from_int_spec(2).num == 2);
    let recip = Rational::from_int_spec(2).reciprocal_spec();
    assert(h == num0.mul_spec(recip));
    Rational::lemma_eqv_reflexive(recip);
    Rational::lemma_eqv_mul_congruence(num0, z, recip, recip);
    Rational::lemma_mul_zero(recip);
    Rational::lemma_eqv_transitive(h, z.mul_spec(recip), z);
}

/// S1: zero-gravity momentum conservation over 1000 steps.
pub fn scene_s1() -> (out: bool)
    ensures
        out == true,
{
    let zero = RuntimeRational::from_int(0);
    let zero2 = RuntimeRational::from_int(0);
    let gravity = RuntimeVec2::new(zero, zero2);
    let dt = RuntimeRational::from_frac(1, 240);
    proof {
        // dt > 0
        assert(Rational::from_int_spec(0).lt_spec(Rational::from_frac_spec(1, 240)));
    }
    let mut w = World::new(gravity, dt, 8);

    // body 1: pos (0,0), vel (1, 2), ω = 0, m = 1, I = 1
    let b1 = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(2)),
        RuntimeRational::from_int(0),
        RuntimeRational::from_int(1),
        RuntimeRational::from_int(1),
        unit_square_compound(),
    );
    // body 2: pos (3,−1), vel (−1, 1/2), ω = 0, m = 2, I = 1
    let b2 = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(3), RuntimeRational::from_int(-1)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(-1), RuntimeRational::from_frac(1, 2)),
        RuntimeRational::from_int(0),
        RuntimeRational::from_frac(1, 2),
        RuntimeRational::from_int(1),
        unit_square_compound(),
    );
    proof {
        lemma_closed_nonneg_one();
        lemma_closed_nonneg_half();
    }
    w.add_body(b1);
    w.add_body(b2);

    let p0 = lin_mom_exec(&w);
    let l0 = ang_mom_exec(&w);
    let ghost init_bodies = w.bodies@;
    proof {
        assert(w.gravity.model@.x == Rational::from_int_spec(0));
        assert(w.gravity.model@.y == Rational::from_int_spec(0));
        assert(w.dt@ == Rational::from_frac_spec(1, 240));
    }

    let mut i: usize = 0;
    while i < 1000
        invariant
            w.wf_spec(),
            w.bodies@.len() == 2 as int,
            w.gravity.model@.x == Rational::from_int_spec(0),
            w.gravity.model@.y == Rational::from_int_spec(0),
            w.dt@ == Rational::from_frac_spec(1, 240),
            forall|j: int|
                0 <= j < 2 ==> (#[trigger] w.bodies@[j]).omega@ == Rational::from_int_spec(0),
            lin_mom_x(w.bodies@, 2 as nat).eqv_spec(lin_mom_x(init_bodies, 2 as nat)),
            lin_mom_y(w.bodies@, 2 as nat).eqv_spec(lin_mom_y(init_bodies, 2 as nat)),
            ang_mom(w.bodies@, 2 as nat).eqv_spec(ang_mom(init_bodies, 2 as nat)),
        decreases 1000 - i,
    {
        proof {
            assert forall|j: int|
                0 <= j < w.bodies@.len() implies t_in_symmetric_unit_interval(
                    tan_half_series_model(half_angle_model(
                        #[trigger] w.bodies@[j].omega@, w.dt@)))
            by {
                lemma_half_angle_zero(w.dt@);
                let z = Rational::from_int_spec(0);
                let h = half_angle_model(w.bodies@[j].omega@, w.dt@);
                Rational::lemma_eqv_symmetric(h, z);
                Rational::lemma_eqv_implies_le(z, h);
                Rational::lemma_eqv_implies_le(h, z);
                assert(Rational::from_int_spec(0).le_spec(Rational::from_frac_spec(1, 2)));
                Rational::lemma_le_transitive(
                    h, z, Rational::from_frac_spec(1, 2));
                lemma_series_unit_interval(h);
                lemma_unit_implies_symmetric(tan_half_series_model(h));
            }
        }
        let r = step_free_flight(&w);
        proof {
            assert(r is Ok);
        }
        let (w2, ts) = match r {
            StepResult::Ok(w2, ts) => (w2, ts),
            StepResult::Reject(_) => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        proof {
            lemma_step_preserves_momentum(w, w2, ts@);
            Rational::lemma_eqv_transitive(
                lin_mom_x(w2.bodies@, 2 as nat),
                lin_mom_x(w.bodies@, 2 as nat),
                lin_mom_x(init_bodies, 2 as nat));
            Rational::lemma_eqv_transitive(
                lin_mom_y(w2.bodies@, 2 as nat),
                lin_mom_y(w.bodies@, 2 as nat),
                lin_mom_y(init_bodies, 2 as nat));
            Rational::lemma_eqv_transitive(
                ang_mom(w2.bodies@, 2 as nat),
                ang_mom(w.bodies@, 2 as nat),
                ang_mom(init_bodies, 2 as nat));
            assert forall|j: int|
                0 <= j < 2 implies (#[trigger] w2.bodies@[j]).omega@ == Rational::from_int_spec(0)
            by {
                let tj = ts@[j];
            }
        }
        w = w2;
        i = i + 1;
    }

    let p1 = lin_mom_exec(&w);
    let l1 = ang_mom_exec(&w);
    let ok = p1.x.eq(&p0.x) && p1.y.eq(&p0.y) && l1.eq(&l0);
    proof {
        assert(p1.x@ == lin_mom_x(w.bodies@, 2 as nat));
        assert(p0.x@ == lin_mom_x(init_bodies, 2 as nat));
        assert(ok == true);
    }
    ok
}

/// S2: ω = 3 spin, 240 steps, ledger width ≤ 240 · 2/19 (k = 8).
pub fn scene_s2() -> (out: bool)
    ensures
        out == true,
{
    let zero = RuntimeRational::from_int(0);
    let zero2 = RuntimeRational::from_int(0);
    let gravity = RuntimeVec2::new(zero, zero2);
    let dt = RuntimeRational::from_frac(1, 240);
    proof {
        assert(Rational::from_int_spec(0).lt_spec(Rational::from_frac_spec(1, 240)));
    }
    let mut w = World::new(gravity, dt, 8);

    // one spinning body: pos (0,0), vel (0,0), ω = 3, m = 1, I = 1
    let b = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RuntimeRational::from_int(3),
        RuntimeRational::from_int(1),
        RuntimeRational::from_int(1),
        unit_square_compound(),
    );
    proof {
        lemma_closed_nonneg_one();
    }
    w.add_body(b);
    proof {
        assert(w.dt@ == Rational::from_frac_spec(1, 240));
        assert(w.series_k == 8);
        assert(w.bodies@[0].omega@ == Rational::from_int_spec(3));
    }

    let mut i: usize = 0;
    while i < 240
        invariant
            i <= 240,
            w.wf_spec(),
            w.bodies@.len() == 1 as int,
            w.dt@ == Rational::from_frac_spec(1, 240),
            w.series_k == 8,
            w.bodies@[0].omega@ == Rational::from_int_spec(3),
            w.angle_err@[0]@.le_spec(
                Rational::from_int_spec(i as int).mul_spec(Rational::from_frac_spec(2, 19))),
        decreases 240 - i,
    {
        proof {
            // h = 3·(1/240)/2 = 3/480 ∈ [0, 1/2]
            let h = half_angle_model(Rational::from_int_spec(3), Rational::from_frac_spec(1, 240));
            let f = Rational::from_int_spec(3).mul_spec(Rational::from_frac_spec(1, 240));
            Rational::lemma_mul_denom_product_int(
                Rational::from_int_spec(3), Rational::from_frac_spec(1, 240));
            assert(f.num == 3);
            assert(f.denom() == 240);
            assert(Rational::from_int_spec(2).num == 2);
            assert(Rational::from_int_spec(2).reciprocal_spec().num == 1);
            assert(Rational::from_int_spec(2).reciprocal_spec().denom() == 2);
            Rational::lemma_mul_denom_product_int(
                f, Rational::from_int_spec(2).reciprocal_spec());
            assert(h.num == 3);
            assert(h.denom() == 480);
            let z = Rational::from_int_spec(0);
            assert(z.num == 0);
            assert(z.denom() == 1);
            assert(z.le_spec(h));
            assert(h.le_spec(Rational::from_frac_spec(1, 2)));
            lemma_series_unit_interval(h);
            lemma_unit_implies_symmetric(tan_half_series_model(h));
            assert(w.bodies@[0].omega@ == Rational::from_int_spec(3));
            assert(t_in_symmetric_unit_interval(
                tan_half_series_model(half_angle_model(w.bodies@[0].omega@, w.dt@))));
            assert forall|j: int|
                0 <= j < w.bodies@.len() implies t_in_symmetric_unit_interval(
                    tan_half_series_model(half_angle_model(
                        #[trigger] w.bodies@[j].omega@, w.dt@)))
            by {
            }
        }
        let r = step_free_flight(&w);
        proof {
            assert(r is Ok);
        }
        let (w2, ts) = match r {
            StepResult::Ok(w2, ts) => (w2, ts),
            StepResult::Reject(_) => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        proof {
            let ghost t0 = ts@[0]@;
            let ghost inc = ledger_increment(t0, 8 as nat);
            let ghost cap = Rational::from_frac_spec(2, 19);
            // inc = 2·|term_9(t0)| ≤ 2·(1/19) == cap (signed uniform bound)
            assert(t_in_symmetric_unit_interval(t0));
            lemma_arctan_term_abs_bound(t0, 9);
            lemma_two_mul_monotone(
                arctan_term(t0, 9).abs_spec(), Rational::from_frac_spec(1, 19));
            assert(two_x(Rational::from_frac_spec(1, 19)) == Rational::from_frac_spec(2, 19));
            assert(inc.le_spec(cap));
            // err' ≡ err + inc ≤ err + cap ≤ i·cap + cap ≡ (i+1)·cap
            Rational::lemma_le_add_both(
                w.angle_err@[0]@,
                Rational::from_int_spec(i as int).mul_spec(cap),
                inc,
                cap);
            Rational::lemma_eqv_implies_le(
                w2.angle_err@[0]@,
                w.angle_err@[0]@.add_spec(inc));
            Rational::lemma_le_transitive(
                w2.angle_err@[0]@,
                w.angle_err@[0]@.add_spec(inc),
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap));
            // (i+1)·cap ≡ i·cap + cap
            Rational::lemma_from_int_add(i as int, 1);
            Rational::lemma_mul_commutative(
                Rational::from_int_spec((i + 1) as int), cap);
            Rational::lemma_mul_distributes_over_add(
                cap, Rational::from_int_spec(i as int), Rational::from_int_spec(1));
            Rational::lemma_mul_one_identity(cap);
            Rational::lemma_mul_commutative(cap, Rational::from_int_spec(i as int));
            assert(Rational::from_int_spec((i + 1) as int).mul_spec(cap).eqv_spec(
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap)));
            Rational::lemma_eqv_symmetric(
                Rational::from_int_spec((i + 1) as int).mul_spec(cap),
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap));
            Rational::lemma_eqv_implies_le(
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap),
                Rational::from_int_spec((i + 1) as int).mul_spec(cap));
            Rational::lemma_le_transitive(
                w2.angle_err@[0]@,
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap),
                Rational::from_int_spec((i + 1) as int).mul_spec(cap));
        }
        w = w2;
        i = i + 1;
    }

    // final: angle_err[0] ≤ 240·(2/19)
    let cap_total = RuntimeRational::from_int(240).mul(&RuntimeRational::from_frac(2, 19));
    let ok = w.angle_err[0].le(&cap_total);
    proof {
        assert(w.angle_err@[0]@.le_spec(
            Rational::from_int_spec(240).mul_spec(Rational::from_frac_spec(2, 19))));
        assert(ok == true);
    }
    ok
}

/// S2-mirror: ω = −3 spin (negative rotation through the signed mirror),
/// 240 steps, ledger width ≤ 240 · 2/19 (k = 8). Exercises the extended
/// |t| ≤ 1 accept range and the odd-series lemmas.
pub fn scene_s2_neg() -> (out: bool)
    ensures
        out == true,
{
    let zero = RuntimeRational::from_int(0);
    let zero2 = RuntimeRational::from_int(0);
    let gravity = RuntimeVec2::new(zero, zero2);
    let dt = RuntimeRational::from_frac(1, 240);
    proof {
        assert(Rational::from_int_spec(0).lt_spec(Rational::from_frac_spec(1, 240)));
    }
    let mut w = World::new(gravity, dt, 8);

    // one spinning body: pos (0,0), vel (0,0), ω = −3, m = 1, I = 1
    let b = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RuntimeRational::from_int(-3),
        RuntimeRational::from_int(1),
        RuntimeRational::from_int(1),
        unit_square_compound(),
    );
    proof {
        lemma_closed_nonneg_one();
    }
    w.add_body(b);
    proof {
        assert(w.dt@ == Rational::from_frac_spec(1, 240));
        assert(w.series_k == 8);
        assert(w.bodies@[0].omega@ == Rational::from_int_spec(-3));
    }

    let mut i: usize = 0;
    while i < 240
        invariant
            i <= 240,
            w.wf_spec(),
            w.bodies@.len() == 1 as int,
            w.dt@ == Rational::from_frac_spec(1, 240),
            w.series_k == 8,
            w.bodies@[0].omega@ == Rational::from_int_spec(-3),
            w.angle_err@[0]@.le_spec(
                Rational::from_int_spec(i as int).mul_spec(Rational::from_frac_spec(2, 19))),
        decreases 240 - i,
    {
        proof {
            // h = −3·(1/240)/2 = −3/480 ∈ [−1/2, 0]
            let h = half_angle_model(Rational::from_int_spec(-3), Rational::from_frac_spec(1, 240));
            let f = Rational::from_int_spec(-3).mul_spec(Rational::from_frac_spec(1, 240));
            Rational::lemma_mul_denom_product_int(
                Rational::from_int_spec(-3), Rational::from_frac_spec(1, 240));
            assert(f.num == -3);
            assert(f.denom() == 240);
            assert(Rational::from_int_spec(2).num == 2);
            assert(Rational::from_int_spec(2).reciprocal_spec().num == 1);
            assert(Rational::from_int_spec(2).reciprocal_spec().denom() == 2);
            Rational::lemma_mul_denom_product_int(
                f, Rational::from_int_spec(2).reciprocal_spec());
            assert(h.num == -3);
            assert(h.denom() == 480);
            let z = Rational::from_int_spec(0);
            let mhalf = Rational::from_frac_spec(-1, 2);
            assert(z.num == 0);
            assert(z.denom() == 1);
            assert(mhalf.num == -1);
            assert(mhalf.denom() == 2);
            assert(mhalf.le_spec(h));
            assert(h.le_spec(z));
            lemma_series_neg_unit_interval(h);
            assert(w.bodies@[0].omega@ == Rational::from_int_spec(-3));
            assert(t_in_symmetric_unit_interval(
                tan_half_series_model(half_angle_model(w.bodies@[0].omega@, w.dt@))));
            assert forall|j: int|
                0 <= j < w.bodies@.len() implies t_in_symmetric_unit_interval(
                    tan_half_series_model(half_angle_model(
                        #[trigger] w.bodies@[j].omega@, w.dt@)))
            by {
            }
        }
        let r = step_free_flight(&w);
        proof {
            assert(r is Ok);
        }
        let (w2, ts) = match r {
            StepResult::Ok(w2, ts) => (w2, ts),
            StepResult::Reject(_) => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        proof {
            let ghost t0 = ts@[0]@;
            let ghost inc = ledger_increment(t0, 8 as nat);
            let ghost cap = Rational::from_frac_spec(2, 19);
            // inc = 2·|term_9(t0)| ≤ 2·(1/19) == cap (signed uniform bound)
            assert(t_in_symmetric_unit_interval(t0));
            lemma_arctan_term_abs_bound(t0, 9);
            lemma_two_mul_monotone(
                arctan_term(t0, 9).abs_spec(), Rational::from_frac_spec(1, 19));
            assert(two_x(Rational::from_frac_spec(1, 19)) == Rational::from_frac_spec(2, 19));
            assert(inc.le_spec(cap));
            // err' ≡ err + inc ≤ err + cap ≤ i·cap + cap ≡ (i+1)·cap
            Rational::lemma_le_add_both(
                w.angle_err@[0]@,
                Rational::from_int_spec(i as int).mul_spec(cap),
                inc,
                cap);
            Rational::lemma_eqv_implies_le(
                w2.angle_err@[0]@,
                w.angle_err@[0]@.add_spec(inc));
            Rational::lemma_le_transitive(
                w2.angle_err@[0]@,
                w.angle_err@[0]@.add_spec(inc),
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap));
            // (i+1)·cap ≡ i·cap + cap
            Rational::lemma_from_int_add(i as int, 1);
            Rational::lemma_mul_commutative(
                Rational::from_int_spec((i + 1) as int), cap);
            Rational::lemma_mul_distributes_over_add(
                cap, Rational::from_int_spec(i as int), Rational::from_int_spec(1));
            Rational::lemma_mul_one_identity(cap);
            Rational::lemma_mul_commutative(cap, Rational::from_int_spec(i as int));
            assert(Rational::from_int_spec((i + 1) as int).mul_spec(cap).eqv_spec(
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap)));
            Rational::lemma_eqv_symmetric(
                Rational::from_int_spec((i + 1) as int).mul_spec(cap),
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap));
            Rational::lemma_eqv_implies_le(
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap),
                Rational::from_int_spec((i + 1) as int).mul_spec(cap));
            Rational::lemma_le_transitive(
                w2.angle_err@[0]@,
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap),
                Rational::from_int_spec((i + 1) as int).mul_spec(cap));
        }
        w = w2;
        i = i + 1;
    }

    // final: angle_err[0] ≤ 240·(2/19)
    let cap_total = RuntimeRational::from_int(240).mul(&RuntimeRational::from_frac(2, 19));
    let ok = w.angle_err[0].le(&cap_total);
    proof {
        assert(w.angle_err@[0]@.le_spec(
            Rational::from_int_spec(240).mul_spec(Rational::from_frac_spec(2, 19))));
        assert(ok == true);
    }
    ok
}

/// M1 helpers: closed evaluation of the unit square's mass properties.
/// Split per-quantity (R5: closed goals in minimal contexts). All closed
/// arithmetic is made STRUCTURAL via the *_closed_int micro-lemmas (Z3
/// does not chain nested spec-fn unfolds to a struct equality on its own).

/// Closed from_int point constructor (tiny spec ctor; avoids struct
/// literals in asserts — workspace pitfall list).
pub open spec fn iv2(x: int, y: int) -> Vec2<Rational> {
    Vec2 { x: Rational::from_int_spec(x), y: Rational::from_int_spec(y) }
}

/// closed: from_int(a) · from_int(b) == from_int(a·b) (structural).
proof fn lemma_raw_mul_closed_int(a: int, b: int)
    ensures
        Rational::from_int_spec(a).mul_spec(Rational::from_int_spec(b))
            == Rational::from_int_spec(a * b),
{
    let x = Rational::from_int_spec(a);
    let y = Rational::from_int_spec(b);
    assert(x.num == a && x.den == 0);
    assert(y.num == b && y.den == 0);
    assert(x.mul_spec(y).num == a * b);
    assert(x.mul_spec(y).den == 0);
}

/// closed: from_int(a) + from_int(b) == from_int(a+b) (structural).
proof fn lemma_raw_add_closed_int(a: int, b: int)
    ensures
        Rational::from_int_spec(a).add_spec(Rational::from_int_spec(b))
            == Rational::from_int_spec(a + b),
{
    let x = Rational::from_int_spec(a);
    let y = Rational::from_int_spec(b);
    assert(x.num == a && x.den == 0 && x.denom_nat() == 1);
    assert(y.num == b && y.den == 0 && y.denom_nat() == 1);
    assert(x.add_spec(y).num == a * (y.denom_nat() as int) + b * (x.denom_nat() as int));
    assert(x.add_spec(y).den == x.den * y.den + x.den + y.den);
    assert(x.add_spec(y).num == a + b);
    assert(x.add_spec(y).den == 0);
}

/// closed: from_int(a) − from_int(b) == from_int(a−b) (structural).
proof fn lemma_raw_sub_closed_int(a: int, b: int)
    ensures
        Rational::from_int_spec(a).sub_spec(Rational::from_int_spec(b))
            == Rational::from_int_spec(a - b),
{
    let x = Rational::from_int_spec(a);
    let y = Rational::from_int_spec(b);
    assert(x.num == a && x.den == 0 && x.denom_nat() == 1);
    assert(y.num == b && y.den == 0 && y.denom_nat() == 1);
    assert(y.neg_spec().num == -b && y.neg_spec().den == 0 && y.neg_spec().denom_nat() == 1);
    assert(x.sub_spec(y).num == a * (y.neg_spec().denom_nat() as int)
        + (-b) * (x.denom_nat() as int));
    assert(x.sub_spec(y).den == x.den * y.neg_spec().den + x.den + y.neg_spec().den);
    assert((x.sub_spec(y).num == a * (y.neg_spec().denom_nat() as int)
            + (-b) * (x.denom_nat() as int)
        && x.denom_nat() == 1 && y.neg_spec().denom_nat() == 1)
        ==> x.sub_spec(y).num == a - b) by (nonlinear_arith);
    assert(x.sub_spec(y).den == 0);
}

/// closed: from_frac(1,d) · from_int(m) == from_frac(m,d) (structural).
proof fn lemma_raw_mul_frac_int(m: int, d: int)
    requires
        d > 0,
    ensures
        Rational::from_frac_spec(1, d).mul_spec(Rational::from_int_spec(m))
            == Rational::from_frac_spec(m, d),
{
    let x = Rational::from_frac_spec(1, d);
    let y = Rational::from_int_spec(m);
    assert(x.num == 1 && x.den == (d - 1) as nat);
    assert(y.num == m && y.den == 0);
    assert(x.mul_spec(y).num == m);
    assert(x.mul_spec(y).den == x.den * y.den + x.den + y.den);
    assert(x.mul_spec(y).den == (d - 1) as nat);
}

/// closed: from_int(m) · from_frac(1,d) == from_frac(m,d) (structural).
proof fn lemma_raw_mul_int_frac(m: int, d: int)
    requires
        d > 0,
    ensures
        Rational::from_int_spec(m).mul_spec(Rational::from_frac_spec(1, d))
            == Rational::from_frac_spec(m, d),
{
    let x = Rational::from_int_spec(m);
    let y = Rational::from_frac_spec(1, d);
    assert(x.num == m && x.den == 0);
    assert(y.num == 1 && y.den == (d - 1) as nat);
    assert(x.mul_spec(y).num == m);
    assert(x.mul_spec(y).den == x.den * y.den + x.den + y.den);
    assert(x.mul_spec(y).den == (d - 1) as nat);
}

/// Unit-square vertex components (shared staging).
proof fn lemma_m1_verts()
    ensures
        square_a()[0] == iv2(0, 0),
        square_a()[1] == iv2(1, 0),
        square_a()[2] == iv2(1, 1),
        square_a()[3] == iv2(0, 1),
{
}

/// closed vcross2 on from_int points (structural).
proof fn lemma_m1_vcross_closed(ax: int, ay: int, bx: int, by: int)
    ensures
        vcross2(iv2(ax, ay), iv2(bx, by)) == Rational::from_int_spec(ax * by - ay * bx),
{
    lemma_raw_mul_closed_int(ax, by);
    lemma_raw_mul_closed_int(ay, bx);
    lemma_raw_sub_closed_int(ax * by, ay * bx);
    assert(vcross2(iv2(ax, ay), iv2(bx, by)) == Rational::from_int_spec(ax).mul_spec(
        Rational::from_int_spec(by)).sub_spec(Rational::from_int_spec(ay).mul_spec(
        Rational::from_int_spec(bx))));
}

/// closed vadd on from_int points (structural).
proof fn lemma_m1_vadd_closed(ax: int, ay: int, bx: int, by: int)
    ensures
        vadd(iv2(ax, ay), iv2(bx, by)) == iv2(ax + bx, ay + by),
{
    lemma_raw_add_closed_int(ax, bx);
    lemma_raw_add_closed_int(ay, by);
    assert(vadd(iv2(ax, ay), iv2(bx, by)) == iv2(ax + bx, ay + by));
}

/// closed vdot on from_int points (structural).
proof fn lemma_m1_vdot_closed(ax: int, ay: int, bx: int, by: int)
    ensures
        vdot(iv2(ax, ay), iv2(bx, by)) == Rational::from_int_spec(ax * bx + ay * by),
{
    lemma_raw_mul_closed_int(ax, bx);
    lemma_raw_mul_closed_int(ay, by);
    lemma_raw_add_closed_int(ax * bx, ay * by);
    assert(vdot(iv2(ax, ay), iv2(bx, by)) == Rational::from_int_spec(ax).mul_spec(
        Rational::from_int_spec(bx)).add_spec(Rational::from_int_spec(ay).mul_spec(
        Rational::from_int_spec(by))));
}

/// closed vscale: from_int(c) · iv2(x,y) == iv2(c·x, c·y) (structural).
proof fn lemma_m1_vscale_closed(c: int, x: int, y: int)
    ensures
        vscale(Rational::from_int_spec(c), iv2(x, y)) == iv2(c * x, c * y),
{
    lemma_raw_mul_closed_int(c, x);
    lemma_raw_mul_closed_int(c, y);
    assert(vscale(Rational::from_int_spec(c), iv2(x, y)) == iv2(c * x, c * y));
}

/// closed inertia edge term (structural).
proof fn lemma_m1_inertia_term_closed(ax: int, ay: int, bx: int, by: int)
    ensures
        inertia_edge_term(iv2(ax, ay), iv2(bx, by)) == Rational::from_int_spec(
            (ax * by - ay * bx) * (ax * ax + ay * ay + ax * bx + ay * by + bx * bx + by * by)),
{
    lemma_m1_vcross_closed(ax, ay, bx, by);
    lemma_m1_vdot_closed(ax, ay, ax, ay);
    lemma_m1_vdot_closed(ax, ay, bx, by);
    lemma_m1_vdot_closed(bx, by, bx, by);
    lemma_raw_add_closed_int(ax * ax + ay * ay, ax * bx + ay * by);
    lemma_raw_add_closed_int(ax * ax + ay * ay + ax * bx + ay * by, bx * bx + by * by);
    lemma_raw_mul_closed_int(
        ax * by - ay * bx, ax * ax + ay * ay + ax * bx + ay * by + bx * bx + by * by);
    assert(inertia_edge_term(iv2(ax, ay), iv2(bx, by)) == vcross2(iv2(ax, ay), iv2(bx, by))
        .mul_spec(vdot(iv2(ax, ay), iv2(ax, ay)).add_spec(
            vdot(iv2(ax, ay), iv2(bx, by))).add_spec(vdot(iv2(bx, by), iv2(bx, by)))));
}

proof fn lemma_m1_area2()
    ensures
        cross_sum(square_a()) == Rational::from_int_spec(2),
{
    let a = square_a();
    lemma_m1_verts();
    lemma_m1_vcross_closed(0, 0, 1, 0);
    lemma_m1_vcross_closed(1, 0, 1, 1);
    lemma_m1_vcross_closed(1, 1, 0, 1);
    lemma_m1_vcross_closed(0, 1, 0, 0);
    assert(vcross2(a[0], a[1]) == Rational::from_int_spec(0));
    assert(vcross2(a[1], a[2]) == Rational::from_int_spec(1));
    assert(vcross2(a[2], a[3]) == Rational::from_int_spec(1));
    assert(vcross2(a[3], a[0]) == Rational::from_int_spec(0));
    assert(chain_cross_sum(a, 0) == Rational::from_int_spec(0));
    assert(chain_cross_sum(a, 1) == chain_cross_sum(a, 0).add_spec(vcross2(a[0], a[1])));
    assert(chain_cross_sum(a, 2) == chain_cross_sum(a, 1).add_spec(vcross2(a[1], a[2])));
    assert(chain_cross_sum(a, 3) == chain_cross_sum(a, 2).add_spec(vcross2(a[2], a[3])));
    lemma_raw_add_closed_int(0, 0);
    lemma_raw_add_closed_int(0, 1);
    lemma_raw_add_closed_int(1, 1);
    assert(chain_cross_sum(a, 1) == Rational::from_int_spec(0));
    assert(chain_cross_sum(a, 2) == Rational::from_int_spec(1));
    assert(chain_cross_sum(a, 3) == Rational::from_int_spec(2));
    assert(cross_sum(a) == chain_cross_sum(a, 3).add_spec(vcross2(a[3], a[0])));
    lemma_raw_add_closed_int(2, 0);
    assert(cross_sum(a) == Rational::from_int_spec(2));
}

proof fn lemma_m1_centroid()
    ensures
        centroid_spec(square_a()).x.eqv_spec(Rational::from_frac_spec(1, 2)),
        centroid_spec(square_a()).y.eqv_spec(Rational::from_frac_spec(1, 2)),
{
    let a = square_a();
    lemma_m1_area2();
    lemma_m1_verts();
    // numerator terms: (0,0), (2,1), (1,2), (0,0)
    lemma_m1_vadd_closed(0, 0, 1, 0);
    lemma_m1_vadd_closed(1, 0, 1, 1);
    lemma_m1_vadd_closed(1, 1, 0, 1);
    lemma_m1_vadd_closed(0, 1, 0, 0);
    lemma_m1_vcross_closed(0, 0, 1, 0);
    lemma_m1_vcross_closed(1, 0, 1, 1);
    lemma_m1_vcross_closed(1, 1, 0, 1);
    lemma_m1_vcross_closed(0, 1, 0, 0);
    lemma_m1_vscale_closed(0, 1, 0);
    lemma_m1_vscale_closed(1, 2, 1);
    lemma_m1_vscale_closed(1, 1, 2);
    lemma_m1_vscale_closed(0, 0, 1);
    assert(vscale(vcross2(a[0], a[1]), vadd(a[0], a[1])) == iv2(0, 0));
    assert(vscale(vcross2(a[1], a[2]), vadd(a[1], a[2])) == iv2(2, 1));
    assert(vscale(vcross2(a[2], a[3]), vadd(a[2], a[3])) == iv2(1, 2));
    assert(vscale(vcross2(a[3], a[0]), vadd(a[3], a[0])) == iv2(0, 0));
    assert(centroid_num_chain(a, 0) == vzero());
    assert(vzero() == iv2(0, 0));
    assert(centroid_num_chain(a, 1) == vadd(centroid_num_chain(a, 0),
        vscale(vcross2(a[0], a[1]), vadd(a[0], a[1]))));
    assert(centroid_num_chain(a, 2) == vadd(centroid_num_chain(a, 1),
        vscale(vcross2(a[1], a[2]), vadd(a[1], a[2]))));
    assert(centroid_num_chain(a, 3) == vadd(centroid_num_chain(a, 2),
        vscale(vcross2(a[2], a[3]), vadd(a[2], a[3]))));
    assert(centroid_num(a) == vadd(centroid_num_chain(a, 3),
        vscale(vcross2(a[3], a[0]), vadd(a[3], a[0]))));
    lemma_m1_vadd_closed(0, 0, 0, 0);
    lemma_m1_vadd_closed(0, 0, 2, 1);
    lemma_m1_vadd_closed(2, 1, 1, 2);
    lemma_m1_vadd_closed(3, 3, 0, 0);
    assert(centroid_num(a) == iv2(3, 3));
    // (3,3)/6 ≡ (1/2, 1/2)
    assert(cross_sum(a) == Rational::from_int_spec(2));
    lemma_raw_mul_closed_int(3, 2);
    assert(Rational::from_int_spec(3).mul_spec(cross_sum(a)) == Rational::from_int_spec(6));
    assert(Rational::from_int_spec(6).num == 6);
    assert(Rational::from_int_spec(6).num > 0);
    assert(Rational::from_int_spec(6).reciprocal_spec() == Rational::from_frac_spec(1, 6));
    assert(centroid_spec(a) == vscale(Rational::from_frac_spec(1, 6), centroid_num(a)));
    lemma_raw_mul_frac_int(3, 6);
    assert(centroid_spec(a).x == Rational::from_frac_spec(3, 6));
    assert(centroid_spec(a).y == Rational::from_frac_spec(3, 6));
    assert(Rational::from_frac_spec(3, 6).num == 3);
    assert(Rational::from_frac_spec(3, 6).denom() == 6);
    assert(Rational::from_frac_spec(1, 2).num == 1);
    assert(Rational::from_frac_spec(1, 2).denom() == 2);
    assert(Rational::from_frac_spec(3, 6).eqv_spec(Rational::from_frac_spec(1, 2))
        == (3 * 2 == 1 * 6));
    assert(Rational::from_frac_spec(3, 6).eqv_spec(Rational::from_frac_spec(1, 2)));
}

proof fn lemma_m1_inertia()
    ensures
        inertia0_spec(square_a()).eqv_spec(Rational::from_frac_spec(2, 3)),
{
    let a = square_a();
    lemma_m1_verts();
    lemma_m1_inertia_term_closed(0, 0, 1, 0);
    lemma_m1_inertia_term_closed(1, 0, 1, 1);
    lemma_m1_inertia_term_closed(1, 1, 0, 1);
    lemma_m1_inertia_term_closed(0, 1, 0, 0);
    assert(inertia_edge_term(a[0], a[1]) == Rational::from_int_spec(0));
    // Z3 does not eagerly evaluate the closed product in the helper's
    // postcondition — pin it.
    assert((1 * 1 - 0 * 1) * (1 * 1 + 0 * 0 + 1 * 1 + 0 * 1 + 1 * 1 + 1 * 1) == 4)
        by (nonlinear_arith);
    assert(inertia_edge_term(a[1], a[2]) == Rational::from_int_spec(4));
    assert((1 * 1 - 1 * 0) * (1 * 1 + 1 * 1 + 1 * 0 + 1 * 1 + 0 * 0 + 1 * 1) == 4)
        by (nonlinear_arith);
    assert(inertia_edge_term(a[2], a[3]) == Rational::from_int_spec(4));
    assert(inertia_edge_term(a[3], a[0]) == Rational::from_int_spec(0));
    assert(inertia_num_chain(a, 0) == Rational::from_int_spec(0));
    assert(inertia_num_chain(a, 1) == inertia_num_chain(a, 0).add_spec(
        inertia_edge_term(a[0], a[1])));
    assert(inertia_num_chain(a, 2) == inertia_num_chain(a, 1).add_spec(
        inertia_edge_term(a[1], a[2])));
    assert(inertia_num_chain(a, 3) == inertia_num_chain(a, 2).add_spec(
        inertia_edge_term(a[2], a[3])));
    assert(inertia_num(a) == inertia_num_chain(a, 3).add_spec(
        inertia_edge_term(a[3], a[0])));
    lemma_raw_add_closed_int(0, 0);
    lemma_raw_add_closed_int(0, 4);
    lemma_raw_add_closed_int(4, 4);
    lemma_raw_add_closed_int(8, 0);
    assert(inertia_num(a) == Rational::from_int_spec(8));
    assert(Rational::from_int_spec(12).num == 12);
    assert(Rational::from_int_spec(12).num > 0);
    assert(Rational::from_int_spec(12).reciprocal_spec() == Rational::from_frac_spec(1, 12));
    assert(inertia0_spec(a) == Rational::from_int_spec(8).mul_spec(
        Rational::from_frac_spec(1, 12)));
    lemma_raw_mul_int_frac(8, 12);
    assert(inertia0_spec(a) == Rational::from_frac_spec(8, 12));
    assert(Rational::from_frac_spec(8, 12).num == 8);
    assert(Rational::from_frac_spec(8, 12).denom() == 12);
    assert(Rational::from_frac_spec(2, 3).num == 2);
    assert(Rational::from_frac_spec(2, 3).denom() == 3);
    assert(Rational::from_frac_spec(8, 12).eqv_spec(Rational::from_frac_spec(2, 3))
        == (8 * 3 == 2 * 12));
    assert(Rational::from_frac_spec(8, 12).eqv_spec(Rational::from_frac_spec(2, 3)));
}

/// M1 (phys-05a): unit square mass properties, all exact — area2 == 2,
/// centroid == (1/2, 1/2), inertia about origin == 2/3.
pub fn scene_m1() -> (out: bool)
    ensures
        out == true,
{
    let mut va: Vec<SVec2> = Vec::new();
    va.push(RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(0)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(1)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(1)));
    let pa_opt = ConvexPoly::new_checked(va);
    proof {
        lemma_unit_square_convex();
        assert(pa_opt is Some);
    }
    let pa = pa_opt.unwrap();
    let a2 = poly_area2_exec(&pa);
    let c = centroid_exec(&pa);
    let i0 = inertia0_exec(&pa);
    let two = RuntimeRational::from_int(2);
    let half = RuntimeRational::from_frac(1, 2);
    let twothirds = RuntimeRational::from_frac(2, 3);
    let ok = a2.eq(&two) && c.x.eq(&half) && c.y.eq(&half) && i0.eq(&twothirds);
    proof {
        lemma_m1_area2();
        lemma_m1_centroid();
        lemma_m1_inertia();
        let a = square_a();
        assert(pa.model_verts() == square_a());
        assert(a2@ == cross_sum(a));
        assert(c.model@ == centroid_spec(a));
        assert(i0@ == inertia0_spec(a));
        assert(a2@.eqv_spec(Rational::from_int_spec(2)));
        assert(c.model@.x.eqv_spec(Rational::from_frac_spec(1, 2)));
        assert(c.model@.y.eqv_spec(Rational::from_frac_spec(1, 2)));
        assert(i0@.eqv_spec(Rational::from_frac_spec(2, 3)));
        assert(two@ == Rational::from_int_spec(2));
        assert(half@ == Rational::from_frac_spec(1, 2));
        assert(twothirds@ == Rational::from_frac_spec(2, 3));
        assert(ok == true);
    }
    ok
}

/// S3: SAT vs known answers over a family of square pairs (SPEC §8).
///
/// A = unit square at origin; B(k) = unit square at (k/4, 0), k ∈ −5..=5.
/// Covers separated (|k| = 5), touching (|k| = 4, edge-edge and
/// vertex-vertex at the corners), overlapping (−4 < k < 4), and
/// parallel-edge cases throughout. The witness validity of every
/// Separated verdict is in sat_classify's ensures; the scene proves the
/// classification matches the known answer in every case.

/// The unit square, ccw.
pub open spec fn square_a() -> Seq<Vec2<Rational>> {
    seq![
        Vec2 { x: Rational::from_int_spec(0), y: Rational::from_int_spec(0) },
        Vec2 { x: Rational::from_int_spec(1), y: Rational::from_int_spec(0) },
        Vec2 { x: Rational::from_int_spec(1), y: Rational::from_int_spec(1) },
        Vec2 { x: Rational::from_int_spec(0), y: Rational::from_int_spec(1) },
    ]
}

/// The translated unit square at (k/4, 0), ccw.
pub open spec fn square_b(k: int) -> Seq<Vec2<Rational>> {
    let x0 = Rational::from_frac_spec(k, 4);
    let x1 = Rational::from_frac_spec(k, 4).add_spec(Rational::from_int_spec(1));
    seq![
        Vec2 { x: x0, y: Rational::from_int_spec(0) },
        Vec2 { x: x1, y: Rational::from_int_spec(0) },
        Vec2 { x: x1, y: Rational::from_int_spec(1) },
        Vec2 { x: x0, y: Rational::from_int_spec(1) },
    ]
}

/// For k > 4: A's right edge (edge 1) strictly separates B(k).
proof fn lemma_s3_separated_right(k: int)
    requires
        k > 4,
    ensures
        Rational::from_int_spec(0).lt_spec(crate::shape::min_sep(
            crate::shape::edge_normal(square_a()[1], square_a()[2]),
            square_a()[1], square_b(k), 0)),
{
    use crate::shape::{axis_sep, edge_normal, min_sep};
    let n = edge_normal(square_a()[1], square_a()[2]);
    let p = square_a()[1];
    let b = square_b(k);
    let f = Rational::from_frac_spec(k, 4);
    let one = Rational::from_int_spec(1);
    // every B vertex has axis_sep == q.x − 1 > 0
    assert forall|j: int| 0 <= j < b.len() implies Rational::from_int_spec(0).lt_spec(
        #[trigger] axis_sep(n, p, b[j]))
    by {
        let q = b[j];
        let s = axis_sep(n, p, q);
        let a1 = square_a()[1];
        let a2 = square_a()[2];
        assert(a1 == (Vec2 { x: one, y: Rational::from_int_spec(0) }));
        assert(a2 == (Vec2 { x: one, y: one }));
        assert(n.x == a2.y.sub_spec(a1.y));
        assert(n.y == a1.x.sub_spec(a2.x));
        assert((a2.y.sub_spec(a1.y).num == a2.y.num * a1.y.denom() + (-a1.y.num) * a2.y.denom()
            && a2.y.num == 1 && a2.y.denom() == 1 && a1.y.num == 0 && a1.y.denom() == 1)
            ==> a2.y.sub_spec(a1.y).num == 1) by (nonlinear_arith);
        assert((a2.y.sub_spec(a1.y).den == a2.y.den * a1.y.den + a2.y.den + a1.y.den
            && a2.y.den == 0 && a1.y.den == 0)
            ==> a2.y.sub_spec(a1.y).den == 0) by (nonlinear_arith);
        assert((a1.x.sub_spec(a2.x).num == a1.x.num * a2.x.denom() + (-a2.x.num) * a1.x.denom()
            && a1.x.num == 1 && a1.x.denom() == 1 && a2.x.num == 1 && a2.x.denom() == 1)
            ==> a1.x.sub_spec(a2.x).num == 0) by (nonlinear_arith);
        assert((a1.x.sub_spec(a2.x).den == a1.x.den * a2.x.den + a1.x.den + a2.x.den
            && a1.x.den == 0 && a2.x.den == 0)
            ==> a1.x.sub_spec(a2.x).den == 0) by (nonlinear_arith);
        assert(one.num == 1);
        assert(one.den == 0);
        assert(Rational::from_int_spec(0).num == 0);
        assert(Rational::from_int_spec(0).den == 0);
        assert(a2.y == one);
        assert(a1.y == Rational::from_int_spec(0));
        assert(a1.x == one);
        assert(a2.x == one);
        assert(a2.y.num == 1 && a2.y.denom() == 1 && a2.y.den == 0);
        assert(a1.y.num == 0 && a1.y.denom() == 1 && a1.y.den == 0);
        assert(a1.x.num == 1 && a1.x.denom() == 1 && a1.x.den == 0);
        assert(a2.x.num == 1 && a2.x.denom() == 1 && a2.x.den == 0);
        assert(n.x.num == 1);
        assert(n.x.den == 0);
        assert(n.y.num == 0);
        assert(n.y.den == 0);
        assert(n.x == one);
        assert(n.y == Rational::from_int_spec(0));
        assert(p == a1);
        assert(p.x == one);
        assert(p.y == Rational::from_int_spec(0));
        if j == 0 {
            assert(q == b[0]);
            assert(q.x == f);
        } else if j == 1 {
            assert(q == b[1]);
            assert(q.x == f.add_spec(one));
        } else if j == 2 {
            assert(q == b[2]);
            assert(q.x == f.add_spec(one));
        } else {
            assert(j == 3);
            assert(q == b[3]);
            assert(q.x == f);
        }
        assert(q.x == f || q.x == f.add_spec(one));
        // axis_sep == q.x − 1
        assert(n.x.eqv_spec(one));
        assert(n.y.eqv_spec(Rational::from_int_spec(0)));
        lemma_s3_axis_right_eval(n, p, q, s);
        // (q.x − 1).num ≥ 1
        lemma_s3_k_over_4_minus_1_pos(k, q.x);
        // 0 < s
        lemma_s3_zero_lt_eval(q.x.sub_spec(one), s);
    }
    crate::proofs::shape::lemma_min_sep_attained(n, p, b, 0);
    // min attained at some j*, and every value is > 0 ⟹ min > 0
    let jstar = choose|j: int| 0 <= j < b.len() && min_sep(n, p, b, 0) == axis_sep(n, p, b[j]);
    assert(min_sep(n, p, b, 0) == axis_sep(n, p, b[jstar]));
}

/// k > 4 and q.x ∈ {k/4, k/4+1} ⟹ (q.x − 1).num ≥ 1.
pub proof fn lemma_s3_k_over_4_minus_1_pos(k: int, qx: Rational)
    requires
        k > 4,
        qx == Rational::from_frac_spec(k, 4)
            || qx == Rational::from_frac_spec(k, 4).add_spec(Rational::from_int_spec(1)),
    ensures
        qx.sub_spec(Rational::from_int_spec(1)).num >= 1,
{
    let one = Rational::from_int_spec(1);
    let f = Rational::from_frac_spec(k, 4);
    let d = qx.sub_spec(one);
    if qx == f {
        assert(f.num == k);
        assert(f.denom() == 4);
        assert(one.num == 1);
        assert(one.denom() == 1);
        assert(d.num == f.num * one.denom() + (-one.num) * f.denom());
        assert((d.num == f.num * one.denom() + (-one.num) * f.denom()
            && f.num == k && f.denom() == 4 && one.num == 1 && one.denom() == 1)
            ==> d.num == k - 4) by (nonlinear_arith);
        assert(d.num == k - 4);
        assert(k - 4 >= 1);
    } else {
        let s = f.add_spec(one);
        assert(qx == s);
        assert(f.num == k);
        assert(f.denom() == 4);
        assert(one.num == 1);
        assert(one.denom() == 1);
        assert(s.num == f.num * one.denom() + one.num * f.denom());
        assert((s.num == f.num * one.denom() + one.num * f.denom()
            && f.num == k && f.denom() == 4 && one.num == 1 && one.denom() == 1)
            ==> s.num == k + 4) by (nonlinear_arith);
        assert(s.num == k + 4);
        Rational::lemma_add_denom_product_int(f, one);
        assert(s.denom() == f.denom() * one.denom());
        assert(s.denom() == 4);
        assert(d.num == s.num * one.denom() + (-one.num) * s.denom());
        assert((d.num == s.num * one.denom() + (-one.num) * s.denom()
            && s.num == k + 4 && s.denom() == 4 && one.num == 1 && one.denom() == 1)
            ==> d.num == (k + 4) - 4) by (nonlinear_arith);
        assert(d.num == (k + 4) - 4);
        assert((k + 4) - 4 >= 1);
    }
}

/// s ≡ v and v.num ≥ 1 ⟹ 0 < s.
pub proof fn lemma_s3_zero_lt_eval(v: Rational, s: Rational)
    requires
        s.eqv_spec(v),
        v.num >= 1,
    ensures
        Rational::from_int_spec(0).lt_spec(s),
{
    let z = Rational::from_int_spec(0);
    Rational::lemma_denom_positive(v);
    Rational::lemma_denom_positive(s);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.lt_spec(s) == (z.num * s.denom() < s.num * z.denom()));
    assert(s.eqv_spec(v) == (s.num * v.denom() == v.num * s.denom()));
    assert((v.num >= 1 && v.denom() >= 1 && s.denom() >= 1
        && s.num * v.denom() == v.num * s.denom())
        ==> s.num >= 1) by (nonlinear_arith);
}

/// axis_sep with n ≡ (1, 0): evaluated form.
pub proof fn lemma_s3_axis_right_eval(
    n: Vec2<Rational>, p: Vec2<Rational>, q: Vec2<Rational>, s: Rational,
)
    requires
        n.x.eqv_spec(Rational::from_int_spec(1)),
        n.y.eqv_spec(Rational::from_int_spec(0)),
        s == crate::shape::axis_sep(n, p, q),
    ensures
        s.eqv_spec(q.x.sub_spec(p.x)),
{
    use crate::proofs::rational_raw::lemma_raw_add_zero_right;
    let t1 = n.x.mul_spec(q.x.sub_spec(p.x));
    let t2 = n.y.mul_spec(q.y.sub_spec(p.y));
    Rational::lemma_eqv_reflexive(q.x.sub_spec(p.x));
    Rational::lemma_eqv_reflexive(q.y.sub_spec(p.y));
    Rational::lemma_eqv_mul_congruence(n.x, Rational::from_int_spec(1), q.x.sub_spec(p.x), q.x.sub_spec(p.x));
    Rational::lemma_eqv_mul_congruence(n.y, Rational::from_int_spec(0), q.y.sub_spec(p.y), q.y.sub_spec(p.y));
        // t1 ≡ 1·dx ≡ dx; t2 ≡ 0·dy ≡ 0; s ≡ dx + 0 ≡ dx
    Rational::lemma_mul_commutative(Rational::from_int_spec(1), q.x.sub_spec(p.x));
    Rational::lemma_mul_one_identity(q.x.sub_spec(p.x));
    Rational::lemma_eqv_transitive(
        t1,
        Rational::from_int_spec(1).mul_spec(q.x.sub_spec(p.x)),
        q.x.sub_spec(p.x));
    Rational::lemma_mul_zero(q.y.sub_spec(p.y));
    Rational::lemma_eqv_transitive(
        t2,
        Rational::from_int_spec(0).mul_spec(q.y.sub_spec(p.y)),
        Rational::from_int_spec(0));
    Rational::lemma_eqv_add_congruence(
        t1, q.x.sub_spec(p.x), t2, Rational::from_int_spec(0));
    lemma_raw_add_zero_right(q.x.sub_spec(p.x));
    Rational::lemma_eqv_transitive(
        s,
        q.x.sub_spec(p.x).add_spec(Rational::from_int_spec(0)),
        q.x.sub_spec(p.x));
}

/// axis_sep with n ≡ (−1, 0): evaluated form.
pub proof fn lemma_s3_axis_left_eval(
    n: Vec2<Rational>, p: Vec2<Rational>, q: Vec2<Rational>, s: Rational,
)
    requires
        n.x.eqv_spec(Rational::from_int_spec(-1)),
        n.y.eqv_spec(Rational::from_int_spec(0)),
        s == crate::shape::axis_sep(n, p, q),
    ensures
        s.eqv_spec(p.x.sub_spec(q.x)),
{
    use crate::proofs::rational_raw::lemma_raw_add_zero_right;
    let t1 = n.x.mul_spec(q.x.sub_spec(p.x));
    let t2 = n.y.mul_spec(q.y.sub_spec(p.y));
    Rational::lemma_eqv_reflexive(q.x.sub_spec(p.x));
    Rational::lemma_eqv_reflexive(q.y.sub_spec(p.y));
    Rational::lemma_eqv_mul_congruence(n.x, Rational::from_int_spec(-1), q.x.sub_spec(p.x), q.x.sub_spec(p.x));
    Rational::lemma_eqv_mul_congruence(n.y, Rational::from_int_spec(0), q.y.sub_spec(p.y), q.y.sub_spec(p.y));
        // t1 ≡ (−1)·dx ≡ −dx ≡ pc − qx; t2 ≡ 0
    assert(Rational::from_int_spec(-1).mul_spec(q.x.sub_spec(p.x)).num
        == -1 * q.x.sub_spec(p.x).num);
    assert(Rational::from_int_spec(-1).mul_spec(q.x.sub_spec(p.x)).den
        == 0 * q.x.sub_spec(p.x).den + 0 + q.x.sub_spec(p.x).den);
    assert((Rational::from_int_spec(-1).mul_spec(q.x.sub_spec(p.x)).num
            == -1 * q.x.sub_spec(p.x).num
        && Rational::from_int_spec(-1).mul_spec(q.x.sub_spec(p.x)).den
            == 0 * q.x.sub_spec(p.x).den + 0 + q.x.sub_spec(p.x).den)
        ==> Rational::from_int_spec(-1).mul_spec(q.x.sub_spec(p.x))
            == q.x.sub_spec(p.x).neg_spec()) by (nonlinear_arith);
    assert(Rational::from_int_spec(-1).mul_spec(q.x.sub_spec(p.x))
        == q.x.sub_spec(p.x).neg_spec());
    assert(q.x.sub_spec(p.x).neg_spec().num == -q.x.sub_spec(p.x).num);
    assert(q.x.sub_spec(p.x).neg_spec().den == q.x.sub_spec(p.x).den);
    assert(q.x.sub_spec(p.x).num == q.x.num * (p.x.denom_nat() as int)
        + (-p.x.num) * (q.x.denom_nat() as int));
    assert(p.x.sub_spec(q.x).num == p.x.num * (q.x.denom_nat() as int)
        + (-q.x.num) * (p.x.denom_nat() as int));
    assert(q.x.sub_spec(p.x).den == q.x.den * p.x.den + q.x.den + p.x.den);
    assert(p.x.sub_spec(q.x).den == p.x.den * q.x.den + p.x.den + q.x.den);
    assert((q.x.sub_spec(p.x).neg_spec().num == -q.x.sub_spec(p.x).num
        && q.x.sub_spec(p.x).num == q.x.num * (p.x.denom_nat() as int)
            + (-p.x.num) * (q.x.denom_nat() as int)
        && p.x.sub_spec(q.x).num == p.x.num * (q.x.denom_nat() as int)
            + (-q.x.num) * (p.x.denom_nat() as int)
        && q.x.sub_spec(p.x).neg_spec().den == q.x.sub_spec(p.x).den
        && q.x.sub_spec(p.x).den == q.x.den * p.x.den + q.x.den + p.x.den
        && p.x.sub_spec(q.x).den == p.x.den * q.x.den + p.x.den + q.x.den)
        ==> q.x.sub_spec(p.x).neg_spec().num == p.x.sub_spec(q.x).num
            && q.x.sub_spec(p.x).neg_spec().den == p.x.sub_spec(q.x).den)
        by (nonlinear_arith);
    assert(q.x.sub_spec(p.x).neg_spec() == p.x.sub_spec(q.x));
    Rational::lemma_eqv_transitive(t1, q.x.sub_spec(p.x).neg_spec(), p.x.sub_spec(q.x));
    Rational::lemma_mul_zero(q.y.sub_spec(p.y));
    Rational::lemma_eqv_transitive(
        t2,
        Rational::from_int_spec(0).mul_spec(q.y.sub_spec(p.y)),
        Rational::from_int_spec(0));
    Rational::lemma_eqv_add_congruence(
        t1, p.x.sub_spec(q.x), t2, Rational::from_int_spec(0));
    lemma_raw_add_zero_right(p.x.sub_spec(q.x));
    Rational::lemma_eqv_transitive(
        s,
        p.x.sub_spec(q.x).add_spec(Rational::from_int_spec(0)),
        p.x.sub_spec(q.x));
}

/// axis_sep with n ≡ (0, 1): evaluated form.
pub proof fn lemma_s3_axis_top_eval(
    n: Vec2<Rational>, p: Vec2<Rational>, q: Vec2<Rational>, s: Rational,
)
    requires
        n.x.eqv_spec(Rational::from_int_spec(0)),
        n.y.eqv_spec(Rational::from_int_spec(1)),
        s == crate::shape::axis_sep(n, p, q),
    ensures
        s.eqv_spec(q.y.sub_spec(p.y)),
{
    use crate::proofs::rational_raw::lemma_raw_add_zero_right;
    let t1 = n.x.mul_spec(q.x.sub_spec(p.x));
    let t2 = n.y.mul_spec(q.y.sub_spec(p.y));
    Rational::lemma_eqv_reflexive(q.x.sub_spec(p.x));
    Rational::lemma_eqv_reflexive(q.y.sub_spec(p.y));
    Rational::lemma_eqv_mul_congruence(n.x, Rational::from_int_spec(0), q.x.sub_spec(p.x), q.x.sub_spec(p.x));
    Rational::lemma_eqv_mul_congruence(n.y, Rational::from_int_spec(1), q.y.sub_spec(p.y), q.y.sub_spec(p.y));
        // t1 ≡ 0; t2 ≡ 1·dy ≡ dy; s ≡ 0 + dy ≡ dy
    Rational::lemma_mul_zero(q.x.sub_spec(p.x));
    Rational::lemma_eqv_transitive(
        t1,
        Rational::from_int_spec(0).mul_spec(q.x.sub_spec(p.x)),
        Rational::from_int_spec(0));
    Rational::lemma_mul_commutative(Rational::from_int_spec(1), q.y.sub_spec(p.y));
    Rational::lemma_mul_one_identity(q.y.sub_spec(p.y));
    Rational::lemma_eqv_transitive(
        t2,
        Rational::from_int_spec(1).mul_spec(q.y.sub_spec(p.y)),
        q.y.sub_spec(p.y));
    Rational::lemma_eqv_add_congruence(
        t1, Rational::from_int_spec(0), t2, q.y.sub_spec(p.y));
    // 0 + dy ≡ dy (add zero LEFT)
    let dz = Rational::from_int_spec(0).add_spec(q.y.sub_spec(p.y));
    Rational::lemma_add_denom_product_int(Rational::from_int_spec(0), q.y.sub_spec(p.y));
    Rational::lemma_denom_positive(q.y.sub_spec(p.y));
    assert(dz.num == 0 * q.y.sub_spec(p.y).denom()
        + q.y.sub_spec(p.y).num * Rational::from_int_spec(0).denom());
    assert(dz.denom() == Rational::from_int_spec(0).denom() * q.y.sub_spec(p.y).denom());
    assert(Rational::from_int_spec(0).num == 0);
    assert(Rational::from_int_spec(0).denom() == 1);
    assert((dz.num == 0 * q.y.sub_spec(p.y).denom()
            + q.y.sub_spec(p.y).num * Rational::from_int_spec(0).denom()
        && dz.denom() == Rational::from_int_spec(0).denom() * q.y.sub_spec(p.y).denom()
        && Rational::from_int_spec(0).num == 0
        && Rational::from_int_spec(0).denom() == 1
        && q.y.sub_spec(p.y).denom() >= 1)
        ==> dz.num * q.y.sub_spec(p.y).denom() == q.y.sub_spec(p.y).num * dz.denom())
        by (nonlinear_arith);
    assert(dz.eqv_spec(q.y.sub_spec(p.y)));
    Rational::lemma_eqv_transitive(s, dz, q.y.sub_spec(p.y));
}

/// axis_sep with n ≡ (0, −1): evaluated form.
pub proof fn lemma_s3_axis_bottom_eval(
    n: Vec2<Rational>, p: Vec2<Rational>, q: Vec2<Rational>, s: Rational,
)
    requires
        n.x.eqv_spec(Rational::from_int_spec(0)),
        n.y.eqv_spec(Rational::from_int_spec(-1)),
        s == crate::shape::axis_sep(n, p, q),
    ensures
        s.eqv_spec(p.y.sub_spec(q.y)),
{
    use crate::proofs::rational_raw::lemma_raw_add_zero_right;
    let t1 = n.x.mul_spec(q.x.sub_spec(p.x));
    let t2 = n.y.mul_spec(q.y.sub_spec(p.y));
    Rational::lemma_eqv_reflexive(q.x.sub_spec(p.x));
    Rational::lemma_eqv_reflexive(q.y.sub_spec(p.y));
    Rational::lemma_eqv_mul_congruence(n.x, Rational::from_int_spec(0), q.x.sub_spec(p.x), q.x.sub_spec(p.x));
    Rational::lemma_eqv_mul_congruence(n.y, Rational::from_int_spec(-1), q.y.sub_spec(p.y), q.y.sub_spec(p.y));
        // t1 ≡ 0; t2 ≡ (−1)·dy ≡ −dy ≡ py − qy; s ≡ 0 + (py − qy) ≡ py − qy
    Rational::lemma_mul_zero(q.x.sub_spec(p.x));
    Rational::lemma_eqv_transitive(
        t1,
        Rational::from_int_spec(0).mul_spec(q.x.sub_spec(p.x)),
        Rational::from_int_spec(0));
    assert(Rational::from_int_spec(-1).mul_spec(q.y.sub_spec(p.y)).num
        == -1 * q.y.sub_spec(p.y).num);
    assert(Rational::from_int_spec(-1).mul_spec(q.y.sub_spec(p.y)).den
        == 0 * q.y.sub_spec(p.y).den + 0 + q.y.sub_spec(p.y).den);
    assert((Rational::from_int_spec(-1).mul_spec(q.y.sub_spec(p.y)).num
            == -1 * q.y.sub_spec(p.y).num
        && Rational::from_int_spec(-1).mul_spec(q.y.sub_spec(p.y)).den
            == 0 * q.y.sub_spec(p.y).den + 0 + q.y.sub_spec(p.y).den)
        ==> Rational::from_int_spec(-1).mul_spec(q.y.sub_spec(p.y))
            == q.y.sub_spec(p.y).neg_spec()) by (nonlinear_arith);
    assert(Rational::from_int_spec(-1).mul_spec(q.y.sub_spec(p.y))
        == q.y.sub_spec(p.y).neg_spec());
    assert(q.y.sub_spec(p.y).neg_spec().num == -q.y.sub_spec(p.y).num);
    assert(q.y.sub_spec(p.y).neg_spec().den == q.y.sub_spec(p.y).den);
    assert(q.y.sub_spec(p.y).num == q.y.num * (p.y.denom_nat() as int)
        + (-p.y.num) * (q.y.denom_nat() as int));
    assert(p.y.sub_spec(q.y).num == p.y.num * (q.y.denom_nat() as int)
        + (-q.y.num) * (p.y.denom_nat() as int));
    assert(q.y.sub_spec(p.y).den == q.y.den * p.y.den + q.y.den + p.y.den);
    assert(p.y.sub_spec(q.y).den == p.y.den * q.y.den + p.y.den + q.y.den);
    assert((q.y.sub_spec(p.y).neg_spec().num == -q.y.sub_spec(p.y).num
        && q.y.sub_spec(p.y).num == q.y.num * (p.y.denom_nat() as int)
            + (-p.y.num) * (q.y.denom_nat() as int)
        && p.y.sub_spec(q.y).num == p.y.num * (q.y.denom_nat() as int)
            + (-q.y.num) * (p.y.denom_nat() as int)
        && q.y.sub_spec(p.y).neg_spec().den == q.y.sub_spec(p.y).den
        && q.y.sub_spec(p.y).den == q.y.den * p.y.den + q.y.den + p.y.den
        && p.y.sub_spec(q.y).den == p.y.den * q.y.den + p.y.den + q.y.den)
        ==> q.y.sub_spec(p.y).neg_spec().num == p.y.sub_spec(q.y).num
            && q.y.sub_spec(p.y).neg_spec().den == p.y.sub_spec(q.y).den)
        by (nonlinear_arith);
    assert(q.y.sub_spec(p.y).neg_spec() == p.y.sub_spec(q.y));
    Rational::lemma_eqv_transitive(t2, q.y.sub_spec(p.y).neg_spec(), p.y.sub_spec(q.y));
    Rational::lemma_eqv_add_congruence(
        t1, Rational::from_int_spec(0), t2, p.y.sub_spec(q.y));
    let dz = Rational::from_int_spec(0).add_spec(p.y.sub_spec(q.y));
    Rational::lemma_add_denom_product_int(Rational::from_int_spec(0), p.y.sub_spec(q.y));
    Rational::lemma_denom_positive(p.y.sub_spec(q.y));
    assert(dz.num == 0 * p.y.sub_spec(q.y).denom()
        + p.y.sub_spec(q.y).num * Rational::from_int_spec(0).denom());
    assert(dz.denom() == Rational::from_int_spec(0).denom() * p.y.sub_spec(q.y).denom());
    assert(Rational::from_int_spec(0).num == 0);
    assert(Rational::from_int_spec(0).denom() == 1);
    assert((dz.num == 0 * p.y.sub_spec(q.y).denom()
            + p.y.sub_spec(q.y).num * Rational::from_int_spec(0).denom()
        && dz.denom() == Rational::from_int_spec(0).denom() * p.y.sub_spec(q.y).denom()
        && Rational::from_int_spec(0).num == 0
        && Rational::from_int_spec(0).denom() == 1
        && p.y.sub_spec(q.y).denom() >= 1)
        ==> dz.num * p.y.sub_spec(q.y).denom() == p.y.sub_spec(q.y).num * dz.denom())
        by (nonlinear_arith);
    assert(dz.eqv_spec(p.y.sub_spec(q.y)));
    Rational::lemma_eqv_transitive(s, dz, p.y.sub_spec(q.y));
}

/// orient on from_int components evaluates STRUCTURALLY to a from_int.
pub proof fn lemma_orient_closed(ax: int, ay: int, bx: int, by: int, cx: int, cy: int)
    ensures
        orient(
            (Vec2 {
                x: Rational::from_int_spec(ax),
                y: Rational::from_int_spec(ay),
            }),
            (Vec2 {
                x: Rational::from_int_spec(bx),
                y: Rational::from_int_spec(by),
            }),
            (Vec2 {
                x: Rational::from_int_spec(cx),
                y: Rational::from_int_spec(cy),
            })) == Rational::from_int_spec((bx - ax) * (cy - ay) - (by - ay) * (cx - ax)),
{
    let a = Vec2 { x: Rational::from_int_spec(ax), y: Rational::from_int_spec(ay) };
    let b = Vec2 { x: Rational::from_int_spec(bx), y: Rational::from_int_spec(by) };
    let c = Vec2 { x: Rational::from_int_spec(cx), y: Rational::from_int_spec(cy) };
    let o = orient(a, b, c);
    // sub nodes: exact body forms, then closed combination
    assert(b.x.sub_spec(a.x).num
        == b.x.num * (a.x.denom_nat() as int) + (-a.x.num) * (b.x.denom_nat() as int));
    assert(b.x.sub_spec(a.x).den == b.x.den * a.x.den + b.x.den + a.x.den);
    assert(b.y.sub_spec(a.y).num
        == b.y.num * (a.y.denom_nat() as int) + (-a.y.num) * (b.y.denom_nat() as int));
    assert(b.y.sub_spec(a.y).den == b.y.den * a.y.den + b.y.den + a.y.den);
    assert(c.x.sub_spec(a.x).num
        == c.x.num * (a.x.denom_nat() as int) + (-a.x.num) * (c.x.denom_nat() as int));
    assert(c.x.sub_spec(a.x).den == c.x.den * a.x.den + c.x.den + a.x.den);
    assert(c.y.sub_spec(a.y).num
        == c.y.num * (a.y.denom_nat() as int) + (-a.y.num) * (c.y.denom_nat() as int));
    assert(c.y.sub_spec(a.y).den == c.y.den * a.y.den + c.y.den + a.y.den);
    assert((b.x.num == bx && b.x.den == 0 && a.x.num == ax && a.x.den == 0
        && b.x.sub_spec(a.x).num
            == b.x.num * (a.x.denom_nat() as int) + (-a.x.num) * (b.x.denom_nat() as int)
        && b.x.sub_spec(a.x).den == b.x.den * a.x.den + b.x.den + a.x.den)
        ==> b.x.sub_spec(a.x).num == bx - ax && b.x.sub_spec(a.x).den == 0)
        by (nonlinear_arith);
    assert(b.x.sub_spec(a.x).num == bx - ax && b.x.sub_spec(a.x).den == 0);
    assert((b.y.num == by && b.y.den == 0 && a.y.num == ay && a.y.den == 0
        && b.y.sub_spec(a.y).num
            == b.y.num * (a.y.denom_nat() as int) + (-a.y.num) * (b.y.denom_nat() as int)
        && b.y.sub_spec(a.y).den == b.y.den * a.y.den + b.y.den + a.y.den)
        ==> b.y.sub_spec(a.y).num == by - ay && b.y.sub_spec(a.y).den == 0)
        by (nonlinear_arith);
    assert(b.y.sub_spec(a.y).num == by - ay && b.y.sub_spec(a.y).den == 0);
    assert((c.x.num == cx && c.x.den == 0 && a.x.num == ax && a.x.den == 0
        && c.x.sub_spec(a.x).num
            == c.x.num * (a.x.denom_nat() as int) + (-a.x.num) * (c.x.denom_nat() as int)
        && c.x.sub_spec(a.x).den == c.x.den * a.x.den + c.x.den + a.x.den)
        ==> c.x.sub_spec(a.x).num == cx - ax && c.x.sub_spec(a.x).den == 0)
        by (nonlinear_arith);
    assert(c.x.sub_spec(a.x).num == cx - ax && c.x.sub_spec(a.x).den == 0);
    assert((c.y.num == cy && c.y.den == 0 && a.y.num == ay && a.y.den == 0
        && c.y.sub_spec(a.y).num
            == c.y.num * (a.y.denom_nat() as int) + (-a.y.num) * (c.y.denom_nat() as int)
        && c.y.sub_spec(a.y).den == c.y.den * a.y.den + c.y.den + a.y.den)
        ==> c.y.sub_spec(a.y).num == cy - ay && c.y.sub_spec(a.y).den == 0)
        by (nonlinear_arith);
    assert(c.y.sub_spec(a.y).num == cy - ay && c.y.sub_spec(a.y).den == 0);
    // mul nodes
    let t1 = b.x.sub_spec(a.x).mul_spec(c.y.sub_spec(a.y));
    let t2 = b.y.sub_spec(a.y).mul_spec(c.x.sub_spec(a.x));
    assert(t1.num == b.x.sub_spec(a.x).num * c.y.sub_spec(a.y).num);
    assert(t1.den == b.x.sub_spec(a.x).den * c.y.sub_spec(a.y).den
        + b.x.sub_spec(a.x).den + c.y.sub_spec(a.y).den);
    assert(t2.num == b.y.sub_spec(a.y).num * c.x.sub_spec(a.x).num);
    assert(t2.den == b.y.sub_spec(a.y).den * c.x.sub_spec(a.x).den
        + b.y.sub_spec(a.y).den + c.x.sub_spec(a.x).den);
    assert((t1.num == b.x.sub_spec(a.x).num * c.y.sub_spec(a.y).num
        && t1.den == b.x.sub_spec(a.x).den * c.y.sub_spec(a.y).den
            + b.x.sub_spec(a.x).den + c.y.sub_spec(a.y).den
        && b.x.sub_spec(a.x).num == bx - ax && b.x.sub_spec(a.x).den == 0
        && c.y.sub_spec(a.y).num == cy - ay && c.y.sub_spec(a.y).den == 0)
        ==> t1.num == (bx - ax) * (cy - ay) && t1.den == 0) by (nonlinear_arith);
    assert(t1.num == (bx - ax) * (cy - ay) && t1.den == 0);
    assert((t2.num == b.y.sub_spec(a.y).num * c.x.sub_spec(a.x).num
        && t2.den == b.y.sub_spec(a.y).den * c.x.sub_spec(a.x).den
            + b.y.sub_spec(a.y).den + c.x.sub_spec(a.x).den
        && b.y.sub_spec(a.y).num == by - ay && b.y.sub_spec(a.y).den == 0
        && c.x.sub_spec(a.x).num == cx - ax && c.x.sub_spec(a.x).den == 0)
        ==> t2.num == (by - ay) * (cx - ax) && t2.den == 0) by (nonlinear_arith);
    assert(t2.num == (by - ay) * (cx - ax) && t2.den == 0);
    // the final sub
    assert(o.num == t1.num * (t2.denom_nat() as int) + (-t2.num) * (t1.denom_nat() as int));
    assert(o.den == t1.den * t2.den + t1.den + t2.den);
    assert((o.num == t1.num * (t2.denom_nat() as int) + (-t2.num) * (t1.denom_nat() as int)
        && o.den == t1.den * t2.den + t1.den + t2.den
        && t1.num == (bx - ax) * (cy - ay) && t1.den == 0
        && t2.num == (by - ay) * (cx - ax) && t2.den == 0)
        ==> o.num == (bx - ax) * (cy - ay) - (by - ay) * (cx - ax) && o.den == 0)
        by (nonlinear_arith);
    assert(o.num == (bx - ax) * (cy - ay) - (by - ay) * (cx - ax));
    assert(o.den == 0);
    assert(o == Rational::from_int_spec((bx - ax) * (cy - ay) - (by - ay) * (cx - ax)));
}

/// The unit square is convex (all 12 non-endpoint orient checks are +1).
pub proof fn lemma_unit_square_convex()
    ensures
        convex_poly_inv(square_a()),
{
    let a = square_a();
    assert(a.len() == 4);
    assert(a.len() >= 3);
    assert forall|i: int, j: int|
        (0 <= i < 4 && 0 <= j < 4 && j != i && j != (i + 1) % (4 as int))
        implies Rational::from_int_spec(0).lt_spec(
            #[trigger] orient(a[i], a[(i + 1) % (4 as int)], a[j]))
    by {
        assert((i == 0 && j == 2) || (i == 0 && j == 3)
            || (i == 1 && j == 0) || (i == 1 && j == 3)
            || (i == 2 && j == 0) || (i == 2 && j == 1)
            || (i == 3 && j == 1) || (i == 3 && j == 2)
            || j == i || j == (i + 1) % (4 as int));
        // every non-endpoint triple of the unit square has orient == 1
        if i == 0 && j == 2 {
            lemma_orient_closed(0, 0, 1, 0, 1, 1);
        } else if i == 0 && j == 3 {
            lemma_orient_closed(0, 0, 1, 0, 0, 1);
        } else if i == 1 && j == 0 {
            lemma_orient_closed(1, 0, 1, 1, 0, 0);
        } else if i == 1 && j == 3 {
            lemma_orient_closed(1, 0, 1, 1, 0, 1);
        } else if i == 2 && j == 0 {
            lemma_orient_closed(1, 1, 0, 1, 0, 0);
        } else if i == 2 && j == 1 {
            lemma_orient_closed(1, 1, 0, 1, 1, 0);
        } else if i == 3 && j == 1 {
            lemma_orient_closed(0, 1, 0, 0, 1, 0);
        } else if i == 3 && j == 2 {
            lemma_orient_closed(0, 1, 0, 0, 1, 1);
        } else {
            // remaining (i, j) are endpoint pairs — impossible here
            assert(j == i || j == (i + 1) % (4 as int));
        }
        assert(a[0] == (Vec2 {
            x: Rational::from_int_spec(0),
            y: Rational::from_int_spec(0),
        }));
        assert(a[1] == (Vec2 {
            x: Rational::from_int_spec(1),
            y: Rational::from_int_spec(0),
        }));
        assert(a[2] == (Vec2 {
            x: Rational::from_int_spec(1),
            y: Rational::from_int_spec(1),
        }));
        assert(a[3] == (Vec2 {
            x: Rational::from_int_spec(0),
            y: Rational::from_int_spec(1),
        }));
        assert(orient(a[i], a[(i + 1) % (4 as int)], a[j]) == Rational::from_int_spec(1));
        assert(Rational::from_int_spec(0).lt_spec(Rational::from_int_spec(1)));
    }
    assert(convex_poly_inv(a));
}

/// Unit-square compound (one convex part) for scene bodies.
pub fn unit_square_compound() -> (out: Compound)
    ensures
        out.wf_spec(),
        out.model_parts().len() == 1,
        out.model_parts()[0] == square_a(),
{
    let mut va: Vec<SVec2> = Vec::new();
    va.push(RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(0)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(1)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(1)));
    let pa_opt = ConvexPoly::new_checked(va);
    proof {
        lemma_unit_square_convex();
        assert(pa_opt is Some);
    }
    let pa = pa_opt.unwrap();
    let mut parts: Vec<ConvexPoly> = Vec::new();
    parts.push(pa);
    let out = Compound::new(parts);
    proof {
        assert(out.model_parts().len() == 1);
        assert(out.model_parts()[0] == pa.model_verts());
        assert(out.model_parts()[0] == square_a());
    }
    out
}

/// B(k) is convex for every k (translation of the unit square).
pub proof fn lemma_square_b_convex(k: int)
    ensures
        convex_poly_inv(square_b(k)),
{
    lemma_unit_square_convex();
    let t = Vec2 {
        x: Rational::from_frac_spec(k, 4),
        y: Rational::from_int_spec(0),
    };
    crate::proofs::shape::lemma_convex_translation(square_a(), t);
    let f = Rational::from_frac_spec(k, 4);
    let one = Rational::from_int_spec(1);
    let zero = Rational::from_int_spec(0);
    assert(t.x == f);
    assert(t.y == zero);
    assert(square_a()[0].x == zero && square_a()[0].y == zero);
    assert(square_a()[1].x == one && square_a()[1].y == zero);
    assert(square_a()[2].x == one && square_a()[2].y == one);
    assert(square_a()[3].x == zero && square_a()[3].y == one);
    // component values of the translated points
    assert(zero.add_spec(f).num == zero.num * (f.denom_nat() as int)
        + f.num * (zero.denom_nat() as int));
    assert(zero.add_spec(f).den == zero.den * f.den + zero.den + f.den);
    assert((zero.add_spec(f).num == zero.num * (f.denom_nat() as int)
            + f.num * (zero.denom_nat() as int)
        && zero.add_spec(f).den == zero.den * f.den + zero.den + f.den
        && zero.num == 0 && zero.den == 0 && f.num == k && f.den == 3)
        ==> zero.add_spec(f).num == f.num && zero.add_spec(f).den == f.den)
        by (nonlinear_arith);
    assert(zero.add_spec(f) == f);
    assert(zero.add_spec(zero).num == zero.num * (zero.denom_nat() as int)
        + zero.num * (zero.denom_nat() as int));
    assert(zero.add_spec(zero).den == zero.den * zero.den + zero.den + zero.den);
    assert((zero.add_spec(zero).num == zero.num * (zero.denom_nat() as int)
            + zero.num * (zero.denom_nat() as int)
        && zero.add_spec(zero).den == zero.den * zero.den + zero.den + zero.den
        && zero.num == 0 && zero.den == 0)
        ==> zero.add_spec(zero) == zero) by (nonlinear_arith);
    assert(one.add_spec(f).num == one.num * (f.denom_nat() as int)
        + f.num * (one.denom_nat() as int));
    assert(one.add_spec(f).den == one.den * f.den + one.den + f.den);
    assert(f.add_spec(one).num == f.num * (one.denom_nat() as int)
        + one.num * (f.denom_nat() as int));
    assert(f.add_spec(one).den == f.den * one.den + f.den + one.den);
    assert((one.add_spec(f).num == one.num * (f.denom_nat() as int)
            + f.num * (one.denom_nat() as int)
        && f.add_spec(one).num == f.num * (one.denom_nat() as int)
            + one.num * (f.denom_nat() as int)
        && one.add_spec(f).den == one.den * f.den + one.den + f.den
        && f.add_spec(one).den == f.den * one.den + f.den + one.den
        && one.num == 1 && one.den == 0 && f.num == k && f.den == 3)
        ==> one.add_spec(f).num == f.add_spec(one).num
            && one.add_spec(f).den == f.add_spec(one).den) by (nonlinear_arith);
    assert(one.add_spec(f) == f.add_spec(one));
    assert(one.add_spec(zero).num == one.num * (zero.denom_nat() as int)
        + zero.num * (one.denom_nat() as int));
    assert(one.add_spec(zero).den == one.den * zero.den + one.den + zero.den);
    assert((one.add_spec(zero).num == one.num * (zero.denom_nat() as int)
            + zero.num * (one.denom_nat() as int)
        && one.add_spec(zero).den == one.den * zero.den + one.den + zero.den
        && one.num == 1 && one.den == 0 && zero.num == 0 && zero.den == 0)
        ==> one.add_spec(zero).num == one.num && one.add_spec(zero).den == one.den)
        by (nonlinear_arith);
    assert(one.add_spec(zero) == one);
    assert(zero.add_spec(one).num == zero.num * (one.denom_nat() as int)
        + one.num * (zero.denom_nat() as int));
    assert(zero.add_spec(one).den == zero.den * one.den + zero.den + one.den);
    assert((zero.add_spec(one).num == zero.num * (one.denom_nat() as int)
            + one.num * (zero.denom_nat() as int)
        && zero.add_spec(one).den == zero.den * one.den + zero.den + one.den
        && one.num == 1 && one.den == 0 && zero.num == 0 && zero.den == 0)
        ==> zero.add_spec(one).num == one.num && zero.add_spec(one).den == one.den)
        by (nonlinear_arith);
    assert(zero.add_spec(one) == one);
    assert(square_b(k)[0] == Vec2 {
        x: square_a()[0].x.add_spec(t.x), y: square_a()[0].y.add_spec(t.y) });
    assert(square_b(k)[1] == Vec2 {
        x: square_a()[1].x.add_spec(t.x), y: square_a()[1].y.add_spec(t.y) });
    assert(square_b(k)[2] == Vec2 {
        x: square_a()[2].x.add_spec(t.x), y: square_a()[2].y.add_spec(t.y) });
    assert(square_b(k)[3] == Vec2 {
        x: square_a()[3].x.add_spec(t.x), y: square_a()[3].y.add_spec(t.y) });
    assert(square_b(k) =~= square_a().map(|_i: int, v: Vec2<Rational>|
        Vec2 { x: v.x.add_spec(t.x), y: v.y.add_spec(t.y) }));
}

/// For k < −4: A's left edge (edge 3) strictly separates B(k).
proof fn lemma_s3_separated_left(k: int)
    requires
        k < -4,
    ensures
        Rational::from_int_spec(0).lt_spec(crate::shape::min_sep(
            crate::shape::edge_normal(square_a()[3], square_a()[0]),
            square_a()[3], square_b(k), 0)),
{
    use crate::shape::{axis_sep, edge_normal, min_sep};
    let n = edge_normal(square_a()[3], square_a()[0]);
    let p = square_a()[3];
    let b = square_b(k);
    let f = Rational::from_frac_spec(k, 4);
    let one = Rational::from_int_spec(1);
    let zero = Rational::from_int_spec(0);
    let mone = Rational::from_int_spec(-1);
    assert(square_a()[3] == (Vec2 { x: zero, y: one }));
    assert(square_a()[0] == (Vec2 { x: zero, y: zero }));
    assert(mone.num == -1);
    assert(mone.den == 0);
    assert(zero.num == 0);
    assert(zero.den == 0);
    assert(n.x == square_a()[0].y.sub_spec(square_a()[3].y));
    assert(n.y == square_a()[3].x.sub_spec(square_a()[0].x));
    assert(n.x.num == square_a()[0].y.num * (square_a()[3].y.denom_nat() as int)
        + (-square_a()[3].y.num) * (square_a()[0].y.denom_nat() as int));
    assert(n.x.den == square_a()[0].y.den * square_a()[3].y.den
        + square_a()[0].y.den + square_a()[3].y.den);
    assert(n.y.num == square_a()[3].x.num * (square_a()[0].x.denom_nat() as int)
        + (-square_a()[0].x.num) * (square_a()[3].x.denom_nat() as int));
    assert(n.y.den == square_a()[3].x.den * square_a()[0].x.den
        + square_a()[3].x.den + square_a()[0].x.den);
    assert((n.x.num == square_a()[0].y.num * (square_a()[3].y.denom_nat() as int)
            + (-square_a()[3].y.num) * (square_a()[0].y.denom_nat() as int)
        && n.x.den == square_a()[0].y.den * square_a()[3].y.den
            + square_a()[0].y.den + square_a()[3].y.den
        && square_a()[0].y.num == 0 && square_a()[0].y.den == 0
        && square_a()[3].y.num == 1 && square_a()[3].y.den == 0)
        ==> n.x.num == -1 && n.x.den == 0) by (nonlinear_arith);
    assert((n.y.num == square_a()[3].x.num * (square_a()[0].x.denom_nat() as int)
            + (-square_a()[0].x.num) * (square_a()[3].x.denom_nat() as int)
        && n.y.den == square_a()[3].x.den * square_a()[0].x.den
            + square_a()[3].x.den + square_a()[0].x.den
        && square_a()[3].x.num == 0 && square_a()[3].x.den == 0
        && square_a()[0].x.num == 0 && square_a()[0].x.den == 0)
        ==> n.y.num == 0 && n.y.den == 0) by (nonlinear_arith);
    assert(n.x.num == -1);
    assert(n.x.den == 0);
    assert(n.y.num == 0);
    assert(n.y.den == 0);
    assert(n.x == mone);
    assert(n.y == zero);
    assert(p.x == zero);
    assert(p.y == one);
    assert forall|j: int| 0 <= j < b.len() implies Rational::from_int_spec(0).lt_spec(
        #[trigger] axis_sep(n, p, b[j]))
    by {
        let q = b[j];
        let s = axis_sep(n, p, q);
        if j == 0 {
            assert(q == b[0]);
            assert(q.x == f);
        } else if j == 1 {
            assert(q == b[1]);
            assert(q.x == f.add_spec(one));
        } else if j == 2 {
            assert(q == b[2]);
            assert(q.x == f.add_spec(one));
        } else {
            assert(j == 3);
            assert(q == b[3]);
            assert(q.x == f);
        }
        assert(q.x == f || q.x == f.add_spec(one));
        // s ≡ 0 − q.x
        assert(n.x.eqv_spec(Rational::from_int_spec(-1)));
        assert(n.y.eqv_spec(zero));
        lemma_s3_axis_left_eval(n, p, q, s);
        // (0 − q.x).num ≥ 1: −k ≥ 5 or −(k+4) ≥ 1
        assert(f.num == k);
        assert(f.denom() == 4);
        assert(one.num == 1);
        assert(one.denom() == 1);
        if q.x == f {
            let v = zero.sub_spec(f);
            assert(v.num == zero.num * f.denom() + (-f.num) * zero.denom());
            assert(v.num == -k);
            assert(-k >= 5);
            assert(v.num >= 1);
            lemma_s3_zero_lt_eval(v, s);
        } else {
            let f1 = f.add_spec(one);
            assert(f1.num == f.num * one.denom() + one.num * f.denom());
            assert((f1.num == f.num * one.denom() + one.num * f.denom()
                && f.num == k && f.denom() == 4 && one.num == 1 && one.denom() == 1)
                ==> f1.num == k + 4) by (nonlinear_arith);
            let v = zero.sub_spec(f1);
            assert(v.num == zero.num * f1.denom() + (-f1.num) * zero.denom());
            assert((v.num == zero.num * f1.denom() + (-f1.num) * zero.denom()
                && f1.num == k + 4 && zero.num == 0 && zero.denom() == 1)
                ==> v.num == -(k + 4)) by (nonlinear_arith);
            assert(v.num == -(k + 4));
            assert(-(k + 4) >= 1);
            lemma_s3_zero_lt_eval(v, s);
        }
    }
    crate::proofs::shape::lemma_min_sep_attained(n, p, b, 0);
    let jstar = choose|j: int| 0 <= j < b.len() && min_sep(n, p, b, 0) == axis_sep(n, p, b[j]);
    assert(min_sep(n, p, b, 0) == axis_sep(n, p, b[jstar]));
}

/// v.num ≤ 0 ⟹ v ≤ 0 (cross form).
proof fn lemma_s3_le_zero_via_num(v: Rational)
    requires
        v.num <= 0,
    ensures
        v.le_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    Rational::lemma_denom_positive(v);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(v.le_spec(z) == (v.num * z.denom() <= z.num * v.denom()));
}

/// A vertex with axis_sep ≡ v ≤ 0 on edge e kills the separation witness.
proof fn lemma_s3_witness_not_sep(
    owner: Seq<Vec2<Rational>>,
    other: Seq<Vec2<Rational>>,
    e: int,
    j: int,
    v: Rational,
)
    requires
        0 <= e < owner.len(),
        0 <= j < other.len(),
        crate::shape::axis_sep(
            crate::shape::edge_normal(owner[e], owner[(e + 1) % (owner.len() as int)]),
            owner[e], other[j]).eqv_spec(v),
        v.le_spec(Rational::from_int_spec(0)),
    ensures
        !crate::narrowphase::axis_separates(owner, other, e),
{
    use crate::shape::{axis_sep, edge_normal};
    let n = edge_normal(owner[e], owner[(e + 1) % (owner.len() as int)]);
    let s = axis_sep(n, owner[e], other[j]);
    Rational::lemma_eqv_symmetric(s, v);
    crate::proofs::shape::lemma_le_eqv_subst_left(v, s, Rational::from_int_spec(0));
    if Rational::from_int_spec(0).lt_spec(s) {
        Rational::lemma_le_lt_transitive(s, Rational::from_int_spec(0), s);
        Rational::lemma_lt_irreflexive(s);
        assert(false);
    }
}

/// For −4 ≤ k ≤ 4: no edge of either square strictly separates (each edge
/// has a witness vertex on the wrong side).
proof fn lemma_s3_not_separated(k: int)
    requires
        -4 <= k <= 4,
    ensures
        forall|e: int|
            0 <= e < 4 ==> !crate::narrowphase::axis_separates(square_a(), square_b(k), e),
        forall|e: int|
            0 <= e < 4 ==> !crate::narrowphase::axis_separates(square_b(k), square_a(), e),
{
    use crate::shape::{axis_sep, edge_normal};
    use crate::narrowphase::axis_separates;
    let f = Rational::from_frac_spec(k, 4);
    let one = Rational::from_int_spec(1);
    let zero = Rational::from_int_spec(0);
    let mone = Rational::from_int_spec(-1);
    let a = square_a();
    let b = square_b(k);
    let f1 = f.add_spec(one);
    assert(a.len() == 4);
    assert(b.len() == 4);
    assert(f.num == k);
    assert(f.denom() == 4);
    assert(f.den == 3);
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(mone.num == -1);
    assert(mone.denom() == 1);
    assert(f1.num == f.num * one.denom() + one.num * f.denom());
    assert((f1.num == f.num * one.denom() + one.num * f.denom()
        && f.num == k && f.denom() == 4 && one.num == 1 && one.denom() == 1)
        ==> f1.num == k + 4) by (nonlinear_arith);
    assert(f1.num == k + 4);
    Rational::lemma_add_denom_product_int(f, one);
    assert(f1.denom() == 4);

    // ── owner = A (normals structural) ──
    // e0 (bottom, n = (0,−1)): witness B[0]: sep ≡ 0 − 0 ≤ 0
    {
        let nrm = edge_normal(a[0], a[1]);
        let s = axis_sep(nrm, a[0], b[0]);
        let v = zero.sub_spec(zero);
        assert(nrm.x == zero);
        assert(nrm.y == mone);
        assert(nrm.x.eqv_spec(zero));
        assert(nrm.y.eqv_spec(mone));
        assert(v.num == 0);
        lemma_s3_le_zero_via_num(v);
        lemma_s3_axis_bottom_eval(nrm, a[0], b[0], s);
        lemma_s3_witness_not_sep(a, b, 0, 0, v);
    }
    // e1 (right, n = (1,0)): witness B[0]: sep ≡ f − 1 ≤ 0
    {
        let nrm = edge_normal(a[1], a[2]);
        let s = axis_sep(nrm, a[1], b[0]);
        let v = f.sub_spec(one);
        assert(nrm.x == one);
        assert(nrm.y == zero);
        assert(nrm.x.eqv_spec(one));
        assert(nrm.y.eqv_spec(zero));
        assert(v.num == f.num * one.denom() + (-one.num) * f.denom());
        assert((v.num == f.num * one.denom() + (-one.num) * f.denom()
            && f.num == k && f.denom() == 4 && one.num == 1 && one.denom() == 1)
            ==> v.num == k - 4) by (nonlinear_arith);
        assert(v.num == k - 4);
        assert(v.num <= 0);
        lemma_s3_le_zero_via_num(v);
        lemma_s3_axis_right_eval(nrm, a[1], b[0], s);
        lemma_s3_witness_not_sep(a, b, 1, 0, v);
    }
    // e2 (top, n = (0,1)): witness B[0]: sep ≡ 0 − 1 ≤ 0
    {
        let nrm = edge_normal(a[2], a[3]);
        let s = axis_sep(nrm, a[2], b[0]);
        let v = zero.sub_spec(one);
        assert(nrm.x == zero);
        assert(nrm.y == one);
        assert(nrm.x.eqv_spec(zero));
        assert(nrm.y.eqv_spec(one));
        assert(v.num == zero.num * one.denom() + (-one.num) * zero.denom());
        assert(v.num == -1);
        lemma_s3_le_zero_via_num(v);
        lemma_s3_axis_top_eval(nrm, a[2], b[0], s);
        lemma_s3_witness_not_sep(a, b, 2, 0, v);
    }
    // e3 (left, n = (−1,0)): witness B[0] (k ≥ 0) or B[1] (k < 0)
    {
        let nrm = edge_normal(a[3], a[0]);
        assert(nrm.x == mone);
        assert(nrm.y == zero);
        assert(nrm.x.eqv_spec(mone));
        assert(nrm.y.eqv_spec(zero));
        if k >= 0 {
            let s = axis_sep(nrm, a[3], b[0]);
            let v = zero.sub_spec(f);
            assert(v.num == zero.num * f.denom() + (-f.num) * zero.denom());
            assert((v.num == zero.num * f.denom() + (-f.num) * zero.denom()
                && f.num == k && zero.num == 0 && zero.denom() == 1)
                ==> v.num == -k) by (nonlinear_arith);
            assert(v.num == -k);
            assert(v.num <= 0);
            lemma_s3_le_zero_via_num(v);
            lemma_s3_axis_left_eval(nrm, a[3], b[0], s);
            lemma_s3_witness_not_sep(a, b, 3, 0, v);
        } else {
            let s = axis_sep(nrm, a[3], b[1]);
            let v = zero.sub_spec(f1);
            assert(v.num == zero.num * (f1.denom_nat() as int) + (-f1.num) * zero.denom());
            assert((v.num == zero.num * (f1.denom_nat() as int) + (-f1.num) * zero.denom()
                && f1.num == k + 4 && zero.num == 0 && zero.denom() == 1)
                ==> v.num == -(k + 4)) by (nonlinear_arith);
            assert(v.num == -(k + 4));
            assert(v.num <= 0);
            lemma_s3_le_zero_via_num(v);
            lemma_s3_axis_left_eval(nrm, a[3], b[1], s);
            lemma_s3_witness_not_sep(a, b, 3, 1, v);
        }
    }
    assert(!axis_separates(a, b, 0));
    assert(!axis_separates(a, b, 1));
    assert(!axis_separates(a, b, 2));
    assert(!axis_separates(a, b, 3));

    // ── owner = B (normals need eqv staging) ──
    // e0 (bottom): witness A[0]: sep ≡ 0 − 0 ≤ 0
    {
        let nrm = edge_normal(b[0], b[1]);
        let s = axis_sep(nrm, b[0], a[0]);
        let v = zero.sub_spec(zero);
        assert(nrm.x == zero);
        assert(nrm.y == f.sub_spec(f1));
        assert(nrm.y.num == f.num * (f1.denom_nat() as int) + (-f1.num) * (f.denom_nat() as int));
        Rational::lemma_add_denom_product_int(f, f1.neg_spec());
        assert(nrm.y.denom() == f.denom() * f1.denom());
        assert((nrm.y.num == f.num * (f1.denom_nat() as int) + (-f1.num) * (f.denom_nat() as int)
            && f.num == k && f.denom() == 4 && f1.num == k + 4 && f1.denom() == 4
            && nrm.y.denom() == f.denom() * f1.denom())
            ==> nrm.y.num == -16 && nrm.y.denom() == 16) by (nonlinear_arith);
        assert(nrm.y.num == -16);
        assert(nrm.y.denom() == 16);
        assert(nrm.y.eqv_spec(mone)) by {
            assert(nrm.y.num * mone.denom() == mone.num * nrm.y.denom());
        }
        assert(nrm.x.eqv_spec(zero));
        assert(v.num == 0);
        lemma_s3_le_zero_via_num(v);
        lemma_s3_axis_bottom_eval(nrm, b[0], a[0], s);
        lemma_s3_witness_not_sep(b, a, 0, 0, v);
    }
    // e1 (right): witness A[0]: sep ≡ 0 − (f+1) ≤ 0
    {
        let nrm = edge_normal(b[1], b[2]);
        let s = axis_sep(nrm, b[1], a[0]);
        let v = zero.sub_spec(f1);
        assert(nrm.x == one);
        assert(nrm.y == f1.sub_spec(f1));
        assert(nrm.y.num == f1.num * (f1.denom_nat() as int) + (-f1.num) * (f1.denom_nat() as int));
        assert(nrm.y.num == 0);
        assert(nrm.y.eqv_spec(zero)) by {
            assert(nrm.y.num * zero.denom() == zero.num * nrm.y.denom());
        }
        assert(nrm.x.eqv_spec(one));
        assert(v.num == zero.num * (f1.denom_nat() as int) + (-f1.num) * zero.denom());
        assert((v.num == zero.num * (f1.denom_nat() as int) + (-f1.num) * zero.denom()
            && f1.num == k + 4 && zero.num == 0 && zero.denom() == 1)
            ==> v.num == -(k + 4)) by (nonlinear_arith);
        assert(v.num == -(k + 4));
        assert(v.num <= 0);
        lemma_s3_le_zero_via_num(v);
        lemma_s3_axis_right_eval(nrm, b[1], a[0], s);
        lemma_s3_witness_not_sep(b, a, 1, 0, v);
    }
    // e2 (top): witness A[0]: sep ≡ 0 − 1 ≤ 0
    {
        let nrm = edge_normal(b[2], b[3]);
        let s = axis_sep(nrm, b[2], a[0]);
        let v = zero.sub_spec(one);
        assert(nrm.x == zero);
        assert(nrm.y == f1.sub_spec(f));
        assert(nrm.y.num == f1.num * (f.denom_nat() as int) + (-f.num) * (f1.denom_nat() as int));
        Rational::lemma_add_denom_product_int(f1, f.neg_spec());
        assert(nrm.y.denom() == f1.denom() * f.denom());
        assert((nrm.y.num == f1.num * (f.denom_nat() as int) + (-f.num) * (f1.denom_nat() as int)
            && f.num == k && f.denom() == 4 && f1.num == k + 4 && f1.denom() == 4
            && nrm.y.denom() == f1.denom() * f.denom())
            ==> nrm.y.num == 16 && nrm.y.denom() == 16) by (nonlinear_arith);
        assert(nrm.y.num == 16);
        assert(nrm.y.denom() == 16);
        assert(nrm.y.eqv_spec(one)) by {
            assert(nrm.y.num * one.denom() == one.num * nrm.y.denom());
        }
        assert(nrm.x.eqv_spec(zero));
        assert(v.num == zero.num * one.denom() + (-one.num) * zero.denom());
        assert(v.num == -1);
        lemma_s3_le_zero_via_num(v);
        lemma_s3_axis_top_eval(nrm, b[2], a[0], s);
        lemma_s3_witness_not_sep(b, a, 2, 0, v);
    }
    // e3 (left): witness A[0] (k ≤ 0) or A[2] (k > 0)
    {
        let nrm = edge_normal(b[3], b[0]);
        assert(nrm.x == mone);
        assert(nrm.y == f.sub_spec(f));
        assert(nrm.y.num == f.num * (f.denom_nat() as int) + (-f.num) * (f.denom_nat() as int));
        assert(nrm.y.num == 0);
        assert(nrm.y.eqv_spec(zero)) by {
            assert(nrm.y.num * zero.denom() == zero.num * nrm.y.denom());
        }
        assert(nrm.x.eqv_spec(mone));
        if k <= 0 {
            let s = axis_sep(nrm, b[3], a[0]);
            let v = f.sub_spec(zero);
            assert(v.num == f.num * zero.denom() + (-zero.num) * f.denom());
            assert((v.num == f.num * zero.denom() + (-zero.num) * f.denom()
                && f.num == k && zero.num == 0 && zero.denom() == 1)
                ==> v.num == k) by (nonlinear_arith);
            assert(v.num == k);
            assert(v.num <= 0);
            lemma_s3_le_zero_via_num(v);
            lemma_s3_axis_left_eval(nrm, b[3], a[0], s);
            lemma_s3_witness_not_sep(b, a, 3, 0, v);
        } else {
            let s = axis_sep(nrm, b[3], a[2]);
            let v = f.sub_spec(one);
            assert(v.num == f.num * one.denom() + (-one.num) * f.denom());
            assert((v.num == f.num * one.denom() + (-one.num) * f.denom()
                && f.num == k && f.denom() == 4 && one.num == 1 && one.denom() == 1)
                ==> v.num == k - 4) by (nonlinear_arith);
            assert(v.num == k - 4);
            assert(v.num <= 0);
            lemma_s3_le_zero_via_num(v);
            lemma_s3_axis_left_eval(nrm, b[3], a[2], s);
            lemma_s3_witness_not_sep(b, a, 3, 2, v);
        }
    }
    assert(!axis_separates(b, a, 0));
    assert(!axis_separates(b, a, 1));
    assert(!axis_separates(b, a, 2));
    assert(!axis_separates(b, a, 3));
}

/// S3 (SPEC §8): SAT vs known answers over the k-family of square pairs.
pub fn scene_s3() -> (out: bool)
    ensures
        out == true,
{
    // A = unit square
    let mut va: Vec<SVec2> = Vec::new();
    va.push(RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(0)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(1)));
    va.push(RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(1)));
    let pa_opt = ConvexPoly::new_checked(va);
    proof {
        lemma_unit_square_convex();
        assert(pa_opt is Some);
    }
    let pa = pa_opt.unwrap();

    let mut k: i64 = -5;
    while k <= 5
        invariant
            -5 <= k <= 6,
            pa.wf_spec(),
            pa.model_verts() == square_a(),
        decreases 6 - k,
    {
        let f = RuntimeRational::from_frac(k, 4);
        let f1 = f.add(&RuntimeRational::from_int(1));
        let f3 = verus_rational::runtime_rational::copy_rational(&f1);
        let f5 = verus_rational::runtime_rational::copy_rational(&f);
        let z1 = RuntimeRational::from_int(0);
        let z2 = RuntimeRational::from_int(0);
        let o1 = RuntimeRational::from_int(1);
        let o2 = RuntimeRational::from_int(1);
        let mut vb: Vec<SVec2> = Vec::new();
        vb.push(RuntimeVec2::new(f, z1));
        vb.push(RuntimeVec2::new(f1, z2));
        vb.push(RuntimeVec2::new(f3, o1));
        vb.push(RuntimeVec2::new(f5, o2));
        proof {
            lemma_square_b_convex(k as int);
        }
        let pb_opt = ConvexPoly::new_checked(vb);
        proof {
            assert(vb@[0].model@ == (Vec2 { x: f@, y: z1@ }));
            assert(vb@[1].model@ == (Vec2 { x: f1@, y: z2@ }));
            assert(vb@[2].model@ == (Vec2 { x: f3@, y: o1@ }));
            assert(vb@[3].model@ == (Vec2 { x: f5@, y: o2@ }));
            assert(f@ == Rational::from_frac_spec(k as int, 4));
            assert(f1@ == Rational::from_frac_spec(k as int, 4).add_spec(
                Rational::from_int_spec(1)));
            assert(f3@ == f1@);
            assert(f5@ == f@);
            assert(z1@ == Rational::from_int_spec(0));
            assert(z2@ == Rational::from_int_spec(0));
            assert(o1@ == Rational::from_int_spec(1));
            assert(o2@ == Rational::from_int_spec(1));
            assert forall|i: int|
                0 <= i < 4 implies (#[trigger] vb@[i]).model@ == square_b(k as int)[i]
            by {
            }
            assert(vb@.map(|_i: int, v: SVec2| v.model@) =~= square_b(k as int));
            assert(convex_poly_inv(square_b(k as int)));
            assert forall|i: int, j: int|
                (0 <= i < square_b(k as int).len() && 0 <= j < square_b(k as int).len()) implies {
                    let o = #[trigger] orient(
                        vb@[i].model@,
                        vb@[(i + 1) % (vb@.len() as int)].model@,
                        vb@[j].model@);
                    if j == i || j == (i + 1) % (vb@.len() as int) {
                        true
                    } else {
                        Rational::from_int_spec(0).lt_spec(o)
                    }
                }
            by {
                assert(vb@[i].model@ == square_b(k as int)[i]);
                assert(vb@[(i + 1) % (vb@.len() as int)].model@
                    == square_b(k as int)[(i + 1) % (square_b(k as int).len() as int)]);
                assert(vb@[j].model@ == square_b(k as int)[j]);
            }
            assert(convex_poly_inv(vb@.map(|_i: int, v: SVec2| v.model@)));
            assert(pb_opt is Some);
            assert(pb_opt->Some_0.model_verts() == square_b(k as int));
        }
        let pb = pb_opt.unwrap();
        let r = sat_classify(&pa, &pb);
        let expected = k > 4 || k < -4;
        let ok = match r {
            SatResult::Separated { from_a, edge } => {
                proof {
                    // a strict separator exists ⟹ k must be outside [−4, 4]
                    if k >= -4 && k <= 4 {
                        lemma_s3_not_separated(k as int);
                        assert(square_a().len() == 4);
                        assert(square_b(k as int).len() == 4);
                        assert(0 <= edge as int && (edge as int) < 4);
                        if from_a {
                            assert(crate::narrowphase::axis_separates(
                                square_a(), square_b(k as int), edge as int));
                            assert(!crate::narrowphase::axis_separates(
                                square_a(), square_b(k as int), edge as int)) by {
                                assert(0 <= edge as int && (edge as int) < 4);
                            }
                        } else {
                            assert(crate::narrowphase::axis_separates(
                                square_b(k as int), square_a(), edge as int));
                            assert(!crate::narrowphase::axis_separates(
                                square_b(k as int), square_a(), edge as int)) by {
                                assert(0 <= edge as int && (edge as int) < 4);
                            }
                        }
                        assert(false);
                    }
                    assert(expected);
                }
                expected
            },
            SatResult::Touching { .. } => {
                proof {
                    assert(square_a().len() == 4);
                    assert(square_b(k as int).len() == 4);
                    assert(crate::narrowphase::no_axis_separates(
                        square_a(), square_b(k as int)));
                    // no edge separates ⟹ k must be inside [−4, 4]
                    if k > 4 {
                        lemma_s3_separated_right(k as int);
                        assert(square_a()[(1 as int + 1) % (square_a().len() as int)] == square_a()[2]);
                        assert(crate::shape::min_sep(
                            crate::shape::edge_normal(square_a()[1], square_a()[2]),
                            square_a()[1], square_b(k as int), 0).le_spec(
                            Rational::from_int_spec(0)));
                        Rational::lemma_le_lt_transitive(
                            crate::shape::min_sep(
                                crate::shape::edge_normal(square_a()[1], square_a()[2]),
                                square_a()[1], square_b(k as int), 0),
                            Rational::from_int_spec(0),
                            crate::shape::min_sep(
                                crate::shape::edge_normal(square_a()[1], square_a()[2]),
                                square_a()[1], square_b(k as int), 0));
                        Rational::lemma_lt_irreflexive(crate::shape::min_sep(
                            crate::shape::edge_normal(square_a()[1], square_a()[2]),
                            square_a()[1], square_b(k as int), 0));
                        assert(false);
                    }
                    if k < -4 {
                        lemma_s3_separated_left(k as int);
                        assert(square_a()[(3 as int + 1) % (square_a().len() as int)] == square_a()[0]);
                        assert(crate::shape::min_sep(
                            crate::shape::edge_normal(square_a()[3], square_a()[0]),
                            square_a()[3], square_b(k as int), 0).le_spec(
                            Rational::from_int_spec(0)));
                        Rational::lemma_le_lt_transitive(
                            crate::shape::min_sep(
                                crate::shape::edge_normal(square_a()[3], square_a()[0]),
                                square_a()[3], square_b(k as int), 0),
                            Rational::from_int_spec(0),
                            crate::shape::min_sep(
                                crate::shape::edge_normal(square_a()[3], square_a()[0]),
                                square_a()[3], square_b(k as int), 0));
                        Rational::lemma_lt_irreflexive(crate::shape::min_sep(
                            crate::shape::edge_normal(square_a()[3], square_a()[0]),
                            square_a()[3], square_b(k as int), 0));
                        assert(false);
                    }
                    assert(!expected);
                }
                !expected
            },
        };
        if !ok {
            proof {
                assert(false);
            }
            return false;
        }
        k = k + 1;
    }
    true
}

} // verus!
