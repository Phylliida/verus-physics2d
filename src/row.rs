//! The ONE constraint row type (E1, SPEC §6) — phys-05c part 2.
//!
//! A row is one scalar constraint between two bodies: J blocks (linear,
//! angular) per body, impulse-accumulator bounds, velocity-level bias, and
//! the accumulated impulse λ. Contact rows have J = [−n, −cross(rₐ, n), n,
//! cross(r_b, n)] with lo = 0, hi = ∞. No square roots anywhere: normals
//! stay unnormalized and |n|² folds into the effective-mass denominator
//! (SPEC §5 standing rule).
//!
//! Raw Rational ops throughout, matching shape.rs/massprops.rs discipline.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::body::Body;
use crate::massprops::{vdot, vscale};
use crate::momentum::vcross;
use crate::shape::vadd;
use crate::types::{copy_svec2, SVec2, Scalar};

verus! {

/// Impulse-accumulator bound (SPEC §6): contact rows are [0, ∞); joint
/// rows vary by type. Inf = no bound on that side.
pub enum BoundQ {
    Finite(Scalar),
    Inf,
}

impl BoundQ {
    pub open spec fn wf_spec(&self) -> bool {
        match self {
            BoundQ::Finite(q) => q.wf_spec(),
            BoundQ::Inf => true,
        }
    }

    /// The bound as a spec value: None = unbounded.
    pub open spec fn val(&self) -> Option<Rational> {
        match self {
            BoundQ::Finite(q) => Option::Some(q@),
            BoundQ::Inf => Option::None,
        }
    }
}

/// λ ≥ lo (vacuous when lo is −∞).
pub open spec fn lambda_ge_lo(lo: Option<Rational>, lambda: Rational) -> bool {
    match lo {
        Option::Some(q) => q.le_spec(lambda),
        Option::None => true,
    }
}

/// λ ≤ hi (vacuous when hi is +∞).
pub open spec fn lambda_le_hi(hi: Option<Rational>, lambda: Rational) -> bool {
    match hi {
        Option::Some(q) => lambda.le_spec(q),
        Option::None => true,
    }
}

/// C2 (SPEC §7): λ within its row's bounds.
pub open spec fn lambda_in_bounds(lo: Option<Rational>, hi: Option<Rational>, lambda: Rational) -> bool {
    &&& lambda_ge_lo(lo, lambda)
    &&& lambda_le_hi(hi, lambda)
}

/// Bounds are consistent: when both sides are finite, lo ≤ hi.
pub open spec fn bounds_consistent(lo: Option<Rational>, hi: Option<Rational>) -> bool {
    match (lo, hi) {
        (Option::Some(l), Option::Some(h)) => l.le_spec(h),
        _ => true,
    }
}

/// Spec-level clamp of x to [lo, hi] (None = unbounded side; lo checked
/// first, matching the exec order).
pub open spec fn clamp_spec(x: Rational, lo: Option<Rational>, hi: Option<Rational>) -> Rational {
    let x1 = match lo {
        Option::Some(l) => if x.lt_spec(l) { l } else { x },
        Option::None => x,
    };
    match hi {
        Option::Some(h) => if h.lt_spec(x1) { h } else { x1 },
        Option::None => x1,
    }
}

pub struct Row {
    pub a: usize,
    pub b: usize,
    /// J blocks for body a (linear, angular).
    pub jla: SVec2,
    pub jaa: Scalar,
    /// J blocks for body b.
    pub jlb: SVec2,
    pub jab: Scalar,
    pub lo: BoundQ,
    pub hi: BoundQ,
    /// Velocity-level bias (0 in phase 1 except restitution; e = 0 default).
    pub bias: Scalar,
    /// Accumulated impulse.
    pub lambda: Scalar,
}

impl Row {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.a != self.b
        &&& self.jla.wf_spec()
        &&& self.jaa.wf_spec()
        &&& self.jlb.wf_spec()
        &&& self.jab.wf_spec()
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.bias.wf_spec()
        &&& self.lambda.wf_spec()
    }
}

// ── spec ops ───────────────────────────────────────────────────────────

/// Effective-mass denominator (SPEC §6):
/// mEff = jlₐ·jlₐ·inv_mₐ + jaₐ²·inv_Iₐ + (same for b).
pub open spec fn eff_mass_spec(
    jla: Vec2<Rational>,
    jaa: Rational,
    jlb: Vec2<Rational>,
    jab: Rational,
    inv_ma: Rational,
    inv_ia: Rational,
    inv_mb: Rational,
    inv_ib: Rational,
) -> Rational {
    vdot(jla, jla).mul_spec(inv_ma).add_spec(jaa.mul_spec(jaa).mul_spec(inv_ia)).add_spec(
        vdot(jlb, jlb).mul_spec(inv_mb),
    ).add_spec(jab.mul_spec(jab).mul_spec(inv_ib))
}

/// Velocity-level row rate J·v = jlₐ·vₐ + jaₐ·ωₐ + jl_b·v_b + ja_b·ω_b.
pub open spec fn row_vel_spec(
    jla: Vec2<Rational>,
    jaa: Rational,
    jlb: Vec2<Rational>,
    jab: Rational,
    va: Vec2<Rational>,
    wa: Rational,
    vb: Vec2<Rational>,
    wb: Rational,
) -> Rational {
    vdot(jla, va).add_spec(jaa.mul_spec(wa)).add_spec(vdot(jlb, vb)).add_spec(jab.mul_spec(wb))
}

/// Velocity of body `bdy` after applying impulse λ through J-block (jl, ja)
/// (SPEC §6: v += inv_m·λ·jl, ω += inv_I·λ·ja).
pub open spec fn vel_after_impulse(
    inv_m: Rational,
    inv_i: Rational,
    jl: Vec2<Rational>,
    ja: Rational,
    lambda: Rational,
    v: Vec2<Rational>,
    w: Rational,
) -> (Vec2<Rational>, Rational) {
    (
        vadd(v, vscale(inv_m.mul_spec(lambda), jl)),
        w.add_spec(inv_i.mul_spec(lambda).mul_spec(ja)),
    )
}

// ── exec evaluators ────────────────────────────────────────────────────

/// mEff with exact model (SPEC §6).
pub fn eff_mass_exec(r: &Row, ba: &Body, bb: &Body) -> (out: Scalar)
    requires
        r.wf_spec(),
        ba.wf_spec(),
        bb.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == eff_mass_spec(
            r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
            ba.inv_mass@, ba.inv_inertia@, bb.inv_mass@, bb.inv_inertia@),
{
    let da = r.jla.x.mul(&r.jla.x).add(&r.jla.y.mul(&r.jla.y)).mul(&ba.inv_mass);
    let aa = r.jaa.mul(&r.jaa).mul(&ba.inv_inertia);
    let db = r.jlb.x.mul(&r.jlb.x).add(&r.jlb.y.mul(&r.jlb.y)).mul(&bb.inv_mass);
    let ab = r.jab.mul(&r.jab).mul(&bb.inv_inertia);
    da.add(&aa).add(&db).add(&ab)
}

/// J·v with exact model.
pub fn row_vel_exec(r: &Row, ba: &Body, bb: &Body) -> (out: Scalar)
    requires
        r.wf_spec(),
        ba.wf_spec(),
        bb.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == row_vel_spec(
            r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
            ba.vel.model@, ba.omega@, bb.vel.model@, bb.omega@),
{
    let t1 = r.jla.x.mul(&ba.vel.x).add(&r.jla.y.mul(&ba.vel.y)).add(&r.jaa.mul(&ba.omega));
    let t2 = t1.add(&r.jlb.x.mul(&bb.vel.x).add(&r.jlb.y.mul(&bb.vel.y)));
    t2.add(&r.jab.mul(&bb.omega))
}

/// Apply impulse λ through (jl, ja) to one body; only velocity/omega
/// change. Exact model matches vel_after_impulse.
pub fn apply_impulse_exec(b: &Body, jl: &SVec2, ja: &Scalar, lambda: &Scalar) -> (out: Body)
    requires
        b.wf_spec(),
        jl.wf_spec(),
        ja.wf_spec(),
        lambda.wf_spec(),
    ensures
        out.wf_spec(),
        (out.vel.model@, out.omega@) == vel_after_impulse(
            b.inv_mass@, b.inv_inertia@, jl.model@, ja@, lambda@,
            b.vel.model@, b.omega@),
        out.pos.model@ == b.pos.model@,
        out.rot.c@ == b.rot.c@,
        out.rot.s@ == b.rot.s@,
        out.inv_mass@ == b.inv_mass@,
        out.inv_inertia@ == b.inv_inertia@,
        out.shape.model_parts() == b.shape.model_parts(),
{
    let c = b.inv_mass.mul(lambda);
    let dvx = c.mul(&jl.x);
    let dvy = c.mul(&jl.y);
    let vel = crate::types::SVec2::new(b.vel.x.add(&dvx), b.vel.y.add(&dvy));
    let ci = b.inv_inertia.mul(lambda);
    let omega = b.omega.add(&ci.mul(ja));
    let pos = copy_svec2(&b.pos);
    let rot = b.rot.copy();
    let inv_mass = verus_rational::runtime_rational::copy_rational(&b.inv_mass);
    let inv_inertia = verus_rational::runtime_rational::copy_rational(&b.inv_inertia);
    let shape = b.shape.copy_compound();
    Body { pos, rot, vel, omega, inv_mass, inv_inertia, shape }
}

/// Contact row (SPEC §6): J = [−n, −cross(rₐ, n), n, cross(r_b, n)],
/// lo = 0, hi = ∞, bias = 0, λ = 0. `ra`/`rb` are point − center for each
/// body (exact); `n` is the (unnormalized) contact normal from a toward b.
pub fn contact_row_exec(
    a: usize,
    b: usize,
    n: &SVec2,
    ra: &SVec2,
    rb: &SVec2,
) -> (out: Row)
    requires
        a != b,
        n.wf_spec(),
        ra.wf_spec(),
        rb.wf_spec(),
    ensures
        out.wf_spec(),
        out.a == a,
        out.b == b,
        out.jla.model@ == vscale(Rational::from_int_spec(-1), n.model@),
        out.jaa@ == vcross(ra.model@, n.model@).neg_spec(),
        out.jlb.model@ == n.model@,
        out.jab@ == vcross(rb.model@, n.model@),
        out.lo.val() == Option::Some(Rational::from_int_spec(0)),
        out.hi is Inf,
        out.bias@ == Rational::from_int_spec(0),
        out.lambda@ == Rational::from_int_spec(0),
{
    let zero = RuntimeRational::from_int(0);
    let jla = crate::types::SVec2::new(n.x.neg(), n.y.neg());
    let jaa = ra.y.mul(&n.x).sub(&ra.x.mul(&n.y));
    let jlb = copy_svec2(n);
    let jab = rb.x.mul(&n.y).sub(&rb.y.mul(&n.x));
    let bias = RuntimeRational::from_int(0);
    let lambda = RuntimeRational::from_int(0);
    proof {
        // −cross(r, n) = r.y·n.x − r.x·n.y (raw neg-sub identity)
        assert(jaa@ == vcross(ra.model@, n.model@).neg_spec()) by {
            let cr = vcross(ra.model@, n.model@);
            crate::proofs::rational_raw::lemma_raw_neg_sub(
                ra.model@.x.mul_spec(n.model@.y),
                ra.model@.y.mul_spec(n.model@.x),
            );
            assert(jaa@ == ra.model@.y.mul_spec(n.model@.x).sub_spec(
                ra.model@.x.mul_spec(n.model@.y)));
        };
        assert(jla.model@ == vscale(Rational::from_int_spec(-1), n.model@)) by {
            assert(jla.model@.x == n.model@.x.neg_spec());
            assert(Rational::from_int_spec(-1).mul_spec(n.model@.x) == n.model@.x.neg_spec()) by {
                crate::proofs::rational_raw::lemma_raw_neg_one_mul(n.model@.x);
            };
            assert(jla.model@.y == n.model@.y.neg_spec());
            assert(Rational::from_int_spec(-1).mul_spec(n.model@.y) == n.model@.y.neg_spec()) by {
                crate::proofs::rational_raw::lemma_raw_neg_one_mul(n.model@.y);
            };
        };
    }
    Row {
        a,
        b,
        jla,
        jaa,
        jlb,
        jab,
        lo: BoundQ::Finite(zero),
        hi: BoundQ::Inf,
        bias,
        lambda,
    }
}

/// One PGS velocity update for a single row (SPEC §6):
/// Δ = −(v_rel + bias)/mEff; λ' = clamp(λ + Δ, lo, hi). Returns λ'.
/// The caller passes mEff (from eff_mass_exec) and must show it positive
/// (rows with mEff = 0 are dropped at construction, SPEC §6).
pub fn solve_row_lambda_exec(r: &Row, ba: &Body, bb: &Body, meff: &Scalar) -> (out: Scalar)
    requires
        r.wf_spec(),
        ba.wf_spec(),
        bb.wf_spec(),
        meff.wf_spec(),
        meff@ == eff_mass_spec(
            r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
            ba.inv_mass@, ba.inv_inertia@, bb.inv_mass@, bb.inv_inertia@),
        Rational::from_int_spec(0).lt_spec(meff@),
        bounds_consistent(r.lo.val(), r.hi.val()),
    ensures
        out.wf_spec(),
        out@ == clamp_spec(
            r.lambda@.sub_spec(
                row_vel_spec(
                    r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                    ba.vel.model@, ba.omega@, bb.vel.model@, bb.omega@)
                    .add_spec(r.bias@).div_spec(meff@)),
            r.lo.val(), r.hi.val()),
        lambda_in_bounds(r.lo.val(), r.hi.val(), out@),
{
    let vrel = row_vel_exec(r, ba, bb);
    let delta = vrel.add(&r.bias).neg().div(meff);
    let cand = r.lambda.add(&delta);
    proof {
        // cand@ == λ + (−(v_rel+bias))/mEff == λ − (v_rel+bias)/mEff
        let vb = row_vel_spec(
            r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
            ba.vel.model@, ba.omega@, bb.vel.model@, bb.omega@).add_spec(r.bias@);
        assert(delta@ == vb.neg_spec().div_spec(meff@));
        crate::proofs::rational_raw::lemma_raw_neg_div(vb, meff@);
        assert(delta@ == vb.div_spec(meff@).neg_spec());
        assert(cand@ == r.lambda@.add_spec(vb.div_spec(meff@).neg_spec()));
        assert(cand@ == r.lambda@.sub_spec(vb.div_spec(meff@)));
    }
    let mut lam = cand;
    let mut clamped_lo = false;
    match &r.lo {
        BoundQ::Finite(l) => {
            if lam.lt(l) {
                lam = verus_rational::runtime_rational::copy_rational(l);
                clamped_lo = true;
            }
        },
        BoundQ::Inf => {},
    }
    let ghost after_lo = lam@;
    match &r.hi {
        BoundQ::Finite(h) => {
            if h.lt(&lam) {
                lam = verus_rational::runtime_rational::copy_rational(h);
            }
        },
        BoundQ::Inf => {},
    }
    proof {
        let x = r.lambda@.sub_spec(
            row_vel_spec(
                r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                ba.vel.model@, ba.omega@, bb.vel.model@, bb.omega@)
                .add_spec(r.bias@).div_spec(meff@));
        let lo = r.lo.val();
        let hi = r.hi.val();
        assert(cand@ == x);
        // lo stage matches clamp_spec's first match arm
        assert(after_lo == (match lo {
            Option::Some(l) => if x.lt_spec(l) { l } else { x },
            Option::None => x,
        })) by {
            match lo {
                Option::Some(l) => {
                    if x.lt_spec(l) {
                        assert(clamped_lo);
                    } else {
                        assert(!clamped_lo);
                    }
                },
                Option::None => {},
            }
        };
        assert(lam@ == clamp_spec(x, lo, hi));
        // lower bound: l ≤ after_lo, and l ≤ lam (via consistency if the
        // hi stage then clamped)
        match lo {
            Option::Some(l) => {
                if x.lt_spec(l) {
                    Rational::lemma_eqv_implies_le(l, l);
                } else {
                    Rational::lemma_trichotomy(l, x);
                    Rational::lemma_le_iff_lt_or_eqv(l, x);
                }
                assert(l.le_spec(after_lo));
                match hi {
                    Option::Some(h) => {
                        if h.lt_spec(after_lo) {
                            assert(l.le_spec(h));
                            Rational::lemma_le_transitive(l, h, lam@);
                        }
                    },
                    Option::None => {},
                }
                assert(l.le_spec(lam@));
            },
            Option::None => {},
        }
        // upper bound
        match hi {
            Option::Some(h) => {
                if h.lt_spec(after_lo) {
                    Rational::lemma_eqv_implies_le(h, h);
                } else {
                    Rational::lemma_trichotomy(after_lo, h);
                    Rational::lemma_le_iff_lt_or_eqv(after_lo, h);
                    assert(after_lo.le_spec(h));
                }
            },
            Option::None => {},
        }
    }
    lam
}

} // verus!
