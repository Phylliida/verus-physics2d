//! RotQ: orientation as an exact rational point on the unit circle (D2/E2).
//!
//! No angles are stored anywhere — an orientation IS a pair (c, s) with
//! c² + s² ≡ 1 (Rational eqv). phys-01 provided the struct, the invariant,
//! and the identity constructor; phys-02 adds apply / compose / inverse /
//! from_tan_half (invariant preservation proved in proofs/rational_raw.rs
//! via integer cross-multiplication) and the untrusted tan-half series
//! chooser (the angle ledger, phys-02b, accounts for what it applies).

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_rational::{Rational, RuntimeRational};
use verus_rational::runtime_rational::copy_rational;

use crate::proofs::rational_raw::{
    lemma_unit_norm_raw, lemma_unit_norm_raw_compose, lemma_unit_norm_raw_neg_s,
    lemma_unit_norm_raw_tan_half,
};
use crate::types::{q_add, q_eqv, q_mul, q_one, q_zero, Scalar, SVec2};

verus! {

/// c² + s² ≡ 1, stated with the Ring trait ops (historical: keeps wf_spec
/// independent of Rational internals). NOTE: RuntimeRational exec ensures
/// produce RAW *_spec models, not trait-op models — proofs/rational_raw.rs
/// bridges the two forms (lemma_unit_norm_raw) wherever they meet.
pub open spec fn unit_norm(c: Rational, s: Rational) -> bool {
    q_eqv(q_add(q_mul(c, c), q_mul(s, s)), q_one())
}

pub struct RotQ {
    pub c: Scalar,
    pub s: Scalar,
}

impl RotQ {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.c.wf_spec()
        &&& self.s.wf_spec()
        &&& unit_norm(self.c@, self.s@)
    }

    /// The identity rotation: (c, s) = (1, 0).
    pub fn identity() -> (out: Self)
        ensures
            out.wf_spec(),
            out.c@ == Rational::from_int_spec(1),
            out.s@ == Rational::from_int_spec(0),
    {
        let c = RuntimeRational::from_int(1);
        let s = RuntimeRational::from_int(0);
        proof {
            lemma_unit_norm_one_zero();
            // from_int_spec(1) is Ring::one, from_int_spec(0) is zero
            assert(c@ == q_one());
            assert(s@ == q_zero());
        }
        RotQ { c, s }
    }

    /// Compose two rotations (exact angle-sum formulas).
    pub fn compose(&self, rhs: &RotQ) -> (out: RotQ)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out.c@ == self.c@.mul_spec(rhs.c@).sub_spec(self.s@.mul_spec(rhs.s@)),
            out.s@ == self.s@.mul_spec(rhs.c@).add_spec(self.c@.mul_spec(rhs.s@)),
    {
        let cc = self.c.mul(&rhs.c);
        let ss = self.s.mul(&rhs.s);
        let sc = self.s.mul(&rhs.c);
        let cs = self.c.mul(&rhs.s);
        let c = cc.sub(&ss);
        let s = sc.add(&cs);
        proof {
            lemma_unit_norm_raw(self.c@, self.s@);
            lemma_unit_norm_raw(rhs.c@, rhs.s@);
            lemma_unit_norm_raw_compose(self.c@, self.s@, rhs.c@, rhs.s@);
            lemma_unit_norm_raw(c@, s@);
        }
        RotQ { c, s }
    }

    /// Deep copy (BigInt witnesses aren't Copy).
    pub fn copy(&self) -> (out: RotQ)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.c@ == self.c@,
            out.s@ == self.s@,
    {
        let c = copy_rational(&self.c);
        let s = copy_rational(&self.s);
        proof {
            lemma_unit_norm_raw(self.c@, self.s@);
            lemma_unit_norm_raw(c@, s@);
        }
        RotQ { c, s }
    }

    /// The inverse rotation: (c, −s).
    pub fn inverse(&self) -> (out: RotQ)    requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.c@ == self.c@,
            out.s@ == self.s@.neg_spec(),
    {
        let c = copy_rational(&self.c);
        let s = self.s.neg();
        proof {
            lemma_unit_norm_raw(self.c@, self.s@);
            lemma_unit_norm_raw_neg_s(self.c@, self.s@);
            lemma_unit_norm_raw(c@, s@);
        }
        RotQ { c, s }
    }

    /// Rotation from a rational tan-half-angle t: ((1−t²)/(1+t²), 2t/(1+t²)).
    /// Exact and always on the unit circle (never divides by zero: 1+t² ≥ 1).
    pub fn from_tan_half(t: &Scalar) -> (out: RotQ)
        requires
            t.wf_spec(),
        ensures
            out.wf_spec(),
            out.c@ == Rational::from_int_spec(1).sub_spec(t@.mul_spec(t@)).div_spec(
                Rational::from_int_spec(1).add_spec(t@.mul_spec(t@))),
            out.s@ == Rational::from_int_spec(2).mul_spec(t@).div_spec(
                Rational::from_int_spec(1).add_spec(t@.mul_spec(t@))),
    {
        let one = RuntimeRational::from_int(1);
        let two = RuntimeRational::from_int(2);
        let tt = t.mul(t);
        let num = one.sub(&tt);
        let den = one.add(&tt);
        proof {
            // den ≉ 0: den.num == dd² + n² ≥ 1 (needed by RuntimeRational::div)
            Rational::lemma_denom_positive(t@);
            Rational::lemma_mul_denom_product_int(t@, t@);
            Rational::lemma_add_denom_product_int(
                Rational::from_int_spec(1), tt@);
            assert(tt@.num == t@.num * t@.num);
            assert(den@.num == Rational::from_int_spec(1).num * (tt@.denom_nat() as int)
                + tt@.num * (Rational::from_int_spec(1).denom_nat() as int));
            assert(Rational::from_int_spec(1).num == 1);
            assert(Rational::from_int_spec(1).denom_nat() == 1);
            assert(tt@.denom() == t@.denom() * t@.denom());
            assert((tt@.denom_nat() as int) == t@.denom() * t@.denom());
            crate::proofs::rational_raw::lemma_nla_sq_pos(t@.denom());
            crate::proofs::rational_raw::lemma_nla_nn_nonneg(t@.num);
            assert(den@.num >= 1);
            assert(den@.eqv_spec(Rational::from_int_spec(0)) == (
                den@.num * Rational::from_int_spec(0).denom()
                    == Rational::from_int_spec(0).num * den@.denom()));
            assert(Rational::from_int_spec(0).num == 0);
            assert(Rational::from_int_spec(0).denom() == 1);
            assert(den@.num >= 1 ==> !den@.eqv_spec(Rational::from_int_spec(0)))
                by (nonlinear_arith);
            assert(!den@.eqv_spec(Rational::from_int_spec(0)));
        }
        let c = num.div(&den);
        let two_t = two.mul(t);
        let s = two_t.div(&den);
        proof {
            lemma_unit_norm_raw_tan_half(t@);
            lemma_unit_norm_raw(c@, s@);
        }
        RotQ { c, s }
    }

    /// Apply the rotation to a vector: (c·vx − s·vy, s·vx + c·vy).
    pub fn apply(&self, v: &SVec2) -> (out: SVec2)
        requires
            self.wf_spec(),
            v.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.c@.mul_spec(v.model@.x).sub_spec(self.s@.mul_spec(v.model@.y)),
            out.model@.y == self.s@.mul_spec(v.model@.x).add_spec(self.c@.mul_spec(v.model@.y)),
    {
        let x = self.c.mul(&v.x).sub(&self.s.mul(&v.y));
        let y = self.s.mul(&v.x).add(&self.c.mul(&v.y));
        RuntimeVec2::new(x, y)
    }

    /// UNTRUSTED tan-half chooser for the integration step (SPEC §2):
    /// t ≈ tan(h) via the truncated series h + h³/3 + 2h⁵/15. No
    /// correctness claim — the angle ledger (phys-02b) encloses what was
    /// actually applied from the t this returns.
    pub fn tan_half_series(h: &Scalar) -> (out: Scalar)
        requires
            h.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == h@.add_spec(
                h@.mul_spec(h@).mul_spec(h@).mul_spec(Rational::from_frac_spec(1, 3)),
            ).add_spec(
                Rational::from_int_spec(2).mul_spec(
                    h@.mul_spec(h@).mul_spec(h@).mul_spec(h@).mul_spec(h@),
                ).mul_spec(Rational::from_frac_spec(1, 15)),
            ),
    {
        let h2 = h.mul(h);
        let h3 = h2.mul(h);
        let h4 = h3.mul(h);
        let h5 = h4.mul(h);
        let third = RuntimeRational::from_frac(1, 3);
        let two = RuntimeRational::from_int(2);
        let fifteenth = RuntimeRational::from_frac(1, 15);
        let t1 = h3.mul(&third);
        let t2 = two.mul(&h5).mul(&fifteenth);
        h.add(&t1).add(&t2)
    }
}

} // verus!

verus! {

/// 1·1 + 0·0 ≡ 1, by the ring axioms (no unfolding of Rational internals).
pub proof fn lemma_unit_norm_one_zero()
    ensures unit_norm(q_one(), q_zero())
{
    let one = q_one();
    let zero = q_zero();
    let a = q_mul(one, one);   // ≡ one
    let b = q_mul(zero, zero); // ≡ zero

    Rational::axiom_mul_one_right(one);       // a ≡ one
    Rational::axiom_mul_zero_right(zero);     // b ≡ zero

    // a + b ≡ one + b
    Rational::axiom_add_congruence_left(a, one, b);
    // one + b ≡ b + one ≡ zero + one ≡ one + zero ≡ one
    Rational::axiom_add_commutative(one, b);
    Rational::axiom_add_congruence_left(b, zero, one);
    Rational::axiom_add_commutative(zero, one);
    Rational::axiom_add_zero_right(one);

    // chain: a+b ≡ one+b ≡ b+one ≡ zero+one ≡ one+zero ≡ one
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(one, b), q_add(b, one));
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(b, one), q_add(zero, one));
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(zero, one), q_add(one, zero));
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(one, zero), one);
}

} // verus!
