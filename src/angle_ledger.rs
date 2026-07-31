//! Angle ledger spec + exec (phys-02b, SPEC §3, E2).
//!
//! For rational t with |t| ≤ 1, the arctan alternating-series partial sums
//!   A_k(t) = Σ_{j=0}^{k} (−1)ʲ · t^(2j+1)/(2j+1)
//! give self-bracketing enclosures of the applied angle 2·arctan(t):
//! consecutive partial sums bracket, with width exactly the next term.
//!
//! Verus's obligations here are PURE RATIONAL ARITHMETIC: the exact
//! endpoint values, the width formula, and monotone shrink in k. The
//! semantic claim "arctan(t) lies inside" is Lean card G0's business (E3).
//!
//! Proofs live in proofs/angle_ledger.rs (trigger hygiene).

use vstd::prelude::*;

use verus_rational::{Rational, RuntimeRational};

use crate::proofs::rpow::rpow;
use crate::types::Scalar;

verus! {

/// The j-th (unsigned) arctan term: t^(2j+1) / (2j+1).
pub open spec fn arctan_term(t: Rational, j: nat) -> Rational {
    rpow(t, 2 * j + 1).div_spec(Rational::from_int_spec((2 * j + 1) as int))
}

/// A_k(t): partial sum Σ_{j=0}^{k} (−1)ʲ · arctan_term(t, j).
pub open spec fn arctan_sum(t: Rational, k: nat) -> Rational
    decreases k
{
    if k == 0 {
        arctan_term(t, 0)
    } else if k % 2 == 0 {
        arctan_sum(t, (k - 1) as nat).add_spec(arctan_term(t, k))
    } else {
        arctan_sum(t, (k - 1) as nat).sub_spec(arctan_term(t, k))
    }
}

/// Doubling (the applied angle is 2·arctan(t)).
pub open spec fn two_x(x: Rational) -> Rational {
    Rational::from_int_spec(2).mul_spec(x)
}

/// The applied-angle enclosure at index k: [lo, hi] for 2·arctan(t),
/// ordered by the parity of k (even sums dominate odd sums for 0 ≤ t ≤ 1;
/// see proofs/angle_ledger.rs).
///
/// INTERNAL API (A9(g)): the standard entry point is
/// `angle_enclosure_signed`, which orders lo ≤ hi on the full symmetric
/// range [−1, 1]; this parity-ordered form remains only as the shared
/// unfolding target of the ledger lemmas. (It must stay `pub` because the
/// signed wrapper is an open spec fn — Verus treats open bodies as part
/// of the public interface.)
pub open spec fn angle_enclosure(t: Rational, k: nat) -> (Rational, Rational) {
    if k % 2 == 0 {
        (two_x(arctan_sum(t, k + 1)), two_x(arctan_sum(t, k)))
    } else {
        (two_x(arctan_sum(t, k)), two_x(arctan_sum(t, k + 1)))
    }
}

/// t is in [0, 1] (raw le_spec form). Phase 1 restricts the tan-half
/// parameter to this interval (SPEC §3; larger |t| needs the π/2 branch).
pub open spec fn t_in_unit_interval(t: Rational) -> bool {
    &&& Rational::from_int_spec(0).le_spec(t)
    &&& t.le_spec(Rational::from_int_spec(1))
}

/// t is in [−1, 1] — the full phase-1 symmetric range (SPEC §3 restricts
/// |ω·dt/2| so that |t| ≤ 1; reject-step otherwise).
pub open spec fn t_in_symmetric_unit_interval(t: Rational) -> bool {
    &&& Rational::from_int_spec(-1).le_spec(t)
    &&& t.le_spec(Rational::from_int_spec(1))
}

/// The signed enclosure: endpoints ordered lo ≤ hi for the sign of t.
/// For 0 ≤ t this is angle_enclosure; for t < 0 the endpoints swap
/// (the series is odd — see the mirror section of proofs/angle_ledger.rs).
pub open spec fn angle_enclosure_signed(t: Rational, k: nat) -> (Rational, Rational) {
    if Rational::from_int_spec(0).le_spec(t) {
        angle_enclosure(t, k)
    } else {
        (angle_enclosure(t, k).1, angle_enclosure(t, k).0)
    }
}

} // verus!

verus! {

/// Exact evaluator for arctan_term(t@, j): t^(2j+1) / (2j+1).
pub fn arctan_term_exec(t: &Scalar, j: usize) -> (out: Scalar)
    requires
        t.wf_spec(),
        j <= 1_000_000,
    ensures
        out.wf_spec(),
        out@ == arctan_term(t@, j as nat),
{
    let p: usize = 2 * j + 1;
    let mut rp = RuntimeRational::from_int(1);
    let mut i: usize = 0;
    while i < p
        invariant
            i <= p,
            p == 2 * j + 1,
            t.wf_spec(),
            rp.wf_spec(),
            rp@ == rpow(t@, i as nat),
        decreases p - i,
    {
        rp = rp.mul(t);
        proof {
            assert(rpow(t@, (i + 1) as nat) == t@.mul_spec(rpow(t@, i as nat))) by {
                reveal_with_fuel(rpow, 2);
            }
        }
        i = i + 1;
    }
    let d = RuntimeRational::from_int((2 * j + 1) as i64);
    proof {
        assert(d@ == Rational::from_int_spec((2 * j + 1) as int));
        assert(d@.num == (2 * j + 1) as int);
        assert(d@.num >= 1);
        assert(d@.eqv_spec(Rational::from_int_spec(0)) == (
            d@.num * Rational::from_int_spec(0).denom()
                == Rational::from_int_spec(0).num * d@.denom()));
        assert(Rational::from_int_spec(0).num == 0);
        assert(Rational::from_int_spec(0).denom() == 1);
        assert(d@.num >= 1 ==> !d@.eqv_spec(Rational::from_int_spec(0))) by (nonlinear_arith);
        assert(!d@.eqv_spec(Rational::from_int_spec(0)));
    }
    rp.div(&d)
}

/// Exact evaluator for arctan_sum(t@, k).
pub fn arctan_sum_exec(t: &Scalar, k: usize) -> (out: Scalar)
    requires
        t.wf_spec(),
        k <= 1_000_000,
    ensures
        out.wf_spec(),
        out@ == arctan_sum(t@, k as nat),
{
    let mut out = arctan_term_exec(t, 0);
    let mut j: usize = 1;
    while j <= k
        invariant
            1 <= j <= k + 1,
            k <= 1_000_000,
            t.wf_spec(),
            out.wf_spec(),
            out@ == arctan_sum(t@, (j - 1) as nat),
        decreases k + 1 - j,
    {
        let term = arctan_term_exec(t, j);
        if j % 2 == 0 {
            out = out.add(&term);
            proof {
                crate::proofs::angle_ledger::lemma_arctan_step_even(t@, j as nat);
            }
        } else {
            out = out.sub(&term);
            proof {
                crate::proofs::angle_ledger::lemma_arctan_step_odd(t@, j as nat);
            }
        }
        j = j + 1;
    }
    out
}

/// Exact evaluator for angle_enclosure_signed(t@, k) — the standard
/// enclosure API (A9(g)) — with the lo ≤ hi guarantee on the full
/// symmetric phase-1 range t ∈ [−1, 1] (SPEC §3).
pub fn angle_enclosure_exec(t: &Scalar, k: usize) -> (out: (Scalar, Scalar))
    requires
        t.wf_spec(),
        t_in_symmetric_unit_interval(t@),
        k < 1_000_000,
    ensures
        out.0.wf_spec(),
        out.1.wf_spec(),
        out.0@ == angle_enclosure_signed(t@, k as nat).0,
        out.1@ == angle_enclosure_signed(t@, k as nat).1,
        out.0@.le_spec(out.1@),
{
    let ak = arctan_sum_exec(t, k);
    let ak1 = arctan_sum_exec(t, k + 1);
    let two = RuntimeRational::from_int(2);
    let ak2 = two.mul(&ak);
    let ak12 = two.mul(&ak1);
    let zero = RuntimeRational::from_int(0);
    let nonneg = zero.le(&t);
    proof {
        crate::proofs::angle_ledger::lemma_angle_enclosure_signed_ordered(t@, k as nat);
    }
    if nonneg {
        proof {
            // 0 ≤ t: the signed enclosure IS the parity-ordered one.
            assert(angle_enclosure_signed(t@, k as nat) == angle_enclosure(t@, k as nat));
        }
        if k % 2 == 0 {
            (ak12, ak2)
        } else {
            (ak2, ak12)
        }
    } else {
        proof {
            // t < 0: the signed enclosure swaps the parity-ordered endpoints.
            assert(angle_enclosure_signed(t@, k as nat).0 == angle_enclosure(t@, k as nat).1);
            assert(angle_enclosure_signed(t@, k as nat).1 == angle_enclosure(t@, k as nat).0);
        }
        if k % 2 == 0 {
            (ak2, ak12)
        } else {
            (ak12, ak2)
        }
    }
}

} // verus!

