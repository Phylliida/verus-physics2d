//! Scalar and vector type aliases + tiny ordering helpers (SPEC §1).
//!
//! Exec scalar: RuntimeRational (bigint-backed exact rational, ghost model
//! Rational). Exec vector: RuntimeVec2<RuntimeRational, Rational>.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_rational::{Rational, RuntimeRational};

verus! {

/// Exec-level exact scalar.
pub type Scalar = RuntimeRational;

/// Exec-level exact 2D vector (ghost model Vec2<Rational>).
pub type SVec2 = RuntimeVec2<RuntimeRational, Rational>;

// ── Qualified spec aliases ─────────────────────────────────────────────
// Rational carries inherent PROOF fns named zero/one/add/mul (witness
// constructors), which shadow the trait spec fns under plain method-call
// syntax in spec mode. These aliases pin the trait spec ops once; all
// engine specs use q_* forms.

pub open spec fn q_zero() -> Rational {
    <Rational as AdditiveCommutativeMonoid>::zero()
}

pub open spec fn q_one() -> Rational {
    <Rational as Ring>::one()
}

pub open spec fn q_add(a: Rational, b: Rational) -> Rational {
    <Rational as AdditiveCommutativeMonoid>::add(a, b)
}

pub open spec fn q_mul(a: Rational, b: Rational) -> Rational {
    <Rational as Ring>::mul(a, b)
}

pub open spec fn q_sub(a: Rational, b: Rational) -> Rational {
    <Rational as AdditiveGroup>::sub(a, b)
}

pub open spec fn q_neg(a: Rational) -> Rational {
    <Rational as AdditiveGroup>::neg(a)
}

pub open spec fn q_eqv(a: Rational, b: Rational) -> bool {
    <Rational as Equivalence>::eqv(a, b)
}

pub open spec fn q_le(a: Rational, b: Rational) -> bool {
    <Rational as PartialOrder>::le(a, b)
}

pub open spec fn q_lt(a: Rational, b: Rational) -> bool {
    <Rational as OrderedRing>::lt(a, b)
}

/// x ≥ 0 at the spec level (OrderedRing order on Rational).
pub open spec fn q_nonneg(x: Rational) -> bool {
    q_le(q_zero(), x)
}

/// Deep copy of an SVec2 (BigInt witnesses aren't Copy).
pub fn copy_svec2(v: &SVec2) -> (out: SVec2)
    requires
        v.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == v.model@,
{
    let x = verus_rational::runtime_rational::copy_rational(&v.x);
    let y = verus_rational::runtime_rational::copy_rational(&v.y);
    RuntimeVec2::new(x, y)
}

/// x > 0 at the spec level.
pub open spec fn q_pos(x: Rational) -> bool {
    q_lt(q_zero(), x)
}

/// 0 ≤ 0 in the OrderedRing order (used by static-body constructors).
pub proof fn lemma_zero_nonneg()
    ensures q_nonneg(Rational::from_int_spec(0))
{
    let zero = q_zero();
    Rational::axiom_eqv_reflexive(zero);
    Rational::axiom_le_total(zero, Rational::from_int_spec(0));
}

} // verus!

// phys-02 design note (supersedes earlier real-valued probes): real-valued
// by(nonlinear_arith) diverges Z3 in this toolchain — both the division
// probe and the pure-polynomial compose-identity probe hung (>15 min).
// Strategy instead: eqv_spec goals unfold to INTEGER cross-multiplication
// polynomial identities (see Rational::eqv_spec/add_spec/mul_spec), which
// by(nonlinear_arith) on int handles. Bridge from trait ops (canonicalized)
// to raw *_spec forms via Rational::lemma_canonical_exists + the
// lemma_eqv_*_congruence lemmas in verus-rational.
