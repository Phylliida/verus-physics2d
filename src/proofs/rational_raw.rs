//! Bridge between the trait-op `unit_norm` statement (canonicalized Ring
//! ops) and raw `*_spec` Rational ops, plus raw unit-norm lemmas proved by
//! integer cross-multiplication + `nonlinear_arith`.
//!
//! Why this file exists: the trait ops on Rational are
//! `*_spec(...).canonical()` (choose-based normalization, see
//! verus-rational/src/rational/algebra.rs), so algebraic identities about
//! them do not unfold. The raw `*_spec` ops unfold to integer polynomial
//! formulas in num/den, and `eqv_spec` IS integer cross-multiplication.
//!
//! Proof discipline (established empirically in this crate, see git
//! history; each rule was learned from a failure):
//!  - R1. Real-valued nonlinear_arith DIVERGES Z3 here. Integers only.
//!  - R2. Z3 auto-unfolds open spec fns only ~1 level via triggers. Every
//!    node is let-bound and given an explicit one-level unfold assert in
//!    the EXACT body form (`x.denom_nat() as int`, not `x.denom()`).
//!  - R3. `by(nonlinear_arith)` does NOT pick up prior local asserts.
//!    Nonlinear steps either call an int-only micro-lemma (minimal
//!    context, nlsat succeeds) or restate their hypotheses as an
//!    implication inside the assert.
//!  - R4. NLA identities beyond ~2-3 atoms rlimit nlsat (e.g. the 4-var
//!    Lagrange identity as one step). Decompose into binom/sq_mul/prod4
//!    micro-steps and finish with congruence chaining.
//!  - R5. Closed (fully concrete) goals: state them FIRST, before
//!    asserting intermediate facts — extra facts can poison the
//!    simplifier's reduction of closed terms.

use vstd::prelude::*;

use verus_rational::Rational;

use crate::angle_ledger::two_x;
use crate::rotq::unit_norm;
use crate::types::{q_add, q_eqv, q_mul, q_neg, q_one, q_sub};

verus! {

/// q_mul by a zero-equivalent is ≡ 0 (canonical + raw chain, packaged).
pub proof fn lemma_q_mul_zero_right_raw(a: Rational, z: Rational)
    requires
        z.eqv_spec(Rational::from_int_spec(0)),
    ensures
        q_eqv(q_mul(a, z), Rational::from_int_spec(0)),
{
    let zero = Rational::from_int_spec(0);
    lemma_q_mul_raw(a, z);
    Rational::lemma_eqv_reflexive(a);
    Rational::lemma_eqv_mul_congruence(a, a, z, zero);
    Rational::lemma_mul_zero(a);
    Rational::lemma_eqv_transitive(a.mul_spec(z), a.mul_spec(zero), zero);
    Rational::lemma_eqv_transitive(q_mul(a, z), a.mul_spec(z), zero);
}

/// q_add of a zero-equivalent on the right is identity (packaged).
pub proof fn lemma_q_add_zero_right_raw(x: Rational, z: Rational)
    requires
        z.eqv_spec(Rational::from_int_spec(0)),
    ensures
        q_eqv(q_add(x, z), x),
{
    let zero = Rational::from_int_spec(0);
    lemma_q_add_raw(x, z);
    Rational::lemma_eqv_reflexive(x);
    Rational::lemma_eqv_add_congruence(x, x, z, zero);
    lemma_raw_add_zero_right(x);
    Rational::lemma_eqv_transitive(q_add(x, z), x.add_spec(z), x.add_spec(zero));
    Rational::lemma_eqv_transitive(q_add(x, z), x.add_spec(zero), x);
}

// ════════════════════════════════════════════════════════════════════
// trait-op -> raw bridges (one-liners via canonical_exists)
// ════════════════════════════════════════════════════════════════════

pub proof fn lemma_q_add_raw(a: Rational, b: Rational)
    ensures
        q_eqv(q_add(a, b), a.add_spec(b)),
{
    Rational::lemma_canonical_exists(a.add_spec(b));
}

pub proof fn lemma_q_mul_raw(a: Rational, b: Rational)
    ensures
        q_eqv(q_mul(a, b), a.mul_spec(b)),
{
    Rational::lemma_canonical_exists(a.mul_spec(b));
}

pub proof fn lemma_q_sub_raw(a: Rational, b: Rational)
    ensures
        q_eqv(q_sub(a, b), a.sub_spec(b)),
{
    Rational::lemma_canonical_exists(a.sub_spec(b));
}

pub proof fn lemma_q_neg_raw(a: Rational)
    ensures
        q_eqv(q_neg(a), a.neg_spec()),
{
    Rational::lemma_canonical_exists(a.neg_spec());
}

/// raw: 0·x ≡ 0
pub proof fn lemma_raw_mul_zero_left(x: Rational)
    ensures
        Rational::from_int_spec(0).mul_spec(x).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    let p = z.mul_spec(x);
    Rational::lemma_mul_denom_product_int(z, x);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(p.num == z.num * x.num);
    assert(p.eqv_spec(z) == (p.num * z.denom() == z.num * p.denom()));
}

/// raw: x + 0 ≡ x
pub proof fn lemma_raw_add_zero_right(x: Rational)
    ensures
        x.add_spec(Rational::from_int_spec(0)).eqv_spec(x),
{
    let z = Rational::from_int_spec(0);
    let s = x.add_spec(z);
    Rational::lemma_add_denom_product_int(x, z);
    Rational::lemma_denom_positive(x);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(s.num == x.num * z.denom() + z.num * x.denom());
    assert(s.denom() == x.denom() * z.denom());
    assert(s.eqv_spec(x) == (s.num * x.denom() == x.num * s.denom()));
    vstd::arithmetic::mul::lemma_mul_basics(x.num);
    vstd::arithmetic::mul::lemma_mul_basics(x.denom());
}

/// raw: (−a)·b == −(a·b) (structural).
pub proof fn lemma_raw_neg_mul_left(a: Rational, b: Rational)
    ensures
        a.neg_spec().mul_spec(b) == a.mul_spec(b).neg_spec(),
{
    Rational::lemma_mul_denom_product_int(a.neg_spec(), b);
    Rational::lemma_mul_denom_product_int(a, b);
    let lhs = a.neg_spec().mul_spec(b);
    let rhs = a.mul_spec(b).neg_spec();
    assert(a.neg_spec().num == -a.num);
    assert(a.neg_spec().denom() == a.denom());
    assert(lhs.num == a.neg_spec().num * b.num);
    assert(rhs.num == -(a.num * b.num));
    assert((lhs.num == a.neg_spec().num * b.num && a.neg_spec().num == -a.num
        && rhs.num == -(a.num * b.num))
        ==> lhs.num == rhs.num) by (nonlinear_arith);
    assert(lhs.denom() == rhs.denom());
    assert(lhs.den == rhs.den);
    assert(lhs == rhs);
}

/// raw: a·(−b) == −(a·b) (structural).
pub proof fn lemma_raw_neg_mul_right(a: Rational, b: Rational)
    ensures
        a.mul_spec(b.neg_spec()) == a.mul_spec(b).neg_spec(),
{
    Rational::lemma_mul_denom_product_int(a, b.neg_spec());
    Rational::lemma_mul_denom_product_int(a, b);
    let lhs = a.mul_spec(b.neg_spec());
    let rhs = a.mul_spec(b).neg_spec();
    assert(b.neg_spec().num == -b.num);
    assert(b.neg_spec().denom() == b.denom());
    assert(lhs.num == a.num * b.neg_spec().num);
    assert(rhs.num == -(a.num * b.num));
    assert((lhs.num == a.num * b.neg_spec().num && b.neg_spec().num == -b.num
        && rhs.num == -(a.num * b.num))
        ==> lhs.num == rhs.num) by (nonlinear_arith);
    assert(lhs.denom() == rhs.denom());
    assert(lhs.den == rhs.den);
    assert(lhs == rhs);
}

/// raw: (−a)·(−b) == a·b (structural).
pub proof fn lemma_raw_neg_mul_neg(a: Rational, b: Rational)
    ensures
        a.neg_spec().mul_spec(b.neg_spec()) == a.mul_spec(b),
{
    lemma_raw_neg_mul_left(a, b.neg_spec());
    lemma_raw_neg_mul_right(a, b);
    Rational::lemma_neg_involution(a.mul_spec(b));
    assert(a.neg_spec().mul_spec(b.neg_spec()) == a.mul_spec(b.neg_spec()).neg_spec());
    assert(a.mul_spec(b.neg_spec()).neg_spec() == a.mul_spec(b).neg_spec().neg_spec());
}

/// raw: congruence of abs nonneg — |x| ≥ 0
pub proof fn lemma_raw_abs_nonneg(x: Rational)
    ensures
        Rational::from_int_spec(0).le_spec(x.abs_spec()),
{
    let z = Rational::from_int_spec(0);
    let a = x.abs_spec();
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(a) == (z.num * a.denom() <= a.num * z.denom()));
    if x.num >= 0 {
        assert(a == x);
    } else {
        assert(a == x.neg_spec());
        assert(a.num == -x.num);
    }
}

/// raw: 0 ≤ x ⇒ 0 ≤ 2·x
pub proof fn lemma_raw_two_nonneg(x: Rational)
    requires
        Rational::from_int_spec(0).le_spec(x),
    ensures
        Rational::from_int_spec(0).le_spec(two_x(x)),
{
    let z = Rational::from_int_spec(0);
    let two = Rational::from_int_spec(2);
    let tx = two_x(x);
    Rational::lemma_mul_denom_product_int(two, x);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(two.num == 2);
    assert(two.denom() == 1);
    assert(tx.num == two.num * x.num);
    assert(z.le_spec(x) == (z.num * x.denom() <= x.num * z.denom()));
    assert(z.le_spec(tx) == (z.num * tx.denom() <= tx.num * z.denom()));
    assert((z.num * x.denom() <= x.num * z.denom() && z.num == 0 && z.denom() == 1)
        ==> x.num >= 0) by (nonlinear_arith);
    assert((x.num >= 0 && tx.num == two.num * x.num && two.num == 2 && z.num == 0)
        ==> z.num * tx.denom() <= tx.num * z.denom()) by (nonlinear_arith);
}

/// raw: 0 ≤ a ∧ 0 ≤ b ⇒ 0 ≤ a + b
pub proof fn lemma_raw_add_nonneg(a: Rational, b: Rational)
    requires
        Rational::from_int_spec(0).le_spec(a),
        Rational::from_int_spec(0).le_spec(b),
    ensures
        Rational::from_int_spec(0).le_spec(a.add_spec(b)),
{
    Rational::lemma_le_add_monotone(Rational::from_int_spec(0), a, b);
    // 0 + b ≤ a + b; 0 + b ≡ b
    let z = Rational::from_int_spec(0);
    let s = z.add_spec(b);
    Rational::lemma_add_denom_product_int(z, b);
    Rational::lemma_denom_positive(b);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(s.num == z.num * b.denom() + b.num * z.denom());
    assert(s.denom() == z.denom() * b.denom());
    assert(s.eqv_spec(b) == (s.num * b.denom() == b.num * s.denom()));
    vstd::arithmetic::mul::lemma_mul_basics(b.num);
    vstd::arithmetic::mul::lemma_mul_basics(b.denom());
    assert((b.denom() >= 1 && s.num == b.num && s.denom() == b.denom())
        ==> s.num * b.denom() == b.num * s.denom()) by (nonlinear_arith);
    Rational::lemma_eqv_implies_le(b, s);
    Rational::lemma_eqv_symmetric(s, b);
    Rational::lemma_le_transitive(z, s, a.add_spec(b));
}

// ════════════════════════════════════════════════════════════════════
// int-only NLA micro-lemmas (R3/R4: minimal context, small identities)
// ════════════════════════════════════════════════════════════════════

pub proof fn lemma_nla_neg_square(x: int)
    ensures (-x) * (-x) == x * x,
{
    assert((-x) * (-x) == x * x) by (nonlinear_arith);
}

pub proof fn lemma_nla_binom_sub(x: int, y: int)
    ensures (x - y) * (x - y) == x * x - 2 * (x * y) + y * y,
{
    assert((x - y) * (x - y) == x * x - 2 * (x * y) + y * y) by (nonlinear_arith);
}

pub proof fn lemma_nla_binom_add(x: int, y: int)
    ensures (x + y) * (x + y) == x * x + 2 * (x * y) + y * y,
{
    assert((x + y) * (x + y) == x * x + 2 * (x * y) + y * y) by (nonlinear_arith);
}

pub proof fn lemma_nla_sq_mul(x: int, y: int)
    ensures (x * y) * (x * y) == (x * x) * (y * y),
{
    assert((x * y) * (x * y) == (x * x) * (y * y)) by (nonlinear_arith);
}

pub proof fn lemma_nla_prod4(a: int, b: int, c: int, d: int)
    ensures (a * b) * (c * d) == a * b * c * d,
{
    assert((a * b) * (c * d) == a * b * c * d) by (nonlinear_arith);
}

pub proof fn lemma_nla_prod4_swap(a: int, b: int, c: int, d: int)
    ensures (a * b) * (c * d) == (a * c) * (b * d),
{
    assert((a * b) * (c * d) == (a * c) * (b * d)) by (nonlinear_arith);
}

pub proof fn lemma_nla_distrib2(x: int, y: int, u: int, v: int)
    ensures (x + y) * (u + v) == x * u + x * v + y * u + y * v,
{
    assert((x + y) * (u + v) == x * u + x * v + y * u + y * v) by (nonlinear_arith);
}

pub proof fn lemma_nla_factor(x: int, y: int, k: int)
    ensures x * k + y * k == (x + y) * k,
{
    assert(x * k + y * k == (x + y) * k) by (nonlinear_arith);
}

pub proof fn lemma_nla_tanhalf(n: int, dd: int)
    ensures
        (dd * dd - n * n) * (dd * dd - n * n) + 4 * (n * n) * (dd * dd)
            == (dd * dd + n * n) * (dd * dd + n * n),
{
    assert((dd * dd - n * n) * (dd * dd - n * n) + 4 * (n * n) * (dd * dd)
        == (dd * dd + n * n) * (dd * dd + n * n)) by (nonlinear_arith);
}

pub proof fn lemma_nla_sq_pos(x: int)
    requires x >= 1,
    ensures x * x >= 1,
{
    assert(x >= 1 ==> x * x >= 1) by (nonlinear_arith);
}

pub proof fn lemma_nla_nn_nonneg(x: int)
    ensures x * x >= 0,
{
    assert(x * x >= 0) by (nonlinear_arith);
}

pub proof fn lemma_nla_shuf4(a: int, b: int, c: int, d: int)
    ensures a * b * c * d == (a * c) * (b * d),
{
    assert(a * b * c * d == (a * c) * (b * d)) by (nonlinear_arith);
}

pub proof fn lemma_nla_comm4(a: int, b: int, c: int, d: int)
    ensures b * c * a * d == a * b * c * d,
{
    assert(b * c * a * d == a * b * c * d) by (nonlinear_arith);
}

pub proof fn lemma_nla_mid4(a: int, b: int, c: int, d: int)
    ensures a * c * b * d == a * b * c * d,
{
    assert(a * c * b * d == a * b * c * d) by (nonlinear_arith);
}

pub proof fn lemma_nla_2nu_sq(n: int, u: int)
    ensures (2 * n * u) * (2 * n * u) == 4 * (n * n) * (u * u),
{
    assert((2 * n * u) * (2 * n * u) == 4 * (n * n) * (u * u)) by (nonlinear_arith);
}

// ════════════════════════════════════════════════════════════════════
// unit_norm_raw + bridge
// ════════════════════════════════════════════════════════════════════

/// unit_norm restated on RAW spec ops (no canonicalization).
pub open spec fn unit_norm_raw(c: Rational, s: Rational) -> bool {
    c.mul_spec(c).add_spec(s.mul_spec(s)).eqv_spec(Rational::from_int_spec(1))
}

/// The trait-op statement and the raw statement coincide.
pub proof fn lemma_unit_norm_raw(c: Rational, s: Rational)
    ensures
        unit_norm(c, s) == unit_norm_raw(c, s),
{
    let mcc = c.mul_spec(c);
    let mss = s.mul_spec(s);
    let raw = mcc.add_spec(mss);
    let one = Rational::from_int_spec(1);

    // q_mul(c, c) ≡ mcc and q_mul(s, s) ≡ mss (canonical preserves eqv).
    Rational::lemma_canonical_exists(mcc);
    Rational::lemma_canonical_exists(mss);
    assert(q_eqv(q_mul(c, c), mcc));
    assert(q_eqv(q_mul(s, s), mss));

    // raw add-congruence, then canonical on the outer add:
    // qexpr ≡ q_mul(c,c).add_spec(q_mul(s,s)) ≡ raw.
    Rational::lemma_eqv_add_congruence(q_mul(c, c), mcc, q_mul(s, s), mss);
    Rational::lemma_canonical_exists(q_mul(c, c).add_spec(q_mul(s, s)));
    let qexpr = q_add(q_mul(c, c), q_mul(s, s));
    Rational::lemma_eqv_transitive(qexpr, q_mul(c, c).add_spec(q_mul(s, s)), raw);

    // qexpr ≡ raw; transfer eqv-to-one in both directions.
    if qexpr.eqv_spec(one) {
        Rational::lemma_eqv_symmetric(qexpr, raw);
        Rational::lemma_eqv_transitive(raw, qexpr, one);
    } else if raw.eqv_spec(one) {
        Rational::lemma_eqv_transitive(qexpr, raw, one);
        assert(false);
    }
}

// ════════════════════════════════════════════════════════════════════
// raw unit-norm lemmas
// ════════════════════════════════════════════════════════════════════

/// 1·1 + 0·0 ≡ 1, raw form. (Robust form: implication combination, R3.)
pub proof fn lemma_unit_norm_raw_one_zero()
    ensures
        unit_norm_raw(Rational::from_int_spec(1), Rational::from_int_spec(0)),
{
    let one = Rational::from_int_spec(1);
    let zero = Rational::from_int_spec(0);
    let m1 = one.mul_spec(one);
    let m2 = zero.mul_spec(zero);
    let s = m1.add_spec(m2);
    Rational::lemma_add_denom_product_int(m1, m2);
    assert(m1.num == 1);
    assert(m2.num == 0);
    assert((m1.denom_nat() as int) == 1);
    assert((m2.denom_nat() as int) == 1);
    assert(m1.denom() == 1);
    assert(m2.denom() == 1);
    assert(s.num == m1.num * (m2.denom_nat() as int) + m2.num * (m1.denom_nat() as int));
    assert((m1.num == 1 && m2.num == 0
        && (m1.denom_nat() as int) == 1 && (m2.denom_nat() as int) == 1
        && s.num == m1.num * (m2.denom_nat() as int) + m2.num * (m1.denom_nat() as int))
        ==> s.num == 1) by (nonlinear_arith);
    assert(s.num == 1);
    assert(s.denom() == m1.denom() * m2.denom());
    assert(s.denom() == 1);
    assert(s.eqv_spec(one));
    assert(unit_norm_raw(one, zero));
}

/// Negating s preserves the unit norm (sign vanishes in the square).
pub proof fn lemma_unit_norm_raw_neg_s(c: Rational, s: Rational)
    requires
        unit_norm_raw(c, s),
    ensures
        unit_norm_raw(c, s.neg_spec()),
{
    let one = Rational::from_int_spec(1);
    let ns = s.neg_spec();
    let mcc = c.mul_spec(c);
    let mss = s.mul_spec(s);
    let mnn = ns.mul_spec(ns);
    let lhs = mcc.add_spec(mss);
    let rhs = mcc.add_spec(mnn);

    // 1-level unfolds, exact body forms (R2)
    assert(ns.num == -s.num);
    assert(ns.denom_nat() == s.denom_nat());
    assert(mcc.num == c.num * c.num);
    assert(mss.num == s.num * s.num);
    assert(mnn.num == ns.num * ns.num);
    assert(lhs.num == mcc.num * (mss.denom_nat() as int) + mss.num * (mcc.denom_nat() as int));
    assert(rhs.num == mcc.num * (mnn.denom_nat() as int) + mnn.num * (mcc.denom_nat() as int));

    // denominators via product lemmas
    Rational::lemma_mul_denom_product_int(s, s);
    Rational::lemma_mul_denom_product_int(ns, ns);
    Rational::lemma_add_denom_product_int(mcc, mss);
    Rational::lemma_add_denom_product_int(mcc, mnn);
    assert(mss.denom() == mnn.denom());
    assert(rhs.denom_nat() == lhs.denom_nat());

    // genuine nonlinearity via int micro-lemma (R3)
    lemma_nla_neg_square(s.num);
    assert(mnn.num == mss.num);
    assert(rhs.num == lhs.num);

    // hypothesis unfolds (R2: 1 level each)
    assert(lhs.eqv_spec(one));
    assert(lhs.num * one.denom() == one.num * lhs.denom());
    assert(one.num == 1);
    assert(one.denom() == 1);

    // goal folds
    assert(rhs.num * one.denom() == one.num * rhs.denom());
    assert(rhs.eqv_spec(one));
    assert(unit_norm_raw(c, ns));
}

/// The composed c/s coordinates of two rotations (angle-sum formulas).
pub open spec fn compose_c(ac: Rational, asn: Rational, bc: Rational, bs: Rational) -> Rational {
    ac.mul_spec(bc).sub_spec(asn.mul_spec(bs))
}

pub open spec fn compose_s(ac: Rational, asn: Rational, bc: Rational, bs: Rational) -> Rational {
    asn.mul_spec(bc).add_spec(ac.mul_spec(bs))
}

/// Lagrange's identity in the form compose needs, int-only (clean nlsat
/// context). Given A² + B² == U² and C² + E² == V²,
///   (A·C − B·E)² + (B·C + A·E)² == (U·V)².
proof fn lemma_lagrange_combined(A: int, B: int, C: int, E: int, U: int, V: int)
    requires
        A * A + B * B == U * U,
        C * C + E * E == V * V,
    ensures
        (A * C - B * E) * (A * C - B * E) + (B * C + A * E) * (B * C + A * E)
            == (U * V) * (U * V),
{
    lemma_nla_binom_sub(A * C, B * E);
    lemma_nla_binom_add(B * C, A * E);
    lemma_nla_sq_mul(A, C);
    lemma_nla_sq_mul(B, E);
    lemma_nla_sq_mul(B, C);
    lemma_nla_sq_mul(A, E);
    lemma_nla_prod4(A, A, C, C);
    lemma_nla_prod4(B, B, E, E);
    lemma_nla_prod4(B, B, C, C);
    lemma_nla_prod4(A, A, E, E);
    lemma_nla_prod4(A, C, B, E);
    lemma_nla_mid4(A, B, C, E);
    lemma_nla_prod4(B, C, A, E);
    lemma_nla_comm4(A, B, C, E);
    lemma_nla_distrib2(A * A, B * B, C * C, E * E);
    // (every antecedent conjunct is a VERBATIM lemma-call postcondition —
    // derived chains make the modus-ponens step fail, R3)
    assert(((A * C - B * E) * (A * C - B * E)
            == (A * C) * (A * C) - 2 * ((A * C) * (B * E)) + (B * E) * (B * E)
        && (B * C + A * E) * (B * C + A * E)
            == (B * C) * (B * C) + 2 * ((B * C) * (A * E)) + (A * E) * (A * E)
        && (A * C) * (A * C) == (A * A) * (C * C)
        && (A * A) * (C * C) == A * A * C * C
        && (B * E) * (B * E) == (B * B) * (E * E)
        && (B * B) * (E * E) == B * B * E * E
        && (B * C) * (B * C) == (B * B) * (C * C)
        && (B * B) * (C * C) == B * B * C * C
        && (A * E) * (A * E) == (A * A) * (E * E)
        && (A * A) * (E * E) == A * A * E * E
        && (A * C) * (B * E) == A * C * B * E
        && A * C * B * E == A * B * C * E
        && (B * C) * (A * E) == B * C * A * E
        && B * C * A * E == A * B * C * E
        && (A * A + B * B) * (C * C + E * E)
            == (A * A) * (C * C) + (A * A) * (E * E) + (B * B) * (C * C) + (B * B) * (E * E))
        ==> (A * C - B * E) * (A * C - B * E) + (B * C + A * E) * (B * C + A * E)
            == (A * A + B * B) * (C * C + E * E))
        by (nonlinear_arith);
    // restate each antecedent conjunct verbatim so MP is purely propositional
    assert((A * C - B * E) * (A * C - B * E)
        == (A * C) * (A * C) - 2 * ((A * C) * (B * E)) + (B * E) * (B * E));
    assert((B * C + A * E) * (B * C + A * E)
        == (B * C) * (B * C) + 2 * ((B * C) * (A * E)) + (A * E) * (A * E));
    assert((A * C) * (A * C) == (A * A) * (C * C));
    assert((A * A) * (C * C) == A * A * C * C);
    assert((B * E) * (B * E) == (B * B) * (E * E));
    assert((B * B) * (E * E) == B * B * E * E);
    assert((B * C) * (B * C) == (B * B) * (C * C));
    assert((B * B) * (C * C) == B * B * C * C);
    assert((A * E) * (A * E) == (A * A) * (E * E));
    assert((A * A) * (E * E) == A * A * E * E);
    assert((A * C) * (B * E) == A * C * B * E);
    assert(A * C * B * E == A * B * C * E);
    assert((B * C) * (A * E) == B * C * A * E);
    assert(B * C * A * E == A * B * C * E);
    assert((A * A + B * B) * (C * C + E * E)
        == (A * A) * (C * C) + (A * A) * (E * E) + (B * B) * (C * C) + (B * B) * (E * E));
    assert((A * C - B * E) * (A * C - B * E) + (B * C + A * E) * (B * C + A * E)
        == (A * A + B * B) * (C * C + E * E));
    // (A²+B²)(C²+E²) == (U·U)·(V·V) == (U·V)²
    lemma_nla_sq_mul(U, V);
    assert((A * A + B * B) * (C * C + E * E) == (U * U) * (V * V));
    assert((U * U) * (V * V) == (U * V) * (U * V));
}

/// Value facts for the composed coordinates: numerators are A·C − B·E and
/// B·C + A·E over the common denominator D = (da·dax)·(db·dbx), and the
/// hypotheses in A/B/C/E form. (All the Rational-node staging for compose
/// lives here so each proof function stays small, R-discipline.)
proof fn lemma_compose_values(ac: Rational, asn: Rational, bc: Rational, bs: Rational)
    requires
        unit_norm_raw(ac, asn),
        unit_norm_raw(bc, bs),
    ensures
        compose_c(ac, asn, bc, bs).num
            == (ac.num * asn.denom()) * (bc.num * bs.denom())
                - (asn.num * ac.denom()) * (bs.num * bc.denom()),
        compose_c(ac, asn, bc, bs).denom()
            == (ac.denom() * asn.denom()) * (bc.denom() * bs.denom()),
        compose_s(ac, asn, bc, bs).num
            == (asn.num * ac.denom()) * (bc.num * bs.denom())
                + (ac.num * asn.denom()) * (bs.num * bc.denom()),
        compose_s(ac, asn, bc, bs).denom()
            == (ac.denom() * asn.denom()) * (bc.denom() * bs.denom()),
        (ac.num * asn.denom()) * (ac.num * asn.denom())
            + (asn.num * ac.denom()) * (asn.num * ac.denom())
            == (ac.denom() * asn.denom()) * (ac.denom() * asn.denom()),
        (bc.num * bs.denom()) * (bc.num * bs.denom())
            + (bs.num * bc.denom()) * (bs.num * bc.denom())
            == (bc.denom() * bs.denom()) * (bc.denom() * bs.denom()),
{
    let one = Rational::from_int_spec(1);
    let ghost da = ac.denom();
    let ghost dax = asn.denom();
    let ghost db = bc.denom();
    let ghost dbx = bs.denom();

    // nodes
    let mac = ac.mul_spec(ac);
    let mas = asn.mul_spec(asn);
    let mbc2 = bc.mul_spec(bc);
    let mbs2 = bs.mul_spec(bs);
    let sum_a = mac.add_spec(mas);
    let sum_b = mbc2.add_spec(mbs2);
    let macbc = ac.mul_spec(bc);
    let masbs = asn.mul_spec(bs);
    let masbc = asn.mul_spec(bc);
    let macbs = ac.mul_spec(bs);
    let nmasbs = masbs.neg_spec();
    let oc = macbc.add_spec(nmasbs);
    let os = masbc.add_spec(macbs);

    // hypothesis unfolds (R2), before the fact-heavy section
    assert(sum_a.eqv_spec(one));
    assert(sum_b.eqv_spec(one));
    assert(sum_a.num * one.denom() == one.num * sum_a.denom());
    assert(sum_b.num * one.denom() == one.num * sum_b.denom());
    assert(one.num == 1);
    assert(one.denom() == 1);

    // denominator products for every node
    Rational::lemma_mul_denom_product_int(ac, ac);
    Rational::lemma_mul_denom_product_int(asn, asn);
    Rational::lemma_mul_denom_product_int(bc, bc);
    Rational::lemma_mul_denom_product_int(bs, bs);
    Rational::lemma_add_denom_product_int(mac, mas);
    Rational::lemma_add_denom_product_int(mbc2, mbs2);
    Rational::lemma_mul_denom_product_int(ac, bc);
    Rational::lemma_mul_denom_product_int(asn, bs);
    Rational::lemma_mul_denom_product_int(asn, bc);
    Rational::lemma_mul_denom_product_int(ac, bs);
    Rational::lemma_add_denom_product_int(macbc, nmasbs);
    Rational::lemma_add_denom_product_int(masbc, macbs);

    // 1-level num unfolds (exact body forms)
    assert(mac.num == ac.num * ac.num);
    assert(mas.num == asn.num * asn.num);
    assert(mbc2.num == bc.num * bc.num);
    assert(mbs2.num == bs.num * bs.num);
    assert(sum_a.num == mac.num * (mas.denom_nat() as int) + mas.num * (mac.denom_nat() as int));
    assert(sum_b.num == mbc2.num * (mbs2.denom_nat() as int) + mbs2.num * (mbc2.denom_nat() as int));
    assert(macbc.num == ac.num * bc.num);
    assert(masbs.num == asn.num * bs.num);
    assert(masbc.num == asn.num * bc.num);
    assert(macbs.num == ac.num * bs.num);
    assert(nmasbs.num == -masbs.num);
    assert(nmasbs.denom_nat() == masbs.denom_nat());
    assert(oc.num == macbc.num * (nmasbs.denom_nat() as int) + nmasbs.num * (macbc.denom_nat() as int));
    assert(os.num == masbc.num * (macbs.denom_nat() as int) + macbs.num * (masbc.denom_nat() as int));

    // denom() <-> denom_nat() bridges
    assert((mac.denom_nat() as int) == mac.denom());
    assert((mas.denom_nat() as int) == mas.denom());
    assert((mbc2.denom_nat() as int) == mbc2.denom());
    assert((mbs2.denom_nat() as int) == mbs2.denom());
    assert((macbc.denom_nat() as int) == macbc.denom());
    assert((masbs.denom_nat() as int) == masbs.denom());
    assert((nmasbs.denom_nat() as int) == nmasbs.denom());
    assert((masbc.denom_nat() as int) == masbc.denom());
    assert((macbs.denom_nat() as int) == macbs.denom());

    // A/B/C/E values (sq_mul links x²y² to (xy)²)
    let ghost A = ac.num * dax;
    let ghost B = asn.num * da;
    let ghost C = bc.num * dbx;
    let ghost E = bs.num * db;
    lemma_nla_sq_mul(ac.num, dax);
    lemma_nla_sq_mul(asn.num, da);
    lemma_nla_sq_mul(bc.num, dbx);
    lemma_nla_sq_mul(bs.num, db);
    assert(sum_a.num == ac.num * ac.num * (dax * dax) + asn.num * asn.num * (da * da));
    assert(sum_a.num == A * A + B * B);
    assert(sum_b.num == bc.num * bc.num * (dbx * dbx) + bs.num * bs.num * (db * db));
    assert(sum_b.num == C * C + E * E);
    assert(sum_a.denom() == (da * da) * (dax * dax));
    lemma_nla_prod4_swap(da, da, dax, dax);
    assert(sum_a.denom() == (da * dax) * (da * dax));
    assert(sum_b.denom() == (db * db) * (dbx * dbx));
    lemma_nla_prod4_swap(db, db, dbx, dbx);
    assert(sum_b.denom() == (db * dbx) * (db * dbx));

    // hypotheses in A/B/C/E form
    assert((sum_a.num * one.denom() == one.num * sum_a.denom()
        && one.num == 1 && one.denom() == 1)
        ==> sum_a.num == sum_a.denom()) by (nonlinear_arith);
    assert(sum_a.num == sum_a.denom());
    assert((sum_b.num * one.denom() == one.num * sum_b.denom()
        && one.num == 1 && one.denom() == 1)
        ==> sum_b.num == sum_b.denom()) by (nonlinear_arith);
    assert(sum_b.num == sum_b.denom());
    assert(A * A + B * B == (da * dax) * (da * dax));
    assert(C * C + E * E == (db * dbx) * (db * dbx));

    // composed numerators and common denominator D = (da·dax)·(db·dbx)
    let ghost D = (da * dax) * (db * dbx);
    assert(oc.num == ac.num * bc.num * (dax * dbx) + (-(asn.num * bs.num)) * (da * db));
    lemma_nla_prod4(ac.num, bc.num, dax, dbx);
    lemma_nla_prod4(asn.num, bs.num, da, db);
    lemma_nla_shuf4(ac.num, bc.num, dax, dbx);
    lemma_nla_shuf4(asn.num, bs.num, da, db);
    assert((oc.num == ac.num * bc.num * (dax * dbx) + (-(asn.num * bs.num)) * (da * db)
        && (ac.num * bc.num) * (dax * dbx) == ac.num * bc.num * dax * dbx
        && (asn.num * bs.num) * (da * db) == asn.num * bs.num * da * db
        && ac.num * bc.num * dax * dbx == A * C
        && asn.num * bs.num * da * db == B * E)
        ==> oc.num == A * C - B * E) by (nonlinear_arith);
    assert(oc.num == A * C - B * E);
    assert(os.num == asn.num * bc.num * (da * dbx) + ac.num * bs.num * (dax * db));
    lemma_nla_prod4(asn.num, bc.num, da, dbx);
    lemma_nla_prod4(ac.num, bs.num, dax, db);
    lemma_nla_shuf4(asn.num, bc.num, da, dbx);
    lemma_nla_shuf4(ac.num, bs.num, dax, db);
    assert((os.num == asn.num * bc.num * (da * dbx) + ac.num * bs.num * (dax * db)
        && (asn.num * bc.num) * (da * dbx) == asn.num * bc.num * da * dbx
        && (ac.num * bs.num) * (dax * db) == ac.num * bs.num * dax * db
        && asn.num * bc.num * da * dbx == B * C
        && ac.num * bs.num * dax * db == A * E)
        ==> os.num == B * C + A * E) by (nonlinear_arith);
    assert(os.num == B * C + A * E);
    // oc.denom() == (da·db)·(dax·dbx) == D ; os.denom() == (dax·db)·(da·dbx) == D
    assert(oc.denom() == (da * db) * (dax * dbx));
    lemma_nla_prod4_swap(da, db, dax, dbx);
    assert(oc.denom() == D);
    assert(os.denom() == (dax * db) * (da * dbx));
    lemma_nla_prod4_swap(dax, db, da, dbx);
    assert(os.denom() == D);

    // oc/os ARE the compose_c/compose_s expressions (1-level unfolds)
    assert(oc == compose_c(ac, asn, bc, bs));
    assert(os == compose_s(ac, asn, bc, bs));
}

/// Finishing step: two rationals over a common denominator D whose
/// numerator squares sum to D² form a unit-norm pair.
proof fn lemma_unit_norm_raw_from_sq(oc: Rational, os: Rational, D: int)
    requires
        oc.denom() == D,
        os.denom() == D,
        oc.num * oc.num + os.num * os.num == D * D,
    ensures
        unit_norm_raw(oc, os),
{
    let one = Rational::from_int_spec(1);
    let moc = oc.mul_spec(oc);
    let mos = os.mul_spec(os);
    let sq = moc.add_spec(mos);

    Rational::lemma_mul_denom_product_int(oc, oc);
    Rational::lemma_mul_denom_product_int(os, os);
    Rational::lemma_add_denom_product_int(moc, mos);

    assert(moc.num == oc.num * oc.num);
    assert(mos.num == os.num * os.num);
    assert(sq.num == moc.num * (mos.denom_nat() as int) + mos.num * (moc.denom_nat() as int));
    assert((moc.denom_nat() as int) == moc.denom());
    assert((mos.denom_nat() as int) == mos.denom());
    assert(moc.denom() == D * D);
    assert(mos.denom() == D * D);
    assert((moc.denom_nat() as int) == D * D);
    assert((mos.denom_nat() as int) == D * D);

    assert((sq.num == moc.num * (mos.denom_nat() as int) + mos.num * (moc.denom_nat() as int)
        && moc.num == oc.num * oc.num && mos.num == os.num * os.num
        && (moc.denom_nat() as int) == D * D && (mos.denom_nat() as int) == D * D)
        ==> sq.num == (oc.num * oc.num) * (D * D) + (os.num * os.num) * (D * D))
        by (nonlinear_arith);
    assert(sq.num == (oc.num * oc.num) * (D * D) + (os.num * os.num) * (D * D));
    lemma_nla_factor(oc.num * oc.num, os.num * os.num, D * D);
    assert(sq.num == (oc.num * oc.num + os.num * os.num) * (D * D));
    assert(sq.num == (D * D) * (D * D));
    assert(sq.denom() == moc.denom() * mos.denom());
    assert(sq.num == sq.denom());

    // goal folds
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert((sq.num == sq.denom() && one.num == 1 && one.denom() == 1)
        ==> sq.num * one.denom() == one.num * sq.denom()) by (nonlinear_arith);
    assert(sq.num * one.denom() == one.num * sq.denom());
    assert(sq.eqv_spec(one));
    assert(unit_norm_raw(oc, os));
}

/// Angle-sum formulas preserve the unit norm:
/// if (ac, asn) and (bc, bs) are on the unit circle, so is their composition.
///
/// Proof: lemma_compose_values (Rational staging) + lemma_lagrange_combined
/// (int identity) + lemma_unit_norm_raw_from_sq (cross-multiplied finish).
pub proof fn lemma_unit_norm_raw_compose(ac: Rational, asn: Rational, bc: Rational, bs: Rational)
    requires
        unit_norm_raw(ac, asn),
        unit_norm_raw(bc, bs),
    ensures
        unit_norm_raw(
            ac.mul_spec(bc).sub_spec(asn.mul_spec(bs)),
            asn.mul_spec(bc).add_spec(ac.mul_spec(bs))),
{
    let ghost da = ac.denom();
    let ghost dax = asn.denom();
    let ghost db = bc.denom();
    let ghost dbx = bs.denom();
    let ghost A = ac.num * dax;
    let ghost B = asn.num * da;
    let ghost C = bc.num * dbx;
    let ghost E = bs.num * db;
    let ghost U = da * dax;
    let ghost V = db * dbx;
    let ghost D = U * V;

    lemma_compose_values(ac, asn, bc, bs);
    let oc = compose_c(ac, asn, bc, bs);
    let os = compose_s(ac, asn, bc, bs);
    lemma_lagrange_combined(A, B, C, E, U, V);
    // oc.num == A·C − B·E, os.num == B·C + A·E, both over D
    assert(oc.num * oc.num + os.num * os.num == D * D);
    lemma_unit_norm_raw_from_sq(oc, os, D);
    // unfold compose_c/compose_s into the postcondition's literal forms
    assert(unit_norm_raw(
        ac.mul_spec(bc).sub_spec(asn.mul_spec(bs)),
        asn.mul_spec(bc).add_spec(ac.mul_spec(bs))));
}

/// The tan-half-angle parametrization lands on the unit circle:
/// ((1 − t²)/(1 + t²))² + (2t/(1 + t²))² ≡ 1.
///
/// With n = t.num, dd = t.denom() ≥ 1, Q = dd² + n², the coordinates are
/// (dd² − n²)·dd² / (dd²·Q) and 2n·dd² / (dd·Q); the cross-multiplied
/// goal reduces to lemma_nla_tanhalf: (dd² − n²)² + 4n²dd² == Q².
pub proof fn lemma_unit_norm_raw_tan_half(t: Rational)
    ensures
        unit_norm_raw(
            Rational::from_int_spec(1).sub_spec(t.mul_spec(t)).div_spec(
                Rational::from_int_spec(1).add_spec(t.mul_spec(t))),
            Rational::from_int_spec(2).mul_spec(t).div_spec(
                Rational::from_int_spec(1).add_spec(t.mul_spec(t)))),
{
    let one = Rational::from_int_spec(1);
    let two = Rational::from_int_spec(2);
    let ghost n = t.num;
    let ghost dd = t.denom();
    Rational::lemma_denom_positive(t);

    // nodes
    let tt = t.mul_spec(t);
    let ntt = tt.neg_spec();
    let num1 = one.add_spec(ntt); // 1 − t² (the sub_spec body)
    let den1 = one.add_spec(tt); //  1 + t²
    let r = den1.reciprocal_spec();
    let two_t = two.mul_spec(t);
    let ct = num1.mul_spec(r);
    let st = two_t.mul_spec(r);
    let mct = ct.mul_spec(ct);
    let mst = st.mul_spec(st);
    let sq = mct.add_spec(mst);

    // closed leaves first (R5)
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(two.num == 2);
    assert(two.denom() == 1);

    // denominator products
    Rational::lemma_mul_denom_product_int(t, t);
    Rational::lemma_add_denom_product_int(one, ntt);
    Rational::lemma_add_denom_product_int(one, tt);
    Rational::lemma_mul_denom_product_int(two, t);
    Rational::lemma_mul_denom_product_int(num1, r);
    Rational::lemma_mul_denom_product_int(two_t, r);
    Rational::lemma_mul_denom_product_int(ct, ct);
    Rational::lemma_mul_denom_product_int(st, st);
    Rational::lemma_add_denom_product_int(mct, mst);

    // 1-level unfolds (exact body forms)
    assert(tt.num == t.num * t.num);
    assert(ntt.num == -tt.num);
    assert(ntt.denom_nat() == tt.denom_nat());
    assert(num1.num == one.num * (ntt.denom_nat() as int) + ntt.num * (one.denom_nat() as int));
    assert(den1.num == one.num * (tt.denom_nat() as int) + tt.num * (one.denom_nat() as int));
    assert(two_t.num == two.num * t.num);
    assert(ct.num == num1.num * r.num);
    assert(st.num == two_t.num * r.num);
    assert(mct.num == ct.num * ct.num);
    assert(mst.num == st.num * st.num);
    assert(sq.num == mct.num * (mst.denom_nat() as int) + mst.num * (mct.denom_nat() as int));

    // denom() <-> denom_nat() bridges + closed denom leaves
    assert((tt.denom_nat() as int) == tt.denom());
    assert((ntt.denom_nat() as int) == ntt.denom());
    assert((one.denom_nat() as int) == one.denom());
    assert((mct.denom_nat() as int) == mct.denom());
    assert((mst.denom_nat() as int) == mst.denom());
    assert(tt.denom() == dd * dd);
    assert(ntt.denom() == dd * dd);

    // numerator values (multi-fact substitution: implication form, R3)
    assert((tt.denom_nat() as int) == dd * dd);
    assert((one.denom_nat() as int) == 1);
    assert((den1.num == one.num * (tt.denom_nat() as int) + tt.num * (one.denom_nat() as int)
        && one.num == 1 && tt.num == n * n
        && (tt.denom_nat() as int) == dd * dd && (one.denom_nat() as int) == 1)
        ==> den1.num == dd * dd + n * n) by (nonlinear_arith);
    assert(den1.num == dd * dd + n * n);
    assert(ntt.num == -(n * n));
    assert((num1.num == one.num * (ntt.denom_nat() as int) + ntt.num * (one.denom_nat() as int)
        && one.num == 1 && ntt.num == -(n * n)
        && (ntt.denom_nat() as int) == dd * dd && (one.denom_nat() as int) == 1)
        ==> num1.num == dd * dd - n * n) by (nonlinear_arith);
    assert(num1.num == dd * dd - n * n);
    assert(two_t.num == 2 * n);
    lemma_nla_sq_pos(dd);
    lemma_nla_nn_nonneg(n);
    assert(den1.num >= 1);

    // reciprocal takes the positive branch (den1.num ≥ 1)
    assert(r.num == den1.denom());
    assert(r.denom() == den1.num);
    assert(den1.denom() == dd * dd);

    // coordinate values: Q = dd² + n²
    let ghost Q = dd * dd + n * n;
    assert(ct.num == (dd * dd - n * n) * (dd * dd));
    assert(ct.denom() == (dd * dd) * Q);
    assert(st.num == 2 * n * (dd * dd));
    assert(st.denom() == dd * Q);

    // squares of the coordinates' num/den (sq_mul + regroups)
    lemma_nla_sq_mul(dd * dd - n * n, dd * dd);
    assert(mct.num == ((dd * dd - n * n) * (dd * dd - n * n)) * ((dd * dd) * (dd * dd)));
    lemma_nla_sq_mul(dd, Q);
    assert(mst.denom() == (dd * dd) * (Q * Q));
    lemma_nla_2nu_sq(n, dd * dd);
    assert(mst.num == 4 * (n * n) * ((dd * dd) * (dd * dd)));
    lemma_nla_sq_mul(dd * dd, Q);
    assert(mct.denom() == ((dd * dd) * (dd * dd)) * (Q * Q));

    // sq.num with the common factor K = dd⁶·Q² = (dd·dd)·(dd·dd)·((dd·dd)·(Q·Q))
    let ghost K = (dd * dd) * (dd * dd) * ((dd * dd) * (Q * Q));
    lemma_nla_tanhalf(n, dd);
    // mct.num·mst.denom() == (dd²−n²)²·K  and  mst.num·mct.denom() == 4n²dd²·K
    // (pure associativity/commutativity shuffles over the established squares)
    assert((mct.num == ((dd * dd - n * n) * (dd * dd - n * n)) * ((dd * dd) * (dd * dd))
        && mst.denom() == (dd * dd) * (Q * Q)
        && K == (dd * dd) * (dd * dd) * ((dd * dd) * (Q * Q)))
        ==> mct.num * mst.denom() == ((dd * dd - n * n) * (dd * dd - n * n)) * K)
        by (nonlinear_arith);
    assert(mct.num * mst.denom() == ((dd * dd - n * n) * (dd * dd - n * n)) * K);
    assert((mst.num == 4 * (n * n) * ((dd * dd) * (dd * dd))
        && mct.denom() == ((dd * dd) * (dd * dd)) * (Q * Q)
        && K == (dd * dd) * (dd * dd) * ((dd * dd) * (Q * Q)))
        ==> mst.num * mct.denom() == (4 * (n * n) * (dd * dd)) * K)
        by (nonlinear_arith);
    assert(mst.num * mct.denom() == (4 * (n * n) * (dd * dd)) * K);
    lemma_nla_factor((dd * dd - n * n) * (dd * dd - n * n), 4 * (n * n) * (dd * dd), K);
    assert(sq.num == (Q * Q) * K);
    // sq.denom() == mct.denom()·mst.denom() == (Q·Q)·K
    assert(sq.denom() == mct.denom() * mst.denom());
    assert((mct.denom() == ((dd * dd) * (dd * dd)) * (Q * Q)
        && mst.denom() == (dd * dd) * (Q * Q)
        && K == (dd * dd) * (dd * dd) * ((dd * dd) * (Q * Q)))
        ==> mct.denom() * mst.denom() == (Q * Q) * K) by (nonlinear_arith);
    assert(sq.denom() == (Q * Q) * K);
    assert(sq.num == sq.denom());

    // goal folds
    assert(sq.num * one.denom() == one.num * sq.denom());
    assert(sq.eqv_spec(one));
    assert(unit_norm_raw(ct, st));

    // ct/st are the div_spec forms in the postcondition
    assert(ct == Rational::from_int_spec(1).sub_spec(t.mul_spec(t)).div_spec(
        Rational::from_int_spec(1).add_spec(t.mul_spec(t))));
    assert(st == Rational::from_int_spec(2).mul_spec(t).div_spec(
        Rational::from_int_spec(1).add_spec(t.mul_spec(t))));
}

} // verus!
