//! Arctan ledger lemmas (phys-02b). All statements are rational arithmetic
//! only (E3): exact endpoints, width formula, monotone shrink. The semantic
//! bracketing of arctan itself is Lean card G0.
//!
//! Same R-discipline as proofs/rational_raw.rs: exact body-form unfolds,
//! implication-form NLA, verbatim modus-ponens antecedents.

use vstd::prelude::*;

use verus_rational::Rational;

use crate::angle_ledger::{
    angle_enclosure, angle_enclosure_signed, arctan_sum, arctan_term, t_in_symmetric_unit_interval,
    t_in_unit_interval, two_x,
};
use crate::proofs::rpow::{
    ipow, lemma_ipow_add, lemma_ipow_congruence, lemma_ipow_double, lemma_ipow_le,
    lemma_ipow_neg_odd, lemma_ipow_nonneg, lemma_ipow_pos, lemma_ipow_zero_base,
    lemma_rpow_num_denom, rpow,
};

verus! {

// ── term structure ───────────────────────────────────────────────────

/// term_j.num == n^(2j+1) and term_j.denom() == dd^(2j+1)·(2j+1).
pub proof fn lemma_arctan_term_num_denom(t: Rational, j: nat)
    ensures
        arctan_term(t, j).num == ipow(t.num, 2 * j + 1),
        arctan_term(t, j).denom() == ipow(t.denom(), 2 * j + 1) * ((2 * j + 1) as int),
{
    let e = 2 * j + 1;
    let m = (2 * j + 1) as int;
    let rp = rpow(t, e);
    let d = Rational::from_int_spec(m);
    let r = d.reciprocal_spec();
    let term = arctan_term(t, j);

    lemma_rpow_num_denom(t, e);
    Rational::lemma_mul_denom_product_int(rp, r);

    // from_int(m): num == m, denom() == 1, and m >= 1 so reciprocal flips
    assert(d.num == m);
    assert(d.denom() == 1);
    assert(d.num > 0);
    // reciprocal_spec positive branch
    assert(r.num == d.denom());
    assert(r.denom() == d.num);
    assert(r.num == 1);
    assert(r.denom() == m);

    // term == rp.div_spec(d) == rp.mul_spec(r)
    assert(term == rp.mul_spec(r));
    assert(term.num == rp.num * r.num);
    assert(term.num == ipow(t.num, e));
    assert(term.denom() == rp.denom() * r.denom());
    assert(term.denom() == ipow(t.denom(), e) * m);
}

/// x^(e+2) == x²·x^e (one-step regroup of lemma_ipow_add).
pub proof fn lemma_ipow_plus_two(x: int, e: nat)
    ensures ipow(x, e + 2) == x * x * ipow(x, e),
{
    lemma_ipow_add(x, e, 2);
    lemma_ipow_double(x, 1);
    assert(ipow(x, 1) == x) by { reveal_with_fuel(ipow, 2); }
    assert(ipow(x, 2) == x * x);
    assert(ipow(x, e + 2) == ipow(x, e) * ipow(x, 2));
    assert(ipow(x, 2) == x * x ==> ipow(x, e) * ipow(x, 2) == x * x * ipow(x, e))
        by (nonlinear_arith);
}

/// 0 ≤ t ⇒ term_j ≥ 0.
pub proof fn lemma_arctan_term_nonneg(t: Rational, j: nat)
    requires
        Rational::from_int_spec(0).le_spec(t),
    ensures
        Rational::from_int_spec(0).le_spec(arctan_term(t, j)),
{
    let zero = Rational::from_int_spec(0);
    lemma_arctan_term_num_denom(t, j);
    // 0 ≤ t ⟺ 0 ≤ t.num
    assert(zero.le_spec(t) == (zero.num * t.denom() <= t.num * zero.denom()));
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(zero.num * t.denom() <= t.num * zero.denom());
    assert((zero.num * t.denom() <= t.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> t.num >= 0) by (nonlinear_arith);
    assert(t.num >= 0);
    lemma_ipow_nonneg(t.num, 2 * j + 1);
    // 0 ≤ term ⟺ 0 ≤ term.num
    assert(zero.le_spec(arctan_term(t, j)) == (
        zero.num * arctan_term(t, j).denom() <= arctan_term(t, j).num * zero.denom()));
}

/// 0 ≤ t ≤ 1 ⇒ term_{j+1} ≤ term_j (terms shrink for unit-interval t).
pub proof fn lemma_arctan_term_decreasing(t: Rational, j: nat)
    requires
        t_in_unit_interval(t),
    ensures
        arctan_term(t, (j + 1) as nat).le_spec(arctan_term(t, j)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    let ghost n = t.num;
    let ghost dd = t.denom();
    Rational::lemma_denom_positive(t);

    // 0 ≤ n ≤ dd from the unit-interval hypothesis
    assert(zero.le_spec(t) == (zero.num * t.denom() <= t.num * zero.denom()));
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(t.le_spec(one) == (t.num * one.denom() <= one.num * t.denom()));
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(zero.num * t.denom() <= t.num * zero.denom());
    assert(t.num * one.denom() <= one.num * t.denom());
    assert((zero.num * t.denom() <= t.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> t.num >= 0) by (nonlinear_arith);
    vstd::arithmetic::mul::lemma_mul_basics(t.num);
    vstd::arithmetic::mul::lemma_mul_basics(t.denom());
    assert(t.num <= dd);
    assert(0 <= n && n <= dd);

    let e = 2 * j + 1;
    let ghost m = (2 * j + 1) as int;
    lemma_arctan_term_num_denom(t, j);
    lemma_arctan_term_num_denom(t, (j + 1) as nat);
    // (j+1) exponent: 2(j+1)+1 == e + 2
    assert(2 * (j + 1) + 1 == e + 2);
    let ghost nn = ipow(n, e);
    let ghost dp = ipow(dd, e);
    lemma_ipow_plus_two(n, e);
    lemma_ipow_plus_two(dd, e);
    lemma_ipow_nonneg(n, e);
    lemma_ipow_nonneg(dd, e);
    lemma_ipow_le(n, dd, 2);
    lemma_ipow_nonneg(n, 2);
    // P = nn·dp ≥ 0, and n²·m ≤ dd²·(m+2)
    assert((0 <= n && n <= dd) ==> n * n <= dd * dd) by (nonlinear_arith);
    assert((n * n <= dd * dd && m >= 1) ==> n * n * m <= dd * dd * (m + 2)) by (nonlinear_arith);
    assert((nn >= 0 && dp >= 0 && n * n * m <= dd * dd * (m + 2))
        ==> (n * n * nn) * (dp * m) <= (nn * (dd * dd)) * (dp * (m + 2))) by (nonlinear_arith);
    // the cross-multiplied goal
    let tj = arctan_term(t, j);
    let tj1 = arctan_term(t, (j + 1) as nat);
    assert(tj1.num == ipow(n, e + 2));
    assert(tj1.denom() == ipow(dd, e + 2) * (m + 2));
    assert(tj.num == nn);
    assert(tj.denom() == dp * m);
    assert((tj1.num == ipow(n, e + 2) && tj1.denom() == ipow(dd, e + 2) * (m + 2)
        && tj.num == nn && tj.denom() == dp * m
        && ipow(n, e + 2) == n * n * nn && ipow(dd, e + 2) == dd * dd * dp
        && (n * n * nn) * (dp * m) <= (nn * (dd * dd)) * (dp * (m + 2)))
        ==> tj1.num * tj.denom() <= tj.num * tj1.denom()) by (nonlinear_arith);
    assert(tj1.le_spec(tj));
}

/// t.num == 0 (t ≡ 0) ⇒ term_j(t) ≡ 0.
pub proof fn lemma_arctan_term_zero(t: Rational, j: nat)
    requires
        t.num == 0,
    ensures
        arctan_term(t, j).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    lemma_arctan_term_num_denom(t, j);
    lemma_ipow_congruence(t.num, 0, 2 * j + 1);
    lemma_ipow_zero_base(2 * j + 1);
    let term = arctan_term(t, j);
    Rational::lemma_denom_positive(term);
    assert(term.num == 0);
    assert(term.eqv_spec(z) == (term.num * z.denom() == z.num * term.denom()));
    assert(z.num == 0);
    assert(z.denom() == 1);
}

/// 0 ≤ t ≤ 1 ⇒ term_j(t) ≤ 1/(2j+1) (uniform term bound).
pub proof fn lemma_arctan_term_bound(t: Rational, j: nat)
    requires
        t_in_unit_interval(t),
    ensures
        arctan_term(t, j).le_spec(Rational::from_frac_spec(1, (2 * j + 1) as int)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    let ghost n = t.num;
    let ghost dd = t.denom();
    let ghost m = (2 * j + 1) as int;
    Rational::lemma_denom_positive(t);
    assert(zero.le_spec(t) == (zero.num * t.denom() <= t.num * zero.denom()));
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(t.le_spec(one) == (t.num * one.denom() <= one.num * t.denom()));
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(zero.num * t.denom() <= t.num * zero.denom());
    assert(t.num * one.denom() <= one.num * t.denom());
    assert((zero.num * t.denom() <= t.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> t.num >= 0) by (nonlinear_arith);
    vstd::arithmetic::mul::lemma_mul_basics(t.num);
    vstd::arithmetic::mul::lemma_mul_basics(t.denom());
    assert(0 <= n && n <= dd);

    lemma_arctan_term_num_denom(t, j);
    lemma_ipow_le(n, dd, 2 * j + 1);
    lemma_ipow_pos(dd, 2 * j + 1);
    let term = arctan_term(t, j);
    let bound = Rational::from_frac_spec(1, m);
    // bound: num == 1, denom() == m (m ≥ 1)
    assert(bound.num == 1);
    assert(bound.denom() == m);
    assert(term.le_spec(bound) == (term.num * bound.denom() <= bound.num * term.denom()));
    assert((ipow(n, 2 * j + 1) <= ipow(dd, 2 * j + 1) && m >= 1
        && term.num == ipow(n, 2 * j + 1) && term.denom() == ipow(dd, 2 * j + 1) * m
        && bound.num == 1 && bound.denom() == m)
        ==> term.num * bound.denom() <= bound.num * term.denom()) by (nonlinear_arith);
}

// ── sum steps ────────────────────────────────────────────────────────

pub proof fn lemma_arctan_step_even(t: Rational, k: nat)
    requires
        k > 0,
        k % 2 == 0,
    ensures
        arctan_sum(t, k) == arctan_sum(t, (k - 1) as nat).add_spec(arctan_term(t, k)),
{
}

pub proof fn lemma_arctan_step_odd(t: Rational, k: nat)
    requires
        k > 0,
        k % 2 == 1,
    ensures
        arctan_sum(t, k) == arctan_sum(t, (k - 1) as nat).sub_spec(arctan_term(t, k)),
{
}

// ── small raw arithmetic lemmas ──────────────────────────────────────

/// 0 ≤ c ⇒ a − c ≤ a.
pub proof fn lemma_raw_sub_nonneg_le(a: Rational, c: Rational)
    requires
        Rational::from_int_spec(0).le_spec(c),
    ensures
        a.sub_spec(c).le_spec(a),
{
    let zero = Rational::from_int_spec(0);
    let s = a.sub_spec(c);
    Rational::lemma_add_denom_product_int(a, c.neg_spec());
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(c);
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(zero.le_spec(c) == (zero.num * c.denom() <= c.num * zero.denom()));
    assert(zero.num * c.denom() <= c.num * zero.denom());
    assert((zero.num * c.denom() <= c.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> c.num >= 0) by (nonlinear_arith);
    assert(c.num >= 0);
    assert(s.num == a.num * c.denom() + (-c.num) * a.denom());
    assert(s.denom() == a.denom() * c.denom());
    assert(s.le_spec(a) == (s.num * a.denom() <= a.num * s.denom()));
    assert((c.num >= 0 && a.denom() >= 1 && c.denom() >= 1
        && s.num == a.num * c.denom() + (-c.num) * a.denom()
        && s.denom() == a.denom() * c.denom())
        ==> s.num * a.denom() <= a.num * s.denom()) by (nonlinear_arith);
}

/// 0 ≤ c ⇒ a ≤ a + c.
pub proof fn lemma_raw_le_add_nonneg(a: Rational, c: Rational)
    requires
        Rational::from_int_spec(0).le_spec(c),
    ensures
        a.le_spec(a.add_spec(c)),
{
    let zero = Rational::from_int_spec(0);
    let s = a.add_spec(c);
    Rational::lemma_add_denom_product_int(a, c);
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(c);
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(zero.le_spec(c) == (zero.num * c.denom() <= c.num * zero.denom()));
    assert(zero.num * c.denom() <= c.num * zero.denom());
    assert((zero.num * c.denom() <= c.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> c.num >= 0) by (nonlinear_arith);
    assert(c.num >= 0);
    assert(s.num == a.num * c.denom() + c.num * a.denom());
    assert(s.denom() == a.denom() * c.denom());
    assert(a.le_spec(s) == (a.num * s.denom() <= s.num * a.denom()));
    assert((c.num >= 0 && a.denom() >= 1 && c.denom() >= 1
        && s.num == a.num * c.denom() + c.num * a.denom()
        && s.denom() == a.denom() * c.denom())
        ==> a.num * s.denom() <= s.num * a.denom()) by (nonlinear_arith);
}

/// a − (a − u) ≡ u.
pub proof fn lemma_raw_sub_sub_cancel(a: Rational, u: Rational)
    ensures
        a.sub_spec(a.sub_spec(u)).eqv_spec(u),
{
    let s = a.sub_spec(u);
    let s2 = a.sub_spec(s);
    Rational::lemma_add_denom_product_int(a, u.neg_spec());
    Rational::lemma_add_denom_product_int(a, s.neg_spec());
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(u);
    assert(s.num == a.num * u.denom() + (-u.num) * a.denom());
    assert(s.denom() == a.denom() * u.denom());
    assert(s2.num == a.num * s.denom() + (-s.num) * a.denom());
    assert(s2.denom() == a.denom() * s.denom());
    assert(s2.eqv_spec(u) == (s2.num * u.denom() == u.num * s2.denom()));
    assert((a.denom() >= 1 && u.denom() >= 1
        && s.num == a.num * u.denom() + (-u.num) * a.denom()
        && s.denom() == a.denom() * u.denom()
        && s2.num == a.num * s.denom() + (-s.num) * a.denom()
        && s2.denom() == a.denom() * s.denom())
        ==> s2.num * u.denom() == u.num * s2.denom()) by (nonlinear_arith);
}

/// 2x − 2y ≡ 2(x − y).
pub proof fn lemma_raw_two_distrib_sub(x: Rational, y: Rational)
    ensures
        two_x(x).sub_spec(two_x(y)).eqv_spec(two_x(x.sub_spec(y))),
{
    let two = Rational::from_int_spec(2);
    let tx = two_x(x);
    let ty = two_x(y);
    let s = tx.sub_spec(ty);
    let xy = x.sub_spec(y);
    let txy = two_x(xy);
    Rational::lemma_mul_denom_product_int(two, x);
    Rational::lemma_mul_denom_product_int(two, y);
    Rational::lemma_mul_denom_product_int(two, xy);
    Rational::lemma_add_denom_product_int(tx, ty.neg_spec());
    Rational::lemma_add_denom_product_int(x, y.neg_spec());
    Rational::lemma_denom_positive(x);
    Rational::lemma_denom_positive(y);
    assert(two.num == 2);
    assert(two.denom() == 1);
    assert(tx.num == two.num * x.num);
    assert(ty.num == two.num * y.num);
    assert(txy.num == two.num * xy.num);
    assert(xy.num == x.num * y.denom() + (-y.num) * x.denom());
    assert(xy.denom() == x.denom() * y.denom());
    assert(s.num == tx.num * ty.denom() + (-ty.num) * tx.denom());
    assert(s.denom() == tx.denom() * ty.denom());
    assert(s.eqv_spec(txy) == (s.num * txy.denom() == txy.num * s.denom()));
    assert((two.num == 2 && x.denom() >= 1 && y.denom() >= 1
        && tx.num == two.num * x.num && tx.denom() == two.denom() * x.denom()
        && ty.num == two.num * y.num && ty.denom() == two.denom() * y.denom()
        && xy.num == x.num * y.denom() + (-y.num) * x.denom()
        && xy.denom() == x.denom() * y.denom()
        && txy.num == two.num * xy.num && txy.denom() == two.denom() * xy.denom()
        && s.num == tx.num * ty.denom() + (-ty.num) * tx.denom()
        && s.denom() == tx.denom() * ty.denom())
        ==> s.num * txy.denom() == txy.num * s.denom()) by (nonlinear_arith);
}

// ── bracket: adjacent sums ───────────────────────────────────────────

/// k even ⇒ A_{k+1} ≤ A_k (A_{k+1} = A_k − term_{k+1}, term ≥ 0).
pub proof fn lemma_arctan_adjacent_even(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 0,
    ensures
        arctan_sum(t, (k + 1) as nat).le_spec(arctan_sum(t, k)),
{
    lemma_arctan_step_odd(t, (k + 1) as nat);
    lemma_arctan_term_nonneg(t, (k + 1) as nat);
    lemma_raw_sub_nonneg_le(arctan_sum(t, k), arctan_term(t, (k + 1) as nat));
}

/// k odd ⇒ A_k ≤ A_{k+1} (A_{k+1} = A_k + term_{k+1}, term ≥ 0).
pub proof fn lemma_arctan_adjacent_odd(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 1,
    ensures
        arctan_sum(t, k).le_spec(arctan_sum(t, (k + 1) as nat)),
{
    lemma_arctan_step_even(t, (k + 1) as nat);
    lemma_arctan_term_nonneg(t, (k + 1) as nat);
    lemma_raw_le_add_nonneg(arctan_sum(t, k), arctan_term(t, (k + 1) as nat));
}

// ── bracket: two-step monotonicity ───────────────────────────────────

/// k even ⇒ A_{k+2} ≤ A_k (even partial sums decrease).
pub proof fn lemma_arctan_two_step_even(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 0,
    ensures
        arctan_sum(t, (k + 2) as nat).le_spec(arctan_sum(t, k)),
{
    lemma_arctan_step_odd(t, (k + 1) as nat);
    lemma_arctan_step_even(t, (k + 2) as nat);
    lemma_arctan_term_decreasing(t, (k + 1) as nat);
    let a1 = arctan_sum(t, (k + 1) as nat);
    let t1 = arctan_term(t, (k + 1) as nat);
    let t2 = arctan_term(t, (k + 2) as nat);
    // A_{k+2} = A_{k+1} + t2 ≤ A_{k+1} + t1 ≡ A_k
    Rational::lemma_le_add_monotone(t2, t1, a1);
    Rational::lemma_sub_then_add_cancel(arctan_sum(t, k), t1);
    Rational::lemma_add_commutative(t1, arctan_sum(t, k).sub_spec(t1));
    Rational::lemma_eqv_symmetric(t1.add_spec(a1), a1.add_spec(t1));
    Rational::lemma_eqv_transitive(
        a1.add_spec(t1), t1.add_spec(a1), arctan_sum(t, k));
    Rational::lemma_eqv_implies_le(a1.add_spec(t1), arctan_sum(t, k));
    // le_add_monotone gives t2+a1 ≤ t1+a1; bridge add commutativity
    // explicitly (fragile under module perturbation if left to Z3).
    assert(a1.add_spec(t2).le_spec(a1.add_spec(t1))) by {
        Rational::lemma_add_commutative(a1, t2);
        Rational::lemma_add_commutative(t1, a1);
        Rational::lemma_eqv_implies_le(a1.add_spec(t2), t2.add_spec(a1));
        Rational::lemma_eqv_implies_le(t1.add_spec(a1), a1.add_spec(t1));
        Rational::lemma_le_transitive(a1.add_spec(t2), t2.add_spec(a1), t1.add_spec(a1));
        Rational::lemma_le_transitive(a1.add_spec(t2), t1.add_spec(a1), a1.add_spec(t1));
    }
    Rational::lemma_le_transitive(a1.add_spec(t2), a1.add_spec(t1), arctan_sum(t, k));
    assert(arctan_sum(t, (k + 2) as nat).le_spec(arctan_sum(t, k)));
}

/// k odd ⇒ A_k ≤ A_{k+2} (odd partial sums increase).
pub proof fn lemma_arctan_two_step_odd(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 1,
    ensures
        arctan_sum(t, k).le_spec(arctan_sum(t, (k + 2) as nat)),
{
    lemma_arctan_step_even(t, (k + 1) as nat);
    lemma_arctan_step_odd(t, (k + 2) as nat);
    lemma_arctan_term_decreasing(t, (k + 1) as nat);
    let a1 = arctan_sum(t, (k + 1) as nat);
    let t1 = arctan_term(t, (k + 1) as nat);
    let t2 = arctan_term(t, (k + 2) as nat);
    // A_k ≡ A_{k+1} − t1 ≤ A_{k+1} − t2 = A_{k+2}
    Rational::lemma_sub_le_monotone_right(t2, t1, a1);
    Rational::lemma_add_then_sub_cancel(t1, arctan_sum(t, k));
    Rational::lemma_add_commutative(arctan_sum(t, k), t1);
    Rational::lemma_eqv_reflexive(t1);
    Rational::lemma_eqv_sub_congruence(
        arctan_sum(t, k).add_spec(t1), t1.add_spec(arctan_sum(t, k)), t1, t1);
    Rational::lemma_eqv_transitive(
        a1.sub_spec(t1), t1.add_spec(arctan_sum(t, k)).sub_spec(t1), arctan_sum(t, k));
    Rational::lemma_eqv_symmetric(a1.sub_spec(t1), arctan_sum(t, k));
    Rational::lemma_eqv_implies_le(arctan_sum(t, k), a1.sub_spec(t1));
    Rational::lemma_le_transitive(arctan_sum(t, k), a1.sub_spec(t1), a1.sub_spec(t2));
    assert(arctan_sum(t, k).le_spec(arctan_sum(t, (k + 2) as nat)));
}

// ── width formula ────────────────────────────────────────────────────

/// k even ⇒ 2A_k − 2A_{k+1} ≡ 2·term_{k+1} (exact width).
pub proof fn lemma_arctan_width_even(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 0,
    ensures
        two_x(arctan_sum(t, k)).sub_spec(two_x(arctan_sum(t, (k + 1) as nat))).eqv_spec(
            two_x(arctan_term(t, (k + 1) as nat))),
{
    lemma_arctan_step_odd(t, (k + 1) as nat);
    let ak = arctan_sum(t, k);
    let ak1 = arctan_sum(t, (k + 1) as nat);
    let term = arctan_term(t, (k + 1) as nat);
    let two = Rational::from_int_spec(2);
    lemma_raw_two_distrib_sub(ak, ak1);
    lemma_raw_sub_sub_cancel(ak, term);
    assert(ak.sub_spec(ak1) == ak.sub_spec(ak.sub_spec(term)));
    Rational::lemma_eqv_reflexive(two);
    Rational::lemma_eqv_mul_congruence(two, two, ak.sub_spec(ak1), term);
    Rational::lemma_eqv_transitive(
        two_x(ak).sub_spec(two_x(ak1)), two_x(ak.sub_spec(ak1)), two_x(term));
}

/// k odd ⇒ 2A_{k+1} − 2A_k ≡ 2·term_{k+1} (exact width).
pub proof fn lemma_arctan_width_odd(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 1,
    ensures
        two_x(arctan_sum(t, (k + 1) as nat)).sub_spec(two_x(arctan_sum(t, k))).eqv_spec(
            two_x(arctan_term(t, (k + 1) as nat))),
{
    lemma_arctan_step_even(t, (k + 1) as nat);
    let ak = arctan_sum(t, k);
    let ak1 = arctan_sum(t, (k + 1) as nat);
    let term = arctan_term(t, (k + 1) as nat);
    let two = Rational::from_int_spec(2);
    lemma_raw_two_distrib_sub(ak1, ak);
    Rational::lemma_add_then_sub_cancel(ak, term);
    assert(ak1.sub_spec(ak) == ak.add_spec(term).sub_spec(ak));
    Rational::lemma_eqv_reflexive(two);
    Rational::lemma_eqv_mul_congruence(two, two, ak1.sub_spec(ak), term);
    Rational::lemma_eqv_transitive(
        two_x(ak1).sub_spec(two_x(ak)), two_x(ak1.sub_spec(ak)), two_x(term));
}

// ── enclosure properties ─────────────────────────────────────────────

/// a ≤ b ⇒ 2a ≤ 2b (two is from_int(2), nonneg).
pub proof fn lemma_two_mul_monotone(a: Rational, b: Rational)
    requires
        a.le_spec(b),
    ensures
        two_x(a).le_spec(two_x(b)),
{
    let two = Rational::from_int_spec(2);
    let zero = Rational::from_int_spec(0);
    assert(zero.le_spec(two));
    Rational::lemma_le_mul_monotone_nonnegative(a, b, two);
    Rational::lemma_mul_commutative(a, two);
    Rational::lemma_mul_commutative(b, two);
    Rational::lemma_eqv_implies_le(two_x(a), a.mul_spec(two));
    Rational::lemma_eqv_symmetric(b.mul_spec(two), two_x(b));
    Rational::lemma_eqv_implies_le(b.mul_spec(two), two_x(b));
    Rational::lemma_le_transitive(two_x(a), a.mul_spec(two), b.mul_spec(two));
    Rational::lemma_le_transitive(two_x(a), b.mul_spec(two), two_x(b));
}

/// The enclosure is always ordered: lo ≤ hi.
pub(crate) proof fn lemma_angle_enclosure_ordered(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
    ensures
        crate::angle_ledger::angle_enclosure(t, k).0.le_spec(
            crate::angle_ledger::angle_enclosure(t, k).1),
{
    if k % 2 == 0 {
        lemma_arctan_adjacent_even(t, k);
        lemma_two_mul_monotone(arctan_sum(t, (k + 1) as nat), arctan_sum(t, k));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, (k + 1) as nat)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, k)));
    } else {
        lemma_arctan_adjacent_odd(t, k);
        lemma_two_mul_monotone(arctan_sum(t, k), arctan_sum(t, (k + 1) as nat));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, k)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, (k + 1) as nat)));
    }
}

/// Enclosures nest: enclosure_{k+2} ⊆ enclosure_k (monotone shrink, SPEC §3).
pub(crate) proof fn lemma_angle_enclosure_shrink(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
    ensures
        crate::angle_ledger::angle_enclosure(t, k).0.le_spec(
            crate::angle_ledger::angle_enclosure(t, (k + 2) as nat).0),
        crate::angle_ledger::angle_enclosure(t, (k + 2) as nat).1.le_spec(
            crate::angle_ledger::angle_enclosure(t, k).1),
{
    assert((k + 2) % 2 == k % 2) by (nonlinear_arith);
    if k % 2 == 0 {
        lemma_arctan_two_step_even(t, k);
        lemma_arctan_two_step_odd(t, (k + 1) as nat);
        lemma_two_mul_monotone(arctan_sum(t, (k + 2) as nat), arctan_sum(t, k));
        lemma_two_mul_monotone(arctan_sum(t, (k + 1) as nat), arctan_sum(t, (k + 3) as nat));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, (k + 1) as nat)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, k)));
        assert(angle_enclosure(t, (k + 2) as nat).0 == two_x(arctan_sum(t, (k + 3) as nat)));
        assert(angle_enclosure(t, (k + 2) as nat).1 == two_x(arctan_sum(t, (k + 2) as nat)));
    } else {
        lemma_arctan_two_step_odd(t, k);
        lemma_arctan_two_step_even(t, (k + 1) as nat);
        lemma_two_mul_monotone(arctan_sum(t, k), arctan_sum(t, (k + 2) as nat));
        lemma_two_mul_monotone(arctan_sum(t, (k + 3) as nat), arctan_sum(t, (k + 1) as nat));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, k)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, (k + 1) as nat)));
        assert(angle_enclosure(t, (k + 2) as nat).0 == two_x(arctan_sum(t, (k + 2) as nat)));
        assert(angle_enclosure(t, (k + 2) as nat).1 == two_x(arctan_sum(t, (k + 3) as nat)));
    }
}

// ── signed mirror (negative t; the v1.4 debt) ────────────────────────
//
// The series is odd: term_j(−t) == −term_j(t) and A_k(−t) == −A_k(t),
// both STRUCTURAL equalities. Hence the enclosure endpoints for negative
// t are the negations of the positive-t endpoints, and the parity-picked
// pair comes out swapped: enc(t,k).1 ≤ enc(t,k).0 for −1 ≤ t ≤ 0. The
// signed enclosure (angle_enclosure_signed) restores a uniform lo ≤ hi
// on [−1, 1] with the uniform width 2·|term_{k+1}|.

/// term_j(−t) == −term_j(t) (structural; odd powers flip sign).
pub proof fn lemma_arctan_term_neg(t: Rational, j: nat)
    ensures
        arctan_term(t.neg_spec(), j) == arctan_term(t, j).neg_spec(),
{
    lemma_arctan_term_num_denom(t, j);
    lemma_arctan_term_num_denom(t.neg_spec(), j);
    lemma_ipow_neg_odd(t.num, 2 * j + 1);
    let lhs = arctan_term(t.neg_spec(), j);
    let rhs = arctan_term(t, j).neg_spec();
    assert(t.neg_spec().num == -t.num);
    assert(t.neg_spec().denom() == t.denom());
    assert(lhs.num == ipow(-t.num, 2 * j + 1));
    assert(rhs.num == -ipow(t.num, 2 * j + 1));
    assert(lhs.num == rhs.num);
    assert(lhs.denom() == ipow(t.denom(), 2 * j + 1) * ((2 * j + 1) as int));
    assert(rhs.denom() == arctan_term(t, j).denom());
    assert(lhs.denom() == rhs.denom());
    assert(lhs.den == rhs.den);
    assert(lhs == rhs);
}

/// A_k(−t) == −A_k(t) (structural), by induction on k.
pub proof fn lemma_arctan_sum_neg(t: Rational, k: nat)
    ensures
        arctan_sum(t.neg_spec(), k) == arctan_sum(t, k).neg_spec(),
    decreases k
{
    if k == 0 {
        lemma_arctan_term_neg(t, 0);
        assert(arctan_sum(t.neg_spec(), 0) == arctan_term(t.neg_spec(), 0));
        assert(arctan_sum(t, 0).neg_spec() == arctan_term(t, 0).neg_spec());
    } else if k % 2 == 0 {
        lemma_arctan_sum_neg(t, (k - 1) as nat);
        lemma_arctan_term_neg(t, k);
        lemma_arctan_step_even(t, k);
        lemma_arctan_step_even(t.neg_spec(), k);
        Rational::lemma_neg_add(arctan_sum(t, (k - 1) as nat), arctan_term(t, k));
        let s = arctan_sum(t, (k - 1) as nat);
        let term = arctan_term(t, k);
        assert(arctan_sum(t.neg_spec(), k)
            == arctan_sum(t.neg_spec(), (k - 1) as nat).add_spec(arctan_term(t.neg_spec(), k)));
        assert(arctan_sum(t.neg_spec(), k) == s.neg_spec().add_spec(term.neg_spec()));
        assert(arctan_sum(t, k).neg_spec() == s.add_spec(term).neg_spec());
        assert(s.neg_spec().add_spec(term.neg_spec()) == s.add_spec(term).neg_spec());
    } else {
        lemma_arctan_sum_neg(t, (k - 1) as nat);
        lemma_arctan_term_neg(t, k);
        lemma_arctan_step_odd(t, k);
        lemma_arctan_step_odd(t.neg_spec(), k);
        Rational::lemma_neg_add(arctan_sum(t, (k - 1) as nat), arctan_term(t, k).neg_spec());
        Rational::lemma_neg_involution(arctan_term(t, k));
        let s = arctan_sum(t, (k - 1) as nat);
        let term = arctan_term(t, k);
        assert(arctan_sum(t.neg_spec(), k)
            == arctan_sum(t.neg_spec(), (k - 1) as nat).sub_spec(arctan_term(t.neg_spec(), k)));
        assert(arctan_sum(t.neg_spec(), k) == s.neg_spec().add_spec(term.neg_spec().neg_spec()));
        assert(arctan_sum(t.neg_spec(), k) == s.neg_spec().add_spec(term));
        assert(arctan_sum(t, k).neg_spec() == s.sub_spec(term).neg_spec());
        assert(s.sub_spec(term).neg_spec() == s.add_spec(term.neg_spec()).neg_spec());
        assert(s.add_spec(term.neg_spec()).neg_spec()
            == s.neg_spec().add_spec(term.neg_spec().neg_spec()));
    }
}

/// 2·(−x) == −(2·x) (structural).
pub proof fn lemma_two_x_neg(x: Rational)
    ensures
        two_x(x.neg_spec()) == two_x(x).neg_spec(),
{
    let two = Rational::from_int_spec(2);
    let lhs = two_x(x.neg_spec());
    let rhs = two_x(x).neg_spec();
    Rational::lemma_mul_denom_product_int(two, x.neg_spec());
    Rational::lemma_mul_denom_product_int(two, x);
    assert(two.num == 2);
    assert(two.denom() == 1);
    assert(x.neg_spec().num == -x.num);
    assert(x.neg_spec().denom() == x.denom());
    assert(lhs.num == two.num * x.neg_spec().num);
    assert(rhs.num == -(two_x(x).num));
    assert(two_x(x).num == two.num * x.num);
    assert((lhs.num == two.num * x.neg_spec().num && x.neg_spec().num == -x.num
        && rhs.num == -(two.num * x.num))
        ==> lhs.num == rhs.num) by (nonlinear_arith);
    assert(lhs.denom() == two.denom() * x.neg_spec().denom());
    assert(rhs.denom() == two_x(x).denom());
    assert(lhs.denom() == rhs.denom());
    assert(lhs.den == rhs.den);
    assert(lhs == rhs);
}

/// The enclosure endpoints negate with t (structural, both parities).
pub(crate) proof fn lemma_angle_enclosure_neg(t: Rational, k: nat)
    ensures
        angle_enclosure(t.neg_spec(), k).0 == angle_enclosure(t, k).0.neg_spec(),
        angle_enclosure(t.neg_spec(), k).1 == angle_enclosure(t, k).1.neg_spec(),
{
    lemma_arctan_sum_neg(t, k);
    lemma_arctan_sum_neg(t, (k + 1) as nat);
    lemma_two_x_neg(arctan_sum(t, k));
    lemma_two_x_neg(arctan_sum(t, (k + 1) as nat));
    if k % 2 == 0 {
        assert(angle_enclosure(t.neg_spec(), k).0
            == two_x(arctan_sum(t.neg_spec(), (k + 1) as nat)));
        assert(angle_enclosure(t.neg_spec(), k).1 == two_x(arctan_sum(t.neg_spec(), k)));
        assert(angle_enclosure(t, k).0.neg_spec()
            == two_x(arctan_sum(t, (k + 1) as nat)).neg_spec());
        assert(angle_enclosure(t, k).1.neg_spec() == two_x(arctan_sum(t, k)).neg_spec());
    } else {
        assert(angle_enclosure(t.neg_spec(), k).0 == two_x(arctan_sum(t.neg_spec(), k)));
        assert(angle_enclosure(t.neg_spec(), k).1
            == two_x(arctan_sum(t.neg_spec(), (k + 1) as nat)));
        assert(angle_enclosure(t, k).0.neg_spec() == two_x(arctan_sum(t, k)).neg_spec());
        assert(angle_enclosure(t, k).1.neg_spec()
            == two_x(arctan_sum(t, (k + 1) as nat)).neg_spec());
    }
}

/// Signed ordering (the v1.4 debt): −1 ≤ t ≤ 0 ⇒ enc(t,k).1 ≤ enc(t,k).0.
/// Mirror of lemma_angle_enclosure_ordered via negation of the endpoints.
pub(crate) proof fn lemma_angle_enclosure_ordered_negative(t: Rational, k: nat)
    requires
        t_in_unit_interval(t.neg_spec()),
    ensures
        angle_enclosure(t, k).1.le_spec(angle_enclosure(t, k).0),
{
    lemma_angle_enclosure_ordered(t.neg_spec(), k);
    lemma_angle_enclosure_neg(t, k);
    Rational::lemma_neg_reverses_le(
        angle_enclosure(t, k).0.neg_spec(), angle_enclosure(t, k).1.neg_spec());
    Rational::lemma_neg_involution(angle_enclosure(t, k).0);
    Rational::lemma_neg_involution(angle_enclosure(t, k).1);
}

/// 0 ≤ t ≤ 1 ⇒ −1 ≤ t ≤ 1.
pub proof fn lemma_unit_implies_symmetric(t: Rational)
    requires
        t_in_unit_interval(t),
    ensures
        t_in_symmetric_unit_interval(t),
{
    let z = Rational::from_int_spec(0);
    let mo = Rational::from_int_spec(-1);
    Rational::lemma_denom_positive(t);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(mo.num == -1);
    assert(mo.denom() == 1);
    assert(z.le_spec(t) == (z.num * t.denom() <= t.num * z.denom()));
    assert(mo.le_spec(t) == (mo.num * t.denom() <= t.num * mo.denom()));
    assert((z.num * t.denom() <= t.num * z.denom() && z.num == 0 && z.denom() == 1
        && mo.num == -1 && mo.denom() == 1 && t.denom() >= 1)
        ==> mo.num * t.denom() <= t.num * mo.denom()) by (nonlinear_arith);
}

/// −1 ≤ t ≤ 1 ⇒ |t| ∈ [0, 1].
pub proof fn lemma_symmetric_abs_unit_interval(t: Rational)
    requires
        t_in_symmetric_unit_interval(t),
    ensures
        t_in_unit_interval(t.abs_spec()),
{
    let z = Rational::from_int_spec(0);
    let mo = Rational::from_int_spec(-1);
    let one = Rational::from_int_spec(1);
    Rational::lemma_denom_positive(t);
    assert(mo.num == -1);
    assert(mo.denom() == 1);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(mo.le_spec(t) == (mo.num * t.denom() <= t.num * mo.denom()));
    assert(t.le_spec(one) == (t.num * one.denom() <= one.num * t.denom()));
    assert((mo.num * t.denom() <= t.num * mo.denom() && mo.num == -1 && mo.denom() == 1)
        ==> t.num >= -t.denom()) by (nonlinear_arith);
    assert((t.num * one.denom() <= one.num * t.denom() && one.num == 1 && one.denom() == 1)
        ==> t.num <= t.denom()) by (nonlinear_arith);
    if t.num >= 0 {
        assert(t.abs_spec() == t);
        assert(z.le_spec(t) == (z.num * t.denom() <= t.num * z.denom()));
        assert((z.num == 0 && z.denom() == 1 && t.num >= 0)
            ==> z.num * t.denom() <= t.num * z.denom()) by (nonlinear_arith);
    } else {
        assert(t.abs_spec() == t.neg_spec());
        let u = t.neg_spec();
        assert(u.num == -t.num);
        assert(u.denom() == t.denom());
        assert(z.le_spec(u) == (z.num * u.denom() <= u.num * z.denom()));
        assert(u.le_spec(one) == (u.num * one.denom() <= one.num * u.denom()));
        assert((u.num == -t.num && u.denom() == t.denom() && t.num < 0 && z.num == 0
            && z.denom() == 1)
            ==> z.num * u.denom() <= u.num * z.denom()) by (nonlinear_arith);
        assert((u.num == -t.num && u.denom() == t.denom() && t.num >= -t.denom()
            && one.num == 1 && one.denom() == 1)
            ==> u.num * one.denom() <= one.num * u.denom()) by (nonlinear_arith);
    }
}

/// The signed enclosure is ordered on the full symmetric range [−1, 1].
pub proof fn lemma_angle_enclosure_signed_ordered(t: Rational, k: nat)
    requires
        t_in_symmetric_unit_interval(t),
    ensures
        angle_enclosure_signed(t, k).0.le_spec(angle_enclosure_signed(t, k).1),
{
    lemma_symmetric_abs_unit_interval(t);
    let z = Rational::from_int_spec(0);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(t) == (z.num * t.denom() <= t.num * z.denom()));
    if z.le_spec(t) {
        assert(angle_enclosure_signed(t, k) == angle_enclosure(t, k));
        assert((z.num == 0 && z.denom() == 1 && z.num * t.denom() <= t.num * z.denom())
            ==> t.num >= 0) by (nonlinear_arith);
        assert(t.abs_spec() == t);
        lemma_angle_enclosure_ordered(t, k);
    } else {
        assert(angle_enclosure_signed(t, k).0 == angle_enclosure(t, k).1);
        assert(angle_enclosure_signed(t, k).1 == angle_enclosure(t, k).0);
        assert((z.num == 0 && z.denom() == 1
            && !(z.num * t.denom() <= t.num * z.denom()))
            ==> t.num < 0) by (nonlinear_arith);
        assert(t.abs_spec() == t.neg_spec());
        lemma_angle_enclosure_ordered_negative(t, k);
    }
}

/// (−a) − (−b) == b − a (structural helper for the width mirror).
pub proof fn lemma_raw_neg_sub_neg(a: Rational, b: Rational)
    ensures
        a.neg_spec().sub_spec(b.neg_spec()) == b.sub_spec(a),
{
    Rational::lemma_neg_involution(b);
    Rational::lemma_neg_add(a, b.neg_spec());
    Rational::lemma_neg_sub(a, b);
    assert(a.neg_spec().sub_spec(b.neg_spec())
        == a.neg_spec().add_spec(b.neg_spec().neg_spec()));
    assert(a.neg_spec().sub_spec(b.neg_spec()) == a.neg_spec().add_spec(b));
    assert(a.sub_spec(b).neg_spec() == a.neg_spec().add_spec(b.neg_spec().neg_spec()));
    assert(a.sub_spec(b).neg_spec() == b.sub_spec(a));
}

/// Uniform width on [−1, 1]: signed.hi − signed.lo ≡ 2·|term_{k+1}|.
/// This is what ties the ledger increment (SPEC §3, 2·|term|) to the
/// signed enclosure width for both signs of t.
pub proof fn lemma_angle_enclosure_signed_width(t: Rational, k: nat)
    requires
        t_in_symmetric_unit_interval(t),
    ensures
        angle_enclosure_signed(t, k).1.sub_spec(angle_enclosure_signed(t, k).0)
            .eqv_spec(two_x(arctan_term(t, (k + 1) as nat).abs_spec())),
{
    lemma_symmetric_abs_unit_interval(t);
    let z = Rational::from_int_spec(0);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(t) == (z.num * t.denom() <= t.num * z.denom()));
    let term = arctan_term(t, (k + 1) as nat);
    if z.le_spec(t) {
        // t ∈ [0,1]: signed == enc, term ≥ 0 so |term| == term
        assert((z.num == 0 && z.denom() == 1 && z.num * t.denom() <= t.num * z.denom())
            ==> t.num >= 0) by (nonlinear_arith);
        assert(angle_enclosure_signed(t, k) == angle_enclosure(t, k));
        lemma_arctan_term_nonneg(t, (k + 1) as nat);
        assert(z.le_spec(term) == (z.num * term.denom() <= term.num * z.denom()));
        assert((z.num == 0 && z.denom() == 1 && z.num * term.denom() <= term.num * z.denom())
            ==> term.num >= 0) by (nonlinear_arith);
        assert(term.abs_spec() == term);
        if k % 2 == 0 {
            lemma_arctan_width_even(t, k);
            assert(angle_enclosure_signed(t, k).1 == two_x(arctan_sum(t, k)));
            assert(angle_enclosure_signed(t, k).0 == two_x(arctan_sum(t, (k + 1) as nat)));
        } else {
            lemma_arctan_width_odd(t, k);
            assert(angle_enclosure_signed(t, k).1 == two_x(arctan_sum(t, (k + 1) as nat)));
            assert(angle_enclosure_signed(t, k).0 == two_x(arctan_sum(t, k)));
        }
    } else {
        // t < 0: u = −t ∈ [0,1]; enc(t) endpoints are negs of enc(u)
        assert((z.num == 0 && z.denom() == 1
            && !(z.num * t.denom() <= t.num * z.denom()))
            ==> t.num < 0) by (nonlinear_arith);
        assert(t.abs_spec() == t.neg_spec());
        let u = t.neg_spec();
        assert(angle_enclosure_signed(t, k).0 == angle_enclosure(t, k).1);
        assert(angle_enclosure_signed(t, k).1 == angle_enclosure(t, k).0);
        lemma_angle_enclosure_neg(t, k);
        if k % 2 == 0 {
            lemma_arctan_width_even(u, k);
        } else {
            lemma_arctan_width_odd(u, k);
        }
        // enc(u).1 − enc(u).0 ≡ 2·term(u) == 2·(−term(t)) == −(2·term(t))
        lemma_arctan_term_neg(t, (k + 1) as nat);
        lemma_two_x_neg(term);
        // |term(t)| == −term(t) since term(t).num < 0 (odd power of negative)
        lemma_arctan_term_num_denom(t, (k + 1) as nat);
        lemma_ipow_neg_odd(-t.num, 2 * (k + 1) + 1);
        lemma_ipow_pos(-t.num, 2 * (k + 1) + 1);
        assert(term.num == ipow(t.num, 2 * (k + 1) + 1));
        assert(term.num == -ipow(-t.num, 2 * (k + 1) + 1));
        assert(term.num < 0);
        assert(term.abs_spec() == term.neg_spec());
        // signed.1 − signed.0 == (−enc(u).0) − (−enc(u).1) == enc(u).1 − enc(u).0
        lemma_raw_neg_sub_neg(angle_enclosure(u, k).0, angle_enclosure(u, k).1);
        assert(angle_enclosure(t, k).0.sub_spec(angle_enclosure(t, k).1)
            == angle_enclosure(u, k).0.neg_spec().sub_spec(
                angle_enclosure(u, k).1.neg_spec()));
        assert(angle_enclosure_signed(t, k).1.sub_spec(angle_enclosure_signed(t, k).0)
            == angle_enclosure(u, k).1.sub_spec(angle_enclosure(u, k).0));
        // rhs: two_x(term.abs) == two_x(term.neg) == two_x(term(u))
        assert(two_x(term.abs_spec()) == two_x(term.neg_spec()));
        assert(two_x(term.neg_spec()) == two_x(arctan_term(u, (k + 1) as nat)));
        Rational::lemma_eqv_reflexive(two_x(arctan_term(u, (k + 1) as nat)));
    }
}

/// |term_j(t)| ≤ 1/(2j+1) on the full symmetric range [−1, 1] (uniform
/// term bound, signed — the mirror of lemma_arctan_term_bound).
pub proof fn lemma_arctan_term_abs_bound(t: Rational, j: nat)
    requires
        t_in_symmetric_unit_interval(t),
    ensures
        arctan_term(t, j).abs_spec().le_spec(
            Rational::from_frac_spec(1, (2 * j + 1) as int)),
{
    lemma_symmetric_abs_unit_interval(t);
    let z = Rational::from_int_spec(0);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(t) == (z.num * t.denom() <= t.num * z.denom()));
    let term = arctan_term(t, j);
    if z.le_spec(t) {
        assert((z.num == 0 && z.denom() == 1 && z.num * t.denom() <= t.num * z.denom())
            ==> t.num >= 0) by (nonlinear_arith);
        assert(t.abs_spec() == t);
        lemma_arctan_term_nonneg(t, j);
        lemma_arctan_term_bound(t, j);
        assert(z.le_spec(term) == (z.num * term.denom() <= term.num * z.denom()));
        assert((z.num == 0 && z.denom() == 1 && z.num * term.denom() <= term.num * z.denom())
            ==> term.num >= 0) by (nonlinear_arith);
        assert(term.abs_spec() == term);
    } else {
        assert((z.num == 0 && z.denom() == 1
            && !(z.num * t.denom() <= t.num * z.denom()))
            ==> t.num < 0) by (nonlinear_arith);
        assert(t.abs_spec() == t.neg_spec());
        let u = t.neg_spec();
        lemma_arctan_term_neg(t, j);
        lemma_arctan_term_bound(u, j);
        // term(t).num < 0 ⇒ |term(t)| == −term(t) == term(u)
        lemma_arctan_term_num_denom(t, j);
        lemma_ipow_neg_odd(-t.num, 2 * j + 1);
        lemma_ipow_pos(-t.num, 2 * j + 1);
        assert(term.num == ipow(t.num, 2 * j + 1));
        assert(term.num == -ipow(-t.num, 2 * j + 1));
        assert(term.num < 0);
        assert(term.abs_spec() == term.neg_spec());
        assert(term.neg_spec() == arctan_term(u, j));
    }
}

} // verus!
