//! Integer and rational power machinery for the angle ledger (phys-02b).
//!
//! `ipow` is ordinary integer exponentiation; `rpow` is exponentiation on
//! raw Rational ops. The connection lemmas reduce every statement about
//! rpow to int arithmetic on num/den, where the R-discipline (see
//! proofs/rational_raw.rs header) applies.

use vstd::prelude::*;

use verus_rational::Rational;

verus! {

/// x^p on integers.
pub open spec fn ipow(x: int, p: nat) -> int
    decreases p
{
    if p == 0 {
        1
    } else {
        x * ipow(x, (p - 1) as nat)
    }
}

/// t^p on raw Rational ops.
pub open spec fn rpow(t: Rational, p: nat) -> Rational
    decreases p
{
    if p == 0 {
        Rational::from_int_spec(1)
    } else {
        t.mul_spec(rpow(t, (p - 1) as nat))
    }
}

// ── ipow basics ──────────────────────────────────────────────────────

pub proof fn lemma_ipow_zero(x: int)
    ensures ipow(x, 0) == 1,
{
}

pub proof fn lemma_ipow_one(x: int)
    ensures ipow(x, 1) == x,
{
    assert(ipow(x, 1) == x * ipow(x, 0));
}

/// x^(a+b) == x^a · x^b, by induction on b.
pub proof fn lemma_ipow_add(x: int, a: nat, b: nat)
    ensures ipow(x, a + b) == ipow(x, a) * ipow(x, b),
    decreases b
{
    if b == 0 {
        assert(ipow(x, a + 0) == ipow(x, a));
        assert(ipow(x, a) * ipow(x, 0) == ipow(x, a));
    } else {
        lemma_ipow_add(x, a, (b - 1) as nat);
        assert(ipow(x, a + b) == x * ipow(x, (a + b - 1) as nat));
        assert(ipow(x, a + b) == x * (ipow(x, a) * ipow(x, (b - 1) as nat)));
        assert(ipow(x, b) == x * ipow(x, (b - 1) as nat));
        assert(x * (ipow(x, a) * ipow(x, (b - 1) as nat)) == ipow(x, a) * (x * ipow(x, (b - 1) as nat)))
            by (nonlinear_arith);
    }
}

/// x^(2p) == (x^p)² — the squaring step used for even exponents.
pub proof fn lemma_ipow_double(x: int, p: nat)
    ensures ipow(x, 2 * p) == ipow(x, p) * ipow(x, p),
{
    lemma_ipow_add(x, p, p);
    assert(p + p == 2 * p);
}

/// x ≥ 0 ⇒ x^p ≥ 0.
pub proof fn lemma_ipow_nonneg(x: int, p: nat)
    requires x >= 0,
    ensures ipow(x, p) >= 0,
    decreases p
{
    if p > 0 {
        lemma_ipow_nonneg(x, (p - 1) as nat);
        assert(x >= 0 && ipow(x, (p - 1) as nat) >= 0
            ==> x * ipow(x, (p - 1) as nat) >= 0) by (nonlinear_arith);
    }
}

/// x ≥ 1 ⇒ x^p ≥ 1.
pub proof fn lemma_ipow_pos(x: int, p: nat)
    requires x >= 1,
    ensures ipow(x, p) >= 1,
    decreases p
{
    if p > 0 {
        lemma_ipow_pos(x, (p - 1) as nat);
        assert(x >= 1 && ipow(x, (p - 1) as nat) >= 1
            ==> x * ipow(x, (p - 1) as nat) >= 1) by (nonlinear_arith);
    }
}

/// 0 ≤ x ≤ y ⇒ x^p ≤ y^p.
pub proof fn lemma_ipow_le(x: int, y: int, p: nat)
    requires 0 <= x, x <= y,
    ensures ipow(x, p) <= ipow(y, p),
    decreases p
{
    if p > 0 {
        lemma_ipow_le(x, y, (p - 1) as nat);
        lemma_ipow_nonneg(y, (p - 1) as nat);
        lemma_ipow_nonneg(x, (p - 1) as nat);
        assert(0 <= x && x <= y
            && 0 <= ipow(x, (p - 1) as nat) && ipow(x, (p - 1) as nat) <= ipow(y, (p - 1) as nat)
            ==> x * ipow(x, (p - 1) as nat) <= y * ipow(y, (p - 1) as nat))
            by (nonlinear_arith);
    }
}

/// Powers of equal ints are equal (congruence helper for staging).
pub proof fn lemma_ipow_congruence(x: int, y: int, p: nat)
    requires x == y,
    ensures ipow(x, p) == ipow(y, p),
    decreases p
{
    if p > 0 {
        lemma_ipow_congruence(x, y, (p - 1) as nat);
    }
}

/// p odd ⇒ (−x)^p == −(x^p) — the sign mirror for odd powers.
pub proof fn lemma_ipow_neg_odd(x: int, p: nat)
    requires
        p % 2 == 1,
    ensures
        ipow(-x, p) == -ipow(x, p),
    decreases p
{
    if p == 1 {
        assert(ipow(-x, 1) == -x) by { reveal_with_fuel(ipow, 2); }
        assert(ipow(x, 1) == x) by { reveal_with_fuel(ipow, 2); }
    } else {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int, 2);
        assert(p == 2 * (p / 2) + 1);
        assert(p >= 3);
        let q = (p - 2) as nat;
        assert(q == 2 * ((p / 2) - 1) + 1);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q as int, 2);
        assert(q % 2 == 1);
        lemma_ipow_neg_odd(x, q);
        lemma_ipow_add(-x, q, 2);
        lemma_ipow_add(x, q, 2);
        lemma_ipow_double(-x, 1);
        lemma_ipow_double(x, 1);
        lemma_ipow_one(-x);
        lemma_ipow_one(x);
        assert((ipow(-x, 2) == ipow(-x, 1) * ipow(-x, 1) && ipow(-x, 1) == -x)
            ==> ipow(-x, 2) == x * x) by (nonlinear_arith);
        assert((ipow(-x, q) == -ipow(x, q) && ipow(-x, 2) == x * x && ipow(x, 2) == x * x)
            ==> (-ipow(x, q)) * (x * x) == -(ipow(x, q) * (x * x))) by (nonlinear_arith);
        assert(ipow(-x, p) == ipow(-x, q) * ipow(-x, 2));
        assert(ipow(x, p) == ipow(x, q) * ipow(x, 2));
    }
}

/// 0^p == 0 for p > 0.
pub proof fn lemma_ipow_zero_base(p: nat)
    requires
        p > 0,
    ensures
        ipow(0, p) == 0,
    decreases p
{
    if p > 1 {
        lemma_ipow_zero_base((p - 1) as nat);
        assert(ipow(0, p) == 0 * ipow(0, (p - 1) as nat));
    } else {
        assert(ipow(0, 1) == 0) by { reveal_with_fuel(ipow, 2); }
    }
}

// ── rpow <-> ipow connection ─────────────────────────────────────────

/// rpow(t, p).num == ipow(t.num, p) and rpow(t, p).denom() == ipow(t.denom(), p).
pub proof fn lemma_rpow_num_denom(t: Rational, p: nat)
    ensures
        rpow(t, p).num == ipow(t.num, p),
        rpow(t, p).denom() == ipow(t.denom(), p),
    decreases p
{
    if p == 0 {
        let one = Rational::from_int_spec(1);
        assert(rpow(t, 0) == one);
        assert(one.num == 1);
        assert(one.denom() == 1);
    } else {
        lemma_rpow_num_denom(t, (p - 1) as nat);
        let prev = rpow(t, (p - 1) as nat);
        let cur = rpow(t, p);
        assert(cur == t.mul_spec(prev));
        // 1-level unfolds of the mul_spec node
        assert(cur.num == t.num * prev.num);
        Rational::lemma_mul_denom_product_int(t, prev);
        // combine
        assert(cur.num == t.num * ipow(t.num, (p - 1) as nat));
        assert(ipow(t.num, p) == t.num * ipow(t.num, (p - 1) as nat));
        assert(cur.denom() == t.denom() * prev.denom());
        assert(cur.denom() == t.denom() * ipow(t.denom(), (p - 1) as nat));
        assert(ipow(t.denom(), p) == t.denom() * ipow(t.denom(), (p - 1) as nat));
    }
}

} // verus!
