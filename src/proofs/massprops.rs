//! Mass-property lemmas (phys-05a): the shoelace sum equals the fan sum,
//! and the fan sum is strictly positive for ccw convex polygons — so
//! area2 > 0, making the centroid and density constructors division-safe.
//!
//! Same R-discipline as proofs/rational_raw.rs: raw *_spec ops, eqv via
//! congruence chaining, implication-form NLA, exact body-form unfolds.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::massprops::{chain_cross_sum, cross_sum, fan_area2, fan_sum_upto};
use crate::proofs::rational_raw::lemma_raw_add_zero_right;
use crate::shape::{convex_poly_inv, orient, vadd, vcross2, vsub};

verus! {

// ── raw additive micro-lemmas ────────────────────────────────────────

/// (a − b) − (c − d) ≡ (a − c) − (b − d).
pub proof fn lemma_raw_sub_sub_swap(a: Rational, b: Rational, c: Rational, d: Rational)
    ensures
        a.sub_spec(b).sub_spec(c.sub_spec(d)).eqv_spec(
            a.sub_spec(c).sub_spec(b.sub_spec(d))),
{
    Rational::lemma_neg_sub(c, d);
    Rational::lemma_neg_sub(b, d);
    Rational::lemma_sub_add_distributes(a, d, b, c);
    Rational::lemma_sub_add_distributes(a, d, c, b);
    Rational::lemma_add_commutative(b, c);
    Rational::lemma_eqv_sub_congruence(
        a.add_spec(d), a.add_spec(d), b.add_spec(c), c.add_spec(b));
    assert(a.sub_spec(b).sub_spec(c.sub_spec(d))
        == a.sub_spec(b).add_spec(d.sub_spec(c)));
    assert(a.sub_spec(c).sub_spec(b.sub_spec(d))
        == a.sub_spec(c).add_spec(d.sub_spec(b)));
    Rational::lemma_eqv_symmetric(
        a.add_spec(d).sub_spec(b.add_spec(c)), a.sub_spec(b).add_spec(d.sub_spec(c)));
    Rational::lemma_eqv_transitive(
        a.sub_spec(b).add_spec(d.sub_spec(c)),
        a.add_spec(d).sub_spec(b.add_spec(c)),
        a.add_spec(d).sub_spec(c.add_spec(b)));
    Rational::lemma_eqv_transitive(
        a.sub_spec(b).add_spec(d.sub_spec(c)),
        a.add_spec(d).sub_spec(c.add_spec(b)),
        a.sub_spec(c).add_spec(d.sub_spec(b)));
}

/// (a − b) − c ≡ (a − c) − b.
pub proof fn lemma_raw_sub_sub_comm(a: Rational, b: Rational, c: Rational)
    ensures
        a.sub_spec(b).sub_spec(c).eqv_spec(a.sub_spec(c).sub_spec(b)),
{
    Rational::lemma_sub_is_add_neg(a.sub_spec(b), c);
    Rational::lemma_sub_is_add_neg(a, b);
    Rational::lemma_sub_is_add_neg(a, c);
    Rational::lemma_sub_is_add_neg(a.sub_spec(c), b);
    Rational::lemma_add_associative(a, b.neg_spec(), c.neg_spec());
    Rational::lemma_add_associative(a, c.neg_spec(), b.neg_spec());
    Rational::lemma_add_commutative(b.neg_spec(), c.neg_spec());
    Rational::lemma_eqv_add_congruence(
        a, a, b.neg_spec().add_spec(c.neg_spec()), c.neg_spec().add_spec(b.neg_spec()));
    Rational::lemma_eqv_transitive(
        a.add_spec(b.neg_spec()).add_spec(c.neg_spec()),
        a.add_spec(b.neg_spec().add_spec(c.neg_spec())),
        a.add_spec(c.neg_spec().add_spec(b.neg_spec())));
    Rational::lemma_eqv_symmetric(
        a.add_spec(c.neg_spec()).add_spec(b.neg_spec()),
        a.add_spec(c.neg_spec().add_spec(b.neg_spec())));
    Rational::lemma_eqv_transitive(
        a.add_spec(b.neg_spec()).add_spec(c.neg_spec()),
        a.add_spec(c.neg_spec().add_spec(b.neg_spec())),
        a.add_spec(c.neg_spec()).add_spec(b.neg_spec()));
    assert(a.sub_spec(b).sub_spec(c) == a.add_spec(b.neg_spec()).add_spec(c.neg_spec()));
    assert(a.sub_spec(c).sub_spec(b) == a.add_spec(c.neg_spec()).add_spec(b.neg_spec()));
}

/// x − 0 ≡ x.
pub proof fn lemma_raw_sub_zero_right(x: Rational)
    ensures
        x.sub_spec(Rational::from_int_spec(0)).eqv_spec(x),
{
    let z = Rational::from_int_spec(0);
    lemma_raw_add_zero_right(x);
    assert(z.neg_spec() == z);
    assert(x.sub_spec(z) == x.add_spec(z));
}

/// 0 < b ∧ a ≡ b ⇒ 0 < a.
pub proof fn lemma_raw_lt_zero_eqv_left(a: Rational, b: Rational)
    requires
        Rational::from_int_spec(0).lt_spec(b),
        a.eqv_spec(b),
    ensures
        Rational::from_int_spec(0).lt_spec(a),
{
    let z = Rational::from_int_spec(0);
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(b);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.lt_spec(b) == (z.num * b.denom() < b.num * z.denom()));
    assert(z.lt_spec(a) == (z.num * a.denom() < a.num * z.denom()));
    assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
    assert((b.num > 0 && a.num * b.denom() == b.num * a.denom()
        && a.denom() >= 1 && b.denom() >= 1)
        ==> a.num > 0) by (nonlinear_arith);
}

/// k·(a − b) ≡ k·a − k·b.
pub proof fn lemma_raw_mul_sub_left(k: Rational, a: Rational, b: Rational)
    ensures
        k.mul_spec(a.sub_spec(b)).eqv_spec(k.mul_spec(a).sub_spec(k.mul_spec(b))),
{
    Rational::lemma_mul_commutative(k, a.sub_spec(b));
    Rational::lemma_sub_mul_right(a, b, k);
    Rational::lemma_mul_commutative(k, a);
    Rational::lemma_mul_commutative(k, b);
    Rational::lemma_eqv_sub_congruence(
        a.mul_spec(k), k.mul_spec(a), b.mul_spec(k), k.mul_spec(b));
    Rational::lemma_eqv_transitive(
        k.mul_spec(a.sub_spec(b)), a.sub_spec(b).mul_spec(k),
        a.mul_spec(k).sub_spec(b.mul_spec(k)));
    Rational::lemma_eqv_transitive(
        k.mul_spec(a.sub_spec(b)),
        a.mul_spec(k).sub_spec(b.mul_spec(k)), k.mul_spec(a).sub_spec(k.mul_spec(b)));
}

// ── vcross2 algebra ──────────────────────────────────────────────────

/// cross(u − w, v) ≡ cross(u, v) − cross(w, v).
pub proof fn lemma_vcross2_sub_left(u: Vec2<Rational>, w: Vec2<Rational>, v: Vec2<Rational>)
    ensures
        vcross2(vsub(u, w), v).eqv_spec(vcross2(u, v).sub_spec(vcross2(w, v))),
{
    Rational::lemma_sub_mul_right(u.x, w.x, v.y);
    Rational::lemma_sub_mul_right(u.y, w.y, v.x);
    Rational::lemma_eqv_sub_congruence(
        u.x.sub_spec(w.x).mul_spec(v.y), u.x.mul_spec(v.y).sub_spec(w.x.mul_spec(v.y)),
        u.y.sub_spec(w.y).mul_spec(v.x), u.y.mul_spec(v.x).sub_spec(w.y.mul_spec(v.x)));
    lemma_raw_sub_sub_swap(
        u.x.mul_spec(v.y), w.x.mul_spec(v.y), u.y.mul_spec(v.x), w.y.mul_spec(v.x));
    assert(vcross2(vsub(u, w), v) == u.x.sub_spec(w.x).mul_spec(v.y).sub_spec(
        u.y.sub_spec(w.y).mul_spec(v.x)));
    assert(vcross2(u, v) == u.x.mul_spec(v.y).sub_spec(u.y.mul_spec(v.x)));
    assert(vcross2(w, v) == w.x.mul_spec(v.y).sub_spec(w.y.mul_spec(v.x)));
    Rational::lemma_eqv_transitive(
        vcross2(vsub(u, w), v),
        u.x.mul_spec(v.y).sub_spec(w.x.mul_spec(v.y)).sub_spec(
            u.y.mul_spec(v.x).sub_spec(w.y.mul_spec(v.x))),
        vcross2(u, v).sub_spec(vcross2(w, v)));
}

/// cross(u, v − w) ≡ cross(u, v) − cross(u, w).
pub proof fn lemma_vcross2_sub_right(u: Vec2<Rational>, v: Vec2<Rational>, w: Vec2<Rational>)
    ensures
        vcross2(u, vsub(v, w)).eqv_spec(vcross2(u, v).sub_spec(vcross2(u, w))),
{
    lemma_raw_mul_sub_left(u.x, v.y, w.y);
    lemma_raw_mul_sub_left(u.y, v.x, w.x);
    Rational::lemma_eqv_sub_congruence(
        u.x.mul_spec(v.y.sub_spec(w.y)), u.x.mul_spec(v.y).sub_spec(u.x.mul_spec(w.y)),
        u.y.mul_spec(v.x.sub_spec(w.x)), u.y.mul_spec(v.x).sub_spec(u.y.mul_spec(w.x)));
    lemma_raw_sub_sub_swap(
        u.x.mul_spec(v.y), u.x.mul_spec(w.y), u.y.mul_spec(v.x), u.y.mul_spec(w.x));
    assert(vcross2(u, vsub(v, w)) == u.x.mul_spec(v.y.sub_spec(w.y)).sub_spec(
        u.y.mul_spec(v.x.sub_spec(w.x))));
    assert(vcross2(u, v) == u.x.mul_spec(v.y).sub_spec(u.y.mul_spec(v.x)));
    assert(vcross2(u, w) == u.x.mul_spec(w.y).sub_spec(u.y.mul_spec(w.x)));
    Rational::lemma_eqv_transitive(
        vcross2(u, vsub(v, w)),
        u.x.mul_spec(v.y).sub_spec(u.x.mul_spec(w.y)).sub_spec(
            u.y.mul_spec(v.x).sub_spec(u.y.mul_spec(w.x))),
        vcross2(u, v).sub_spec(vcross2(u, w)));
}

/// cross(a, a) ≡ 0.
pub proof fn lemma_vcross2_self(a: Vec2<Rational>)
    ensures
        vcross2(a, a).eqv_spec(Rational::from_int_spec(0)),
{
    Rational::lemma_mul_commutative(a.x, a.y);
    Rational::lemma_eqv_reflexive(a.y.mul_spec(a.x));
    Rational::lemma_eqv_sub_congruence(
        a.x.mul_spec(a.y), a.y.mul_spec(a.x), a.y.mul_spec(a.x), a.y.mul_spec(a.x));
    Rational::lemma_sub_self(a.y.mul_spec(a.x));
    assert(vcross2(a, a) == a.x.mul_spec(a.y).sub_spec(a.y.mul_spec(a.x)));
    Rational::lemma_eqv_transitive(
        vcross2(a, a),
        a.y.mul_spec(a.x).sub_spec(a.y.mul_spec(a.x)),
        Rational::from_int_spec(0));
}

/// cross(a, b) ≡ −cross(b, a).
pub proof fn lemma_vcross2_antisym(a: Vec2<Rational>, b: Vec2<Rational>)
    ensures
        vcross2(a, b).eqv_spec(vcross2(b, a).neg_spec()),
{
    Rational::lemma_neg_sub(b.x.mul_spec(a.y), b.y.mul_spec(a.x));
    Rational::lemma_mul_commutative(b.y, a.x);
    Rational::lemma_mul_commutative(b.x, a.y);
    Rational::lemma_eqv_sub_congruence(
        b.y.mul_spec(a.x), a.x.mul_spec(b.y), b.x.mul_spec(a.y), a.y.mul_spec(b.x));
    assert(vcross2(b, a).neg_spec() == b.y.mul_spec(a.x).sub_spec(b.x.mul_spec(a.y)));
    assert(vcross2(a, b) == a.x.mul_spec(b.y).sub_spec(a.y.mul_spec(b.x)));
    Rational::lemma_eqv_symmetric(
        b.y.mul_spec(a.x).sub_spec(b.x.mul_spec(a.y)), vcross2(a, b));
    Rational::lemma_eqv_transitive(
        vcross2(a, b),
        b.y.mul_spec(a.x).sub_spec(b.x.mul_spec(a.y)),
        vcross2(b, a).neg_spec());
}

/// orient(a,b,c) ≡ cross(b,c) − cross(b,a) − cross(a,c).
pub proof fn lemma_orient_expand(a: Vec2<Rational>, b: Vec2<Rational>, c: Vec2<Rational>)
    ensures
        orient(a, b, c).eqv_spec(
            vcross2(b, c).sub_spec(vcross2(b, a)).sub_spec(vcross2(a, c))),
{
    lemma_vcross2_sub_left(b, a, vsub(c, a));
    lemma_vcross2_sub_right(b, c, a);
    lemma_vcross2_sub_right(a, c, a);
    lemma_vcross2_self(a);
    lemma_raw_sub_zero_right(vcross2(a, c));
    // cross(a, c−a) ≡ cross(a,c) − cross(a,a) ≡ cross(a,c) − 0 ≡ cross(a,c)
    Rational::lemma_eqv_sub_congruence(
        vcross2(a, c), vcross2(a, c), vcross2(a, a), Rational::from_int_spec(0));
    Rational::lemma_eqv_transitive(
        vcross2(a, vsub(c, a)), vcross2(a, c).sub_spec(vcross2(a, a)),
        vcross2(a, c).sub_spec(Rational::from_int_spec(0)));
    Rational::lemma_eqv_transitive(
        vcross2(a, vsub(c, a)), vcross2(a, c).sub_spec(Rational::from_int_spec(0)),
        vcross2(a, c));
    Rational::lemma_eqv_sub_congruence(
        vcross2(b, vsub(c, a)), vcross2(b, c).sub_spec(vcross2(b, a)),
        vcross2(a, vsub(c, a)), vcross2(a, c));
    assert(orient(a, b, c) == vcross2(vsub(b, a), vsub(c, a)));
    Rational::lemma_eqv_transitive(
        orient(a, b, c),
        vcross2(b, vsub(c, a)).sub_spec(vcross2(a, vsub(c, a))),
        vcross2(b, c).sub_spec(vcross2(b, a)).sub_spec(vcross2(a, c)));
}

/// orient(a,b,c) ≡ orient(b,c,a) (cyclic rotation).
pub proof fn lemma_orient_rotate(a: Vec2<Rational>, b: Vec2<Rational>, c: Vec2<Rational>)
    ensures
        orient(a, b, c).eqv_spec(orient(b, c, a)),
{
    lemma_orient_expand(a, b, c);
    lemma_orient_expand(b, c, a);
    lemma_vcross2_antisym(c, a);
    lemma_vcross2_antisym(c, b);
    // orient(b,c,a) ≡ cross(c,a) − cross(c,b) − cross(b,a)
    //   ≡ (−cross(a,c)) − (−cross(b,c)) − cross(b,a)
    //   ≡ (cross(b,c) − cross(a,c)) − cross(b,a)   [neg arithmetic]
    //   ≡ (cross(b,c) − cross(b,a)) − cross(a,c)   [sub_sub_comm]
    Rational::lemma_neg_involution(vcross2(b, c));
    Rational::lemma_add_commutative(vcross2(a, c).neg_spec(), vcross2(b, c));
    Rational::lemma_eqv_sub_congruence(
        vcross2(c, a), vcross2(a, c).neg_spec(), vcross2(c, b), vcross2(b, c).neg_spec());
    assert(vcross2(c, a).sub_spec(vcross2(c, b)).eqv_spec(
        vcross2(a, c).neg_spec().add_spec(vcross2(b, c))));
    assert(vcross2(a, c).neg_spec().add_spec(vcross2(b, c)) ==
        vcross2(b, c).sub_spec(vcross2(a, c)));
    Rational::lemma_eqv_symmetric(
        vcross2(a, c).neg_spec().add_spec(vcross2(b, c)),
        vcross2(b, c).add_spec(vcross2(a, c).neg_spec()));
    Rational::lemma_eqv_transitive(
        vcross2(c, a).sub_spec(vcross2(c, b)),
        vcross2(a, c).neg_spec().add_spec(vcross2(b, c)),
        vcross2(b, c).sub_spec(vcross2(a, c)));
    lemma_raw_sub_sub_comm(vcross2(b, c), vcross2(a, c), vcross2(b, a));
    Rational::lemma_eqv_sub_congruence(
        vcross2(c, a).sub_spec(vcross2(c, b)), vcross2(b, c).sub_spec(vcross2(a, c)),
        vcross2(b, a), vcross2(b, a));
    Rational::lemma_eqv_transitive(
        vcross2(c, a).sub_spec(vcross2(c, b)).sub_spec(vcross2(b, a)),
        vcross2(b, c).sub_spec(vcross2(a, c)).sub_spec(vcross2(b, a)),
        vcross2(b, c).sub_spec(vcross2(b, a)).sub_spec(vcross2(a, c)));
    // link orient(b,c,a) through its expansion to the rearranged form
    Rational::lemma_eqv_transitive(
        orient(b, c, a),
        vcross2(c, a).sub_spec(vcross2(c, b)).sub_spec(vcross2(b, a)),
        vcross2(b, c).sub_spec(vcross2(b, a)).sub_spec(vcross2(a, c)));
    Rational::lemma_eqv_symmetric(
        orient(b, c, a),
        vcross2(b, c).sub_spec(vcross2(b, a)).sub_spec(vcross2(a, c)));
    Rational::lemma_eqv_transitive(
        orient(a, b, c),
        vcross2(b, c).sub_spec(vcross2(b, a)).sub_spec(vcross2(a, c)),
        orient(b, c, a));
}

// ── the fan identity ─────────────────────────────────────────────────

/// chain_cross_sum(vs, i) ≡ fan_sum_upto(vs, i) + cross(vs[0], vs[i]).
pub proof fn lemma_chain_fan(vs: Seq<Vec2<Rational>>, i: int)
    requires
        1 <= i <= vs.len() - 1,
    ensures
        chain_cross_sum(vs, i).eqv_spec(
            fan_sum_upto(vs, i).add_spec(vcross2(vs[0], vs[i]))),
    decreases i
{
    let z = Rational::from_int_spec(0);
    if i == 1 {
        assert(chain_cross_sum(vs, 1) == chain_cross_sum(vs, 0).add_spec(
            vcross2(vs[0], vs[1])));
        assert(chain_cross_sum(vs, 0) == z);
        assert(fan_sum_upto(vs, 1) == z);
        Rational::lemma_add_commutative(z, vcross2(vs[0], vs[1]));
        lemma_raw_add_zero_right(vcross2(vs[0], vs[1]));
        Rational::lemma_eqv_transitive(
            z.add_spec(vcross2(vs[0], vs[1])),
            vcross2(vs[0], vs[1]).add_spec(z),
            vcross2(vs[0], vs[1]));
        Rational::lemma_eqv_transitive(
            chain_cross_sum(vs, 1),
            z.add_spec(vcross2(vs[0], vs[1])),
            vcross2(vs[0], vs[1]));
        Rational::lemma_eqv_symmetric(
            fan_sum_upto(vs, 1).add_spec(vcross2(vs[0], vs[1])), vcross2(vs[0], vs[1]));
        Rational::lemma_eqv_transitive(
            chain_cross_sum(vs, 1),
            vcross2(vs[0], vs[1]),
            fan_sum_upto(vs, 1).add_spec(vcross2(vs[0], vs[1])));
    } else {
        lemma_chain_fan(vs, i - 1);
        lemma_orient_expand(vs[0], vs[i - 1], vs[i]);
        lemma_vcross2_antisym(vs[i - 1], vs[0]);
        // orient_j ≡ (t − (−u)) − v == (t + u) − v
        let t = vcross2(vs[i - 1], vs[i]);
        let u = vcross2(vs[0], vs[i - 1]);
        let v = vcross2(vs[0], vs[i]);
        let f = fan_sum_upto(vs, i - 1);
        let oj = orient(vs[0], vs[i - 1], vs[i]);
        Rational::lemma_neg_involution(u);
        Rational::lemma_eqv_sub_congruence(t, t, vcross2(vs[i - 1], vs[0]), u.neg_spec());
        assert(t.sub_spec(vcross2(vs[i - 1], vs[0])) == t.add_spec(
            vcross2(vs[i - 1], vs[0]).neg_spec()));
        assert(t.add_spec(u.neg_spec().neg_spec()) == t.add_spec(u));
        Rational::lemma_eqv_sub_congruence(
            t.sub_spec(vcross2(vs[i - 1], vs[0])), t.add_spec(u), v, v);
        Rational::lemma_eqv_transitive(
            oj,
            t.sub_spec(vcross2(vs[i - 1], vs[0])).sub_spec(v),
            t.add_spec(u).sub_spec(v));
        // (f + oj) + v ≡ (f + x) + v ≡ f + (x + v) ≡ f + (t+u), x = (t+u) − v
        assert(fan_sum_upto(vs, i) == f.add_spec(oj));
        Rational::lemma_eqv_add_congruence(f, f, oj, t.add_spec(u).sub_spec(v));
        Rational::lemma_eqv_add_congruence(
            f.add_spec(oj), f.add_spec(t.add_spec(u).sub_spec(v)), v, v);
        Rational::lemma_add_associative(f, t.add_spec(u).sub_spec(v), v);
        Rational::lemma_sub_then_add_cancel(t.add_spec(u), v);
        Rational::lemma_eqv_add_congruence(f, f, t.add_spec(u).sub_spec(v).add_spec(v), t.add_spec(u));
        Rational::lemma_eqv_transitive(
            f.add_spec(oj).add_spec(v),
            f.add_spec(t.add_spec(u).sub_spec(v)).add_spec(v),
            f.add_spec(t.add_spec(u).sub_spec(v).add_spec(v)));
        Rational::lemma_eqv_transitive(
            f.add_spec(oj).add_spec(v),
            f.add_spec(t.add_spec(u).sub_spec(v).add_spec(v)),
            f.add_spec(t.add_spec(u)));
        // f + (t+u) ≡ f + (u+t) ≡ (f+u) + t ≡ chain(i−1) + t == chain(i)
        Rational::lemma_add_commutative(t, u);
        Rational::lemma_eqv_add_congruence(f, f, t.add_spec(u), u.add_spec(t));
        Rational::lemma_eqv_transitive(
            f.add_spec(oj).add_spec(v), f.add_spec(t.add_spec(u)), f.add_spec(u.add_spec(t)));
        Rational::lemma_add_associative(f, u, t);
        Rational::lemma_eqv_symmetric(f.add_spec(u).add_spec(t), f.add_spec(u.add_spec(t)));
        Rational::lemma_eqv_transitive(
            f.add_spec(oj).add_spec(v), f.add_spec(u.add_spec(t)), f.add_spec(u).add_spec(t));
        Rational::lemma_eqv_add_congruence(f.add_spec(u), chain_cross_sum(vs, i - 1), t, t);
        Rational::lemma_eqv_transitive(
            f.add_spec(oj).add_spec(v),
            f.add_spec(u).add_spec(t),
            chain_cross_sum(vs, i - 1).add_spec(t));
        assert(chain_cross_sum(vs, i) == chain_cross_sum(vs, i - 1).add_spec(
            vcross2(vs[i - 1], vs[i])));
        assert(fan_sum_upto(vs, i).add_spec(v) == f.add_spec(oj).add_spec(v));
        Rational::lemma_eqv_symmetric(
            fan_sum_upto(vs, i).add_spec(v), chain_cross_sum(vs, i));
    }
}

/// The shoelace sum equals the fan sum (twice the signed area).
pub proof fn lemma_cross_sum_eqv_fan(vs: Seq<Vec2<Rational>>)
    requires
        vs.len() >= 3,
    ensures
        cross_sum(vs).eqv_spec(fan_area2(vs)),
{
    let n = vs.len();
    lemma_chain_fan(vs, n - 1);
    lemma_vcross2_antisym(vs[n - 1], vs[0]);
    let u = vcross2(vs[0], vs[n - 1]);
    let closing = vcross2(vs[n - 1], vs[0]);
    let f = fan_sum_upto(vs, n - 1);
    // closing ≡ −u;  u + (−u) == u − u ≡ 0
    Rational::lemma_sub_self(u);
    assert(u.add_spec(u.neg_spec()) == u.sub_spec(u));
    Rational::lemma_eqv_add_congruence(u, u, closing, u.neg_spec());
    Rational::lemma_eqv_transitive(
        u.add_spec(closing), u.add_spec(u.neg_spec()), Rational::from_int_spec(0));
    // (f + u) + closing ≡ f + (u + closing) ≡ f + 0 ≡ f
    Rational::lemma_add_associative(f, u, closing);
    Rational::lemma_eqv_add_congruence(f, f, u.add_spec(closing), Rational::from_int_spec(0));
    lemma_raw_add_zero_right(f);
    Rational::lemma_eqv_transitive(
        f.add_spec(u).add_spec(closing),
        f.add_spec(u.add_spec(closing)),
        f.add_spec(Rational::from_int_spec(0)));
    Rational::lemma_eqv_transitive(
        f.add_spec(u).add_spec(closing), f.add_spec(Rational::from_int_spec(0)), f);
    // cross_sum == chain(n−1) + closing ≡ (f + u) + closing
    assert(cross_sum(vs) == chain_cross_sum(vs, n - 1).add_spec(closing));
    Rational::lemma_eqv_add_congruence(chain_cross_sum(vs, n - 1), f.add_spec(u), closing, closing);
    Rational::lemma_eqv_transitive(
        cross_sum(vs), f.add_spec(u).add_spec(closing), f);
    assert(fan_area2(vs) == f);
}

// ── positivity ───────────────────────────────────────────────────────

/// 1 ≤ j ≤ n−2 ⇒ orient(vs[0], vs[j], vs[j+1]) > 0 (global convexity +
/// cyclic rotation of orient).
pub proof fn lemma_fan_term_pos(vs: Seq<Vec2<Rational>>, j: int)
    requires
        convex_poly_inv(vs),
        1 <= j <= vs.len() - 2,
    ensures
        Rational::from_int_spec(0).lt_spec(orient(vs[0], vs[j], vs[j + 1])),
{
    let n = vs.len() as int;
    assert(3 <= n);
    assert(0 <= j < n);
    assert(0 <= 0 < n);
    assert(j + 1 < n);
    vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, n as nat);
    assert((j + 1) % n == j + 1);
    assert(0 != j && 0 != (j + 1) % n);
    // global invariant at edge j, vertex 0
    assert(Rational::from_int_spec(0).lt_spec(orient(vs[j], vs[(j + 1) % n], vs[0])));
    lemma_orient_rotate(vs[0], vs[j], vs[j + 1]);
    lemma_raw_lt_zero_eqv_left(orient(vs[0], vs[j], vs[j + 1]), orient(vs[j], vs[j + 1], vs[0]));
}

/// The fan sum is strictly positive (sum of strictly positive terms).
pub proof fn lemma_fan_pos(vs: Seq<Vec2<Rational>>, i: int)
    requires
        convex_poly_inv(vs),
        2 <= i <= vs.len() - 1,
    ensures
        Rational::from_int_spec(0).lt_spec(fan_sum_upto(vs, i)),
    decreases i
{
    let z = Rational::from_int_spec(0);
    if i == 2 {
        lemma_fan_term_pos(vs, 1);
        assert(fan_sum_upto(vs, 2) == fan_sum_upto(vs, 1).add_spec(
            orient(vs[0], vs[1], vs[2])));
        assert(fan_sum_upto(vs, 1) == z);
        Rational::lemma_add_commutative(z, orient(vs[0], vs[1], vs[2]));
        lemma_raw_add_zero_right(orient(vs[0], vs[1], vs[2]));
        Rational::lemma_eqv_transitive(
            z.add_spec(orient(vs[0], vs[1], vs[2])),
            orient(vs[0], vs[1], vs[2]).add_spec(z),
            orient(vs[0], vs[1], vs[2]));
        lemma_raw_lt_zero_eqv_left(
            z.add_spec(orient(vs[0], vs[1], vs[2])), orient(vs[0], vs[1], vs[2]));
    } else {
        lemma_fan_pos(vs, i - 1);
        lemma_fan_term_pos(vs, i - 1);
        Rational::lemma_lt_add_both(
            z, fan_sum_upto(vs, i - 1), z, orient(vs[0], vs[i - 1], vs[i]));
        assert(z.add_spec(z) == z);
        assert(fan_sum_upto(vs, i) == fan_sum_upto(vs, i - 1).add_spec(
            orient(vs[0], vs[i - 1], vs[i])));
    }
}

/// area2 > 0 for ccw convex polygons (SPEC §4, division safety).
pub proof fn lemma_area2_pos(vs: Seq<Vec2<Rational>>)
    requires
        convex_poly_inv(vs),
    ensures
        Rational::from_int_spec(0).lt_spec(cross_sum(vs)),
{
    assert(vs.len() >= 3);
    lemma_fan_pos(vs, vs.len() - 1);
    lemma_cross_sum_eqv_fan(vs);
    assert(fan_area2(vs) == fan_sum_upto(vs, vs.len() - 1));
    lemma_raw_lt_zero_eqv_left(cross_sum(vs), fan_area2(vs));
}

} // verus!
