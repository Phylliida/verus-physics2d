//! Proof helpers for manifold construction (SPEC §5 step 3): dot-product
//! linearity through interpolation, the clip span bounds, and the exact
//! point-to-face separation of reported contact points. House discipline:
//! eqv chains via verus-rational's algebra/ordering lemmas, no closed
//! eval, no real-valued NLA.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::massprops::{vdot, vscale};
use crate::shape::{axis_sep, convex_poly_inv, edge_normal, orient, vadd, vsub};

verus! {

//  ── Scalar micro-lemmas ─────────────────────────────────────────────

/// a·(b − c) ≡ a·b − a·c.
pub proof fn lemma_mul_distributes_over_sub(a: Rational, b: Rational, c: Rational)
    ensures
        a.mul_spec(b.sub_spec(c)).eqv_spec(a.mul_spec(b).sub_spec(a.mul_spec(c))),
{
    // sub_spec is definitionally add-neg; mul_neg_right is structural.
    Rational::lemma_mul_distributes_over_add(a, b, c.neg_spec());
    Rational::lemma_mul_neg_right(a, c);
    Rational::lemma_eqv_reflexive(a.mul_spec(b));
}

/// (x + y) − z ≡ (x − z) + y.
pub proof fn lemma_add_sub_swap(x: Rational, y: Rational, z: Rational)
    ensures
        x.add_spec(y).sub_spec(z).eqv_spec(x.sub_spec(z).add_spec(y)),
{
    // Both sides unfold to add-neg forms; chain assoc/comm.
    Rational::lemma_add_associative(x, y, z.neg_spec());
    // (x+y)+(−z) ≡ x+(y+(−z))
    Rational::lemma_add_commutative(y, z.neg_spec());
    Rational::lemma_eqv_reflexive(x);
    Rational::lemma_eqv_add_congruence(
        x, x, y.add_spec(z.neg_spec()), z.neg_spec().add_spec(y));
    // x+(y+(−z)) ≡ x+((−z)+y)
    Rational::lemma_add_associative(x, z.neg_spec(), y);
    Rational::lemma_eqv_symmetric(
        x.add_spec(z.neg_spec()).add_spec(y), x.add_spec(z.neg_spec().add_spec(y)));
    // x+((−z)+y) ≡ (x+(−z))+y
    Rational::lemma_eqv_transitive(
        x.add_spec(y).add_spec(z.neg_spec()),
        x.add_spec(y.add_spec(z.neg_spec())),
        x.add_spec(z.neg_spec().add_spec(y)));
    Rational::lemma_eqv_transitive(
        x.add_spec(y).add_spec(z.neg_spec()),
        x.add_spec(z.neg_spec().add_spec(y)),
        x.add_spec(z.neg_spec()).add_spec(y));
}

/// (x − z) − (y − z) ≡ x − y.
pub proof fn lemma_sub_sub_cancel(x: Rational, y: Rational, z: Rational)
    ensures
        x.sub_spec(z).sub_spec(y.sub_spec(z)).eqv_spec(x.sub_spec(y)),
{
    // −(y + (−z)) == (−y) + z  (structural: neg_add + neg involution)
    Rational::lemma_neg_add(y, z.neg_spec());
    // (x + (−z)) + ((−y) + z)
    Rational::lemma_add_associative(x, z.neg_spec(), y.neg_spec().add_spec(z));
    // ≡ x + ((−z) + ((−y) + z))
    Rational::lemma_add_commutative(z.neg_spec(), y.neg_spec().add_spec(z));
    Rational::lemma_add_associative(y.neg_spec(), z, z.neg_spec());
    // (y.neg_spec().add_spec(z)).add_spec(z.neg_spec()) ≡ (−y) + (z + (−z))
    Rational::lemma_eqv_symmetric(
        y.neg_spec().add_spec(z.add_spec(z.neg_spec())),
        y.neg_spec().add_spec(z).add_spec(z.neg_spec()));
    Rational::lemma_add_inverse(z);
    // z + (−z) ≡ 0
    Rational::lemma_eqv_reflexive(y.neg_spec());
    Rational::lemma_eqv_add_congruence(
        y.neg_spec(), y.neg_spec(), z.add_spec(z.neg_spec()), Rational::from_int_spec(0));
    Rational::lemma_eqv_transitive(
        y.neg_spec().add_spec(z).add_spec(z.neg_spec()),
        y.neg_spec().add_spec(z.add_spec(z.neg_spec())),
        y.neg_spec().add_spec(Rational::from_int_spec(0)));
    // (−y) + 0 ≡ −y
    Rational::lemma_add_zero_identity(y.neg_spec());
    Rational::lemma_eqv_transitive(
        y.neg_spec().add_spec(z).add_spec(z.neg_spec()),
        y.neg_spec().add_spec(Rational::from_int_spec(0)),
        y.neg_spec());
    // lift under x + (·) and commute the inner sum
    Rational::lemma_eqv_add_congruence(
        x, x,
        z.neg_spec().add_spec(y.neg_spec().add_spec(z)),
        y.neg_spec().add_spec(z).add_spec(z.neg_spec()));
    Rational::lemma_eqv_add_congruence(x, x, y.neg_spec().add_spec(z).add_spec(z.neg_spec()), y.neg_spec());
    Rational::lemma_eqv_transitive(
        x.add_spec(z.neg_spec().add_spec(y.neg_spec().add_spec(z))),
        x.add_spec(y.neg_spec().add_spec(z).add_spec(z.neg_spec())),
        x.add_spec(y.neg_spec()));
    Rational::lemma_eqv_transitive(
        x.add_spec(z.neg_spec()).add_spec(y.neg_spec().add_spec(z)),
        x.add_spec(z.neg_spec().add_spec(y.neg_spec().add_spec(z))),
        x.add_spec(y.neg_spec()));
}

/// x − y ≡ −(y − x).
pub proof fn lemma_sub_neg_swap(x: Rational, y: Rational)
    ensures
        x.sub_spec(y).eqv_spec(y.sub_spec(x).neg_spec()),
{
    // y − x == y + (−x); −(y − x) == (−y) + (−(−x)) == (−y) + x
    Rational::lemma_neg_add(y, x.neg_spec());
    // (−y) + x ≡ x + (−y) == x − y
    Rational::lemma_add_commutative(y.neg_spec(), x);
}

/// x − y == −(y − x) (structural — the den formula is symmetric).
pub proof fn lemma_sub_neg_structural(x: Rational, y: Rational)
    ensures
        x.sub_spec(y) == y.sub_spec(x).neg_spec(),
{
    let d1 = x.denom_nat() as int;
    let d2 = y.denom_nat() as int;
    assert(x.sub_spec(y).num == x.num * d2 + (-y.num) * d1);
    assert(y.sub_spec(x).neg_spec().num == -(y.num * d1 + (-x.num) * d2));
    assert(x.sub_spec(y).den == x.den * y.den + x.den + y.den);
    assert(y.sub_spec(x).den == y.den * x.den + y.den + x.den);
    assert(x.sub_spec(y).num == y.sub_spec(x).neg_spec().num) by (nonlinear_arith)
        requires
            x.sub_spec(y).num == x.num * d2 + (-y.num) * d1,
            y.sub_spec(x).neg_spec().num == -(y.num * d1 + (-x.num) * d2);
    assert(x.sub_spec(y).den == y.sub_spec(x).neg_spec().den);
    assert(x.sub_spec(y) == y.sub_spec(x).neg_spec());
}

//  ── vdot linearity ──────────────────────────────────────────────────

/// Congruence: component-wise eqv vectors have eqv dots.
pub proof fn lemma_vdot_congruence_right(
    n: Vec2<Rational>,
    x: Vec2<Rational>,
    xp: Vec2<Rational>,
)
    requires
        x.x.eqv_spec(xp.x),
        x.y.eqv_spec(xp.y),
    ensures
        vdot(n, x).eqv_spec(vdot(n, xp)),
{
    Rational::lemma_eqv_reflexive(n.x);
    Rational::lemma_eqv_reflexive(n.y);
    Rational::lemma_eqv_mul_congruence(n.x, n.x, x.x, xp.x);
    Rational::lemma_eqv_mul_congruence(n.y, n.y, x.y, xp.y);
    Rational::lemma_eqv_add_congruence(
        n.x.mul_spec(x.x), n.x.mul_spec(xp.x),
        n.y.mul_spec(x.y), n.y.mul_spec(xp.y));
}

/// dot(n, x + y) ≡ dot(n, x) + dot(n, y).
pub proof fn lemma_vdot_add(n: Vec2<Rational>, x: Vec2<Rational>, y: Vec2<Rational>)
    ensures
        vdot(n, vadd(x, y)).eqv_spec(vdot(n, x).add_spec(vdot(n, y))),
{
    let a = n.x.mul_spec(x.x);
    let b = n.x.mul_spec(y.x);
    let c = n.y.mul_spec(x.y);
    let d = n.y.mul_spec(y.y);
    Rational::lemma_mul_distributes_over_add(n.x, x.x, y.x);
    Rational::lemma_mul_distributes_over_add(n.y, x.y, y.y);
    Rational::lemma_eqv_add_congruence(
        n.x.mul_spec(x.x.add_spec(y.x)), a.add_spec(b),
        n.y.mul_spec(x.y.add_spec(y.y)), c.add_spec(d));
    // LHS ≡ (A + B) + (C + D); rearrange to (A + C) + (B + D).
    Rational::lemma_eqv_symmetric(
        a.add_spec(b).add_spec(c.add_spec(d)),
        a.add_spec(b).add_spec(c).add_spec(d));
    Rational::lemma_add_associative(a.add_spec(b), c, d);
    Rational::lemma_add_associative(a, b, c);
    // (A+B)+C ≡ A+(B+C); lift under (·)+D
    Rational::lemma_eqv_reflexive(d);
    Rational::lemma_eqv_add_congruence(
        a.add_spec(b).add_spec(c), a.add_spec(b.add_spec(c)), d, d);
    Rational::lemma_add_commutative(b, c);
    Rational::lemma_eqv_reflexive(a);
    Rational::lemma_eqv_add_congruence(a, a, b.add_spec(c), c.add_spec(b));
    Rational::lemma_eqv_symmetric(
        a.add_spec(c).add_spec(b), a.add_spec(c.add_spec(b)));
    Rational::lemma_add_associative(a, c, b);
    // A+(B+C) ≡ A+(C+B) ≡ (A+C)+B; chain under (·)+D
    Rational::lemma_eqv_transitive(
        a.add_spec(b.add_spec(c)), a.add_spec(c.add_spec(b)), a.add_spec(c).add_spec(b));
    Rational::lemma_eqv_add_congruence(
        a.add_spec(b.add_spec(c)), a.add_spec(c).add_spec(b), d, d);
    Rational::lemma_add_associative(a.add_spec(c), b, d);
    // ((A+C)+B)+D ≡ (A+C)+(B+D)
    Rational::lemma_eqv_transitive(
        a.add_spec(b.add_spec(c)).add_spec(d),
        a.add_spec(c).add_spec(b).add_spec(d),
        a.add_spec(c).add_spec(b.add_spec(d)));
    Rational::lemma_eqv_transitive(
        a.add_spec(b).add_spec(c).add_spec(d),
        a.add_spec(b.add_spec(c)).add_spec(d),
        a.add_spec(c).add_spec(b.add_spec(d)));
    Rational::lemma_eqv_transitive(
        a.add_spec(b).add_spec(c.add_spec(d)),
        a.add_spec(b).add_spec(c).add_spec(d),
        a.add_spec(c).add_spec(b.add_spec(d)));
    // assemble: LHS ≡ (A+C)+(B+D) == vdot(n,x) + vdot(n,y)
    Rational::lemma_eqv_transitive(
        vdot(n, vadd(x, y)),
        a.add_spec(b).add_spec(c.add_spec(d)),
        vdot(n, x).add_spec(vdot(n, y)));
}

/// dot(n, u·x) ≡ u·dot(n, x).
pub proof fn lemma_vdot_scale(n: Vec2<Rational>, u: Rational, x: Vec2<Rational>)
    ensures
        vdot(n, vscale(u, x)).eqv_spec(u.mul_spec(vdot(n, x))),
{
    let a = n.x.mul_spec(x.x);
    let c = n.y.mul_spec(x.y);
    // n.x·(u·x.x) ≡ (n.x·u)·x.x == (u·n.x)·x.x ≡ u·(n.x·x.x)
    Rational::lemma_mul_associative(n.x, u, x.x);
    Rational::lemma_eqv_symmetric(
        n.x.mul_spec(u.mul_spec(x.x)), n.x.mul_spec(u).mul_spec(x.x));
    Rational::lemma_mul_commutative(n.x, u);
    Rational::lemma_mul_associative(u, n.x, x.x);
    Rational::lemma_eqv_transitive(
        n.x.mul_spec(u.mul_spec(x.x)),
        n.x.mul_spec(u).mul_spec(x.x),
        u.mul_spec(n.x).mul_spec(x.x));
    Rational::lemma_eqv_transitive(
        n.x.mul_spec(u.mul_spec(x.x)),
        u.mul_spec(n.x).mul_spec(x.x),
        u.mul_spec(n.x.mul_spec(x.x)));
    Rational::lemma_mul_associative(n.y, u, x.y);
    Rational::lemma_eqv_symmetric(
        n.y.mul_spec(u.mul_spec(x.y)), n.y.mul_spec(u).mul_spec(x.y));
    Rational::lemma_mul_commutative(n.y, u);
    Rational::lemma_mul_associative(u, n.y, x.y);
    Rational::lemma_eqv_transitive(
        n.y.mul_spec(u.mul_spec(x.y)),
        n.y.mul_spec(u).mul_spec(x.y),
        u.mul_spec(n.y).mul_spec(x.y));
    Rational::lemma_eqv_transitive(
        n.y.mul_spec(u.mul_spec(x.y)),
        u.mul_spec(n.y).mul_spec(x.y),
        u.mul_spec(n.y.mul_spec(x.y)));
    // add congruence: LHS ≡ u·A + u·C ≡ u·(A + C) [distributes, symmetric]
    Rational::lemma_eqv_add_congruence(
        n.x.mul_spec(u.mul_spec(x.x)), u.mul_spec(a),
        n.y.mul_spec(u.mul_spec(x.y)), u.mul_spec(c));
    Rational::lemma_mul_distributes_over_add(u, a, c);
    Rational::lemma_eqv_symmetric(
        u.mul_spec(a.add_spec(c)), u.mul_spec(a).add_spec(u.mul_spec(c)));
    Rational::lemma_eqv_transitive(
        vdot(n, vscale(u, x)),
        u.mul_spec(a).add_spec(u.mul_spec(c)),
        u.mul_spec(vdot(n, x)));
}

/// dot(n, x − y) ≡ dot(n, x) − dot(n, y).
pub proof fn lemma_vdot_sub(n: Vec2<Rational>, x: Vec2<Rational>, y: Vec2<Rational>)
    ensures
        vdot(n, vsub(x, y)).eqv_spec(vdot(n, x).sub_spec(vdot(n, y))),
{
    let a = n.x.mul_spec(x.x);
    let b = n.x.mul_spec(y.x);
    let c = n.y.mul_spec(x.y);
    let d = n.y.mul_spec(y.y);
    lemma_mul_distributes_over_sub(n.x, x.x, y.x);
    lemma_mul_distributes_over_sub(n.y, x.y, y.y);
    Rational::lemma_eqv_add_congruence(
        n.x.mul_spec(x.x.sub_spec(y.x)), a.sub_spec(b),
        n.y.mul_spec(x.y.sub_spec(y.y)), c.sub_spec(d));
    // (A − B) + (C − D) ≡ (A + C) − (B + D) [sub_add_distributes, symmetric]
    Rational::lemma_sub_add_distributes(a, c, b, d);
    Rational::lemma_eqv_symmetric(
        a.add_spec(c).sub_spec(b.add_spec(d)),
        a.sub_spec(b).add_spec(c.sub_spec(d)));
    Rational::lemma_eqv_transitive(
        vdot(n, vsub(x, y)),
        a.sub_spec(b).add_spec(c.sub_spec(d)),
        vdot(n, x).sub_spec(vdot(n, y)));
}

} // verus!

verus! {

//  ── axis_sep through interpolation ──────────────────────────────────

/// axis_sep congruence in the query point (component-wise eqv).
pub proof fn lemma_axis_sep_eqv_q(
    n: Vec2<Rational>,
    base: Vec2<Rational>,
    q1: Vec2<Rational>,
    q2: Vec2<Rational>,
)
    requires
        q1.x.eqv_spec(q2.x),
        q1.y.eqv_spec(q2.y),
    ensures
        axis_sep(n, base, q1).eqv_spec(axis_sep(n, base, q2)),
{
    Rational::lemma_eqv_reflexive(base.x);
    Rational::lemma_eqv_reflexive(base.y);
    Rational::lemma_eqv_reflexive(n.x);
    Rational::lemma_eqv_reflexive(n.y);
    Rational::lemma_eqv_sub_congruence(q1.x, q2.x, base.x, base.x);
    Rational::lemma_eqv_sub_congruence(q1.y, q2.y, base.y, base.y);
    Rational::lemma_eqv_mul_congruence(
        n.x, n.x, q1.x.sub_spec(base.x), q2.x.sub_spec(base.x));
    Rational::lemma_eqv_mul_congruence(
        n.y, n.y, q1.y.sub_spec(base.y), q2.y.sub_spec(base.y));
    Rational::lemma_eqv_add_congruence(
        n.x.mul_spec(q1.x.sub_spec(base.x)), n.x.mul_spec(q2.x.sub_spec(base.x)),
        n.y.mul_spec(q1.y.sub_spec(base.y)), n.y.mul_spec(q2.y.sub_spec(base.y)));
}

/// a + (b − a) ≡ b.
pub proof fn lemma_add_sub_cancel(a: Rational, b: Rational)
    ensures
        a.add_spec(b.sub_spec(a)).eqv_spec(b),
{
    Rational::lemma_add_associative(a, b, a.neg_spec());
    Rational::lemma_eqv_symmetric(
        a.add_spec(b).add_spec(a.neg_spec()), a.add_spec(b.add_spec(a.neg_spec())));
    Rational::lemma_add_commutative(a, b);
    Rational::lemma_eqv_reflexive(a.neg_spec());
    Rational::lemma_eqv_add_congruence(
        a.add_spec(b), b.add_spec(a), a.neg_spec(), a.neg_spec());
    Rational::lemma_add_associative(b, a, a.neg_spec());
    Rational::lemma_add_inverse(a);
    Rational::lemma_eqv_reflexive(b);
    Rational::lemma_eqv_add_congruence(
        b, b, a.add_spec(a.neg_spec()), Rational::from_int_spec(0));
    Rational::lemma_add_zero_identity(b);
    Rational::lemma_eqv_transitive(
        b.add_spec(a.add_spec(a.neg_spec())),
        b.add_spec(Rational::from_int_spec(0)),
        b);
    Rational::lemma_eqv_transitive(
        b.add_spec(a).add_spec(a.neg_spec()),
        b.add_spec(a.add_spec(a.neg_spec())),
        b);
    Rational::lemma_eqv_transitive(
        a.add_spec(b).add_spec(a.neg_spec()),
        b.add_spec(a).add_spec(a.neg_spec()),
        b);
    Rational::lemma_eqv_transitive(
        a.add_spec(b.add_spec(a.neg_spec())),
        a.add_spec(b).add_spec(a.neg_spec()),
        b);
}

/// axis_sep(n, a, b) ≡ axis_sep(n, base, b) − axis_sep(n, base, a).
pub proof fn lemma_axis_sep_between(
    n: Vec2<Rational>,
    base: Vec2<Rational>,
    a: Vec2<Rational>,
    b: Vec2<Rational>,
)
    ensures
        axis_sep(n, a, b).eqv_spec(
            axis_sep(n, base, b).sub_spec(axis_sep(n, base, a))),
{
    // axis_sep(n, p, q) == vdot(n, vsub(q, p)) — structural.
    lemma_vdot_sub(n, vsub(b, base), vsub(a, base));
    // RHS ≡ vdot(n, vsub(vsub(b,base), vsub(a,base)))
    lemma_sub_sub_cancel(b.x, a.x, base.x);
    lemma_sub_sub_cancel(b.y, a.y, base.y);
    lemma_vdot_congruence_right(
        n, vsub(vsub(b, base), vsub(a, base)), vsub(b, a));
    Rational::lemma_eqv_transitive(
        axis_sep(n, base, b).sub_spec(axis_sep(n, base, a)),
        vdot(n, vsub(vsub(b, base), vsub(a, base))),
        vdot(n, vsub(b, a)));
    Rational::lemma_eqv_symmetric(
        axis_sep(n, base, b).sub_spec(axis_sep(n, base, a)),
        axis_sep(n, a, b));
}

/// The key linearity: axis_sep at an interpolated point.
pub proof fn lemma_axis_sep_interp(
    n: Vec2<Rational>,
    base: Vec2<Rational>,
    a: Vec2<Rational>,
    b: Vec2<Rational>,
    u: Rational,
)
    ensures
        axis_sep(n, base, vadd(a, vscale(u, vsub(b, a)))).eqv_spec(
            axis_sep(n, base, a).add_spec(
                u.mul_spec(axis_sep(n, base, b).sub_spec(axis_sep(n, base, a))))),
{
    let w = vscale(u, vsub(b, a));
    let q = vadd(a, w);
    // axis_sep(n, base, q) == vdot(n, vsub(q, base)) — structural.
    lemma_add_sub_swap(a.x, w.x, base.x);
    lemma_add_sub_swap(a.y, w.y, base.y);
    lemma_vdot_congruence_right(n, vsub(q, base), vadd(vsub(a, base), w));
    lemma_vdot_add(n, vsub(a, base), w);
    // ≡ vdot(n, vsub(a, base)) + vdot(n, w) == axis_sep(n, base, a) + vdot(n, w)
    lemma_vdot_scale(n, u, vsub(b, a));
    // vdot(n, w) ≡ u·vdot(n, vsub(b, a)) == u·axis_sep(n, a, b)
    lemma_axis_sep_between(n, base, a, b);
    Rational::lemma_eqv_reflexive(u);
    Rational::lemma_eqv_mul_congruence(
        u, u, axis_sep(n, a, b),
        axis_sep(n, base, b).sub_spec(axis_sep(n, base, a)));
    Rational::lemma_eqv_reflexive(vdot(n, vsub(a, base)));
    Rational::lemma_eqv_add_congruence(
        vdot(n, vsub(a, base)), vdot(n, vsub(a, base)),
        vdot(n, w), u.mul_spec(axis_sep(n, a, b)));
    Rational::lemma_eqv_add_congruence(
        vdot(n, vsub(a, base)), vdot(n, vsub(a, base)),
        u.mul_spec(axis_sep(n, a, b)),
        u.mul_spec(axis_sep(n, base, b).sub_spec(axis_sep(n, base, a))));
    Rational::lemma_eqv_transitive(
        vdot(n, vsub(a, base)).add_spec(vdot(n, w)),
        vdot(n, vsub(a, base)).add_spec(u.mul_spec(axis_sep(n, a, b))),
        axis_sep(n, base, a).add_spec(
            u.mul_spec(axis_sep(n, base, b).sub_spec(axis_sep(n, base, a)))));
    Rational::lemma_eqv_transitive(
        vdot(n, vsub(q, base)),
        vdot(n, vadd(vsub(a, base), w)),
        vdot(n, vsub(a, base)).add_spec(vdot(n, w)));
    Rational::lemma_eqv_transitive(
        vdot(n, vsub(q, base)),
        vdot(n, vsub(a, base)).add_spec(vdot(n, w)),
        axis_sep(n, base, a).add_spec(
            u.mul_spec(axis_sep(n, base, b).sub_spec(axis_sep(n, base, a)))));
}

/// va + u·(vb − va) ≡ (1 − u)·va + u·vb.
pub proof fn lemma_interp_combo_id(u: Rational, va: Rational, vb: Rational)
    ensures
        va.add_spec(u.mul_spec(vb.sub_spec(va))).eqv_spec(
            Rational::from_int_spec(1).sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb))),
{
    let one = Rational::from_int_spec(1);
    lemma_mul_distributes_over_sub(u, vb, va);
    // u·(vb − va) ≡ u·vb − u·va
    Rational::lemma_eqv_reflexive(va);
    Rational::lemma_eqv_add_congruence(
        va, va, u.mul_spec(vb.sub_spec(va)), u.mul_spec(vb).sub_spec(u.mul_spec(va)));
    // va + (u·vb − u·va) ≡ (va + u·vb) − u·va [assoc, symmetric]
    Rational::lemma_add_associative(va, u.mul_spec(vb), u.mul_spec(va).neg_spec());
    Rational::lemma_eqv_symmetric(
        va.add_spec(u.mul_spec(vb)).add_spec(u.mul_spec(va).neg_spec()),
        va.add_spec(u.mul_spec(vb).add_spec(u.mul_spec(va).neg_spec())));
    lemma_add_sub_swap(va, u.mul_spec(vb), u.mul_spec(va));
    // (va + u·vb) − u·va ≡ (va − u·va) + u·vb
    Rational::lemma_eqv_transitive(
        va.add_spec(u.mul_spec(vb).sub_spec(u.mul_spec(va))),
        va.add_spec(u.mul_spec(vb)).sub_spec(u.mul_spec(va)),
        va.sub_spec(u.mul_spec(va)).add_spec(u.mul_spec(vb)));
    Rational::lemma_eqv_transitive(
        va.add_spec(u.mul_spec(vb.sub_spec(va))),
        va.add_spec(u.mul_spec(vb).sub_spec(u.mul_spec(va))),
        va.sub_spec(u.mul_spec(va)).add_spec(u.mul_spec(vb)));
    // (1−u)·va == va·(1+(−u)) ≡ va·1 + va·(−u) ≡ va − u·va
    Rational::lemma_mul_distributes_over_add(va, one, u.neg_spec());
    Rational::lemma_mul_one_identity(va);
    Rational::lemma_mul_neg_right(va, u);
    Rational::lemma_mul_commutative(va, u);
    assert(va.mul_spec(one) == va);
    assert(va.mul_spec(u.neg_spec()) == u.mul_spec(va).neg_spec());
    Rational::lemma_eqv_reflexive(va);
    Rational::lemma_eqv_reflexive(u.mul_spec(va).neg_spec());
    Rational::lemma_eqv_add_congruence(
        va.mul_spec(one), va, va.mul_spec(u.neg_spec()), u.mul_spec(va).neg_spec());
    // (1−u)·va == va·(1+(−u)) — stage the nested commute + sub-def rewrite
    assert(one.sub_spec(u) == one.add_spec(u.neg_spec()));
    Rational::lemma_mul_commutative(one.sub_spec(u), va);
    assert(one.sub_spec(u).mul_spec(va) == va.mul_spec(one.add_spec(u.neg_spec())));
    Rational::lemma_eqv_reflexive(va.mul_spec(one.add_spec(u.neg_spec())));
    // (1−u)·va ≡ va·1 + va·(−u) ≡ va − u·va
    Rational::lemma_eqv_transitive(
        one.sub_spec(u).mul_spec(va),
        va.mul_spec(one).add_spec(va.mul_spec(u.neg_spec())),
        va.sub_spec(u.mul_spec(va)));
    // va·(1−u) + u·vb ≡ (va − u·va) + u·vb
    Rational::lemma_eqv_reflexive(u.mul_spec(vb));
    Rational::lemma_eqv_add_congruence(
        one.sub_spec(u).mul_spec(va), va.sub_spec(u.mul_spec(va)),
        u.mul_spec(vb), u.mul_spec(vb));
    Rational::lemma_eqv_symmetric(
        one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)),
        va.sub_spec(u.mul_spec(va)).add_spec(u.mul_spec(vb)));
    Rational::lemma_eqv_transitive(
        va.add_spec(u.mul_spec(vb.sub_spec(va))),
        va.sub_spec(u.mul_spec(va)).add_spec(u.mul_spec(vb)),
        one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)));
}

/// Interpolating between two in-half-plane points stays in the half-plane:
/// dot(n, q − base) ≥ 0 when both endpoints qualify and 0 ≤ u ≤ 1.
pub proof fn lemma_interp_value_nonneg(
    n: Vec2<Rational>,
    base: Vec2<Rational>,
    a: Vec2<Rational>,
    b: Vec2<Rational>,
    q: Vec2<Rational>,
    u: Rational,
)
    requires
        Rational::from_int_spec(0).le_spec(u),
        u.le_spec(Rational::from_int_spec(1)),
        Rational::from_int_spec(0).le_spec(axis_sep(n, base, a)),
        Rational::from_int_spec(0).le_spec(axis_sep(n, base, b)),
        q.x.eqv_spec(vadd(a, vscale(u, vsub(b, a))).x),
        q.y.eqv_spec(vadd(a, vscale(u, vsub(b, a))).y),
    ensures
        Rational::from_int_spec(0).le_spec(axis_sep(n, base, q)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    let va = axis_sep(n, base, a);
    let vb = axis_sep(n, base, b);
    let interp = vadd(a, vscale(u, vsub(b, a)));
    // value chain: axis_sep(n,base,q) ≡ axis_sep(n,base,interp)
    //            ≡ va + u·(vb − va) ≡ (1−u)·va + u·vb
    lemma_axis_sep_eqv_q(n, base, q, interp);
    lemma_axis_sep_interp(n, base, a, b, u);
    lemma_interp_combo_id(u, va, vb);
    Rational::lemma_eqv_transitive(
        axis_sep(n, base, q), axis_sep(n, base, interp),
        va.add_spec(u.mul_spec(vb.sub_spec(va))));
    Rational::lemma_eqv_transitive(
        axis_sep(n, base, q),
        va.add_spec(u.mul_spec(vb.sub_spec(va))),
        one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)));
    // 0 ≤ 1 − u
    Rational::lemma_neg_reverses_le(u, one);
    Rational::lemma_le_add_monotone(one.neg_spec(), u.neg_spec(), one);
    Rational::lemma_add_inverse(one);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        one.neg_spec().add_spec(one), zero, u.neg_spec().add_spec(one));
    Rational::lemma_add_commutative(u.neg_spec(), one);
    crate::proofs::shape::lemma_le_eqv_subst_right(
        zero, u.neg_spec().add_spec(one), one.sub_spec(u));
    // 0 ≤ (1−u)·va and 0 ≤ u·vb
    Rational::lemma_le_mul_nonneg(zero, va, one.sub_spec(u));
    Rational::lemma_mul_zero(one.sub_spec(u));
    crate::proofs::shape::lemma_le_eqv_subst_left(
        zero.mul_spec(one.sub_spec(u)), zero, va.mul_spec(one.sub_spec(u)));
    Rational::lemma_le_mul_nonneg(zero, vb, u);
    Rational::lemma_mul_zero(u);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        zero.mul_spec(u), zero, vb.mul_spec(u));
    // 0 ≤ sum
    Rational::lemma_le_add_both(
        zero, va.mul_spec(one.sub_spec(u)), zero, u.mul_spec(vb));
    Rational::lemma_add_zero_identity(zero);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        zero.add_spec(zero), zero,
        va.mul_spec(one.sub_spec(u)).add_spec(u.mul_spec(vb)));
    // substitute through the value chain
    Rational::lemma_eqv_symmetric(
        axis_sep(n, base, q),
        one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)));
    // stage the commute rewrite between the two combo forms
    Rational::lemma_mul_commutative(va, one.sub_spec(u));
    assert(va.mul_spec(one.sub_spec(u)).add_spec(u.mul_spec(vb))
        == one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)));
    assert(zero.le_spec(one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb))));
    assert(one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)).eqv_spec(
        axis_sep(n, base, q)));
    crate::proofs::shape::lemma_le_eqv_subst_right(
        zero,
        one.sub_spec(u).mul_spec(va).add_spec(u.mul_spec(vb)),
        axis_sep(n, base, q));
}

//  ── Clip parameter bounds and zero value ────────────────────────────

/// t = v0 / (v0 − v1) is in [0, 1] when v0 ≥ 0 > v1; the denominator is
/// strictly positive (so nonzero).
pub proof fn lemma_clip_t_bounds(v0: Rational, v1: Rational)
    requires
        Rational::from_int_spec(0).le_spec(v0),
        v1.lt_spec(Rational::from_int_spec(0)),
    ensures
        Rational::from_int_spec(0).lt_spec(v0.sub_spec(v1)),
        !v0.sub_spec(v1).eqv_spec(Rational::from_int_spec(0)),
        Rational::from_int_spec(0).le_spec(v0.div_spec(v0.sub_spec(v1))),
        v0.div_spec(v0.sub_spec(v1)).le_spec(Rational::from_int_spec(1)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    let den = v0.sub_spec(v1);
    // den > 0
    Rational::lemma_neg_reverses_lt(v1, zero);
    Rational::lemma_le_lt_add(zero, v0, zero, v1.neg_spec());
    // 0 + 0 < v0 + (−v1); 0 + 0 == 0 structural
    Rational::lemma_add_zero_identity(zero);
    Rational::lemma_trichotomy(zero, den);
    // 0 ≤ v0/den
    Rational::lemma_div_le_monotone(zero, v0, den);
    Rational::lemma_mul_zero(den.reciprocal_spec());
    crate::proofs::shape::lemma_le_eqv_subst_left(
        zero.div_spec(den), zero, v0.div_spec(den));
    // v0 ≤ den
    Rational::lemma_lt_implies_le(zero, v1.neg_spec());
    Rational::lemma_eqv_reflexive(v0);
    Rational::lemma_le_add_both(v0, v0, zero, v1.neg_spec());
    Rational::lemma_add_zero_identity(v0);
    // v0/den ≤ den/den ≡ 1
    Rational::lemma_div_le_monotone(v0, den, den);
    Rational::lemma_div_self(den);
    crate::proofs::shape::lemma_le_eqv_subst_right(
        v0.div_spec(den), den.div_spec(den), one);
}

/// The interpolated point sits exactly on the clip plane:
/// v0 + t·(v1 − v0) ≡ 0 for t = v0/(v0 − v1).
pub proof fn lemma_clip_value_zero(v0: Rational, v1: Rational)
    requires
        Rational::from_int_spec(0).le_spec(v0),
        v1.lt_spec(Rational::from_int_spec(0)),
    ensures
        v0.add_spec(
            v0.div_spec(v0.sub_spec(v1)).mul_spec(v1.sub_spec(v0))).eqv_spec(
            Rational::from_int_spec(0)),
{
    let zero = Rational::from_int_spec(0);
    let den = v0.sub_spec(v1);
    let t = v0.div_spec(den);
    lemma_clip_t_bounds(v0, v1);
    // t·(v1 − v0) ≡ t·(−den) == −(t·den) ≡ −v0
    lemma_sub_neg_swap(v1, v0);
    Rational::lemma_eqv_reflexive(t);
    Rational::lemma_eqv_mul_congruence(t, t, v1.sub_spec(v0), den.neg_spec());
    Rational::lemma_mul_neg_right(t, den);
    // t·den ≡ v0
    Rational::lemma_div_mul_assoc(v0, den, den);
    Rational::lemma_div_mul_cancel(v0, den);
    Rational::lemma_eqv_transitive(
        t.mul_spec(den), v0.mul_spec(den).div_spec(den), v0);
    Rational::lemma_eqv_neg_congruence(t.mul_spec(den), v0);
    // t·(−den) == −(t·den) ≡ −v0
    Rational::lemma_eqv_transitive(
        t.mul_spec(v1.sub_spec(v0)), t.mul_spec(den.neg_spec()), v0.neg_spec());
    // v0 + (−v0) ≡ 0
    Rational::lemma_eqv_reflexive(v0);
    Rational::lemma_eqv_add_congruence(
        v0, v0, t.mul_spec(v1.sub_spec(v0)), v0.neg_spec());
    Rational::lemma_add_inverse(v0);
    Rational::lemma_eqv_transitive(
        v0.add_spec(t.mul_spec(v1.sub_spec(v0))),
        v0.add_spec(v0.neg_spec()),
        zero);
}

} // verus!

verus! {

//  ── Exec-model bridges ──────────────────────────────────────────────

/// The exec interpolation chain (canonical trait ops) is eqv to the raw
/// spec form: out == a.add(u.mul(b.sub(a))) implies
/// out ≡ a + u·(b − a). (Stated in canonical-expanded form — the trait
/// ops canonicalize: x.op(y) == x.op_spec(y).canonical().)
pub proof fn lemma_canonical_interp_component(
    a: Rational,
    b: Rational,
    u: Rational,
    out: Rational,
)
    requires
        out == a.add_spec(
            u.mul_spec(b.sub_spec(a).canonical()).canonical()).canonical(),
    ensures
        out.eqv_spec(a.add_spec(u.mul_spec(b.sub_spec(a)))),
{
    Rational::lemma_canonical_exists(b.sub_spec(a));
    Rational::lemma_eqv_reflexive(u);
    Rational::lemma_eqv_mul_congruence(
        u, u, b.sub_spec(a).canonical(), b.sub_spec(a));
    Rational::lemma_canonical_exists(u.mul_spec(b.sub_spec(a).canonical()));
    Rational::lemma_eqv_transitive(
        u.mul_spec(b.sub_spec(a).canonical()).canonical(),
        u.mul_spec(b.sub_spec(a).canonical()),
        u.mul_spec(b.sub_spec(a)));
    Rational::lemma_eqv_reflexive(a);
    Rational::lemma_eqv_add_congruence(
        a, a,
        u.mul_spec(b.sub_spec(a).canonical()).canonical(),
        u.mul_spec(b.sub_spec(a)));
    Rational::lemma_canonical_exists(
        a.add_spec(u.mul_spec(b.sub_spec(a).canonical()).canonical()));
    Rational::lemma_eqv_transitive(
        out,
        a.add_spec(u.mul_spec(b.sub_spec(a).canonical()).canonical()),
        a.add_spec(u.mul_spec(b.sub_spec(a))));
}

/// b + t·(a − b) ≡ a + (1 − t)·(b − a).
pub proof fn lemma_interp_flip(a: Rational, b: Rational, t: Rational)
    ensures
        b.add_spec(t.mul_spec(a.sub_spec(b))).eqv_spec(
            a.add_spec(Rational::from_int_spec(1).sub_spec(t).mul_spec(b.sub_spec(a)))),
{
    let one = Rational::from_int_spec(1);
    // t·(a − b) ≡ −(t·(b − a))
    lemma_sub_neg_swap(a, b);
    Rational::lemma_eqv_reflexive(t);
    Rational::lemma_eqv_mul_congruence(t, t, a.sub_spec(b), b.sub_spec(a).neg_spec());
    Rational::lemma_mul_neg_right(t, b.sub_spec(a));
    Rational::lemma_eqv_transitive(
        t.mul_spec(a.sub_spec(b)),
        t.mul_spec(b.sub_spec(a).neg_spec()),
        t.mul_spec(b.sub_spec(a)).neg_spec());
    // b + t·(a − b) ≡ b − t·(b − a)
    Rational::lemma_eqv_reflexive(b);
    Rational::lemma_eqv_add_congruence(
        b, b, t.mul_spec(a.sub_spec(b)), t.mul_spec(b.sub_spec(a)).neg_spec());
    // (1−t)·(b−a) ≡ (b−a) − t·(b−a)
    Rational::lemma_mul_distributes_over_add(b.sub_spec(a), one, t.neg_spec());
    Rational::lemma_mul_one_identity(b.sub_spec(a));
    Rational::lemma_mul_neg_right(b.sub_spec(a), t);
    Rational::lemma_mul_commutative(b.sub_spec(a), t);
    assert(b.sub_spec(a).mul_spec(one) == b.sub_spec(a));
    assert(b.sub_spec(a).mul_spec(t.neg_spec()) == t.mul_spec(b.sub_spec(a)).neg_spec());
    assert(one.sub_spec(t) == one.add_spec(t.neg_spec()));
    Rational::lemma_mul_commutative(one.sub_spec(t), b.sub_spec(a));
    assert(one.sub_spec(t).mul_spec(b.sub_spec(a))
        == b.sub_spec(a).mul_spec(one.add_spec(t.neg_spec())));
    Rational::lemma_eqv_reflexive(b.sub_spec(a));
    Rational::lemma_eqv_reflexive(t.mul_spec(b.sub_spec(a)).neg_spec());
    Rational::lemma_eqv_add_congruence(
        b.sub_spec(a).mul_spec(one), b.sub_spec(a),
        b.sub_spec(a).mul_spec(t.neg_spec()), t.mul_spec(b.sub_spec(a)).neg_spec());
    Rational::lemma_eqv_transitive(
        one.sub_spec(t).mul_spec(b.sub_spec(a)),
        b.sub_spec(a).mul_spec(one).add_spec(b.sub_spec(a).mul_spec(t.neg_spec())),
        b.sub_spec(a).sub_spec(t.mul_spec(b.sub_spec(a))));
    // a + ((b−a) − t·(b−a)) ≡ (a + (b−a)) − t·(b−a) [assoc, symmetric]
    Rational::lemma_add_associative(a, b.sub_spec(a), t.mul_spec(b.sub_spec(a)).neg_spec());
    Rational::lemma_eqv_symmetric(
        a.add_spec(b.sub_spec(a)).add_spec(t.mul_spec(b.sub_spec(a)).neg_spec()),
        a.add_spec(b.sub_spec(a).add_spec(t.mul_spec(b.sub_spec(a)).neg_spec())));
    // (a + (b−a)) ≡ b; substitute under (·) − t·(b−a)
    lemma_add_sub_cancel(a, b);
    Rational::lemma_eqv_reflexive(t.mul_spec(b.sub_spec(a)));
    Rational::lemma_eqv_sub_congruence(
        a.add_spec(b.sub_spec(a)), b,
        t.mul_spec(b.sub_spec(a)), t.mul_spec(b.sub_spec(a)));
    // a + (1−t)·(b−a) ≡ a + ((b−a) − t·(b−a))
    Rational::lemma_eqv_reflexive(a);
    Rational::lemma_eqv_add_congruence(
        a, a,
        one.sub_spec(t).mul_spec(b.sub_spec(a)),
        b.sub_spec(a).sub_spec(t.mul_spec(b.sub_spec(a))));
    Rational::lemma_eqv_symmetric(
        a.add_spec(b.sub_spec(a)).add_spec(t.mul_spec(b.sub_spec(a)).neg_spec()),
        a.add_spec(b.sub_spec(a).add_spec(t.mul_spec(b.sub_spec(a)).neg_spec())));
    // assemble: b + t·(a−b) ≡ b − t·(b−a) ≡ (a+(b−a)) − t·(b−a)
    //         ≡ a + ((b−a) − t·(b−a)) ≡ a + (1−t)·(b−a)
    Rational::lemma_eqv_symmetric(
        a.add_spec(b.sub_spec(a)).sub_spec(t.mul_spec(b.sub_spec(a))),
        b.sub_spec(t.mul_spec(b.sub_spec(a))));
    Rational::lemma_eqv_transitive(
        b.add_spec(t.mul_spec(a.sub_spec(b))),
        b.sub_spec(t.mul_spec(b.sub_spec(a))),
        a.add_spec(b.sub_spec(a)).sub_spec(t.mul_spec(b.sub_spec(a))));
    Rational::lemma_eqv_symmetric(
        a.add_spec(b.sub_spec(a).sub_spec(t.mul_spec(b.sub_spec(a)))),
        a.add_spec(b.sub_spec(a)).sub_spec(t.mul_spec(b.sub_spec(a))));
    Rational::lemma_eqv_transitive(
        b.add_spec(t.mul_spec(a.sub_spec(b))),
        a.add_spec(b.sub_spec(a)).sub_spec(t.mul_spec(b.sub_spec(a))),
        a.add_spec(b.sub_spec(a).sub_spec(t.mul_spec(b.sub_spec(a)))));
    Rational::lemma_eqv_symmetric(
        a.add_spec(one.sub_spec(t).mul_spec(b.sub_spec(a))),
        a.add_spec(b.sub_spec(a).sub_spec(t.mul_spec(b.sub_spec(a)))));
    Rational::lemma_eqv_transitive(
        b.add_spec(t.mul_spec(a.sub_spec(b))),
        a.add_spec(b.sub_spec(a).sub_spec(t.mul_spec(b.sub_spec(a)))),
        a.add_spec(one.sub_spec(t).mul_spec(b.sub_spec(a))));
}

} // verus!

verus! {

//  ── Per-case clip point facts ───────────────────────────────────────

/// 0 ≤ 1 − t ≤ 1 when 0 ≤ t ≤ 1.
pub proof fn lemma_one_sub_bounds(t: Rational)
    requires
        Rational::from_int_spec(0).le_spec(t),
        t.le_spec(Rational::from_int_spec(1)),
    ensures
        Rational::from_int_spec(0).le_spec(Rational::from_int_spec(1).sub_spec(t)),
        Rational::from_int_spec(1).sub_spec(t).le_spec(Rational::from_int_spec(1)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    // 0 ≤ 1 − t
    Rational::lemma_neg_reverses_le(t, one);
    Rational::lemma_le_add_monotone(one.neg_spec(), t.neg_spec(), one);
    Rational::lemma_add_inverse(one);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        one.neg_spec().add_spec(one), zero, t.neg_spec().add_spec(one));
    Rational::lemma_add_commutative(t.neg_spec(), one);
    crate::proofs::shape::lemma_le_eqv_subst_right(
        zero, t.neg_spec().add_spec(one), one.sub_spec(t));
    // 1 − t ≤ 1
    Rational::lemma_neg_reverses_le(zero, t);
    assert(zero.neg_spec() == zero);
    Rational::lemma_le_add_monotone(t.neg_spec(), zero, one);
    Rational::lemma_add_commutative(t.neg_spec(), one);
    Rational::lemma_add_zero_identity(one);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        t.neg_spec().add_spec(one), one.sub_spec(t), one);
}

/// Facts about the clip intersection point (keep0 && !keep1 case): it
/// lies exactly on the clip plane and interpolates the segment at t.
pub proof fn lemma_clip_point_facts(
    d: Vec2<Rational>,
    base: Vec2<Rational>,
    q0: Vec2<Rational>,
    q1: Vec2<Rational>,
    q: Vec2<Rational>,
    t: Rational,
)
    requires
        Rational::from_int_spec(0).le_spec(axis_sep(d, base, q0)),
        axis_sep(d, base, q1).lt_spec(Rational::from_int_spec(0)),
        t == axis_sep(d, base, q0).div_spec(
            axis_sep(d, base, q0).sub_spec(axis_sep(d, base, q1))),
        q.x == q0.x.add_spec(
            t.mul_spec(q1.x.sub_spec(q0.x).canonical()).canonical()).canonical(),
        q.y == q0.y.add_spec(
            t.mul_spec(q1.y.sub_spec(q0.y).canonical()).canonical()).canonical(),
    ensures
        axis_sep(d, base, q).eqv_spec(Rational::from_int_spec(0)),
        crate::narrowphase::interp_rel(q0, q1, q, t),
{
    let v0 = axis_sep(d, base, q0);
    let v1 = axis_sep(d, base, q1);
    lemma_clip_t_bounds(v0, v1);
    lemma_canonical_interp_component(q0.x, q1.x, t, q.x);
    lemma_canonical_interp_component(q0.y, q1.y, t, q.y);
    // interp_rel: bounds from t_bounds, components from the bridge
    assert(crate::narrowphase::interp_rel(q0, q1, q, t));
    // value: chain to the interp form, then clip_value_zero
    lemma_axis_sep_eqv_q(d, base, q, vadd(q0, vscale(t, vsub(q1, q0))));
    lemma_axis_sep_interp(d, base, q0, q1, t);
    lemma_clip_value_zero(v0, v1);
    Rational::lemma_eqv_transitive(
        axis_sep(d, base, q),
        axis_sep(d, base, vadd(q0, vscale(t, vsub(q1, q0)))),
        v0.add_spec(t.mul_spec(v1.sub_spec(v0))));
    Rational::lemma_eqv_transitive(
        axis_sep(d, base, q),
        v0.add_spec(t.mul_spec(v1.sub_spec(v0))),
        Rational::from_int_spec(0));
}

/// Facts about the clip intersection point (!keep0 && keep1 case): it
/// lies exactly on the clip plane and interpolates the segment at 1 − t1
/// (where t1 = v1/(v1 − v0) parameterizes from q1).
pub proof fn lemma_clip_point_facts_swapped(
    d: Vec2<Rational>,
    base: Vec2<Rational>,
    q0: Vec2<Rational>,
    q1: Vec2<Rational>,
    q: Vec2<Rational>,
    t1: Rational,
)
    requires
        axis_sep(d, base, q0).lt_spec(Rational::from_int_spec(0)),
        Rational::from_int_spec(0).le_spec(axis_sep(d, base, q1)),
        t1 == axis_sep(d, base, q1).div_spec(
            axis_sep(d, base, q1).sub_spec(axis_sep(d, base, q0))),
        q.x == q1.x.add_spec(
            t1.mul_spec(q0.x.sub_spec(q1.x).canonical()).canonical()).canonical(),
        q.y == q1.y.add_spec(
            t1.mul_spec(q0.y.sub_spec(q1.y).canonical()).canonical()).canonical(),
    ensures
        axis_sep(d, base, q).eqv_spec(Rational::from_int_spec(0)),
        crate::narrowphase::interp_rel(
            q0, q1, q, Rational::from_int_spec(1).sub_spec(t1)),
{
    let v0 = axis_sep(d, base, q0);
    let v1 = axis_sep(d, base, q1);
    let one = Rational::from_int_spec(1);
    let u = one.sub_spec(t1);
    lemma_clip_t_bounds(v1, v0);
    lemma_one_sub_bounds(t1);
    // bridge to the q1-side interp form
    lemma_canonical_interp_component(q1.x, q0.x, t1, q.x);
    lemma_canonical_interp_component(q1.y, q0.y, t1, q.y);
    // value: q1-side interp + clip_value_zero(v1, v0)
    lemma_axis_sep_eqv_q(d, base, q, vadd(q1, vscale(t1, vsub(q0, q1))));
    lemma_axis_sep_interp(d, base, q1, q0, t1);
    lemma_clip_value_zero(v1, v0);
    Rational::lemma_eqv_transitive(
        axis_sep(d, base, q),
        axis_sep(d, base, vadd(q1, vscale(t1, vsub(q0, q1)))),
        v1.add_spec(t1.mul_spec(v0.sub_spec(v1))));
    Rational::lemma_eqv_transitive(
        axis_sep(d, base, q),
        v1.add_spec(t1.mul_spec(v0.sub_spec(v1))),
        Rational::from_int_spec(0));
    // interp_rel at u = 1 − t1: flip the q1-side form
    lemma_interp_flip(q0.x, q1.x, t1);
    lemma_interp_flip(q0.y, q1.y, t1);
    Rational::lemma_eqv_transitive(
        q.x,
        vadd(q1, vscale(t1, vsub(q0, q1))).x,
        vadd(q0, vscale(u, vsub(q1, q0))).x);
    Rational::lemma_eqv_transitive(
        q.y,
        vadd(q1, vscale(t1, vsub(q0, q1))).y,
        vadd(q0, vscale(u, vsub(q1, q0))).y);
    assert(crate::narrowphase::interp_rel(q0, q1, q, u));
}

} // verus!

verus! {

/// The segment endpoints interpolate themselves: interp_rel(a, b, a, 0)
/// and interp_rel(a, b, b, 1).
pub proof fn lemma_interp_rel_endpoints(a: Vec2<Rational>, b: Vec2<Rational>)
    ensures
        crate::narrowphase::interp_rel(a, b, a, Rational::from_int_spec(0)),
        crate::narrowphase::interp_rel(a, b, b, Rational::from_int_spec(1)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    // bounds: 0 ≤ 0 ≤ 1 and 0 ≤ 1 ≤ 1 (closed)
    Rational::lemma_eqv_reflexive(zero);
    Rational::lemma_eqv_implies_le(zero, zero);
    Rational::lemma_from_int_preserves_le(0, 1);
    Rational::lemma_eqv_reflexive(one);
    Rational::lemma_eqv_implies_le(one, one);
    // u = 0: a ≡ a + 0·(b − a) per component
    Rational::lemma_mul_zero(b.x.sub_spec(a.x));
    Rational::lemma_mul_zero(b.y.sub_spec(a.y));
    Rational::lemma_eqv_reflexive(a.x);
    Rational::lemma_eqv_reflexive(a.y);
    Rational::lemma_eqv_add_congruence(
        a.x, a.x, zero.mul_spec(b.x.sub_spec(a.x)), zero);
    Rational::lemma_eqv_add_congruence(
        a.y, a.y, zero.mul_spec(b.y.sub_spec(a.y)), zero);
    Rational::lemma_add_zero_identity(a.x);
    Rational::lemma_add_zero_identity(a.y);
    Rational::lemma_eqv_symmetric(
        a.x.add_spec(zero.mul_spec(b.x.sub_spec(a.x))), a.x);
    Rational::lemma_eqv_symmetric(
        a.y.add_spec(zero.mul_spec(b.y.sub_spec(a.y))), a.y);
    // u = 1: b ≡ a + 1·(b − a) per component
    Rational::lemma_mul_one_identity(b.x.sub_spec(a.x));
    Rational::lemma_mul_one_identity(b.y.sub_spec(a.y));
    assert(one.mul_spec(b.x.sub_spec(a.x)) == b.x.sub_spec(a.x));
    assert(one.mul_spec(b.y.sub_spec(a.y)) == b.y.sub_spec(a.y));
    lemma_add_sub_cancel(a.x, b.x);
    lemma_add_sub_cancel(a.y, b.y);
    Rational::lemma_eqv_symmetric(
        a.x.add_spec(one.mul_spec(b.x.sub_spec(a.x))), b.x);
    Rational::lemma_eqv_symmetric(
        a.y.add_spec(one.mul_spec(b.y.sub_spec(a.y))), b.y);
}

} // verus!

verus! {

//  ── Negated-axis and zero-product lemmas ────────────────────────────

/// vdot with a negated left argument (canonical trait neg).
pub proof fn lemma_vdot_neg_left(d: Vec2<Rational>, w: Vec2<Rational>)
    ensures
        vdot(d.neg(), w).eqv_spec(vdot(d, w).neg_spec()),
{
    // trait neg canonicalizes: d.neg().x == d.x.neg_spec().canonical()
    Rational::lemma_canonical_exists(d.x.neg_spec());
    Rational::lemma_canonical_exists(d.y.neg_spec());
    Rational::lemma_eqv_reflexive(w.x);
    Rational::lemma_eqv_reflexive(w.y);
    Rational::lemma_eqv_mul_congruence(
        d.x.neg_spec().canonical(), d.x.neg_spec(), w.x, w.x);
    Rational::lemma_eqv_mul_congruence(
        d.y.neg_spec().canonical(), d.y.neg_spec(), w.y, w.y);
    // (−dx)·wx ≡ −(dx·wx) etc. (mul_neg_right + commutativity, structural)
    Rational::lemma_mul_neg_right(w.x, d.x);
    Rational::lemma_mul_commutative(w.x, d.x);
    Rational::lemma_mul_commutative(d.x.neg_spec(), w.x);
    Rational::lemma_mul_neg_right(w.y, d.y);
    Rational::lemma_mul_commutative(w.y, d.y);
    Rational::lemma_mul_commutative(d.y.neg_spec(), w.y);
    assert(d.x.neg_spec().mul_spec(w.x) == d.x.mul_spec(w.x).neg_spec());
    assert(d.y.neg_spec().mul_spec(w.y) == d.y.mul_spec(w.y).neg_spec());
    Rational::lemma_eqv_transitive(
        d.neg().x.mul_spec(w.x), d.x.neg_spec().mul_spec(w.x), d.x.mul_spec(w.x).neg_spec());
    Rational::lemma_eqv_transitive(
        d.neg().y.mul_spec(w.y), d.y.neg_spec().mul_spec(w.y), d.y.mul_spec(w.y).neg_spec());
    // sum ≡ −(dx·wx) + −(dy·wy) == −(dx·wx + dy·wy) (neg_add, structural)
    Rational::lemma_eqv_add_congruence(
        d.neg().x.mul_spec(w.x), d.x.mul_spec(w.x).neg_spec(),
        d.neg().y.mul_spec(w.y), d.y.mul_spec(w.y).neg_spec());
    Rational::lemma_neg_add(d.x.mul_spec(w.x), d.y.mul_spec(w.y));
    Rational::lemma_eqv_transitive(
        vdot(d.neg(), w),
        d.x.mul_spec(w.x).neg_spec().add_spec(d.y.mul_spec(w.y).neg_spec()),
        vdot(d, w).neg_spec());
}

/// axis_sep with a negated axis.
pub proof fn lemma_axis_sep_neg_left(
    d: Vec2<Rational>,
    base: Vec2<Rational>,
    q: Vec2<Rational>,
)
    ensures
        axis_sep(d.neg(), base, q).eqv_spec(axis_sep(d, base, q).neg_spec()),
{
    // axis_sep(n, base, q) == vdot(n, vsub(q, base)) — structural.
    lemma_vdot_neg_left(d, vsub(q, base));
}

/// x ≡ 0 ⟹ x·y ≡ 0.
pub proof fn lemma_eqv_zero_mul_left(x: Rational, y: Rational)
    requires
        x.eqv_spec(Rational::from_int_spec(0)),
    ensures
        x.mul_spec(y).eqv_spec(Rational::from_int_spec(0)),
{
    Rational::lemma_eqv_zero_iff_num_zero(x);
    Rational::lemma_eqv_zero_iff_num_zero(x.mul_spec(y));
    assert(x.num == 0);
    assert(x.mul_spec(y).num == x.num * y.num);
}

/// x·x ≡ 0 ⟹ x ≡ 0.
pub proof fn lemma_sq_eqv_zero(x: Rational)
    requires
        x.mul_spec(x).eqv_spec(Rational::from_int_spec(0)),
    ensures
        x.eqv_spec(Rational::from_int_spec(0)),
{
    Rational::lemma_eqv_zero_iff_num_zero(x.mul_spec(x));
    Rational::lemma_eqv_zero_iff_num_zero(x);
    assert(x.mul_spec(x).num == x.num * x.num);
    assert(x.num * x.num == 0 ==> x.num == 0) by (nonlinear_arith);
}

/// a ≥ 0 ∧ b ≥ 0 ∧ a + b ≡ 0 ⟹ a ≡ 0 ∧ b ≡ 0.
pub proof fn lemma_nonneg_sum_zero(a: Rational, b: Rational)
    requires
        Rational::from_int_spec(0).le_spec(a),
        Rational::from_int_spec(0).le_spec(b),
        a.add_spec(b).eqv_spec(Rational::from_int_spec(0)),
    ensures
        a.eqv_spec(Rational::from_int_spec(0)),
        b.eqv_spec(Rational::from_int_spec(0)),
{
    let zero = Rational::from_int_spec(0);
    // a ≤ a + b ≤ 0
    Rational::lemma_eqv_reflexive(a);
    Rational::lemma_le_add_both(a, a, zero, b);
    Rational::lemma_add_zero_identity(a);
    crate::proofs::shape::lemma_le_eqv_subst_right(a, a.add_spec(b), zero);
    Rational::lemma_le_antisymmetric(a, zero);
    // b ≤ a + b ≤ 0
    Rational::lemma_eqv_reflexive(b);
    Rational::lemma_le_add_both(b, b, zero, a);
    Rational::lemma_add_zero_identity(b);
    // b ≤ b + a ≡ a + b ≡ 0
    Rational::lemma_add_commutative(b, a);
    Rational::lemma_eqv_transitive(b.add_spec(a), a.add_spec(b), zero);
    crate::proofs::shape::lemma_le_eqv_subst_right(b, b.add_spec(a), zero);
    Rational::lemma_le_antisymmetric(b, zero);
}

/// Adjacent vertices of a convex polygon differ: the edge normal of every
/// edge has nonzero squared length (the |n|² ≢ 0 gate of SPEC §5 step 3).
pub proof fn lemma_edge_normal_nonzero(vs: Seq<Vec2<Rational>>, i: int)
    requires
        convex_poly_inv(vs),
        0 <= i < vs.len(),
    ensures
        !vdot(
            edge_normal(vs[i], vs[(i + 1) % (vs.len() as int)]),
            edge_normal(vs[i], vs[(i + 1) % (vs.len() as int)])).eqv_spec(
            Rational::from_int_spec(0)),
{
    let n = vs.len();
    let i1 = (i + 1) % (n as int);
    let j = (i + 2) % (n as int);
    let en = edge_normal(vs[i], vs[i1]);
    // j is a valid off-edge index: j ≠ i and j ≠ i1 (n ≥ 3)
    assert(n >= 3);
    assert(j != i && j != i1) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 2) as int, n as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 1) as int, n as int);
        assert(0 <= j && j < n);
        assert(0 <= i1 && i1 < n);
        assert(j != i) by (nonlinear_arith)
            requires
                n >= 3,
                0 <= i < n as int,
                i + 2 == (n as int) * ((i + 2) / (n as int)) + j,
                0 <= j < n as int;
        assert(j != i1) by (nonlinear_arith)
            requires
                n >= 3,
                0 <= i < n as int,
                i + 2 == (n as int) * ((i + 2) / (n as int)) + j,
                i + 1 == (n as int) * ((i + 1) / (n as int)) + i1,
                0 <= j < n as int,
                0 <= i1 < n as int;
    }
    // convexity: orient > 0 at (i, i1, j)
    assert(Rational::from_int_spec(0).lt_spec(orient(vs[i], vs[i1], vs[j])));
    if vdot(en, en).eqv_spec(Rational::from_int_spec(0)) {
        let zero = Rational::from_int_spec(0);
        let d = vsub(vs[i1], vs[i]);
        // en = (d.y, −d.x); |en|² ≡ 0 with squares ≥ 0 forces d.x ≡ d.y ≡ 0
        Rational::lemma_square_le_nonneg(en.x);
        Rational::lemma_square_le_nonneg(en.y);
        lemma_nonneg_sum_zero(en.x.mul_spec(en.x), en.y.mul_spec(en.y));
        lemma_sq_eqv_zero(en.x);
        lemma_sq_eqv_zero(en.y);
        assert(en.y == d.x.neg_spec()) by {
            assert(en.y == vs[i].x.sub_spec(vs[i1].x));
            assert(d.x == vs[i1].x.sub_spec(vs[i].x));
            lemma_sub_neg_structural(vs[i].x, vs[i1].x);
        }
        Rational::lemma_eqv_neg_congruence(en.y, zero);
        assert(zero.neg_spec() == zero);
        // orient = d.x·w.y − d.y·w.x ≡ 0 — contradiction
        let w = vsub(vs[j], vs[i]);
        lemma_eqv_zero_mul_left(d.x, w.y);
        lemma_eqv_zero_mul_left(d.y, w.x);
        Rational::lemma_eqv_reflexive(zero);
        Rational::lemma_eqv_sub_congruence(
            d.x.mul_spec(w.y), zero, d.y.mul_spec(w.x), zero);
        assert(d.x.mul_spec(w.y).sub_spec(d.y.mul_spec(w.x)).eqv_spec(
            zero.sub_spec(zero)));
        Rational::lemma_add_zero_identity(zero.neg_spec());
        assert(zero.sub_spec(zero) == zero.add_spec(zero.neg_spec()));
        assert(orient(vs[i], vs[i1], vs[j]).eqv_spec(zero));
        Rational::lemma_trichotomy(zero, orient(vs[i], vs[i1], vs[j]));
        assert(false);
    }
}

} // verus!

verus! {

//  ── Basis decomposition over the reference edge ─────────────────────

/// (a·b)·c ≡ (a·c)·b.
pub proof fn lemma_mul_perm3(a: Rational, b: Rational, c: Rational)
    ensures
        a.mul_spec(b).mul_spec(c).eqv_spec(a.mul_spec(c).mul_spec(b)),
{
    Rational::lemma_mul_associative(a, b, c);
    Rational::lemma_mul_commutative(b, c);
    assert(a.mul_spec(b.mul_spec(c)) == a.mul_spec(c.mul_spec(b)));
    Rational::lemma_mul_associative(a, c, b);
    Rational::lemma_eqv_symmetric(
        a.mul_spec(c).mul_spec(b), a.mul_spec(c.mul_spec(b)));
    Rational::lemma_eqv_transitive(
        a.mul_spec(b).mul_spec(c),
        a.mul_spec(b.mul_spec(c)),
        a.mul_spec(c).mul_spec(b));
}

/// (P + Q) + (R − Q) ≡ P + R.
pub proof fn lemma_add_cancel_right(P: Rational, Q: Rational, R: Rational)
    ensures
        P.add_spec(Q).add_spec(R.sub_spec(Q)).eqv_spec(P.add_spec(R)),
{
    // (P+Q)+(R+(−Q)) ≡ P+(Q+(R+(−Q)))
    Rational::lemma_add_associative(P, Q, R.sub_spec(Q));
    // Q+(R+(−Q)) ≡ (R+(−Q))+Q ≡ R+((−Q)+Q) ≡ R+0 ≡ R
    Rational::lemma_add_commutative(Q, R.sub_spec(Q));
    Rational::lemma_add_associative(R, Q.neg_spec(), Q);
    Rational::lemma_add_inverse(Q);
    Rational::lemma_eqv_reflexive(R);
    Rational::lemma_eqv_add_congruence(
        R, R, Q.neg_spec().add_spec(Q), Rational::from_int_spec(0));
    Rational::lemma_add_zero_identity(R);
    Rational::lemma_eqv_transitive(
        R.sub_spec(Q).add_spec(Q),
        R.add_spec(Q.neg_spec().add_spec(Q)),
        R.add_spec(Rational::from_int_spec(0)));
    Rational::lemma_eqv_transitive(
        R.sub_spec(Q).add_spec(Q),
        R.add_spec(Rational::from_int_spec(0)),
        R);
    Rational::lemma_eqv_transitive(
        Q.add_spec(R.sub_spec(Q)),
        R.sub_spec(Q).add_spec(Q),
        R);
    // lift under P + (·)
    Rational::lemma_eqv_reflexive(P);
    Rational::lemma_eqv_add_congruence(P, P, Q.add_spec(R.sub_spec(Q)), R);
    Rational::lemma_eqv_transitive(
        P.add_spec(Q).add_spec(R.sub_spec(Q)),
        P.add_spec(Q.add_spec(R.sub_spec(Q))),
        P.add_spec(R));
}

/// (X + Y) − X ≡ Y.
pub proof fn lemma_add_sub_cancel_right(X: Rational, Y: Rational)
    ensures
        X.add_spec(Y).sub_spec(X).eqv_spec(Y),
{
    // (X+Y)−X == (Y+X)+(−X) ≡ Y+(X+(−X)) ≡ Y+0 ≡ Y
    Rational::lemma_add_commutative(X, Y);
    Rational::lemma_add_associative(Y, X, X.neg_spec());
    Rational::lemma_eqv_symmetric(
        Y.add_spec(X).add_spec(X.neg_spec()), Y.add_spec(X.add_spec(X.neg_spec())));
    Rational::lemma_add_inverse(X);
    Rational::lemma_eqv_reflexive(Y);
    Rational::lemma_eqv_add_congruence(
        Y, Y, X.add_spec(X.neg_spec()), Rational::from_int_spec(0));
    Rational::lemma_add_zero_identity(Y);
    Rational::lemma_eqv_transitive(
        Y.add_spec(X.add_spec(X.neg_spec())),
        Y.add_spec(Rational::from_int_spec(0)),
        Y);
    Rational::lemma_eqv_transitive(
        Y.add_spec(X).add_spec(X.neg_spec()),
        Y.add_spec(X.add_spec(X.neg_spec())),
        Y);
    Rational::lemma_eqv_transitive(
        X.add_spec(Y).add_spec(X.neg_spec()),
        Y.add_spec(X).add_spec(X.neg_spec()),
        Y);
}

/// (X + Y) − (X − W) ≡ Y + W.
pub proof fn lemma_sub_sub_swap_xy(X: Rational, Y: Rational, W: Rational)
    ensures
        X.add_spec(Y).sub_spec(X.sub_spec(W)).eqv_spec(Y.add_spec(W)),
{
    // −(X−W) == W−X (structural)
    lemma_sub_neg_structural(W, X);
    // (X+Y)+(W−X) ≡ ((X+Y)+W)−X [assoc, symmetric]
    Rational::lemma_add_associative(X.add_spec(Y), W, X.neg_spec());
    Rational::lemma_eqv_symmetric(
        X.add_spec(Y).add_spec(W).add_spec(X.neg_spec()),
        X.add_spec(Y).add_spec(W.add_spec(X.neg_spec())));
    // ((X+Y)+W)−X ≡ ((X+Y)−X)+W [swap]
    lemma_add_sub_swap(X.add_spec(Y), W, X);
    // (X+Y)−X ≡ Y [cancel_right]; lift under (·)+W
    lemma_add_sub_cancel_right(X, Y);
    Rational::lemma_eqv_reflexive(W);
    Rational::lemma_eqv_add_congruence(
        X.add_spec(Y).sub_spec(X), Y, W, W);
    // chain
    Rational::lemma_eqv_transitive(
        X.add_spec(Y).add_spec(W).sub_spec(X),
        X.add_spec(Y).sub_spec(X).add_spec(W),
        Y.add_spec(W));
    Rational::lemma_eqv_transitive(
        X.add_spec(Y).add_spec(W).add_spec(X.neg_spec()),
        X.add_spec(Y).add_spec(W).sub_spec(X),
        Y.add_spec(W));
    Rational::lemma_eqv_transitive(
        X.add_spec(Y).add_spec(W.add_spec(X.neg_spec())),
        X.add_spec(Y).add_spec(W).add_spec(X.neg_spec()),
        Y.add_spec(W));
    // (X+Y)−(X−W) == (X+Y)+(W−X) — sub is add-neg, structural
    assert(X.add_spec(Y).sub_spec(X.sub_spec(W))
        == X.add_spec(Y).add_spec(W.sub_spec(X)));
    Rational::lemma_eqv_transitive(
        X.add_spec(Y).sub_spec(X.sub_spec(W)),
        X.add_spec(Y).add_spec(W.sub_spec(X)),
        Y.add_spec(W));
}

/// (dx·ux + dy·uy)·dx ≡ dx²·ux + (dx·dy)·uy.
pub proof fn lemma_basis_term_x1(
    dx: Rational,
    dy: Rational,
    ux: Rational,
    uy: Rational,
)
    ensures
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dx).eqv_spec(
            dx.mul_spec(dx).mul_spec(ux).add_spec(dx.mul_spec(dy).mul_spec(uy))),
{
    let a = dx.mul_spec(ux);
    let b = dy.mul_spec(uy);
    // dx·(a+b) ≡ dx·a + dx·b
    Rational::lemma_mul_distributes_over_add(dx, a, b);
    // dx·a == a·dx ≡ dx²·ux ; dx·b == b·dx ≡ (dy·dx)·uy == (dx·dy)·uy
    lemma_mul_perm3(dx, ux, dx);
    lemma_mul_perm3(dy, uy, dx);
    Rational::lemma_mul_commutative(dx, a);
    Rational::lemma_mul_commutative(dx, b);
    Rational::lemma_mul_commutative(dy, dx);
    assert(dx.mul_spec(b) == dy.mul_spec(dx).mul_spec(uy)
        || dx.mul_spec(b) == dy.mul_spec(uy).mul_spec(dx));
    assert(dy.mul_spec(dx).mul_spec(uy) == dx.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_reflexive(a.mul_spec(dx));
    Rational::lemma_eqv_reflexive(dx.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_add_congruence(
        dx.mul_spec(a), a.mul_spec(dx),
        dx.mul_spec(b), dx.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_reflexive(dx.mul_spec(dx).mul_spec(ux));
    Rational::lemma_eqv_add_congruence(
        a.mul_spec(dx), dx.mul_spec(dx).mul_spec(ux),
        dx.mul_spec(dy).mul_spec(uy), dx.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(a).add_spec(dx.mul_spec(b)),
        a.mul_spec(dx).add_spec(dx.mul_spec(dy).mul_spec(uy)),
        dx.mul_spec(dx).mul_spec(ux).add_spec(dx.mul_spec(dy).mul_spec(uy)));
    // (a+b)·dx == dx·(a+b) structural
    Rational::lemma_mul_commutative(a.add_spec(b), dx);
    Rational::lemma_eqv_transitive(
        a.add_spec(b).mul_spec(dx),
        dx.mul_spec(a).add_spec(dx.mul_spec(b)),
        dx.mul_spec(dx).mul_spec(ux).add_spec(dx.mul_spec(dy).mul_spec(uy)));
}

/// (dy·ux − dx·uy)·dy ≡ dy²·ux − (dx·dy)·uy.
pub proof fn lemma_basis_term_x2(
    dx: Rational,
    dy: Rational,
    ux: Rational,
    uy: Rational,
)
    ensures
        dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dy).eqv_spec(
            dy.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dy).mul_spec(uy))),
{
    let c = dy.mul_spec(ux);
    let d = dx.mul_spec(uy);
    // dy·(c−d) ≡ dy·c − dy·d
    lemma_mul_distributes_over_sub(dy, c, d);
    lemma_mul_perm3(dy, ux, dy);
    // dy·c == c·dy ≡ dy²·ux
    lemma_mul_perm3(dx, uy, dy);
    // dy·d == d·dy ≡ (dx·dy)·uy
    Rational::lemma_mul_commutative(dy, c);
    Rational::lemma_mul_commutative(dy, d);
    Rational::lemma_eqv_reflexive(c.mul_spec(dy));
    Rational::lemma_eqv_reflexive(d.mul_spec(dy));
    Rational::lemma_eqv_sub_congruence(
        dy.mul_spec(c), c.mul_spec(dy), dy.mul_spec(d), d.mul_spec(dy));
    Rational::lemma_eqv_reflexive(dy.mul_spec(dy).mul_spec(ux));
    Rational::lemma_eqv_reflexive(dx.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_sub_congruence(
        c.mul_spec(dy), dy.mul_spec(dy).mul_spec(ux),
        d.mul_spec(dy), dx.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dy.mul_spec(c).sub_spec(dy.mul_spec(d)),
        c.mul_spec(dy).sub_spec(d.mul_spec(dy)),
        dy.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dy).mul_spec(uy)));
    Rational::lemma_mul_commutative(c.sub_spec(d), dy);
    Rational::lemma_eqv_transitive(
        c.sub_spec(d).mul_spec(dy),
        dy.mul_spec(c).sub_spec(dy.mul_spec(d)),
        dy.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dy).mul_spec(uy)));
}

/// The x-component numerator of the edge-basis expansion:
/// (dx·ux + dy·uy)·dx + (dy·ux − dx·uy)·dy ≡ (dx² + dy²)·ux.
pub proof fn lemma_basis_decomp_scalar_x(
    dx: Rational,
    dy: Rational,
    ux: Rational,
    uy: Rational,
)
    ensures
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dx).add_spec(
            dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dy)).eqv_spec(
            dx.mul_spec(dx).add_spec(dy.mul_spec(dy)).mul_spec(ux)),
{
    let l = dx.mul_spec(dx).add_spec(dy.mul_spec(dy));
    lemma_basis_term_x1(dx, dy, ux, uy);
    lemma_basis_term_x2(dx, dy, ux, uy);
    // sum ≡ (dx²·ux + dxdy·uy) + (dy²·ux − dxdy·uy) ≡ dx²·ux + dy²·ux
    Rational::lemma_eqv_add_congruence(
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dx),
        dx.mul_spec(dx).mul_spec(ux).add_spec(dx.mul_spec(dy).mul_spec(uy)),
        dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dy),
        dy.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dy).mul_spec(uy)));
    lemma_add_cancel_right(
        dx.mul_spec(dx).mul_spec(ux),
        dx.mul_spec(dy).mul_spec(uy),
        dy.mul_spec(dy).mul_spec(ux));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dx).add_spec(
            dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dy)),
        dx.mul_spec(dx).mul_spec(ux).add_spec(dx.mul_spec(dy).mul_spec(uy)).add_spec(
            dy.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dy).mul_spec(uy))),
        dx.mul_spec(dx).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(ux)));
    // dx²·ux + dy²·ux ≡ ux·(dx²+dy²) == l·ux
    Rational::lemma_mul_distributes_over_add(ux, dx.mul_spec(dx), dy.mul_spec(dy));
    Rational::lemma_mul_commutative(ux, dx.mul_spec(dx));
    Rational::lemma_mul_commutative(ux, dy.mul_spec(dy));
    assert(ux.mul_spec(dx.mul_spec(dx)) == dx.mul_spec(dx).mul_spec(ux));
    assert(ux.mul_spec(dy.mul_spec(dy)) == dy.mul_spec(dy).mul_spec(ux));
    Rational::lemma_mul_commutative(l, ux);
    Rational::lemma_eqv_reflexive(l.mul_spec(ux));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(dx).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(ux)),
        ux.mul_spec(l),
        l.mul_spec(ux));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dx).add_spec(
            dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dy)),
        dx.mul_spec(dx).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(ux)),
        l.mul_spec(ux));
}

/// (dx·ux + dy·uy)·dy ≡ (dx·dy)·ux + dy²·uy.
pub proof fn lemma_basis_term_y1(
    dx: Rational,
    dy: Rational,
    ux: Rational,
    uy: Rational,
)
    ensures
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dy).eqv_spec(
            dx.mul_spec(dy).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(uy))),
{
    let a = dx.mul_spec(ux);
    let b = dy.mul_spec(uy);
    Rational::lemma_mul_distributes_over_add(dy, a, b);
    lemma_mul_perm3(dx, ux, dy);
    // dy·a == a·dy ≡ (dx·dy)·ux
    lemma_mul_perm3(dy, uy, dy);
    // dy·b == b·dy ≡ dy²·uy
    Rational::lemma_mul_commutative(dy, a);
    Rational::lemma_mul_commutative(dy, b);
    Rational::lemma_eqv_reflexive(a.mul_spec(dy));
    Rational::lemma_eqv_reflexive(b.mul_spec(dy));
    Rational::lemma_eqv_add_congruence(
        dy.mul_spec(a), a.mul_spec(dy), dy.mul_spec(b), b.mul_spec(dy));
    Rational::lemma_eqv_reflexive(dx.mul_spec(dy).mul_spec(ux));
    Rational::lemma_eqv_reflexive(dy.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_add_congruence(
        a.mul_spec(dy), dx.mul_spec(dy).mul_spec(ux),
        b.mul_spec(dy), dy.mul_spec(dy).mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dy.mul_spec(a).add_spec(dy.mul_spec(b)),
        a.mul_spec(dy).add_spec(b.mul_spec(dy)),
        dx.mul_spec(dy).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(uy)));
    Rational::lemma_mul_commutative(a.add_spec(b), dy);
    Rational::lemma_eqv_transitive(
        a.add_spec(b).mul_spec(dy),
        dy.mul_spec(a).add_spec(dy.mul_spec(b)),
        dx.mul_spec(dy).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(uy)));
}

/// (dy·ux − dx·uy)·dx ≡ (dx·dy)·ux − dx²·uy.
pub proof fn lemma_basis_term_y2(
    dx: Rational,
    dy: Rational,
    ux: Rational,
    uy: Rational,
)
    ensures
        dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dx).eqv_spec(
            dx.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dx).mul_spec(uy))),
{
    let c = dy.mul_spec(ux);
    let d = dx.mul_spec(uy);
    lemma_mul_distributes_over_sub(dx, c, d);
    lemma_mul_perm3(dy, ux, dx);
    // dx·c == c·dx ≡ (dy·dx)·ux == (dx·dy)·ux
    lemma_mul_perm3(dx, uy, dx);
    // dx·d == d·dx ≡ dx²·uy
    Rational::lemma_mul_commutative(dx, c);
    Rational::lemma_mul_commutative(dx, d);
    Rational::lemma_mul_commutative(dy, dx);
    assert(dy.mul_spec(dx).mul_spec(ux) == dx.mul_spec(dy).mul_spec(ux));
    Rational::lemma_eqv_reflexive(dx.mul_spec(dy).mul_spec(ux));
    Rational::lemma_eqv_reflexive(dx.mul_spec(dx).mul_spec(uy));
    Rational::lemma_eqv_sub_congruence(
        dx.mul_spec(c), dx.mul_spec(dy).mul_spec(ux),
        dx.mul_spec(d), dx.mul_spec(dx).mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(c).sub_spec(dx.mul_spec(d)),
        dx.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dx).mul_spec(uy)),
        dx.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dx).mul_spec(uy)));
    Rational::lemma_mul_commutative(c.sub_spec(d), dx);
    Rational::lemma_eqv_transitive(
        c.sub_spec(d).mul_spec(dx),
        dx.mul_spec(c).sub_spec(dx.mul_spec(d)),
        dx.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dx).mul_spec(uy)));
}

/// The y-component numerator: (dx·ux + dy·uy)·dy − (dy·ux − dx·uy)·dx
/// ≡ (dx² + dy²)·uy.
pub proof fn lemma_basis_decomp_scalar_y(
    dx: Rational,
    dy: Rational,
    ux: Rational,
    uy: Rational,
)
    ensures
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dy).sub_spec(
            dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dx)).eqv_spec(
            dx.mul_spec(dx).add_spec(dy.mul_spec(dy)).mul_spec(uy)),
{
    let l = dx.mul_spec(dx).add_spec(dy.mul_spec(dy));
    lemma_basis_term_y1(dx, dy, ux, uy);
    lemma_basis_term_y2(dx, dy, ux, uy);
    // (X + Y) − (X − W) ≡ Y + W with X = dxdy·ux, Y = dy²·uy, W = dx²·uy
    Rational::lemma_eqv_sub_congruence(
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dy),
        dx.mul_spec(dy).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(uy)),
        dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dx),
        dx.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dx).mul_spec(uy)));
    lemma_sub_sub_swap_xy(
        dx.mul_spec(dy).mul_spec(ux),
        dy.mul_spec(dy).mul_spec(uy),
        dx.mul_spec(dx).mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dy).sub_spec(
            dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dx)),
        dx.mul_spec(dy).mul_spec(ux).add_spec(dy.mul_spec(dy).mul_spec(uy)).sub_spec(
            dx.mul_spec(dy).mul_spec(ux).sub_spec(dx.mul_spec(dx).mul_spec(uy))),
        dy.mul_spec(dy).mul_spec(uy).add_spec(dx.mul_spec(dx).mul_spec(uy)));
    // dy²·uy + dx²·uy ≡ uy·l == l·uy
    Rational::lemma_mul_distributes_over_add(uy, dx.mul_spec(dx), dy.mul_spec(dy));
    Rational::lemma_mul_commutative(uy, dx.mul_spec(dx));
    Rational::lemma_mul_commutative(uy, dy.mul_spec(dy));
    assert(uy.mul_spec(dx.mul_spec(dx)) == dx.mul_spec(dx).mul_spec(uy));
    assert(uy.mul_spec(dy.mul_spec(dy)) == dy.mul_spec(dy).mul_spec(uy));
    Rational::lemma_mul_commutative(l, uy);
    Rational::lemma_eqv_reflexive(l.mul_spec(uy));
    Rational::lemma_add_commutative(
        dy.mul_spec(dy).mul_spec(uy), dx.mul_spec(dx).mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dy.mul_spec(dy).mul_spec(uy).add_spec(dx.mul_spec(dx).mul_spec(uy)),
        dx.mul_spec(dx).mul_spec(uy).add_spec(dy.mul_spec(dy).mul_spec(uy)),
        uy.mul_spec(l));
    Rational::lemma_eqv_transitive(
        dy.mul_spec(dy).mul_spec(uy).add_spec(dx.mul_spec(dx).mul_spec(uy)),
        uy.mul_spec(l),
        l.mul_spec(uy));
    Rational::lemma_eqv_transitive(
        dx.mul_spec(ux).add_spec(dy.mul_spec(uy)).mul_spec(dy).sub_spec(
            dy.mul_spec(ux).sub_spec(dx.mul_spec(uy)).mul_spec(dx)),
        dy.mul_spec(dy).mul_spec(uy).add_spec(dx.mul_spec(dx).mul_spec(uy)),
        l.mul_spec(uy));
}

/// The exact decomposition of a point over the reference-edge basis:
/// q ≡ p0 + t·d + s·n with t = dot(d, q − p0)/|d|², s = dot(n, q − p0)/|d|².
pub proof fn lemma_basis_decomposition(
    p0: Vec2<Rational>,
    p1: Vec2<Rational>,
    q: Vec2<Rational>,
)
    requires
        !vdot(vsub(p1, p0), vsub(p1, p0)).eqv_spec(Rational::from_int_spec(0)),
    ensures ({
        let d = vsub(p1, p0);
        let n = edge_normal(p0, p1);
        let l = vdot(d, d);
        let delta = vsub(q, p0);
        let t = vdot(d, delta).div_spec(l);
        let s = vdot(n, delta).div_spec(l);
        &&& q.x.eqv_spec(vadd(p0, vadd(vscale(t, d), vscale(s, n))).x)
        &&& q.y.eqv_spec(vadd(p0, vadd(vscale(t, d), vscale(s, n))).y)
    }),
{
    let d = vsub(p1, p0);
    let n = edge_normal(p0, p1);
    let l = vdot(d, d);
    let delta = vsub(q, p0);
    let t = vdot(d, delta).div_spec(l);
    let s = vdot(n, delta).div_spec(l);
    // structural forms
    assert(n.x == d.y);
    assert(n.y == p0.x.sub_spec(p1.x));
    lemma_sub_neg_structural(p0.x, p1.x);
    assert(n.y == d.x.neg_spec());
    assert(vdot(d, delta) == d.x.mul_spec(delta.x).add_spec(d.y.mul_spec(delta.y)));
    assert(vdot(n, delta) == d.y.mul_spec(delta.x).add_spec(d.x.neg_spec().mul_spec(delta.y)));
    Rational::lemma_mul_neg_right(delta.y, d.x);
    Rational::lemma_mul_commutative(delta.y, d.x);
    Rational::lemma_mul_commutative(d.x.neg_spec(), delta.y);
    assert(d.x.neg_spec().mul_spec(delta.y) == d.x.mul_spec(delta.y).neg_spec());
    // t·d.x + s·n.x ≡ (vdot(d,Δ)·d.x + vdot(n,Δ)·d.y) / l ≡ (l·Δ.x)/l ≡ Δ.x
    Rational::lemma_div_mul_assoc(vdot(d, delta), l, d.x);
    Rational::lemma_div_mul_assoc(vdot(n, delta), l, n.x);
    Rational::lemma_div_add_numerator(
        vdot(d, delta).mul_spec(d.x), vdot(n, delta).mul_spec(n.x), l);
    Rational::lemma_eqv_symmetric(
        vdot(d, delta).mul_spec(d.x).add_spec(vdot(n, delta).mul_spec(n.x)).div_spec(l),
        vdot(d, delta).mul_spec(d.x).div_spec(l).add_spec(
            vdot(n, delta).mul_spec(n.x).div_spec(l)));
    lemma_basis_decomp_scalar_x(d.x, d.y, delta.x, delta.y);
    assert(vdot(d, delta).mul_spec(d.x).add_spec(vdot(n, delta).mul_spec(n.x))
        == d.x.mul_spec(delta.x).add_spec(d.y.mul_spec(delta.y)).mul_spec(d.x).add_spec(
            d.y.mul_spec(delta.x).sub_spec(d.x.mul_spec(delta.y)).mul_spec(d.y)));
    Rational::lemma_eqv_transitive(
        vdot(d, delta).mul_spec(d.x).add_spec(vdot(n, delta).mul_spec(n.x)),
        d.x.mul_spec(delta.x).add_spec(d.y.mul_spec(delta.y)).mul_spec(d.x).add_spec(
            d.y.mul_spec(delta.x).sub_spec(d.x.mul_spec(delta.y)).mul_spec(d.y)),
        l.mul_spec(delta.x));
    Rational::lemma_div_congruence(
        vdot(d, delta).mul_spec(d.x).add_spec(vdot(n, delta).mul_spec(n.x)),
        l.mul_spec(delta.x), l);
    Rational::lemma_mul_commutative(l, delta.x);
    Rational::lemma_div_mul_cancel(delta.x, l);
    assert(delta.x.mul_spec(l) == l.mul_spec(delta.x));
    // chain x: t·d.x + s·n.x ≡ Δ.x
    Rational::lemma_eqv_add_congruence(
        t.mul_spec(d.x), vdot(d, delta).mul_spec(d.x).div_spec(l),
        s.mul_spec(n.x), vdot(n, delta).mul_spec(n.x).div_spec(l));
    Rational::lemma_eqv_transitive(
        t.mul_spec(d.x).add_spec(s.mul_spec(n.x)),
        vdot(d, delta).mul_spec(d.x).div_spec(l).add_spec(
            vdot(n, delta).mul_spec(n.x).div_spec(l)),
        vdot(d, delta).mul_spec(d.x).add_spec(vdot(n, delta).mul_spec(n.x)).div_spec(l));
    Rational::lemma_eqv_transitive(
        t.mul_spec(d.x).add_spec(s.mul_spec(n.x)),
        vdot(d, delta).mul_spec(d.x).add_spec(vdot(n, delta).mul_spec(n.x)).div_spec(l),
        l.mul_spec(delta.x).div_spec(l));
    Rational::lemma_eqv_transitive(
        t.mul_spec(d.x).add_spec(s.mul_spec(n.x)),
        l.mul_spec(delta.x).div_spec(l),
        delta.x);
    // p0.x + Δ.x ≡ q.x
    lemma_add_sub_cancel(p0.x, q.x);
    Rational::lemma_eqv_reflexive(p0.x);
    Rational::lemma_eqv_add_congruence(
        p0.x, p0.x, t.mul_spec(d.x).add_spec(s.mul_spec(n.x)), delta.x);
    assert(delta.x == q.x.sub_spec(p0.x));
    Rational::lemma_eqv_transitive(
        p0.x.add_spec(t.mul_spec(d.x).add_spec(s.mul_spec(n.x))),
        p0.x.add_spec(delta.x),
        q.x);
    Rational::lemma_eqv_symmetric(
        p0.x.add_spec(t.mul_spec(d.x).add_spec(s.mul_spec(n.x))), q.x);
    // t·d.y + s·n.y ≡ (vdot(d,Δ)·d.y − vdot(n,Δ)·d.x) / l ≡ (l·Δ.y)/l ≡ Δ.y
    Rational::lemma_div_mul_assoc(vdot(d, delta), l, d.y);
    Rational::lemma_div_mul_assoc(vdot(n, delta), l, d.x);
    // s·n.y == s·(−d.x) == −(s·d.x) ≡ −(vdot(n,Δ)·d.x / l)
    assert(s.mul_spec(n.y) == s.mul_spec(d.x.neg_spec()));
    Rational::lemma_mul_neg_right(s, d.x);
    assert(s.mul_spec(d.x.neg_spec()) == s.mul_spec(d.x).neg_spec());
    Rational::lemma_eqv_neg_congruence(
        s.mul_spec(d.x), vdot(n, delta).mul_spec(d.x).div_spec(l));
    // (−X)/l == −(X/l) — structural through mul_neg_right
    assert(vdot(n, delta).mul_spec(d.x).neg_spec().div_spec(l)
        == vdot(n, delta).mul_spec(d.x).div_spec(l).neg_spec()) by {
        Rational::lemma_mul_neg_right(l.reciprocal_spec(), vdot(n, delta).mul_spec(d.x));
        Rational::lemma_mul_commutative(l.reciprocal_spec(), vdot(n, delta).mul_spec(d.x));
        Rational::lemma_mul_commutative(
            vdot(n, delta).mul_spec(d.x).neg_spec(), l.reciprocal_spec());
    }
    // combine
    Rational::lemma_eqv_add_congruence(
        t.mul_spec(d.y), vdot(d, delta).mul_spec(d.y).div_spec(l),
        s.mul_spec(n.y), vdot(n, delta).mul_spec(d.x).div_spec(l).neg_spec());
    Rational::lemma_div_add_numerator(
        vdot(d, delta).mul_spec(d.y),
        vdot(n, delta).mul_spec(d.x).neg_spec(), l);
    Rational::lemma_eqv_transitive(
        t.mul_spec(d.y).add_spec(s.mul_spec(n.y)),
        vdot(d, delta).mul_spec(d.y).div_spec(l).add_spec(
            vdot(n, delta).mul_spec(d.x).div_spec(l).neg_spec()),
        vdot(d, delta).mul_spec(d.y).add_spec(
            vdot(n, delta).mul_spec(d.x).neg_spec()).div_spec(l));
    // numerator ≡ l·Δ.y
    lemma_basis_decomp_scalar_y(d.x, d.y, delta.x, delta.y);
    assert(vdot(d, delta).mul_spec(d.y).add_spec(vdot(n, delta).mul_spec(d.x).neg_spec())
        == vdot(d, delta).mul_spec(d.y).sub_spec(vdot(n, delta).mul_spec(d.x)));
    assert(vdot(d, delta).mul_spec(d.y).sub_spec(vdot(n, delta).mul_spec(d.x))
        == d.x.mul_spec(delta.x).add_spec(d.y.mul_spec(delta.y)).mul_spec(d.y).sub_spec(
            d.y.mul_spec(delta.x).sub_spec(d.x.mul_spec(delta.y)).mul_spec(d.x)));
    Rational::lemma_eqv_transitive(
        vdot(d, delta).mul_spec(d.y).add_spec(vdot(n, delta).mul_spec(d.x).neg_spec()),
        vdot(d, delta).mul_spec(d.y).sub_spec(vdot(n, delta).mul_spec(d.x)),
        l.mul_spec(delta.y));
    Rational::lemma_div_congruence(
        vdot(d, delta).mul_spec(d.y).add_spec(vdot(n, delta).mul_spec(d.x).neg_spec()),
        l.mul_spec(delta.y), l);
    Rational::lemma_mul_commutative(l, delta.y);
    Rational::lemma_div_mul_cancel(delta.y, l);
    Rational::lemma_eqv_transitive(
        t.mul_spec(d.y).add_spec(s.mul_spec(n.y)),
        vdot(d, delta).mul_spec(d.y).add_spec(
            vdot(n, delta).mul_spec(d.x).neg_spec()).div_spec(l),
        l.mul_spec(delta.y).div_spec(l));
    Rational::lemma_eqv_transitive(
        t.mul_spec(d.y).add_spec(s.mul_spec(n.y)),
        l.mul_spec(delta.y).div_spec(l),
        delta.y);
    lemma_add_sub_cancel(p0.y, q.y);
    Rational::lemma_eqv_reflexive(p0.y);
    Rational::lemma_eqv_add_congruence(
        p0.y, p0.y, t.mul_spec(d.y).add_spec(s.mul_spec(n.y)), delta.y);
    assert(delta.y == q.y.sub_spec(p0.y));
    Rational::lemma_eqv_transitive(
        p0.y.add_spec(t.mul_spec(d.y).add_spec(s.mul_spec(n.y))),
        p0.y.add_spec(delta.y),
        q.y);
    Rational::lemma_eqv_symmetric(
        p0.y.add_spec(t.mul_spec(d.y).add_spec(s.mul_spec(n.y))), q.y);
}

} // verus!

verus! {

//  ── Span assembly ───────────────────────────────────────────────────

/// Congruence: component-wise eqv axes have eqv dots.
pub proof fn lemma_vdot_congruence_left(
    n1: Vec2<Rational>,
    n2: Vec2<Rational>,
    w: Vec2<Rational>,
)
    requires
        n1.x.eqv_spec(n2.x),
        n1.y.eqv_spec(n2.y),
    ensures
        vdot(n1, w).eqv_spec(vdot(n2, w)),
{
    Rational::lemma_eqv_reflexive(w.x);
    Rational::lemma_eqv_reflexive(w.y);
    Rational::lemma_eqv_mul_congruence(n1.x, n2.x, w.x, w.x);
    Rational::lemma_eqv_mul_congruence(n1.y, n2.y, w.y, w.y);
    Rational::lemma_eqv_add_congruence(
        n1.x.mul_spec(w.x), n2.x.mul_spec(w.x),
        n1.y.mul_spec(w.y), n2.y.mul_spec(w.y));
}

/// Bridge: axis_sep with a canonical-sub model axis ≡ raw vsub axis.
pub proof fn lemma_axis_sep_canonical_sub_axis(
    d: Vec2<Rational>,
    p0: Vec2<Rational>,
    p1: Vec2<Rational>,
    base: Vec2<Rational>,
    q: Vec2<Rational>,
)
    requires
        d.x == p1.x.sub_spec(p0.x).canonical(),
        d.y == p1.y.sub_spec(p0.y).canonical(),
    ensures
        axis_sep(d, base, q).eqv_spec(axis_sep(vsub(p1, p0), base, q)),
{
    Rational::lemma_canonical_exists(p1.x.sub_spec(p0.x));
    Rational::lemma_canonical_exists(p1.y.sub_spec(p0.y));
    lemma_vdot_congruence_left(d, vsub(p1, p0), vsub(q, base));
    // axis_sep(n, base, q) == vdot(n, vsub(q, base)) — structural.
}

/// The full span claim: a point between the two side half-planes of the
/// reference edge decomposes over the edge basis with t ∈ [0, 1].
pub proof fn lemma_manifold_point_span(
    p0: Vec2<Rational>,
    p1: Vec2<Rational>,
    q: Vec2<Rational>,
)
    requires
        !vdot(vsub(p1, p0), vsub(p1, p0)).eqv_spec(Rational::from_int_spec(0)),
        Rational::from_int_spec(0).le_spec(axis_sep(vsub(p1, p0), p0, q)),
        axis_sep(vsub(p1, p0), p1, q).le_spec(Rational::from_int_spec(0)),
    ensures
        crate::narrowphase::on_face_span(p0, p1, edge_normal(p0, p1), q),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    let d = vsub(p1, p0);
    let l = vdot(d, d);
    let delta = vsub(q, p0);
    let t = vdot(d, delta).div_spec(l);
    // l > 0 from nonzero + square nonnegativity
    Rational::lemma_square_le_nonneg(d.x);
    Rational::lemma_square_le_nonneg(d.y);
    Rational::lemma_eqv_reflexive(zero);
    Rational::lemma_le_add_both(
        zero, d.x.mul_spec(d.x), zero, d.y.mul_spec(d.y));
    Rational::lemma_add_zero_identity(zero);
    crate::proofs::shape::lemma_le_eqv_subst_left(zero.add_spec(zero), zero, l);
    Rational::lemma_trichotomy(zero, l);
    // t ≥ 0: axis_sep(d, p0, q) == vdot(d, delta) structural
    assert(axis_sep(d, p0, q) == vdot(d, delta));
    Rational::lemma_div_le_monotone(zero, vdot(d, delta), l);
    Rational::lemma_mul_zero(l.reciprocal_spec());
    assert(zero.div_spec(l) == zero.mul_spec(l.reciprocal_spec()));
    crate::proofs::shape::lemma_le_eqv_subst_left(zero.div_spec(l), zero, t);
    // t ≤ 1: vdot(d, delta) ≤ l
    lemma_axis_sep_between(d, p0, p1, q);
    assert(axis_sep(d, p0, p1) == l);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        axis_sep(d, p1, q), axis_sep(d, p0, q).sub_spec(l), zero);
    Rational::lemma_le_add_monotone(axis_sep(d, p0, q).sub_spec(l), zero, l);
    lemma_add_sub_cancel(l, axis_sep(d, p0, q));
    Rational::lemma_add_commutative(axis_sep(d, p0, q).sub_spec(l), l);
    Rational::lemma_eqv_transitive(
        axis_sep(d, p0, q).sub_spec(l).add_spec(l),
        l.add_spec(axis_sep(d, p0, q).sub_spec(l)),
        axis_sep(d, p0, q));
    Rational::lemma_add_zero_identity(l);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        axis_sep(d, p0, q).sub_spec(l).add_spec(l), axis_sep(d, p0, q), l);
    // axis_sep(d, p0, q) == vdot(d, delta) structural
    Rational::lemma_div_le_monotone(vdot(d, delta), l, l);
    Rational::lemma_div_self(l);
    crate::proofs::shape::lemma_le_eqv_subst_right(t, l.div_spec(l), one);
    // decomposition + assemble
    lemma_basis_decomposition(p0, p1, q);
    assert(crate::narrowphase::on_face_span(p0, p1, edge_normal(p0, p1), q));
}

} // verus!

verus! {

/// Assemble the on_face_span fact for a final manifold point from the
/// two model-axis clip facts (canonical-sub axis model).
pub proof fn lemma_manifold_final_span(
    dm: Vec2<Rational>,
    p0m: Vec2<Rational>,
    p1m: Vec2<Rational>,
    q: Vec2<Rational>,
)
    requires
        dm.x == p1m.x.sub_spec(p0m.x).canonical(),
        dm.y == p1m.y.sub_spec(p0m.y).canonical(),
        !vdot(vsub(p1m, p0m), vsub(p1m, p0m)).eqv_spec(Rational::from_int_spec(0)),
        Rational::from_int_spec(0).le_spec(axis_sep(dm, p0m, q)),
        Rational::from_int_spec(0).le_spec(axis_sep(dm.neg(), p1m, q)),
    ensures
        crate::narrowphase::on_face_span(p0m, p1m, edge_normal(p0m, p1m), q),
{
    let zero = Rational::from_int_spec(0);
    // bridge the model axis to the raw vsub form
    lemma_axis_sep_canonical_sub_axis(dm, p0m, p1m, p0m, q);
    crate::proofs::shape::lemma_le_eqv_subst_right(
        zero, axis_sep(dm, p0m, q), axis_sep(vsub(p1m, p0m), p0m, q));
    // 0 ≤ axis_sep(−d, p1, q) ≡ −axis_sep(d, p1, q) → axis_sep(d, p1, q) ≤ 0
    lemma_axis_sep_neg_left(dm, p1m, q);
    Rational::lemma_neg_reverses_le(zero, axis_sep(dm.neg(), p1m, q));
    Rational::lemma_eqv_neg_congruence(
        axis_sep(dm.neg(), p1m, q), axis_sep(dm, p1m, q).neg_spec());
    assert(axis_sep(dm, p1m, q).neg_spec().neg_spec() == axis_sep(dm, p1m, q));
    assert(zero.neg_spec() == zero);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        axis_sep(dm.neg(), p1m, q).neg_spec(), axis_sep(dm, p1m, q), zero);
    // bridge the second axis fact
    lemma_axis_sep_canonical_sub_axis(dm, p0m, p1m, p1m, q);
    crate::proofs::shape::lemma_le_eqv_subst_left(
        axis_sep(dm, p1m, q), axis_sep(vsub(p1m, p0m), p1m, q), zero);
    lemma_manifold_point_span(p0m, p1m, q);
}

} // verus!
