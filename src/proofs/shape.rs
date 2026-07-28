//! Lemmas about orient, edge normals, and axis separations (phys-04).
//!
//! Key relations:
//!  - dot(n, q − p) with outward normal n of edge a→b equals −orient(a, b, q)
//!    (so "owner vertices on the inner side" is exactly the convexity
//!    invariant),
//!  - min over a vertex sequence is a lower bound attained at some index.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::shape::{axis_sep, convex_poly_inv, edge_normal, orient, vsub};

verus! {

/// dot(n, p − p) ≡ 0: the self-distance vanishes.
pub proof fn lemma_axis_sep_self_zero(n: Vec2<Rational>, p: Vec2<Rational>)
    ensures
        axis_sep(n, p, p).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    let s = axis_sep(n, p, p);
    let dx = p.x.sub_spec(p.x);
    let dy = p.y.sub_spec(p.y);
    let t1 = n.x.mul_spec(dx);
    let t2 = n.y.mul_spec(dy);
    Rational::lemma_denom_positive(s);
    assert(dx.num == p.x.num * (p.x.denom_nat() as int)
        + (-p.x.num) * (p.x.denom_nat() as int));
    assert(dy.num == p.y.num * (p.y.denom_nat() as int)
        + (-p.y.num) * (p.y.denom_nat() as int));
    assert((dx.num == p.x.num * (p.x.denom_nat() as int)
            + (-p.x.num) * (p.x.denom_nat() as int))
        ==> dx.num == 0) by (nonlinear_arith);
    assert((dy.num == p.y.num * (p.y.denom_nat() as int)
            + (-p.y.num) * (p.y.denom_nat() as int))
        ==> dy.num == 0) by (nonlinear_arith);
    assert(t1.num == n.x.num * dx.num);
    assert(t2.num == n.y.num * dy.num);
    assert((t1.num == n.x.num * dx.num && dx.num == 0)
        ==> t1.num == 0) by (nonlinear_arith);
    assert((t2.num == n.y.num * dy.num && dy.num == 0)
        ==> t2.num == 0) by (nonlinear_arith);
    assert(s == t1.add_spec(t2));
    assert(s.num == t1.num * (t2.denom_nat() as int)
        + t2.num * (t1.denom_nat() as int));
    assert((s.num == t1.num * (t2.denom_nat() as int)
            + t2.num * (t1.denom_nat() as int)
        && t1.num == 0 && t2.num == 0)
        ==> s.num == 0) by (nonlinear_arith);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(s.eqv_spec(z));
}

/// orient degenerates at the edge endpoints: orient(a, b, a) ≡ 0.
pub proof fn lemma_orient_left_endpoint_zero(a: Vec2<Rational>, b: Vec2<Rational>)
    ensures
        orient(a, b, a).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    lemma_axis_sep_eq_neg_orient(a, b, a);
    lemma_axis_sep_self_zero(edge_normal(a, b), a);
    // orient(a,b,a).neg ≡ 0 ⟹ orient(a,b,a) ≡ 0 (neg is structural involution)
    let o = orient(a, b, a);
    assert(o.neg_spec().neg_spec() == o);
    assert(z.neg_spec() == z);
    Rational::lemma_eqv_symmetric(axis_sep(edge_normal(a, b), a, a), o.neg_spec());
    Rational::lemma_eqv_transitive(o.neg_spec(), axis_sep(edge_normal(a, b), a, a), z);
    Rational::lemma_eqv_symmetric(o.neg_spec(), z);
    Rational::lemma_eqv_reflexive(o);
    assert(o.eqv_spec(z));
}

/// orient degenerates at the edge endpoints: orient(a, b, b) ≡ 0.
pub proof fn lemma_orient_right_endpoint_zero(a: Vec2<Rational>, b: Vec2<Rational>)
    ensures
        orient(a, b, b).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    lemma_axis_sep_eq_neg_orient(a, b, b);
    lemma_axis_sep_self_zero(edge_normal(a, b), a);
    // orient(a,b,b).neg ≡ axis_sep(n, a, b) ≡ 0? NO — axis_sep(n, a, b) is
    // NOT self-distance. Direct: orient(a,b,b) = cross(b−a, b−a) ≡ 0 since
    // the two factors are identical.
    let o = orient(a, b, b);
    let u = vsub(b, a);
    assert(o == u.x.mul_spec(u.y).sub_spec(u.y.mul_spec(u.x)));
    // t1 − t2 with t1 == t2 structurally: t1 ≡ t2 ⟹ sub ≡ 0
    Rational::lemma_eqv_reflexive(u.x.mul_spec(u.y));
    Rational::lemma_eqv_reflexive(u.y.mul_spec(u.x));
    Rational::lemma_mul_commutative(u.x, u.y);
    assert(u.x.mul_spec(u.y) == u.y.mul_spec(u.x));
    Rational::lemma_sub_eqv_zero_iff_eqv(u.x.mul_spec(u.y), u.y.mul_spec(u.x));
    assert(o.eqv_spec(z));
}

/// dot(outward-normal(a→b), q − a) ≡ −orient(a, b, q).
///
/// The whole identity is STRUCTURAL on Rational: neg distributes over sub
/// and mul with no canonicalization, so no NLA is needed.
pub proof fn lemma_axis_sep_eq_neg_orient(
    a: Vec2<Rational>, b: Vec2<Rational>, q: Vec2<Rational>,
)
    ensures
        axis_sep(edge_normal(a, b), a, q).eqv_spec(orient(a, b, q).neg_spec()),
{
    let n = edge_normal(a, b);
    let s = axis_sep(n, a, q);
    let o = orient(a, b, q);
    let dx = vsub(q, a).x;
    let dy = vsub(q, a).y;
    let ux = vsub(b, a).x;
    let uy = vsub(b, a).y;
    // n.x == uy and n.y == −ux, both structural
    assert(n.x == uy);
    assert(n.y == a.x.sub_spec(b.x));
    assert(n.y.num == a.x.num * (b.x.denom_nat() as int)
        + (-b.x.num) * (a.x.denom_nat() as int));
    assert(n.y.den == a.x.den * b.x.den + a.x.den + b.x.den);
    assert(ux.neg_spec().num == -ux.num);
    assert(ux.neg_spec().den == ux.den);
    assert(ux.num == b.x.num * (a.x.denom_nat() as int)
        + (-a.x.num) * (b.x.denom_nat() as int));
    assert(ux.den == b.x.den * a.x.den + b.x.den + a.x.den);
    assert((n.y.num == a.x.num * (b.x.denom_nat() as int)
            + (-b.x.num) * (a.x.denom_nat() as int)
        && ux.neg_spec().num == -ux.num
        && ux.num == b.x.num * (a.x.denom_nat() as int)
            + (-a.x.num) * (b.x.denom_nat() as int)
        && n.y.den == a.x.den * b.x.den + a.x.den + b.x.den
        && ux.neg_spec().den == ux.den
        && ux.den == b.x.den * a.x.den + b.x.den + a.x.den)
        ==> n.y.num == ux.neg_spec().num && n.y.den == ux.neg_spec().den)
        by (nonlinear_arith);
    assert(n.y == ux.neg_spec());
    assert(n.y == vsub(a, b).x);
    assert(ux.neg_spec() == vsub(a, b).x);
    // t1 == uy·dx (structural); t2 == −(ux·dy) (structural)
    let t1 = n.x.mul_spec(dx);
    let t2 = n.y.mul_spec(dy);
    let u1 = ux.mul_spec(dy);
    let u2 = uy.mul_spec(dx);
    assert(t1 == u2);
    assert(t2 == ux.neg_spec().mul_spec(dy));
    assert(ux.neg_spec().num == -ux.num);
    assert(ux.neg_spec().den == ux.den);
    assert(ux.neg_spec().mul_spec(dy).num == ux.neg_spec().num * dy.num);
    assert(ux.neg_spec().mul_spec(dy).den
        == ux.neg_spec().den * dy.den + ux.neg_spec().den + dy.den);
    assert(u1.num == ux.num * dy.num);
    assert(u1.den == ux.den * dy.den + ux.den + dy.den);
    assert((ux.neg_spec().mul_spec(dy).num == ux.neg_spec().num * dy.num
        && ux.neg_spec().num == -ux.num && u1.num == ux.num * dy.num)
        ==> ux.neg_spec().mul_spec(dy).num == -u1.num) by (nonlinear_arith);
    assert((ux.neg_spec().mul_spec(dy).den
            == ux.neg_spec().den * dy.den + ux.neg_spec().den + dy.den
        && ux.neg_spec().den == ux.den
        && u1.den == ux.den * dy.den + ux.den + dy.den)
        ==> ux.neg_spec().mul_spec(dy).den == u1.den) by (nonlinear_arith);
    assert(ux.neg_spec().mul_spec(dy) == u1.neg_spec());
    assert(t2 == u1.neg_spec());
    // s == u2 + (−u1) == −(u1 − u2) == −o (all structural)
    assert(s == t1.add_spec(t2));
    assert(s == u2.add_spec(u1.neg_spec()));
    assert(u2.add_spec(u1.neg_spec()) == u2.sub_spec(u1));
    assert(u2.sub_spec(u1).num == u2.num * (u1.denom_nat() as int)
        + (-u1.num) * (u2.denom_nat() as int));
    assert(u1.sub_spec(u2).neg_spec().num == -u1.sub_spec(u2).num);
    assert(u1.sub_spec(u2).num == u1.num * (u2.denom_nat() as int)
        + (-u2.num) * (u1.denom_nat() as int));
    assert(u2.sub_spec(u1).den == u2.den * u1.den + u2.den + u1.den);
    assert(u1.sub_spec(u2).neg_spec().den == u1.sub_spec(u2).den);
    assert(u1.sub_spec(u2).den == u1.den * u2.den + u1.den + u2.den);
    assert((u2.sub_spec(u1).num == u2.num * (u1.denom_nat() as int)
            + (-u1.num) * (u2.denom_nat() as int)
        && u1.sub_spec(u2).neg_spec().num == -u1.sub_spec(u2).num
        && u1.sub_spec(u2).num == u1.num * (u2.denom_nat() as int)
            + (-u2.num) * (u1.denom_nat() as int)
        && u2.sub_spec(u1).den == u2.den * u1.den + u2.den + u1.den
        && u1.sub_spec(u2).neg_spec().den == u1.sub_spec(u2).den
        && u1.sub_spec(u2).den == u1.den * u2.den + u1.den + u2.den)
        ==> u2.sub_spec(u1).num == u1.sub_spec(u2).neg_spec().num
            && u2.sub_spec(u1).den == u1.sub_spec(u2).neg_spec().den)
        by (nonlinear_arith);
    assert(u2.sub_spec(u1) == u1.sub_spec(u2).neg_spec());
    assert(o == u1.sub_spec(u2));
    assert(s == o.neg_spec());
    Rational::lemma_eqv_reflexive(s);
}

/// le with eqv substituted on the left: a₁ ≤ b ∧ a₁ ≡ a₂ ⟹ a₂ ≤ b.
pub proof fn lemma_le_eqv_subst_left(a1: Rational, a2: Rational, b: Rational)
    requires
        a1.le_spec(b),
        a1.eqv_spec(a2),
    ensures
        a2.le_spec(b),
{
    Rational::lemma_denom_positive(a1);
    Rational::lemma_denom_positive(a2);
    Rational::lemma_denom_positive(b);
    assert(a1.le_spec(b) == (a1.num * b.denom() <= b.num * a1.denom()));
    assert(a1.eqv_spec(a2) == (a1.num * a2.denom() == a2.num * a1.denom()));
    assert(a2.le_spec(b) == (a2.num * b.denom() <= b.num * a2.denom()));
    assert((a1.denom() >= 1 && a2.denom() >= 1 && b.denom() >= 1
        && a1.num * b.denom() <= b.num * a1.denom()
        && a1.num * a2.denom() == a2.num * a1.denom())
        ==> a2.num * b.denom() <= b.num * a2.denom()) by (nonlinear_arith);
}

/// le with eqv substituted on the right: a ≤ b₁ ∧ b₁ ≡ b₂ ⟹ a ≤ b₂.
pub proof fn lemma_le_eqv_subst_right(a: Rational, b1: Rational, b2: Rational)
    requires
        a.le_spec(b1),
        b1.eqv_spec(b2),
    ensures
        a.le_spec(b2),
{
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(b1);
    Rational::lemma_denom_positive(b2);
    assert(a.le_spec(b1) == (a.num * b1.denom() <= b1.num * a.denom()));
    assert(b1.eqv_spec(b2) == (b1.num * b2.denom() == b2.num * b1.denom()));
    assert(a.le_spec(b2) == (a.num * b2.denom() <= b2.num * a.denom()));
    assert((a.denom() >= 1 && b1.denom() >= 1 && b2.denom() >= 1
        && a.num * b1.denom() <= b1.num * a.denom()
        && b1.num * b2.denom() == b2.num * b1.denom())
        ==> a.num * b2.denom() <= b2.num * a.denom()) by (nonlinear_arith);
}

/// lt with eqv substituted on the right: a < b ∧ b ≡ c ⟹ a < c.
pub proof fn lemma_lt_eqv_subst_right(a: Rational, b: Rational, c: Rational)
    requires
        a.lt_spec(b),
        b.eqv_spec(c),
    ensures
        a.lt_spec(c),
{
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(b);
    Rational::lemma_denom_positive(c);
    assert(a.lt_spec(b) == (a.num * b.denom() < b.num * a.denom()));
    assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
    assert(a.lt_spec(c) == (a.num * c.denom() < c.num * a.denom()));
    assert((a.denom() >= 1 && b.denom() >= 1 && c.denom() >= 1
        && a.num * b.denom() < b.num * a.denom()
        && b.num * c.denom() == c.num * b.denom())
        ==> a.num * c.denom() < c.num * a.denom()) by (nonlinear_arith);
}

/// min over the tail qs[i..] is a lower bound for every element it spans.
pub proof fn lemma_min_sep_le_all(
    n: Vec2<Rational>, p: Vec2<Rational>, qs: Seq<Vec2<Rational>>, i: int, j: int,
)
    requires
        0 <= i <= j < qs.len(),
    ensures
        crate::shape::min_sep(n, p, qs, i).le_spec(crate::shape::axis_sep(n, p, qs[j])),
    decreases qs.len() - i,
{
    use crate::shape::{axis_sep, min_sep};
    if i < qs.len() - 1 {
        assert(min_sep(n, p, qs, i)
            == Rational::min_spec(axis_sep(n, p, qs[i]), min_sep(n, p, qs, i + 1))) by {
            reveal_with_fuel(min_sep, 2);
        }
        lemma_min_le_left(axis_sep(n, p, qs[i]), min_sep(n, p, qs, i + 1));
        lemma_min_le_right(axis_sep(n, p, qs[i]), min_sep(n, p, qs, i + 1));
        if j == i {
            Rational::lemma_le_transitive(
                min_sep(n, p, qs, i), axis_sep(n, p, qs[i]), axis_sep(n, p, qs[j]));
        } else {
            lemma_min_sep_le_all(n, p, qs, i + 1, j);
            Rational::lemma_le_transitive(
                min_sep(n, p, qs, i), min_sep(n, p, qs, i + 1), axis_sep(n, p, qs[j]));
        }
    } else {
        assert(i == qs.len() - 1);
        assert(j == i);
        assert(min_sep(n, p, qs, i) == axis_sep(n, p, qs[j])) by {
            reveal_with_fuel(min_sep, 2);
        }
        Rational::lemma_eqv_implies_le(min_sep(n, p, qs, i), axis_sep(n, p, qs[j]));
    }
}

/// min over the tail is ATTAINED at some index (witness existence).
pub proof fn lemma_min_sep_attained(
    n: Vec2<Rational>, p: Vec2<Rational>, qs: Seq<Vec2<Rational>>, i: int,
)
    requires
        0 <= i < qs.len(),
    ensures
        exists|j: int|
            i <= j < qs.len()
                && crate::shape::min_sep(n, p, qs, i) == crate::shape::axis_sep(n, p, qs[j]),
    decreases qs.len() - i,
{
    use crate::shape::{axis_sep, min_sep};
    if i < qs.len() - 1 {
        lemma_min_sep_attained(n, p, qs, i + 1);
        let a = axis_sep(n, p, qs[i]);
        let b = min_sep(n, p, qs, i + 1);
        if a.le_spec(b) {
            assert(min_sep(n, p, qs, i) == a);
            assert(min_sep(n, p, qs, i) == axis_sep(n, p, qs[i]));
        } else {
            assert(min_sep(n, p, qs, i) == b);
        }
    } else {
        assert(min_sep(n, p, qs, i) == axis_sep(n, p, qs[i]));
    }
}

/// min_spec(x, y) ≤ x.
pub proof fn lemma_min_le_left(x: Rational, y: Rational)
    ensures
        Rational::min_spec(x, y).le_spec(x),
{
    if x.le_spec(y) {
        assert(Rational::min_spec(x, y) == x);
        Rational::lemma_eqv_implies_le(x, x);
    } else {
        assert(Rational::min_spec(x, y) == y);
        Rational::lemma_le_iff_lt_or_eqv(y, x);
        Rational::lemma_lt_implies_le(y, x);
    }
}

/// min_spec(x, y) ≤ y.
pub proof fn lemma_min_le_right(x: Rational, y: Rational)
    ensures
        Rational::min_spec(x, y).le_spec(y),
{
    if x.le_spec(y) {
        assert(Rational::min_spec(x, y) == x);
        Rational::lemma_eqv_implies_le(x, x);
        Rational::lemma_le_transitive(Rational::min_spec(x, y), x, y);
    } else {
        assert(Rational::min_spec(x, y) == y);
        Rational::lemma_eqv_implies_le(y, y);
    }
}

/// Strict positivity of a min lifts to every element.
pub proof fn lemma_min_pos_all(
    n: Vec2<Rational>, p: Vec2<Rational>, qs: Seq<Vec2<Rational>>, j: int,
)
    requires
        0 <= j < qs.len(),
        Rational::from_int_spec(0).lt_spec(crate::shape::min_sep(n, p, qs, 0)),
    ensures
        Rational::from_int_spec(0).lt_spec(crate::shape::axis_sep(n, p, qs[j])),
{
    lemma_min_sep_le_all(n, p, qs, 0, j);
    Rational::lemma_lt_le_transitive(
        Rational::from_int_spec(0),
        crate::shape::min_sep(n, p, qs, 0),
        crate::shape::axis_sep(n, p, qs[j]));
}

/// Translation cancels in differences: (a + t) − (b + t) ≡ a − b (per
/// coordinate; one cross-multiplied identity).
pub proof fn lemma_sub_spec_translation(
    a: Rational, b: Rational, t: Rational,
)
    ensures
        a.add_spec(t).sub_spec(b.add_spec(t)).eqv_spec(a.sub_spec(b)),
{
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(b);
    Rational::lemma_denom_positive(t);
    Rational::lemma_add_denom_product_int(a, t);
    Rational::lemma_add_denom_product_int(b, t);
    let l = a.add_spec(t).sub_spec(b.add_spec(t));
    let r = a.sub_spec(b);
    Rational::lemma_add_denom_product_int(a.add_spec(t), b.add_spec(t).neg_spec());
    Rational::lemma_add_denom_product_int(a, b.neg_spec());
    assert(l.num == (a.num * t.denom() + t.num * a.denom()) * (b.denom() * t.denom())
        + (-(b.num * t.denom() + t.num * b.denom())) * (a.denom() * t.denom()));
    assert(l.denom() == (a.denom() * t.denom()) * (b.denom() * t.denom()));
    assert(r.num == a.num * b.denom() + (-b.num) * a.denom());
    assert(r.denom() == a.denom() * b.denom());
    // decomposed into small NLA steps (mega-implication rlimits)
    assert(((a.num * t.denom() + t.num * a.denom()) * (b.denom() * t.denom())
        == (a.num * b.denom()) * (t.denom() * t.denom())
            + (t.num * a.denom() * b.denom()) * t.denom())) by (nonlinear_arith);
    assert(((b.num * t.denom() + t.num * b.denom()) * (a.denom() * t.denom())
        == (b.num * a.denom()) * (t.denom() * t.denom())
            + (t.num * a.denom() * b.denom()) * t.denom())) by (nonlinear_arith);
    let ghost dd = a.num * b.denom() + (-b.num) * a.denom();
    let ghost X1 = (a.num * t.denom() + t.num * a.denom()) * (b.denom() * t.denom());
    let ghost X2 = (b.num * t.denom() + t.num * b.denom()) * (a.denom() * t.denom());
    assert(l.num == X1 + (-(b.num * t.denom() + t.num * b.denom())) * (a.denom() * t.denom()));
    assert((X2 == (b.num * t.denom() + t.num * b.denom()) * (a.denom() * t.denom()))
        ==> X2 + (-(b.num * t.denom() + t.num * b.denom())) * (a.denom() * t.denom()) == 0)
        by (nonlinear_arith);
    assert(l.num == X1 - X2);
    assert((X1 == (a.num * b.denom()) * (t.denom() * t.denom())
            + (t.num * a.denom() * b.denom()) * t.denom()
        && X2 == (b.num * a.denom()) * (t.denom() * t.denom())
            + (t.num * a.denom() * b.denom()) * t.denom()
        && dd == a.num * b.denom() + (-b.num) * a.denom()
        && l.num == X1 - X2)
        ==> l.num == (t.denom() * t.denom()) * dd) by (nonlinear_arith);
    assert(l.num == (t.denom() * t.denom()) * dd);
    assert((l.denom() == (a.denom() * t.denom()) * (b.denom() * t.denom())
        && r.denom() == a.denom() * b.denom()
        && l.num == (t.denom() * t.denom()) * dd
        && r.num == dd)
        ==> l.num * r.denom() == r.num * l.denom()) by (nonlinear_arith);
    assert(l.eqv_spec(r));
}

/// orient is translation-invariant.
pub proof fn lemma_orient_translation(
    a: Vec2<Rational>, b: Vec2<Rational>, c: Vec2<Rational>, t: Vec2<Rational>,
)
    ensures
        orient(
            Vec2 { x: a.x.add_spec(t.x), y: a.y.add_spec(t.y) },
            Vec2 { x: b.x.add_spec(t.x), y: b.y.add_spec(t.y) },
            Vec2 { x: c.x.add_spec(t.x), y: c.y.add_spec(t.y) })
            .eqv_spec(orient(a, b, c)),
{
    let a2 = Vec2 { x: a.x.add_spec(t.x), y: a.y.add_spec(t.y) };
    let b2 = Vec2 { x: b.x.add_spec(t.x), y: b.y.add_spec(t.y) };
    let c2 = Vec2 { x: c.x.add_spec(t.x), y: c.y.add_spec(t.y) };
    lemma_sub_spec_translation(b.x, a.x, t.x);
    lemma_sub_spec_translation(b.y, a.y, t.y);
    lemma_sub_spec_translation(c.x, a.x, t.x);
    lemma_sub_spec_translation(c.y, a.y, t.y);
    assert(vsub(b2, a2).x.eqv_spec(vsub(b, a).x));
    assert(vsub(b2, a2).y.eqv_spec(vsub(b, a).y));
    assert(vsub(c2, a2).x.eqv_spec(vsub(c, a).x));
    assert(vsub(c2, a2).y.eqv_spec(vsub(c, a).y));
    Rational::lemma_eqv_mul_congruence(
        vsub(b2, a2).x, vsub(b, a).x, vsub(c2, a2).y, vsub(c, a).y);
    Rational::lemma_eqv_mul_congruence(
        vsub(b2, a2).y, vsub(b, a).y, vsub(c2, a2).x, vsub(c, a).x);
    Rational::lemma_eqv_sub_congruence(
        vsub(b2, a2).x.mul_spec(vsub(c2, a2).y),
        vsub(b, a).x.mul_spec(vsub(c, a).y),
        vsub(b2, a2).y.mul_spec(vsub(c2, a2).x),
        vsub(b, a).y.mul_spec(vsub(c, a).x));
}

/// Translation preserves the global convexity invariant.
pub proof fn lemma_convex_translation(vs: Seq<Vec2<Rational>>, t: Vec2<Rational>)
    requires
        convex_poly_inv(vs),
    ensures
        convex_poly_inv(vs.map(|_i: int, v: Vec2<Rational>|
            Vec2 { x: v.x.add_spec(t.x), y: v.y.add_spec(t.y) })),
{
    let ws = vs.map(|_i: int, v: Vec2<Rational>|
        Vec2 { x: v.x.add_spec(t.x), y: v.y.add_spec(t.y) });
    assert(ws.len() == vs.len());
    assert forall|i: int, j: int|
        (0 <= i < ws.len() && 0 <= j < ws.len() && j != i && j != (i + 1) % (ws.len() as int))
        implies Rational::from_int_spec(0).lt_spec(
            #[trigger] orient(ws[i], ws[(i + 1) % (ws.len() as int)], ws[j]))
    by {
        lemma_orient_translation(
            vs[i], vs[(i + 1) % (vs.len() as int)], vs[j], t);
        assert(orient(ws[i], ws[(i + 1) % (ws.len() as int)], ws[j]).eqv_spec(
            orient(vs[i], vs[(i + 1) % (vs.len() as int)], vs[j])));
        assert(Rational::from_int_spec(0).lt_spec(
            orient(vs[i], vs[(i + 1) % (vs.len() as int)], vs[j])));
        lemma_lt_eqv_subst_right(
            Rational::from_int_spec(0),
            orient(vs[i], vs[(i + 1) % (vs.len() as int)], vs[j]),
            orient(ws[i], ws[(i + 1) % (ws.len() as int)], ws[j]));
    }
    assert(convex_poly_inv(ws));
}

} // verus!
