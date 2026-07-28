//! Broadphase lemmas (phys-05b): coordinate fold bounds and the
//! range-disjointness ⇒ pointwise-separation soundness lemma.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::broadphase::{x_max_upto, x_min_upto, y_max_upto, y_min_upto};

verus! {

// ── min/max raw micro-lemmas ─────────────────────────────────────────

/// y ≤ x ⇒ min(x, y) ≡ y.
pub proof fn lemma_min_eqv_right(x: Rational, y: Rational)
    requires
        y.le_spec(x),
    ensures
        Rational::min_spec(x, y).eqv_spec(y),
{
    if x.le_spec(y) {
        Rational::lemma_le_antisymmetric(x, y);
        assert(Rational::min_spec(x, y) == x);
        Rational::lemma_eqv_symmetric(x, y);
    } else {
        assert(Rational::min_spec(x, y) == y);
        Rational::lemma_eqv_reflexive(y);
    }
}

/// y ≤ x ⇒ max(x, y) ≡ x.
pub proof fn lemma_max_eqv_left(x: Rational, y: Rational)
    requires
        y.le_spec(x),
    ensures
        Rational::max_spec(x, y).eqv_spec(x),
{
    if x.le_spec(y) {
        Rational::lemma_le_antisymmetric(x, y);
        assert(Rational::max_spec(x, y) == y);
    } else {
        assert(Rational::max_spec(x, y) == x);
        Rational::lemma_eqv_reflexive(x);
    }
}

// ── fold bounds ──────────────────────────────────────────────────────

/// The x-min fold bounds every vertex in its range from below.
pub proof fn lemma_x_min_le_all(vs: Seq<Vec2<Rational>>, i: int, j: int)
    requires
        1 <= i <= vs.len(),
        0 <= j < i,
    ensures
        x_min_upto(vs, i).le_spec(vs[j].x),
    decreases i
{
    if i == 1 {
        assert(j == 0);
        assert(x_min_upto(vs, 1) == vs[0].x) by { reveal_with_fuel(x_min_upto, 2); }
        Rational::lemma_eqv_implies_le(x_min_upto(vs, 1), vs[j].x);
    } else {
        assert(x_min_upto(vs, i) == Rational::min_spec(x_min_upto(vs, i - 1), vs[i - 1].x))
            by { reveal_with_fuel(x_min_upto, 2); }
        crate::proofs::shape::lemma_min_le_left(x_min_upto(vs, i - 1), vs[i - 1].x);
        crate::proofs::shape::lemma_min_le_right(x_min_upto(vs, i - 1), vs[i - 1].x);
        if j == i - 1 {
        } else {
            lemma_x_min_le_all(vs, i - 1, j);
            Rational::lemma_le_transitive(
                x_min_upto(vs, i), x_min_upto(vs, i - 1), vs[j].x);
        }
    }
}

/// The x-max fold bounds every vertex in its range from above.
pub proof fn lemma_x_max_ge_all(vs: Seq<Vec2<Rational>>, i: int, j: int)
    requires
        1 <= i <= vs.len(),
        0 <= j < i,
    ensures
        vs[j].x.le_spec(x_max_upto(vs, i)),
    decreases i
{
    if i == 1 {
        assert(j == 0);
        assert(x_max_upto(vs, 1) == vs[0].x) by { reveal_with_fuel(x_max_upto, 2); }
        Rational::lemma_eqv_implies_le(vs[j].x, x_max_upto(vs, 1));
    } else {
        assert(x_max_upto(vs, i) == Rational::max_spec(x_max_upto(vs, i - 1), vs[i - 1].x))
            by { reveal_with_fuel(x_max_upto, 2); }
        lemma_max_ge_left(x_max_upto(vs, i - 1), vs[i - 1].x);
        lemma_max_ge_right(x_max_upto(vs, i - 1), vs[i - 1].x);
        if j == i - 1 {
        } else {
            lemma_x_max_ge_all(vs, i - 1, j);
            Rational::lemma_le_transitive(
                vs[j].x, x_max_upto(vs, i - 1), x_max_upto(vs, i));
        }
    }
}

/// The y-min fold bounds every vertex in its range from below.
pub proof fn lemma_y_min_le_all(vs: Seq<Vec2<Rational>>, i: int, j: int)
    requires
        1 <= i <= vs.len(),
        0 <= j < i,
    ensures
        y_min_upto(vs, i).le_spec(vs[j].y),
    decreases i
{
    if i == 1 {
        assert(j == 0);
        assert(y_min_upto(vs, 1) == vs[0].y) by { reveal_with_fuel(y_min_upto, 2); }
        Rational::lemma_eqv_implies_le(y_min_upto(vs, 1), vs[j].y);
    } else {
        assert(y_min_upto(vs, i) == Rational::min_spec(y_min_upto(vs, i - 1), vs[i - 1].y))
            by { reveal_with_fuel(y_min_upto, 2); }
        crate::proofs::shape::lemma_min_le_left(y_min_upto(vs, i - 1), vs[i - 1].y);
        crate::proofs::shape::lemma_min_le_right(y_min_upto(vs, i - 1), vs[i - 1].y);
        if j == i - 1 {
        } else {
            lemma_y_min_le_all(vs, i - 1, j);
            Rational::lemma_le_transitive(
                y_min_upto(vs, i), y_min_upto(vs, i - 1), vs[j].y);
        }
    }
}

/// The y-max fold bounds every vertex in its range from above.
pub proof fn lemma_y_max_ge_all(vs: Seq<Vec2<Rational>>, i: int, j: int)
    requires
        1 <= i <= vs.len(),
        0 <= j < i,
    ensures
        vs[j].y.le_spec(y_max_upto(vs, i)),
    decreases i
{
    if i == 1 {
        assert(j == 0);
        assert(y_max_upto(vs, 1) == vs[0].y) by { reveal_with_fuel(y_max_upto, 2); }
        Rational::lemma_eqv_implies_le(vs[j].y, y_max_upto(vs, 1));
    } else {
        assert(y_max_upto(vs, i) == Rational::max_spec(y_max_upto(vs, i - 1), vs[i - 1].y))
            by { reveal_with_fuel(y_max_upto, 2); }
        lemma_max_ge_left(y_max_upto(vs, i - 1), vs[i - 1].y);
        lemma_max_ge_right(y_max_upto(vs, i - 1), vs[i - 1].y);
        if j == i - 1 {
        } else {
            lemma_y_max_ge_all(vs, i - 1, j);
            Rational::lemma_le_transitive(
                vs[j].y, y_max_upto(vs, i - 1), y_max_upto(vs, i));
        }
    }
}

/// max_spec(x, y) ≥ x.
pub proof fn lemma_max_ge_left(x: Rational, y: Rational)
    ensures
        x.le_spec(Rational::max_spec(x, y)),
{
    if x.le_spec(y) {
        assert(Rational::max_spec(x, y) == y);
        Rational::lemma_le_transitive(x, y, Rational::max_spec(x, y));
    } else {
        assert(Rational::max_spec(x, y) == x);
        Rational::lemma_eqv_implies_le(x, x);
    }
}

/// max_spec(x, y) ≥ y.
pub proof fn lemma_max_ge_right(x: Rational, y: Rational)
    ensures
        y.le_spec(Rational::max_spec(x, y)),
{
    if x.le_spec(y) {
        assert(Rational::max_spec(x, y) == y);
        Rational::lemma_eqv_implies_le(y, y);
    } else {
        assert(Rational::max_spec(x, y) == x);
        Rational::lemma_le_iff_lt_or_eqv(y, x);
        Rational::lemma_lt_implies_le(y, x);
        Rational::lemma_le_transitive(y, x, Rational::max_spec(x, y));
    }
}

/// min ≤ max for the x folds (both attained at index 0).
pub proof fn lemma_x_min_le_max(vs: Seq<Vec2<Rational>>, i: int)
    requires
        1 <= i <= vs.len(),
    ensures
        x_min_upto(vs, i).le_spec(x_max_upto(vs, i)),
{
    lemma_x_min_le_all(vs, i, 0);
    lemma_x_max_ge_all(vs, i, 0);
    Rational::lemma_le_transitive(x_min_upto(vs, i), vs[0].x, x_max_upto(vs, i));
}

/// min ≤ max for the y folds.
pub proof fn lemma_y_min_le_max(vs: Seq<Vec2<Rational>>, i: int)
    requires
        1 <= i <= vs.len(),
    ensures
        y_min_upto(vs, i).le_spec(y_max_upto(vs, i)),
{
    lemma_y_min_le_all(vs, i, 0);
    lemma_y_max_ge_all(vs, i, 0);
    Rational::lemma_le_transitive(y_min_upto(vs, i), vs[0].y, y_max_upto(vs, i));
}

// ── filter soundness ─────────────────────────────────────────────────

/// Disjoint x-ranges (a entirely left of b) ⇒ vertex sets pointwise
/// x-separated — an excluded broadphase pair cannot be touching.
pub proof fn lemma_disjoint_x_pointwise(a: Seq<Vec2<Rational>>, b: Seq<Vec2<Rational>>)
    requires
        a.len() >= 1,
        b.len() >= 1,
        x_max_upto(a, a.len() as int).lt_spec(x_min_upto(b, b.len() as int)),
    ensures
        forall|i: int, j: int|
            (0 <= i < a.len() && 0 <= j < b.len())
                ==> (#[trigger] a[i]).x.lt_spec((#[trigger] b[j]).x),
{
    assert forall|i: int, j: int|
        (0 <= i < a.len() && 0 <= j < b.len())
            implies (#[trigger] a[i]).x.lt_spec((#[trigger] b[j]).x)
    by {
        lemma_x_max_ge_all(a, a.len() as int, i);
        lemma_x_min_le_all(b, b.len() as int, j);
        Rational::lemma_le_lt_transitive(
            a[i].x, x_max_upto(a, a.len() as int), x_min_upto(b, b.len() as int));
        Rational::lemma_lt_le_transitive(
            a[i].x, x_min_upto(b, b.len() as int), b[j].x);
    }
}

/// Disjoint y-ranges (a entirely below b) ⇒ vertex sets pointwise
/// y-separated.
pub proof fn lemma_disjoint_y_pointwise(a: Seq<Vec2<Rational>>, b: Seq<Vec2<Rational>>)
    requires
        a.len() >= 1,
        b.len() >= 1,
        y_max_upto(a, a.len() as int).lt_spec(y_min_upto(b, b.len() as int)),
    ensures
        forall|i: int, j: int|
            (0 <= i < a.len() && 0 <= j < b.len())
                ==> (#[trigger] a[i]).y.lt_spec((#[trigger] b[j]).y),
{
    assert forall|i: int, j: int|
        (0 <= i < a.len() && 0 <= j < b.len())
            implies (#[trigger] a[i]).y.lt_spec((#[trigger] b[j]).y)
    by {
        lemma_y_max_ge_all(a, a.len() as int, i);
        lemma_y_min_le_all(b, b.len() as int, j);
        Rational::lemma_le_lt_transitive(
            a[i].y, y_max_upto(a, a.len() as int), y_min_upto(b, b.len() as int));
        Rational::lemma_lt_le_transitive(
            a[i].y, y_min_upto(b, b.len() as int), b[j].y);
    }
}

} // verus!
