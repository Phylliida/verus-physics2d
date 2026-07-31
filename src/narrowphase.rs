//! SAT narrowphase (phys-04, SPEC §5): separating-axis classification for
//! convex polygons, with witnesses.
//!
//! For every edge of A and B, compute the minimum signed projection of the
//! other polygon's vertices onto the edge's outward normal. If any is
//! strictly positive, that axis strictly separates the vertex sets
//! (proved: the two foralls in axis_separates). Otherwise no edge-normal
//! axis separates (Touching carries the max-separation reference feature
//! for phys-05's manifold work).

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::proofs::shape::{
    lemma_axis_sep_eq_neg_orient, lemma_min_pos_all, lemma_min_sep_attained,
    lemma_min_sep_le_all,
};
use crate::massprops::vdot;
use crate::massprops::vscale;
use crate::shape::{axis_sep, edge_normal, min_sep, orient, vadd, vsub, ConvexPoly};
use crate::types::{copy_svec2, SVec2, Scalar};

verus! {

pub enum SatResult {
    Separated { from_a: bool, edge: usize },
    Touching { from_a: bool, edge: usize },
}

/// A single contact point on the reference face (SPEC §5 step 3).
/// sep ≤ 0 relative to the reference face (exact axis_sep value).
pub struct ContactPoint {
    pub point: SVec2,
    pub sep: Scalar,
}

/// Contact manifold for a touching pair (SPEC §5 step 3, phys-06).
/// The normal is UNNORMALIZED (never sqrt) and points A → B; points are
/// lex-sorted (E6 canonical order), 1 or 2 of them.
pub struct ContactManifold {
    pub a: usize,
    pub b: usize,
    pub normal: SVec2,
    pub points: Vec<ContactPoint>,
    /// (reference edge, incident edge).
    pub feature: (usize, usize),
}

/// The separating witness, spec-side: the axis from `owner`'s edge
/// strictly separates owner's vertices (inner side, ≤ 0) from other's
/// (strictly outward, > 0).
pub open spec fn axis_separates(
    owner: Seq<Vec2<Rational>>,
    other: Seq<Vec2<Rational>>,
    edge: int,
) -> bool {
    let n = owner.len();
    &&& 0 <= edge < n
    &&& {
        let norm = edge_normal(owner[edge], owner[(edge + 1) % (n as int)]);
        let p0 = owner[edge];
        &&& forall|j: int|
            0 <= j < other.len() ==> Rational::from_int_spec(0).lt_spec(
                #[trigger] axis_sep(norm, p0, other[j]))
        &&& forall|j: int|
            0 <= j < n ==> axis_sep(norm, p0, owner[j]).le_spec(
                Rational::from_int_spec(0))
    }
}

/// No edge-normal of either polygon separates (the Touching claim).
pub open spec fn no_axis_separates(
    a: Seq<Vec2<Rational>>,
    b: Seq<Vec2<Rational>>,
) -> bool {
    &&& forall|e: int|
        0 <= e < a.len() ==> #[trigger] min_sep(
            edge_normal(a[e], a[(e + 1) % (a.len() as int)]), a[e], b, 0).le_spec(
            Rational::from_int_spec(0))
    &&& forall|e: int|
        0 <= e < b.len() ==> #[trigger] min_sep(
            edge_normal(b[e], b[(e + 1) % (b.len() as int)]), b[e], a, 0).le_spec(
            Rational::from_int_spec(0))
}

/// dot(n, q − p) with exact model.
pub fn axis_sep_exec(n: &SVec2, p: &SVec2, q: &SVec2) -> (out: Scalar)
    requires
        n.wf_spec(),
        p.wf_spec(),
        q.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == axis_sep(n.model@, p.model@, q.model@),
{
    let dx = q.x.sub(&p.x);
    let dy = q.y.sub(&p.y);
    let t1 = n.x.mul(&dx);
    let t2 = n.y.mul(&dy);
    t1.add(&t2)
}

/// edge_normal with exact model.
pub fn edge_normal_exec(a: &SVec2, b: &SVec2) -> (out: SVec2)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == edge_normal(a.model@, b.model@),
{
    let nx = b.y.sub(&a.y);
    let ny = a.x.sub(&b.x);
    RuntimeVec2::new(nx, ny)
}

/// min axis projection of `other`'s vertices onto n from p, with the
/// attaining index.
pub fn min_axis_sep_exec(n: &SVec2, p: &SVec2, other: &ConvexPoly) -> (out: (Scalar, usize))
    requires
        n.wf_spec(),
        p.wf_spec(),
        other.wf_spec(),
    ensures
        out.0.wf_spec(),
        out.1 < other.verts@.len(),
        out.0@.eqv_spec(min_sep(n.model@, p.model@, other.model_verts(), 0)),
        out.0@ == axis_sep(n.model@, p.model@, other.model_verts()[out.1 as int]),
{
    let mut best = axis_sep_exec(n, p, &other.verts[0]);
    let mut best_i: usize = 0;
    let mut j: usize = 1;
    while j < other.verts.len()
        invariant
            n.wf_spec(),
            p.wf_spec(),
            other.wf_spec(),
            1 <= j <= other.verts@.len(),
            other.verts@.len() >= 3,
            best_i < j,
            best.wf_spec(),
            best@ == axis_sep(n.model@, p.model@, other.model_verts()[best_i as int]),
            forall|k: int|
                0 <= k < j as int ==> best@.le_spec(
                    axis_sep(n.model@, p.model@, other.model_verts()[k])),
        decreases other.verts.len() - j,
    {
        let s = axis_sep_exec(n, p, &other.verts[j]);
        let ghost prev_best = best@;
        let is_less = s.lt(&best);
        if is_less {
            best = s;
            best_i = j;
        }
        proof {
            if is_less {
                assert(best@ == s@);
                assert(s@.lt_spec(prev_best));
                Rational::lemma_lt_implies_le(s@, prev_best);
                assert forall|k: int|
                    0 <= k < j as int + 1 implies best@.le_spec(
                        axis_sep(n.model@, p.model@, other.model_verts()[k]))
                by {
                    if k == j as int {
                        assert(best@ == axis_sep(n.model@, p.model@, other.model_verts()[k]));
                        Rational::lemma_eqv_implies_le(best@, best@);
                    } else {
                        Rational::lemma_le_transitive(
                            best@, prev_best,
                            axis_sep(n.model@, p.model@, other.model_verts()[k]));
                    }
                }
            } else {
                assert(best@ == prev_best);
                assert(!s@.lt_spec(prev_best));
                Rational::lemma_trichotomy(prev_best, s@);
                assert(prev_best.le_spec(s@));
            }
        }
        j = j + 1;
    }
    proof {
        // best ≤ every element; min is attained at some index (≤ best);
        // antisymmetric gives eqv
        lemma_min_sep_attained(n.model@, p.model@, other.model_verts(), 0);
        lemma_min_sep_le_all(n.model@, p.model@, other.model_verts(), 0, best_i as int);
        assert forall|k: int|
            0 <= k < other.model_verts().len() implies best@.le_spec(
                axis_sep(n.model@, p.model@, other.model_verts()[k]))
        by {
        }
        // min == axis at its attaining index, so min ≤ best as well
        assert(min_sep(n.model@, p.model@, other.model_verts(), 0).le_spec(best@)) by {
            lemma_min_sep_attained(n.model@, p.model@, other.model_verts(), 0);
        }
        Rational::lemma_le_antisymmetric(
            best@, min_sep(n.model@, p.model@, other.model_verts(), 0));
    }
    (best, best_i)
}

/// vdot with exact model.
pub fn dot_exec(a: &SVec2, b: &SVec2) -> (out: Scalar)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == vdot(a.model@, b.model@),
{
    let t1 = a.x.mul(&b.x);
    let t2 = a.y.mul(&b.y);
    t1.add(&t2)
}

/// Dot of the reference normal with incident edge e's outward normal.
pub open spec fn inc_normal_dot(
    ref_n: Vec2<Rational>,
    inc: Seq<Vec2<Rational>>,
    e: int,
) -> Rational
    recommends 0 <= e < inc.len()
{
    vdot(ref_n, edge_normal(inc[e], inc[(e + 1) % (inc.len() as int)]))
}

/// q ≡ a + u·(b − a) component-wise with 0 ≤ u ≤ 1: q interpolates the
/// segment a–b (the clipping span witness, SPEC §5 step 3).
pub open spec fn interp_rel(
    a: Vec2<Rational>,
    b: Vec2<Rational>,
    q: Vec2<Rational>,
    u: Rational,
) -> bool {
    &&& Rational::from_int_spec(0).le_spec(u)
    &&& u.le_spec(Rational::from_int_spec(1))
    &&& q.x.eqv_spec(vadd(a, vscale(u, vsub(b, a))).x)
    &&& q.y.eqv_spec(vadd(a, vscale(u, vsub(b, a))).y)
}

/// Incident edge selection (SPEC §5 step 3): the edge of `inc` whose
/// outward normal has minimal dot with the reference normal (ties: lower
/// index). Ensures the returned index attains the min.
pub fn incident_edge_exec(ref_n: &SVec2, inc: &ConvexPoly) -> (out: usize)
    requires
        ref_n.wf_spec(),
        inc.wf_spec(),
    ensures
        out < inc.verts@.len(),
        forall|e: int|
            0 <= e < inc.verts@.len() ==> inc_normal_dot(
                ref_n.model@, inc.model_verts(), out as int).le_spec(
                #[trigger] inc_normal_dot(ref_n.model@, inc.model_verts(), e)),
{
    let n0 = edge_normal_exec(&inc.verts[0], &inc.verts[1 % inc.verts.len()]);
    let mut best = dot_exec(ref_n, &n0);
    let mut best_e: usize = 0;
    proof {
        assert(inc.verts@.len() >= 3);
        assert(inc.model_verts()[0] == inc.verts@[0].model@);
        assert(inc.model_verts()[(0 as int + 1) % (inc.model_verts().len() as int)]
            == inc.verts@[(1usize % inc.verts.len()) as int].model@);
        assert(best@ == inc_normal_dot(ref_n.model@, inc.model_verts(), 0));
    }
    let mut e: usize = 1;
    while e < inc.verts.len()
        invariant
            ref_n.wf_spec(),
            inc.wf_spec(),
            1 <= e <= inc.verts@.len(),
            best_e < e,
            best.wf_spec(),
            best@ == inc_normal_dot(ref_n.model@, inc.model_verts(), best_e as int),
            forall|k: int|
                0 <= k < e as int ==> best@.le_spec(
                    #[trigger] inc_normal_dot(ref_n.model@, inc.model_verts(), k)),
        decreases inc.verts.len() - e,
    {
        let va = &inc.verts[e];
        let vb = &inc.verts[(e + 1) % inc.verts.len()];
        let en = edge_normal_exec(va, vb);
        let d = dot_exec(ref_n, &en);
        let ghost prev = best@;
        let is_less = d.lt(&best);
        if is_less {
            best = d;
            best_e = e;
        }
        proof {
            assert(va.model@ == inc.model_verts()[e as int]);
            assert(vb.model@ == inc.model_verts()[
                (e as int + 1) % (inc.model_verts().len() as int)]);
            assert(d@ == inc_normal_dot(ref_n.model@, inc.model_verts(), e as int));
            if is_less {
                assert(best@ == d@);
                assert(best@ == inc_normal_dot(ref_n.model@, inc.model_verts(), e as int));
                assert(d@.lt_spec(prev));
                Rational::lemma_lt_implies_le(d@, prev);
                assert forall|k: int|
                    0 <= k < e as int + 1 implies best@.le_spec(
                        #[trigger] inc_normal_dot(ref_n.model@, inc.model_verts(), k))
                by {
                    if k == e as int {
                        Rational::lemma_eqv_implies_le(best@, best@);
                    } else {
                        Rational::lemma_le_transitive(
                            best@, prev,
                            inc_normal_dot(ref_n.model@, inc.model_verts(), k));
                    }
                }
            } else {
                assert(best@ == prev);
                assert(!d@.lt_spec(prev));
                Rational::lemma_trichotomy(prev, d@);
                assert(prev.le_spec(d@));
                assert(prev.le_spec(inc_normal_dot(ref_n.model@, inc.model_verts(), e as int)));
            }
        }
        e = e + 1;
    }
    best_e
}

/// One-sided pass over owner's edges. Returns the separating edge if any,
/// plus the max-separation edge (reference feature for phys-05).
pub fn classify_side(
    owner: &ConvexPoly,
    other: &ConvexPoly,
) -> (out: (Option<usize>, usize, Scalar))
    requires
        owner.wf_spec(),
        other.wf_spec(),
    ensures
        out.0 is Some ==> axis_separates(
            owner.model_verts(), other.model_verts(), out.0->Some_0 as int),
        out.2.wf_spec(),
        out.0 is None ==> forall|e: int|
            0 <= e < owner.verts@.len() ==> #[trigger] min_sep(
                edge_normal(
                    owner.model_verts()[e],
                    owner.model_verts()[(e + 1) % (owner.model_verts().len() as int)]),
                owner.model_verts()[e], other.model_verts(), 0).le_spec(
                Rational::from_int_spec(0)),
        out.0 is None ==> {
            &&& out.1 < owner.verts@.len()
            &&& out.2@.eqv_spec(min_sep(
                edge_normal(
                    owner.model_verts()[out.1 as int],
                    owner.model_verts()[(out.1 as int + 1) % (owner.model_verts().len() as int)]),
                owner.model_verts()[out.1 as int], other.model_verts(), 0))
            &&& forall|e: int|
                0 <= e < owner.verts@.len() ==> #[trigger] min_sep(
                    edge_normal(
                        owner.model_verts()[e],
                        owner.model_verts()[(e + 1) % (owner.model_verts().len() as int)]),
                    owner.model_verts()[e], other.model_verts(), 0).le_spec(out.2@)
        },
{
    let n0 = edge_normal_exec(&owner.verts[0], &owner.verts[1 % owner.verts.len()]);
    let (best_sep0, _idx0) = min_axis_sep_exec(&n0, &owner.verts[0], other);
    let mut best_sep = best_sep0;
    let mut best_e: usize = 0;
    let zero = RuntimeRational::from_int(0);
    proof {
        assert(owner.verts@.len() >= 3);
        assert(owner.model_verts()[0] == owner.verts@[0].model@);
        assert(owner.model_verts()[(0 as int + 1) % (owner.model_verts().len() as int)]
            == owner.verts@[(1usize % owner.verts.len()) as int].model@);
        assert(n0.model@ == edge_normal(
            owner.model_verts()[0],
            owner.model_verts()[(0 as int + 1) % (owner.model_verts().len() as int)]));
        assert(best_sep@.eqv_spec(min_sep(
            edge_normal(
                owner.model_verts()[0],
                owner.model_verts()[(0 as int + 1) % (owner.model_verts().len() as int)]),
            owner.model_verts()[0], other.model_verts(), 0)));
    }
    let mut e: usize = 0;
    while e < owner.verts.len()
        invariant
            owner.wf_spec(),
            other.wf_spec(),
            zero.wf_spec(),
            zero@ == Rational::from_int_spec(0),
            e <= owner.verts@.len(),
            best_e < owner.verts@.len(),
            best_sep.wf_spec(),
            best_sep@.eqv_spec(min_sep(
                edge_normal(
                    owner.model_verts()[best_e as int],
                    owner.model_verts()[(best_e as int + 1) % (owner.model_verts().len() as int)]),
                owner.model_verts()[best_e as int], other.model_verts(), 0)),
            forall|ee: int|
                0 <= ee < e as int ==> #[trigger] min_sep(
                    edge_normal(
                        owner.model_verts()[ee],
                        owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                    owner.model_verts()[ee], other.model_verts(), 0).le_spec(best_sep@),
            forall|ee: int|
                0 <= ee < e as int ==> #[trigger] min_sep(
                    edge_normal(
                        owner.model_verts()[ee],
                        owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                    owner.model_verts()[ee], other.model_verts(), 0).le_spec(
                    Rational::from_int_spec(0)),
            best_e < e || (e == 0 && best_e == 0),
        decreases owner.verts.len() - e,
    {
        let va = &owner.verts[e];
        let vb = &owner.verts[(e + 1) % owner.verts.len()];
        let n = edge_normal_exec(va, vb);
        let (sep, _idx) = min_axis_sep_exec(&n, va, other);
        let ghost prev_sep = best_sep@;
        let is_better = sep.gt(&best_sep);
        let is_sep = zero.lt(&sep);
        if is_better {
            best_sep = verus_rational::runtime_rational::copy_rational(&sep);
            best_e = e;
        }
        if is_sep {
            proof {
                // the axis strictly separates: every other vertex is
                // strictly outward (min > 0), every owner vertex inward
                // (convexity: orient ≥ 0 ⟹ dot ≤ 0)
                assert(zero@.lt_spec(sep@));
                assert(sep@.eqv_spec(min_sep(n.model@, va.model@, other.model_verts(), 0)));
                crate::proofs::shape::lemma_lt_eqv_subst_right(
                    Rational::from_int_spec(0),
                    sep@,
                    min_sep(n.model@, va.model@, other.model_verts(), 0));
                assert forall|j: int|
                    0 <= j < other.model_verts().len() implies Rational::from_int_spec(0).lt_spec(
                        #[trigger] axis_sep(n.model@, va.model@, other.model_verts()[j]))
                by {
                    lemma_min_pos_all(n.model@, va.model@, other.model_verts(), j);
                }
                assert forall|j: int|
                    0 <= j < owner.model_verts().len() implies axis_sep(
                        n.model@, va.model@, owner.model_verts()[j]).le_spec(
                        Rational::from_int_spec(0))
                by {
                    lemma_axis_sep_eq_neg_orient(
                        va.model@, vb.model@, owner.model_verts()[j]);
                    let o = orient(va.model@, vb.model@, owner.model_verts()[j]);
                    assert(va.model@ == owner.model_verts()[e as int]);
                    assert(vb.model@ == owner.model_verts()[
                        (e as int + 1) % (owner.model_verts().len() as int)]);
                    if j == e as int {
                        crate::proofs::shape::lemma_orient_left_endpoint_zero(
                            va.model@, vb.model@);
                        Rational::lemma_eqv_implies_le(Rational::from_int_spec(0), o);
                    } else if j == (e as int + 1) % (owner.model_verts().len() as int) {
                        crate::proofs::shape::lemma_orient_right_endpoint_zero(
                            va.model@, vb.model@);
                        Rational::lemma_eqv_implies_le(Rational::from_int_spec(0), o);
                    } else {
                        assert(Rational::from_int_spec(0).lt_spec(o));
                        Rational::lemma_lt_implies_le(Rational::from_int_spec(0), o);
                    }
                    assert(Rational::from_int_spec(0).le_spec(o));
                    Rational::lemma_neg_reverses_le(Rational::from_int_spec(0), o);
                    assert(o.neg_spec().le_spec(Rational::from_int_spec(0).neg_spec()));
                    assert(Rational::from_int_spec(0).neg_spec() == Rational::from_int_spec(0));
                    Rational::lemma_le_transitive(
                        axis_sep(n.model@, va.model@, owner.model_verts()[j]),
                        o.neg_spec(),
                        Rational::from_int_spec(0));
                }
                assert(axis_separates(owner.model_verts(), other.model_verts(), e as int));
            }
            return (Some(e), best_e, best_sep);
        }
        proof {
            assert(sep@.eqv_spec(min_sep(
                edge_normal(
                    owner.model_verts()[e as int],
                    owner.model_verts()[(e as int + 1) % (owner.model_verts().len() as int)]),
                owner.model_verts()[e as int], other.model_verts(), 0)));
            assert(!Rational::from_int_spec(0).lt_spec(sep@));
            Rational::lemma_trichotomy(Rational::from_int_spec(0), sep@);
            assert(sep@.le_spec(Rational::from_int_spec(0)));
            if is_better {
                assert(best_sep@ == sep@);
                assert(prev_sep.lt_spec(best_sep@));
                Rational::lemma_lt_implies_le(prev_sep, best_sep@);
            } else {
                assert(sep@.le_spec(best_sep@));
                assert(prev_sep == best_sep@);
            }
            assert(best_e < e as int + 1);
            assert forall|ee: int|
                0 <= ee < e as int + 1 implies #[trigger] min_sep(
                    edge_normal(
                        owner.model_verts()[ee],
                        owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                    owner.model_verts()[ee], other.model_verts(), 0).le_spec(best_sep@)
            by {
                if ee == e as int {
                    crate::proofs::shape::lemma_le_eqv_subst_left(
                        sep@,
                        min_sep(
                            edge_normal(
                                owner.model_verts()[ee],
                                owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                            owner.model_verts()[ee], other.model_verts(), 0),
                        best_sep@);
                } else {
                    Rational::lemma_le_transitive(
                        min_sep(
                            edge_normal(
                                owner.model_verts()[ee],
                                owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                            owner.model_verts()[ee], other.model_verts(), 0),
                        prev_sep,
                        best_sep@);
                }
            }
            assert forall|ee: int|
                0 <= ee < e as int + 1 implies #[trigger] min_sep(
                    edge_normal(
                        owner.model_verts()[ee],
                        owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                    owner.model_verts()[ee], other.model_verts(), 0).le_spec(
                    Rational::from_int_spec(0))
            by {
                if ee == e as int {
                    crate::proofs::shape::lemma_le_eqv_subst_left(
                        sep@,
                        min_sep(
                            edge_normal(
                                owner.model_verts()[ee],
                                owner.model_verts()[(ee + 1) % (owner.model_verts().len() as int)]),
                            owner.model_verts()[ee], other.model_verts(), 0),
                        Rational::from_int_spec(0));
                }
            }
        }
        e = e + 1;
    }
    (None, best_e, best_sep)
}

/// SAT classification over all edges of both polygons.
pub fn sat_classify(a: &ConvexPoly, b: &ConvexPoly) -> (out: SatResult)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        match out {
            SatResult::Separated { from_a, edge } => {
                if from_a {
                    axis_separates(a.model_verts(), b.model_verts(), edge as int)
                } else {
                    axis_separates(b.model_verts(), a.model_verts(), edge as int)
                }
            },
            SatResult::Touching { .. } => {
                no_axis_separates(a.model_verts(), b.model_verts())
            },
        },
{
    let (sep_a, max_a, ms_a) = classify_side(a, b);
    if sep_a.is_some() {
        return SatResult::Separated { from_a: true, edge: sep_a.unwrap() };
    }
    let (sep_b, max_b, ms_b) = classify_side(b, a);
    if sep_b.is_some() {
        return SatResult::Separated { from_a: false, edge: sep_b.unwrap() };
    }
    proof {
        assert(no_axis_separates(a.model_verts(), b.model_verts()));
    }
    if ms_a.ge(&ms_b) {
        SatResult::Touching { from_a: true, edge: max_a }
    } else {
        SatResult::Touching { from_a: false, edge: max_b }
    }
}

/// The plane intersection point of segment q0–q1 (exactly one endpoint
/// inside the half-plane {q : dot(d, q − base) ≥ 0}). Exact rational
/// interpolation, no sqrt. Ensures: the point lies exactly on the clip
/// plane and interpolates the segment (SPEC §5 step 3).
pub fn clip_intersection_exec(
    d: &SVec2,
    base: &SVec2,
    q0: &SVec2,
    q1: &SVec2,
    keep0: bool,
) -> (out: SVec2)
    requires
        d.wf_spec(),
        base.wf_spec(),
        q0.wf_spec(),
        q1.wf_spec(),
        keep0 ==> {
            &&& Rational::from_int_spec(0).le_spec(axis_sep(d.model@, base.model@, q0.model@))
            &&& axis_sep(d.model@, base.model@, q1.model@).lt_spec(Rational::from_int_spec(0))
        },
        !keep0 ==> {
            &&& axis_sep(d.model@, base.model@, q0.model@).lt_spec(Rational::from_int_spec(0))
            &&& Rational::from_int_spec(0).le_spec(axis_sep(d.model@, base.model@, q1.model@))
        },
    ensures
        out.wf_spec(),
        axis_sep(d.model@, base.model@, out.model@).eqv_spec(Rational::from_int_spec(0)),
        exists|u: Rational| interp_rel(q0.model@, q1.model@, out.model@, u),
{
    let v0 = axis_sep_exec(d, base, q0);
    let v1 = axis_sep_exec(d, base, q1);
    if keep0 {
        let den = v0.sub(&v1);
        proof {
            crate::proofs::manifold::lemma_clip_t_bounds(v0@, v1@);
        }
        let t = v0.div(&den);
        let dq = q1.sub(q0);
        let tdq = dq.scaled(&t);
        let q = q0.add(&tdq);
        proof {
            assert(q.model@ == q0.model@.add(tdq.model@));
            assert(q.model@.x == q0.model@.x.add_spec(tdq.model@.x).canonical());
            assert(q.model@.y == q0.model@.y.add_spec(tdq.model@.y).canonical());
            assert(tdq.model@.x == t@.mul_spec(dq.model@.x).canonical());
            assert(tdq.model@.y == t@.mul_spec(dq.model@.y).canonical());
            assert(dq.model@.x == q1.model@.x.sub_spec(q0.model@.x).canonical());
            assert(dq.model@.y == q1.model@.y.sub_spec(q0.model@.y).canonical());
            assert(q.model@.x == q0.model@.x.add_spec(
                t@.mul_spec(q1.model@.x.sub_spec(q0.model@.x).canonical()).canonical()).canonical());
            assert(q.model@.y == q0.model@.y.add_spec(
                t@.mul_spec(q1.model@.y.sub_spec(q0.model@.y).canonical()).canonical()).canonical());
            assert(t@ == v0@.div_spec(v0@.sub_spec(v1@)));
            crate::proofs::manifold::lemma_clip_point_facts(
                d.model@, base.model@, q0.model@, q1.model@, q.model@, t@);
            assert(exists|u: Rational| interp_rel(q0.model@, q1.model@, q.model@, u));
        }
        q
    } else {
        let den = v1.sub(&v0);
        proof {
            crate::proofs::manifold::lemma_clip_t_bounds(v1@, v0@);
        }
        let t1 = v1.div(&den);
        let dq = q0.sub(q1);
        let tdq = dq.scaled(&t1);
        let q = q1.add(&tdq);
        proof {
            assert(q.model@ == q1.model@.add(tdq.model@));
            assert(q.model@.x == q1.model@.x.add_spec(tdq.model@.x).canonical());
            assert(q.model@.y == q1.model@.y.add_spec(tdq.model@.y).canonical());
            assert(tdq.model@.x == t1@.mul_spec(dq.model@.x).canonical());
            assert(tdq.model@.y == t1@.mul_spec(dq.model@.y).canonical());
            assert(dq.model@.x == q0.model@.x.sub_spec(q1.model@.x).canonical());
            assert(dq.model@.y == q0.model@.y.sub_spec(q1.model@.y).canonical());
            assert(q.model@.x == q1.model@.x.add_spec(
                t1@.mul_spec(q0.model@.x.sub_spec(q1.model@.x).canonical()).canonical()).canonical());
            assert(q.model@.y == q1.model@.y.add_spec(
                t1@.mul_spec(q0.model@.y.sub_spec(q1.model@.y).canonical()).canonical()).canonical());
            assert(t1@ == v1@.div_spec(v1@.sub_spec(v0@)));
            crate::proofs::manifold::lemma_clip_point_facts_swapped(
                d.model@, base.model@, q0.model@, q1.model@, q.model@, t1@);
            assert(exists|u: Rational| interp_rel(q0.model@, q1.model@, q.model@, u));
        }
        q
    }
}

/// Clip the segment q0–q1 against the half-plane {q : dot(d, q − base) ≥ 0}
/// (one side plane of the reference edge, SPEC §5 step 3). Output: 0–2
/// points in segment order, each inside the half-plane and interpolating
/// the input segment.
pub fn clip_halfplane_exec(
    d: &SVec2,
    base: &SVec2,
    q0: &SVec2,
    q1: &SVec2,
) -> (out: Vec<SVec2>)
    requires
        d.wf_spec(),
        base.wf_spec(),
        q0.wf_spec(),
        q1.wf_spec(),
    ensures
        out@.len() <= 2,
        forall|k: int|
            0 <= k < out@.len() ==> {
                let q = (#[trigger] out@[k]);
                &&& q.wf_spec()
                &&& Rational::from_int_spec(0).le_spec(
                        axis_sep(d.model@, base.model@, q.model@))
                &&& exists|u: Rational|
                        interp_rel(q0.model@, q1.model@, q.model@, u)
            },
{
    let v0 = axis_sep_exec(d, base, q0);
    let v1 = axis_sep_exec(d, base, q1);
    let zero = RuntimeRational::from_int(0);
    let keep0 = zero.le(&v0);
    let keep1 = zero.le(&v1);
    let mut out: Vec<SVec2> = Vec::new();
    if keep0 && keep1 {
        proof {
            assert(zero@.le_spec(v0@));
            assert(zero@.le_spec(v1@));
        }
        out.push(copy_svec2(q0));
        out.push(copy_svec2(q1));
        proof {
            assert forall|k: int|
                0 <= k < out@.len() implies {
                    let q = (#[trigger] out@[k]);
                    &&& q.wf_spec()
                    &&& Rational::from_int_spec(0).le_spec(
                            axis_sep(d.model@, base.model@, q.model@))
                    &&& exists|u: Rational|
                            interp_rel(q0.model@, q1.model@, q.model@, u)
                }
            by {
                crate::proofs::manifold::lemma_interp_rel_endpoints(q0.model@, q1.model@);
                if k == 0 {
                    assert(out@[k].model@ == q0.model@);
                } else {
                    assert(out@[k].model@ == q1.model@);
                }
            }
        }
    } else if keep0 {
        proof {
            assert(zero@.le_spec(v0@));
            assert(!zero@.le_spec(v1@));
            Rational::lemma_trichotomy(zero@, v1@);
        }
        let qi = clip_intersection_exec(d, base, q0, q1, true);
        out.push(copy_svec2(q0));
        out.push(qi);
        proof {
            assert forall|k: int|
                0 <= k < out@.len() implies {
                    let q = (#[trigger] out@[k]);
                    &&& q.wf_spec()
                    &&& Rational::from_int_spec(0).le_spec(
                            axis_sep(d.model@, base.model@, q.model@))
                    &&& exists|u: Rational|
                            interp_rel(q0.model@, q1.model@, q.model@, u)
                }
            by {
                if k == 0 {
                    assert(out@[k].model@ == q0.model@);
                    crate::proofs::manifold::lemma_interp_rel_endpoints(
                        q0.model@, q1.model@);
                } else {
                    Rational::lemma_eqv_implies_le(
                        axis_sep(d.model@, base.model@, out@[k].model@),
                        Rational::from_int_spec(0));
                }
            }
        }
    } else if keep1 {
        proof {
            assert(!zero@.le_spec(v0@));
            assert(zero@.le_spec(v1@));
            Rational::lemma_trichotomy(zero@, v0@);
        }
        let qi = clip_intersection_exec(d, base, q0, q1, false);
        out.push(qi);
        out.push(copy_svec2(q1));
        proof {
            assert forall|k: int|
                0 <= k < out@.len() implies {
                    let q = (#[trigger] out@[k]);
                    &&& q.wf_spec()
                    &&& Rational::from_int_spec(0).le_spec(
                            axis_sep(d.model@, base.model@, q.model@))
                    &&& exists|u: Rational|
                            interp_rel(q0.model@, q1.model@, q.model@, u)
                }
            by {
                if k == 1 {
                    assert(out@[k].model@ == q1.model@);
                    crate::proofs::manifold::lemma_interp_rel_endpoints(
                        q0.model@, q1.model@);
                } else {
                    Rational::lemma_eqv_implies_le(
                        axis_sep(d.model@, base.model@, out@[k].model@),
                        Rational::from_int_spec(0));
                }
            }
        }
    } else {
        proof {
            assert(out@.len() == 0);
        }
    }
    out
}

} // verus!
