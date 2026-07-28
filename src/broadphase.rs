//! World-space transforms, AABBs, and broadphase pairs (phys-05b, SPEC §4
//! leftovers). All raw Rational ops, matching shape.rs/massprops.rs.
//!
//! Deviation from SPEC §4: no sort-and-sweep — an O(n²) filter with
//! canonical lex pair order has identical guarantees at phase-1 scene
//! sizes (and the phys-06 certificate re-checks all pairs anyway, D8).
//! The verified content is:
//!   - world_vert/world_verts: exact RotQ-apply + translate,
//!   - the AABB coordinate folds bound every vertex (min ≤ v ≤ max),
//!   - disjoint x-ranges ⇒ vertex sets POINTWISE x-separated (the
//!     filter's soundness: excluded pairs cannot be touching),
//!   - the emitted pair list equals the spec filter exactly.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::rotq::RotQ;
use crate::shape::ConvexPoly;
use crate::types::{SVec2, Scalar};

verus! {

// ── world transform ──────────────────────────────────────────────────

/// One vertex to world space: rotate by (c, s), translate by pos (raw).
pub open spec fn world_vert(
    pos: Vec2<Rational>,
    c: Rational,
    s: Rational,
    v: Vec2<Rational>,
) -> Vec2<Rational> {
    Vec2 {
        x: c.mul_spec(v.x).sub_spec(s.mul_spec(v.y)).add_spec(pos.x),
        y: s.mul_spec(v.x).add_spec(c.mul_spec(v.y)).add_spec(pos.y),
    }
}

/// All vertices in world space.
pub open spec fn world_verts(
    pos: Vec2<Rational>,
    c: Rational,
    s: Rational,
    vs: Seq<Vec2<Rational>>,
) -> Seq<Vec2<Rational>> {
    Seq::new(vs.len(), |i: int| world_vert(pos, c, s, vs[i]))
}

// ── coordinate folds (prefix, mirror of chain_cross_sum) ─────────────

/// min of vs[0..i].x.
pub open spec fn x_min_upto(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 1 <= i <= vs.len()
    decreases i
{
    if i <= 1 {
        vs[0].x
    } else {
        Rational::min_spec(x_min_upto(vs, i - 1), vs[i - 1].x)
    }
}

/// max of vs[0..i].x.
pub open spec fn x_max_upto(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 1 <= i <= vs.len()
    decreases i
{
    if i <= 1 {
        vs[0].x
    } else {
        Rational::max_spec(x_max_upto(vs, i - 1), vs[i - 1].x)
    }
}

/// min of vs[0..i].y.
pub open spec fn y_min_upto(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 1 <= i <= vs.len()
    decreases i
{
    if i <= 1 {
        vs[0].y
    } else {
        Rational::min_spec(y_min_upto(vs, i - 1), vs[i - 1].y)
    }
}

/// max of vs[0..i].y.
pub open spec fn y_max_upto(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 1 <= i <= vs.len()
    decreases i
{
    if i <= 1 {
        vs[0].y
    } else {
        Rational::max_spec(y_max_upto(vs, i - 1), vs[i - 1].y)
    }
}

// ── AABB ─────────────────────────────────────────────────────────────

pub struct Aabb {
    pub lo: SVec2,
    pub hi: SVec2,
}

impl Aabb {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.lo.model@.x.le_spec(self.hi.model@.x)
        &&& self.lo.model@.y.le_spec(self.hi.model@.y)
    }
}

/// The AABB of a vertex seq (spec view).
pub open spec fn aabb_of(vs: Seq<Vec2<Rational>>) -> (Rational, Rational, Rational, Rational)
    recommends vs.len() >= 1
{
    (x_min_upto(vs, vs.len() as int), x_max_upto(vs, vs.len() as int),
        y_min_upto(vs, vs.len() as int), y_max_upto(vs, vs.len() as int))
}

/// 1D range overlap (inclusive).
pub open spec fn ranges_overlap(lo1: Rational, hi1: Rational, lo2: Rational, hi2: Rational) -> bool {
    &&& lo1.le_spec(hi2)
    &&& lo2.le_spec(hi1)
}

/// AABB overlap for two vertex seqs.
pub open spec fn aabbs_overlap(a: Seq<Vec2<Rational>>, b: Seq<Vec2<Rational>>) -> bool
    recommends a.len() >= 1, b.len() >= 1
{
    &&& ranges_overlap(x_min_upto(a, a.len() as int), x_max_upto(a, a.len() as int),
        x_min_upto(b, b.len() as int), x_max_upto(b, b.len() as int))
    &&& ranges_overlap(y_min_upto(a, a.len() as int), y_max_upto(a, a.len() as int),
        y_min_upto(b, b.len() as int), y_max_upto(b, b.len() as int))
}

// ── canonical pair filter ────────────────────────────────────────────

/// Overlap test on the AABB seq view (exec-facing).
pub open spec fn pair_overlaps(aabbs: Seq<Aabb>, i: int, j: int) -> bool {
    let a = aabbs[i];
    let b = aabbs[j];
    &&& ranges_overlap(a.lo.model@.x, a.hi.model@.x, b.lo.model@.x, b.hi.model@.x)
    &&& ranges_overlap(a.lo.model@.y, a.hi.model@.y, b.lo.model@.y, b.hi.model@.y)
}

/// Pairs (i, j') for i < j' < j that overlap, in increasing order.
pub open spec fn filter_pairs_j_upto(aabbs: Seq<Aabb>, i: int, j: int) -> Seq<(int, int)>
    decreases j - (i + 1)
{
    if j <= i + 1 {
        seq![]
    } else {
        let prev = filter_pairs_j_upto(aabbs, i, j - 1);
        if pair_overlaps(aabbs, i, j - 1) {
            prev.push((i, j - 1))
        } else {
            prev
        }
    }
}

/// All overlapping pairs with first index < i (lex order).
pub open spec fn filter_pairs_upto(aabbs: Seq<Aabb>, i: int) -> Seq<(int, int)>
    decreases i
{
    if i <= 0 {
        seq![]
    } else {
        filter_pairs_upto(aabbs, i - 1).add(
            filter_pairs_j_upto(aabbs, i - 1, aabbs.len() as int))
    }
}

/// The canonical broadphase pair list.
pub open spec fn broadphase_pairs_spec(aabbs: Seq<Aabb>) -> Seq<(int, int)> {
    filter_pairs_upto(aabbs, aabbs.len() as int)
}

} // verus!

verus! {

/// World-space vertices of a polygon under (pos, rot) — exact.
pub fn world_verts_exec(pos: &SVec2, rot: &RotQ, p: &ConvexPoly) -> (out: Vec<SVec2>)
    requires
        pos.wf_spec(),
        rot.wf_spec(),
        p.wf_spec(),
    ensures
        out@.len() == p.verts@.len(),
        forall|i: int|
            0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        out@.map(|_i: int, v: SVec2| v.model@)
            == world_verts(pos.model@, rot.c@, rot.s@, p.model_verts()),
{
    let n = p.verts.len();
    let mut out: Vec<SVec2> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == p.verts@.len(),
            i <= n,
            pos.wf_spec(),
            rot.wf_spec(),
            p.wf_spec(),
            out@.len() == i as int,
            forall|k: int|
                0 <= k < i as int ==> (#[trigger] out@[k]).wf_spec(),
            out@.map(|_i: int, v: SVec2| v.model@)
                == world_verts(pos.model@, rot.c@, rot.s@, p.model_verts()).take(i as int),
        decreases n - i,
    {
        let r = rot.apply(&p.verts[i]);
        let wx = r.x.add(&pos.x);
        let wy = r.y.add(&pos.y);
        let wv = verus_linalg::runtime::vec2::RuntimeVec2::new(wx, wy);
        proof {
            let m = p.model_verts();
            let w = world_verts(pos.model@, rot.c@, rot.s@, m);
            assert(w[i as int] == world_vert(pos.model@, rot.c@, rot.s@, m[i as int]));
            assert(w[i as int] == wv.model@);
            assert(w.take(i as int).push(w[i as int]) =~= w.take((i + 1) as int));
            assert(out@.map(|_i: int, v: SVec2| v.model@).push(wv.model@)
                =~= world_verts(pos.model@, rot.c@, rot.s@, p.model_verts()).take((i + 1) as int));
        }
        out.push(wv);
        i = i + 1;
    }
    proof {
        let w = world_verts(pos.model@, rot.c@, rot.s@, p.model_verts());
        assert(w.take(out@.len() as int) =~= w);
    }
    out
}

/// Exact AABB of a vertex list (values eqv to the spec folds; eqv rather
/// than == because min/max picks are non-unique at ties).
pub fn compute_aabb(vs: &Vec<SVec2>) -> (out: Aabb)
    requires
        vs@.len() >= 1,
        forall|i: int|
            0 <= i < vs@.len() ==> (#[trigger] vs@[i]).wf_spec(),
    ensures
        out.wf_spec(),
        out.lo.model@.x.eqv_spec(x_min_upto(vs@.map(|_i: int, v: SVec2| v.model@), vs@.len() as int)),
        out.hi.model@.x.eqv_spec(x_max_upto(vs@.map(|_i: int, v: SVec2| v.model@), vs@.len() as int)),
        out.lo.model@.y.eqv_spec(y_min_upto(vs@.map(|_i: int, v: SVec2| v.model@), vs@.len() as int)),
        out.hi.model@.y.eqv_spec(y_max_upto(vs@.map(|_i: int, v: SVec2| v.model@), vs@.len() as int)),
{
    let n = vs.len();
    let ghost m = vs@.map(|_i: int, v: SVec2| v.model@);
    let mut lo_x = verus_rational::runtime_rational::copy_rational(&vs[0].x);
    let mut hi_x = verus_rational::runtime_rational::copy_rational(&vs[0].x);
    let mut lo_y = verus_rational::runtime_rational::copy_rational(&vs[0].y);
    let mut hi_y = verus_rational::runtime_rational::copy_rational(&vs[0].y);
    proof {
        assert(m.len() == n as int);
        assert(m[0] == vs@[0].model@);
        assert(x_min_upto(m, 1) == m[0].x) by { reveal_with_fuel(x_min_upto, 2); }
        assert(x_max_upto(m, 1) == m[0].x) by { reveal_with_fuel(x_max_upto, 2); }
        assert(y_min_upto(m, 1) == m[0].y) by { reveal_with_fuel(y_min_upto, 2); }
        assert(y_max_upto(m, 1) == m[0].y) by { reveal_with_fuel(y_max_upto, 2); }
        Rational::lemma_eqv_reflexive(lo_x@);
        Rational::lemma_eqv_reflexive(lo_y@);
    }
    let mut i: usize = 1;
    while i < n
        invariant
            n == vs@.len(),
            n >= 1,
            1 <= i <= n,
            m == vs@.map(|_i: int, v: SVec2| v.model@),
            m.len() == n as int,
            forall|k: int|
                0 <= k < n as int ==> (#[trigger] vs@[k]).wf_spec(),
            lo_x.wf_spec(),
            hi_x.wf_spec(),
            lo_y.wf_spec(),
            hi_y.wf_spec(),
            lo_x@.eqv_spec(x_min_upto(m, i as int)),
            hi_x@.eqv_spec(x_max_upto(m, i as int)),
            lo_y@.eqv_spec(y_min_upto(m, i as int)),
            hi_y@.eqv_spec(y_max_upto(m, i as int)),
        decreases n - i,
    {
        proof {
            assert(m[i as int] == vs@[i as int].model@);
            assert(x_min_upto(m, (i + 1) as int)
                == Rational::min_spec(x_min_upto(m, i as int), m[i as int].x))
                by { reveal_with_fuel(x_min_upto, 2); }
            assert(x_max_upto(m, (i + 1) as int)
                == Rational::max_spec(x_max_upto(m, i as int), m[i as int].x))
                by { reveal_with_fuel(x_max_upto, 2); }
            assert(y_min_upto(m, (i + 1) as int)
                == Rational::min_spec(y_min_upto(m, i as int), m[i as int].y))
                by { reveal_with_fuel(y_min_upto, 2); }
            assert(y_max_upto(m, (i + 1) as int)
                == Rational::max_spec(y_max_upto(m, i as int), m[i as int].y))
                by { reveal_with_fuel(y_max_upto, 2); }
        }
        if vs[i].x.le(&lo_x) {
            proof {
                // m[i].x ≤ lo_x@ ≡ fold ⇒ m[i].x ≤ fold ⇒ min(fold, m[i].x) ≡ m[i].x
                assert(vs@[i as int].model@.x.le_spec(lo_x@));
                crate::proofs::shape::lemma_le_eqv_subst_right(
                    m[i as int].x, lo_x@, x_min_upto(m, i as int));
                crate::proofs::broadphase::lemma_min_eqv_right(
                    x_min_upto(m, i as int), m[i as int].x);
                Rational::lemma_eqv_symmetric(
                    Rational::min_spec(x_min_upto(m, i as int), m[i as int].x), m[i as int].x);
            }
            lo_x = verus_rational::runtime_rational::copy_rational(&vs[i].x);
        } else {
            proof {
                // !(m[i].x ≤ lo_x@) ⇒ !(m[i].x ≤ fold) ⇒ fold ≤ m[i].x ⇒ min == fold
                assert(!vs@[i as int].model@.x.le_spec(lo_x@));
                if m[i as int].x.le_spec(x_min_upto(m, i as int)) {
                    Rational::lemma_eqv_symmetric(lo_x@, x_min_upto(m, i as int));
                    crate::proofs::shape::lemma_le_eqv_subst_right(
                        m[i as int].x, x_min_upto(m, i as int), lo_x@);
                    assert(false);
                }
                Rational::lemma_trichotomy(x_min_upto(m, i as int), m[i as int].x);
                if m[i as int].x.lt_spec(x_min_upto(m, i as int)) {
                    Rational::lemma_lt_implies_le(m[i as int].x, x_min_upto(m, i as int));
                    assert(false);
                }
                if x_min_upto(m, i as int).eqv_spec(m[i as int].x) {
                    Rational::lemma_eqv_implies_le(x_min_upto(m, i as int), m[i as int].x);
                } else {
                    Rational::lemma_lt_implies_le(x_min_upto(m, i as int), m[i as int].x);
                }
                assert(Rational::min_spec(x_min_upto(m, i as int), m[i as int].x)
                    == x_min_upto(m, i as int));
            }
        }
        if hi_x.lt(&vs[i].x) {
            proof {
                // fold ≡ hi_x@ < m[i].x ⇒ fold ≤ hi_x@ < m[i].x ⇒ fold < m[i].x
                assert(hi_x@.lt_spec(vs@[i as int].model@.x));
                Rational::lemma_eqv_symmetric(hi_x@, x_max_upto(m, i as int));
                Rational::lemma_eqv_implies_le(x_max_upto(m, i as int), hi_x@);
                Rational::lemma_le_lt_transitive(
                    x_max_upto(m, i as int), hi_x@, m[i as int].x);
                Rational::lemma_lt_implies_le(x_max_upto(m, i as int), m[i as int].x);
                assert(Rational::max_spec(x_max_upto(m, i as int), m[i as int].x)
                    == m[i as int].x);
            }
            hi_x = verus_rational::runtime_rational::copy_rational(&vs[i].x);
        } else {
            proof {
                assert(!hi_x@.lt_spec(vs@[i as int].model@.x));
                if x_max_upto(m, i as int).lt_spec(m[i as int].x) {
                    Rational::lemma_eqv_implies_le(hi_x@, x_max_upto(m, i as int));
                    Rational::lemma_le_lt_transitive(
                        hi_x@, x_max_upto(m, i as int), m[i as int].x);
                    assert(false);
                }
                Rational::lemma_trichotomy(x_max_upto(m, i as int), m[i as int].x);
                if m[i as int].x.lt_spec(x_max_upto(m, i as int)) {
                    Rational::lemma_lt_implies_le(m[i as int].x, x_max_upto(m, i as int));
                } else {
                    Rational::lemma_eqv_symmetric(x_max_upto(m, i as int), m[i as int].x);
                    Rational::lemma_eqv_implies_le(m[i as int].x, x_max_upto(m, i as int));
                }
                crate::proofs::broadphase::lemma_max_eqv_left(
                    x_max_upto(m, i as int), m[i as int].x);
                Rational::lemma_eqv_symmetric(
                    Rational::max_spec(x_max_upto(m, i as int), m[i as int].x),
                    x_max_upto(m, i as int));
                Rational::lemma_eqv_transitive(
                    hi_x@, x_max_upto(m, i as int),
                    Rational::max_spec(x_max_upto(m, i as int), m[i as int].x));
            }
        }
        if vs[i].y.le(&lo_y) {
            proof {
                assert(vs@[i as int].model@.y.le_spec(lo_y@));
                crate::proofs::shape::lemma_le_eqv_subst_right(
                    m[i as int].y, lo_y@, y_min_upto(m, i as int));
                crate::proofs::broadphase::lemma_min_eqv_right(
                    y_min_upto(m, i as int), m[i as int].y);
                Rational::lemma_eqv_symmetric(
                    Rational::min_spec(y_min_upto(m, i as int), m[i as int].y), m[i as int].y);
            }
            lo_y = verus_rational::runtime_rational::copy_rational(&vs[i].y);
        } else {
            proof {
                assert(!vs@[i as int].model@.y.le_spec(lo_y@));
                if m[i as int].y.le_spec(y_min_upto(m, i as int)) {
                    Rational::lemma_eqv_symmetric(lo_y@, y_min_upto(m, i as int));
                    crate::proofs::shape::lemma_le_eqv_subst_right(
                        m[i as int].y, y_min_upto(m, i as int), lo_y@);
                    assert(false);
                }
                Rational::lemma_trichotomy(y_min_upto(m, i as int), m[i as int].y);
                if m[i as int].y.lt_spec(y_min_upto(m, i as int)) {
                    Rational::lemma_lt_implies_le(m[i as int].y, y_min_upto(m, i as int));
                    assert(false);
                }
                if y_min_upto(m, i as int).eqv_spec(m[i as int].y) {
                    Rational::lemma_eqv_implies_le(y_min_upto(m, i as int), m[i as int].y);
                } else {
                    Rational::lemma_lt_implies_le(y_min_upto(m, i as int), m[i as int].y);
                }
                assert(Rational::min_spec(y_min_upto(m, i as int), m[i as int].y)
                    == y_min_upto(m, i as int));
            }
        }
        if hi_y.lt(&vs[i].y) {
            proof {
                assert(hi_y@.lt_spec(vs@[i as int].model@.y));
                Rational::lemma_eqv_symmetric(hi_y@, y_max_upto(m, i as int));
                Rational::lemma_eqv_implies_le(y_max_upto(m, i as int), hi_y@);
                Rational::lemma_le_lt_transitive(
                    y_max_upto(m, i as int), hi_y@, m[i as int].y);
                Rational::lemma_lt_implies_le(y_max_upto(m, i as int), m[i as int].y);
                assert(Rational::max_spec(y_max_upto(m, i as int), m[i as int].y)
                    == m[i as int].y);
            }
            hi_y = verus_rational::runtime_rational::copy_rational(&vs[i].y);
        } else {
            proof {
                assert(!hi_y@.lt_spec(vs@[i as int].model@.y));
                if y_max_upto(m, i as int).lt_spec(m[i as int].y) {
                    Rational::lemma_eqv_implies_le(hi_y@, y_max_upto(m, i as int));
                    Rational::lemma_le_lt_transitive(
                        hi_y@, y_max_upto(m, i as int), m[i as int].y);
                    assert(false);
                }
                Rational::lemma_trichotomy(y_max_upto(m, i as int), m[i as int].y);
                if m[i as int].y.lt_spec(y_max_upto(m, i as int)) {
                    Rational::lemma_lt_implies_le(m[i as int].y, y_max_upto(m, i as int));
                } else {
                    Rational::lemma_eqv_symmetric(y_max_upto(m, i as int), m[i as int].y);
                    Rational::lemma_eqv_implies_le(m[i as int].y, y_max_upto(m, i as int));
                }
                crate::proofs::broadphase::lemma_max_eqv_left(
                    y_max_upto(m, i as int), m[i as int].y);
                Rational::lemma_eqv_symmetric(
                    Rational::max_spec(y_max_upto(m, i as int), m[i as int].y),
                    y_max_upto(m, i as int));
                Rational::lemma_eqv_transitive(
                    hi_y@, y_max_upto(m, i as int),
                    Rational::max_spec(y_max_upto(m, i as int), m[i as int].y));
            }
        }
        i = i + 1;
    }
    let lo = verus_linalg::runtime::vec2::RuntimeVec2::new(lo_x, lo_y);
    let hi = verus_linalg::runtime::vec2::RuntimeVec2::new(hi_x, hi_y);
    proof {
        crate::proofs::broadphase::lemma_x_min_le_max(m, n as int);
        crate::proofs::broadphase::lemma_y_min_le_max(m, n as int);
        // lo ≤ hi through the eqv chain: lo ≡ min ≤ max ≡ hi
        Rational::lemma_eqv_implies_le(lo_x@, x_min_upto(m, n as int));
        Rational::lemma_eqv_symmetric(hi_x@, x_max_upto(m, n as int));
        Rational::lemma_eqv_implies_le(x_max_upto(m, n as int), hi_x@);
        Rational::lemma_le_transitive(
            lo.model@.x, x_min_upto(m, n as int), x_max_upto(m, n as int));
        Rational::lemma_le_transitive(
            lo.model@.x, x_max_upto(m, n as int), hi.model@.x);
        Rational::lemma_eqv_implies_le(lo_y@, y_min_upto(m, n as int));
        Rational::lemma_eqv_symmetric(hi_y@, y_max_upto(m, n as int));
        Rational::lemma_eqv_implies_le(y_max_upto(m, n as int), hi_y@);
        Rational::lemma_le_transitive(
            lo.model@.y, y_min_upto(m, n as int), y_max_upto(m, n as int));
        Rational::lemma_le_transitive(
            lo.model@.y, y_max_upto(m, n as int), hi.model@.y);
    }
    Aabb { lo, hi }
}

/// The canonical overlapping-pair list (E6 lex order).
pub fn broadphase_pairs(aabbs: &Vec<Aabb>) -> (out: Vec<(usize, usize)>)
    requires
        forall|i: int|
            0 <= i < aabbs@.len() ==> (#[trigger] aabbs@[i]).wf_spec(),
    ensures
        out@.map(|_i: int, p: (usize, usize)| (p.0 as int, p.1 as int))
            == broadphase_pairs_spec(aabbs@),
{
    let n = aabbs.len();
    let mut out: Vec<(usize, usize)> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == aabbs@.len(),
            i <= n,
            forall|k: int|
                0 <= k < n as int ==> (#[trigger] aabbs@[k]).wf_spec(),
            out@.map(|_i: int, p: (usize, usize)| (p.0 as int, p.1 as int))
                == filter_pairs_upto(aabbs@, i as int),
        decreases n - i,
    {
        let mut j: usize = i + 1;
        proof {
            assert(filter_pairs_j_upto(aabbs@, i as int, (i + 1) as int)
                == Seq::<(int, int)>::empty())
                by { reveal_with_fuel(filter_pairs_j_upto, 2); }
            assert(out@.map(|_i: int, p: (usize, usize)| (p.0 as int, p.1 as int))
                =~= filter_pairs_upto(aabbs@, i as int).add(Seq::<(int, int)>::empty()));
            assert(out@.map(|_i: int, p: (usize, usize)| (p.0 as int, p.1 as int))
                == filter_pairs_upto(aabbs@, i as int).add(
                    filter_pairs_j_upto(aabbs@, i as int, (i + 1) as int)));
        }
        while j < n
            invariant
                n == aabbs@.len(),
                i < n,
                i + 1 <= j <= n,
                forall|k: int|
                    0 <= k < n as int ==> (#[trigger] aabbs@[k]).wf_spec(),
                out@.map(|_i: int, p: (usize, usize)| (p.0 as int, p.1 as int))
                    == filter_pairs_upto(aabbs@, i as int).add(
                        filter_pairs_j_upto(aabbs@, i as int, j as int)),
            decreases n - j,
        {
            let ox = aabbs[i].lo.x.le(&aabbs[j].hi.x) && aabbs[j].lo.x.le(&aabbs[i].hi.x);
            let oy = aabbs[i].lo.y.le(&aabbs[j].hi.y) && aabbs[j].lo.y.le(&aabbs[i].hi.y);
            let overlaps = ox && oy;
            proof {
                assert(overlaps == pair_overlaps(aabbs@, i as int, j as int));
            }
            if overlaps {
                proof {
                    let mapped = out@.map(|_i: int, p: (usize, usize)| (p.0 as int, p.1 as int));
                    assert(filter_pairs_j_upto(aabbs@, i as int, (j + 1) as int)
                        == filter_pairs_j_upto(aabbs@, i as int, j as int).push(
                            (i as int, j as int)));
                    assert(mapped.push((i as int, j as int))
                        =~= filter_pairs_upto(aabbs@, i as int).add(
                            filter_pairs_j_upto(aabbs@, i as int, j as int).push(
                                (i as int, j as int))));
                    assert(filter_pairs_upto(aabbs@, i as int).add(
                        filter_pairs_j_upto(aabbs@, i as int, j as int).push((i as int, j as int)))
                        =~= filter_pairs_upto(aabbs@, i as int).add(
                            filter_pairs_j_upto(aabbs@, i as int, j as int)).push(
                                (i as int, j as int)));
                    assert(mapped.push((i as int, j as int))
                        =~= filter_pairs_upto(aabbs@, i as int).add(
                            filter_pairs_j_upto(aabbs@, i as int, (j + 1) as int)));
                    assert(mapped.push((i as int, j as int))
                        == filter_pairs_upto(aabbs@, i as int).add(
                            filter_pairs_j_upto(aabbs@, i as int, (j + 1) as int)));
                }
                out.push((i, j));
            } else {
                proof {
                    assert(filter_pairs_j_upto(aabbs@, i as int, (j + 1) as int)
                        == filter_pairs_j_upto(aabbs@, i as int, j as int));
                }
            }
            j = j + 1;
        }
        proof {
            assert(filter_pairs_upto(aabbs@, (i + 1) as int)
                == filter_pairs_upto(aabbs@, i as int).add(
                    filter_pairs_j_upto(aabbs@, i as int, n as int)));
        }
        i = i + 1;
    }
    out
}

} // verus!
