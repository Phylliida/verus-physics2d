//! Convex rational polygons (phys-04, SPEC §4).
//!
//! Design note: we use our own raw-form `orient` instead of verus-geometry's
//! Point2/orient2d. The geometry crate's predicates are trait-op based on
//! its own point types; converting back and forth costs more than it saves,
//! and the raw form plugs directly into this crate's integer
//! cross-multiplication discipline (see proofs/rational_raw.rs).
//!
//! The convexity invariant is the GLOBAL form — every vertex lies on the
//! inner side of every edge (orient ≥ 0, strict for non-edge vertices).
//! This is O(n²) but makes every downstream proof (SAT correctness, area
//! positivity) a direct instantiation. Construction is nlsat-style: an
//! untrusted producer supplies vertices, the checked constructor VERIFIES
//! the invariant at runtime and rejects otherwise. The local-to-global
//! convexity lemma (consecutive positive turns suffice) is future work —
//! generators can always fall back on the global check.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_rational::{Rational, RuntimeRational};

use crate::types::{copy_svec2, SVec2, Scalar};

verus! {

/// 2D cross product (z-component), raw ops.
pub open spec fn vcross2(a: Vec2<Rational>, b: Vec2<Rational>) -> Rational {
    a.x.mul_spec(b.y).sub_spec(a.y.mul_spec(b.x))
}

/// Raw vector subtraction on models.
pub open spec fn vsub(a: Vec2<Rational>, b: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 { x: a.x.sub_spec(b.x), y: a.y.sub_spec(b.y) }
}

/// Raw vector addition on models.
pub open spec fn vadd(a: Vec2<Rational>, b: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 { x: a.x.add_spec(b.x), y: a.y.add_spec(b.y) }
}

/// orient(a, b, c) = cross(b − a, c − a): positive iff c is strictly left
/// of the directed edge a → b.
pub open spec fn orient(a: Vec2<Rational>, b: Vec2<Rational>, c: Vec2<Rational>) -> Rational {
    vcross2(vsub(b, a), vsub(c, a))
}

/// Outward (right-hand) normal of edge a → b for a ccw polygon.
pub open spec fn edge_normal(a: Vec2<Rational>, b: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 { x: b.y.sub_spec(a.y), y: a.x.sub_spec(b.x) }
}

/// dot(n, q − p): signed distance (times |n|) of q along n from p.
pub open spec fn axis_sep(n: Vec2<Rational>, p: Vec2<Rational>, q: Vec2<Rational>) -> Rational {
    n.x.mul_spec(q.x.sub_spec(p.x)).add_spec(n.y.mul_spec(q.y.sub_spec(p.y)))
}

/// min of axis_sep over the tail qs[i..] (recursive min fold).
pub open spec fn min_sep(
    n: Vec2<Rational>,
    p: Vec2<Rational>,
    qs: Seq<Vec2<Rational>>,
    i: int,
) -> Rational
    recommends 0 <= i < qs.len()
    decreases qs.len() - i
{
    if i >= qs.len() - 1 {
        axis_sep(n, p, qs[qs.len() - 1])
    } else {
        Rational::min_spec(axis_sep(n, p, qs[i]), min_sep(n, p, qs, i + 1))
    }
}

/// The global convexity invariant: for every edge i → i+1 (cyclic), every
/// vertex j is on the inner (left) side — strictly unless j IS an endpoint.
pub open spec fn convex_poly_inv(vs: Seq<Vec2<Rational>>) -> bool {
    let n = vs.len();
    &&& n >= 3
    &&& forall|i: int, j: int|
        (0 <= i < n && 0 <= j < n) ==> {
            let o = #[trigger] orient(vs[i], vs[(i + 1) % (n as int)], vs[j]);
            if j == i || j == (i + 1) % (n as int) {
                true
            } else {
                Rational::from_int_spec(0).lt_spec(o)
            }
        }
}

pub struct ConvexPoly {
    pub verts: Vec<SVec2>,
}

impl ConvexPoly {
    pub open spec fn wf_spec(&self) -> bool {
        &&& forall|i: int|
            0 <= i < self.verts@.len() ==> (#[trigger] self.verts@[i]).wf_spec()
        &&& convex_poly_inv(self.verts@.map(|_i: int, v: SVec2| v.model@))
    }

    /// The model vertex sequence.
    pub open spec fn model_verts(&self) -> Seq<Vec2<Rational>> {
        self.verts@.map(|_i: int, v: SVec2| v.model@)
    }

    /// nlsat-style checked construction: verify the global invariant at
    /// runtime, reject otherwise. Untrusted producers stay outside.
    pub fn new_checked(verts: Vec<SVec2>) -> (out: Option<ConvexPoly>)
        requires
            forall|i: int|
                0 <= i < verts@.len() ==> (#[trigger] verts@[i]).wf_spec(),
        ensures
            out is Some ==> {
                let p = out->Some_0;
                &&& p.wf_spec()
                &&& p.model_verts() == verts@.map(|_i: int, v: SVec2| v.model@)
            },
            out is None ==> !convex_poly_inv(verts@.map(|_i: int, v: SVec2| v.model@)),
    {
        let n = verts.len();
        if n < 3 {
            return None;
        }
        let zero = RuntimeRational::from_int(0);
        let mut i: usize = 0;
        while i < n
            invariant
                n == verts@.len(),
                n >= 3,
                i <= n,
                zero.wf_spec(),
                zero@ == Rational::from_int_spec(0),
                forall|k: int|
                    0 <= k < n ==> (#[trigger] verts@[k]).wf_spec(),
                // all edges before i are fully verified
                forall|e: int, j: int|
                    (0 <= e < i as int && 0 <= j < n as int) ==> {
                        let o = #[trigger] orient(
                            verts@[e].model@, verts@[(e + 1) % (n as int)].model@, verts@[j].model@);
                        if j == e || j == (e + 1) % (n as int) {
                            true
                        } else {
                            Rational::from_int_spec(0).lt_spec(o)
                        }
                    },
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    n == verts@.len(),
                    n >= 3,
                    i < n,
                    j <= n,
                    zero.wf_spec(),
                    zero@ == Rational::from_int_spec(0),
                    forall|k: int|
                        0 <= k < n ==> (#[trigger] verts@[k]).wf_spec(),
                    forall|jj: int|
                        0 <= jj < j as int ==> {
                            let o = #[trigger] orient(
                                verts@[i as int].model@,
                                verts@[(i as int + 1) % (n as int)].model@,
                                verts@[jj].model@);
                            if jj == i as int || jj == (i as int + 1) % (n as int) {
                                true
                            } else {
                                Rational::from_int_spec(0).lt_spec(o)
                            }
                        },
                decreases n - j,
            {
                let a = &verts[i];
                let b = &verts[(i + 1) % n];
                let c = &verts[j];
                let o = orient_exec(a, b, c);
                let is_endpoint = j == i || j == (i + 1) % n;
                if !is_endpoint {
                    let pos = zero.lt(&o);
                    if !pos {
                        proof {
                            // the violating witness: edge i, vertex j
                            let m = verts@.map(|_i: int, v: SVec2| v.model@);
                            assert(m.len() == n as int);
                            assert(n as int >= 3);
                            assert(m.len() >= 3);
                            assert(m[i as int] == verts@[i as int].model@);
                            assert(m[(i as int + 1) % (m.len() as int)]
                                == verts@[(i as int + 1) % (n as int)].model@);
                            assert(m[j as int] == verts@[j as int].model@);
                            assert(o@ == orient(
                                m[i as int], m[(i as int + 1) % (m.len() as int)], m[j as int]));
                            assert(j as int != i as int
                                && j as int != (i as int + 1) % (m.len() as int));
                            assert(zero@ == Rational::from_int_spec(0));
                            assert(!Rational::from_int_spec(0).lt_spec(o@));
                            assert(!convex_poly_inv(m));
                        }
                        return None;
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        let p = ConvexPoly { verts };
        proof {
            assert(p.wf_spec()) by {
                assert(p.model_verts() =~= verts@.map(|_i: int, v: SVec2| v.model@));
                assert(convex_poly_inv(p.model_verts())) by {
                    assert forall|e: int, j: int|
                        (0 <= e < p.model_verts().len() && 0 <= j < p.model_verts().len()) implies {
                            let o = #[trigger] orient(
                                p.model_verts()[e], p.model_verts()[(e + 1) % (p.model_verts().len() as int)],
                                p.model_verts()[j]);
                            if j == e || j == (e + 1) % (p.model_verts().len() as int) {
                                true
                            } else {
                                Rational::from_int_spec(0).lt_spec(o)
                            }
                        }
                    by {
                        assert(p.model_verts()[e] == verts@[e].model@);
                        assert(p.model_verts()[(e + 1) % (p.model_verts().len() as int)]
                            == verts@[(e + 1) % (n as int)].model@);
                        assert(p.model_verts()[j] == verts@[j].model@);
                    }
                }
            }
        }
        Some(p)
    }
}

/// Deep copy of a ConvexPoly (BigInt witnesses aren't Copy).
pub fn copy_poly(p: &ConvexPoly) -> (out: ConvexPoly)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out.model_verts() == p.model_verts(),
{
    let mut vs: Vec<SVec2> = Vec::new();
    let mut i: usize = 0;
    while i < p.verts.len()
        invariant
            i <= p.verts@.len(),
            p.wf_spec(),
            vs@.len() == i as int,
            forall|j: int|
                0 <= j < i as int ==> {
                    &&& (#[trigger] vs@[j]).wf_spec()
                    &&& vs@[j].model@ == p.verts@[j].model@
                },
        decreases p.verts.len() - i,
    {
        vs.push(copy_svec2(&p.verts[i]));
        i = i + 1;
    }
    let out = ConvexPoly { verts: vs };
    proof {
        assert(out.model_verts() =~= p.model_verts());
    }
    out
}

/// Compound shape: union semantics over convex parts (SPEC §4). Parts may
/// overlap (double-counts mass properties — compounds SHOULD be disjoint-
/// interior; not an invariant in phase 1).
pub struct Compound {
    pub parts: Vec<ConvexPoly>,
}

impl Compound {
    pub open spec fn wf_spec(&self) -> bool {
        forall|i: int|
            0 <= i < self.parts@.len() ==> (#[trigger] self.parts@[i]).wf_spec()
    }

    /// Model: the sequence of per-part vertex models.
    pub open spec fn model_parts(&self) -> Seq<Seq<Vec2<Rational>>> {
        self.parts@.map(|_i: int, p: ConvexPoly| p.model_verts())
    }

    /// Construct from already-checked convex parts.
    pub fn new(parts: Vec<ConvexPoly>) -> (out: Self)
        requires
            forall|i: int|
                0 <= i < parts@.len() ==> (#[trigger] parts@[i]).wf_spec(),
        ensures
            out.wf_spec(),
            out.parts@ == parts@,
    {
        Compound { parts }
    }

    /// Deep copy.
    pub fn copy_compound(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.model_parts() == self.model_parts(),
    {
        let mut ps: Vec<ConvexPoly> = Vec::new();
        let mut i: usize = 0;
        while i < self.parts.len()
            invariant
                i <= self.parts@.len(),
                self.wf_spec(),
                ps@.len() == i as int,
                forall|j: int|
                    0 <= j < i as int ==> {
                        &&& (#[trigger] ps@[j]).wf_spec()
                        &&& ps@[j].model_verts() == self.parts@[j].model_verts()
                    },
            decreases self.parts.len() - i,
        {
            ps.push(copy_poly(&self.parts[i]));
            i = i + 1;
        }
        let out = Compound { parts: ps };
        proof {
            assert(out.model_parts() =~= self.model_parts());
        }
        out
    }
}

/// orient with exact model: out@ == orient(a.model@, b.model@, c.model@).
pub fn orient_exec(a: &SVec2, b: &SVec2, c: &SVec2) -> (out: Scalar)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == orient(a.model@, b.model@, c.model@),
{
    let bax = b.x.sub(&a.x);
    let bay = b.y.sub(&a.y);
    let cax = c.x.sub(&a.x);
    let cay = c.y.sub(&a.y);
    let t1 = bax.mul(&cay);
    let t2 = bay.mul(&cax);
    t1.sub(&t2)
}

} // verus!
