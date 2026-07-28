//! Exact mass properties of convex rational polygons (phys-05a, SPEC §4).
//!
//! All formulas are the classical polygon (Green's theorem) sums over
//! edges, computed with exact raw Rational ops:
//!   area2      = Σ cross(v_i, v_{i+1})            (twice the signed area)
//!   centroid   = (1/(3·area2))·Σ (v_i + v_{i+1})·cross(v_i, v_{i+1})
//!   inertia0   = (1/12)·Σ cross(v_i,v_{i+1})·(v_i·v_i + v_i·v_{i+1}
//!                                               + v_{i+1}·v_{i+1})
//! (sums cyclic, v_n = v_0; centroid written with area2 so 6A = 3·area2).
//!
//! area2 > 0 for ccw convex polygons: the shoelace sum equals the fan sum
//! Σ orient(v_0, v_i, v_{i+1}) (proofs/massprops.rs), and every fan term
//! is strictly positive by the global convexity invariant (E7).
//!
//! Inertia nonnegativity is NOT yet proved in general (the fan
//! decomposition of the inertia sum is future work); concrete closed
//! polygons can still be checked by evaluation (see scenes).

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_rational::{Rational, RuntimeRational};

use crate::shape::{vcross2, ConvexPoly};
use crate::types::{q_pos, Scalar};

verus! {

/// Scalar times vector, raw ops.
pub open spec fn vscale(s: Rational, v: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 { x: s.mul_spec(v.x), y: s.mul_spec(v.y) }
}

/// Dot product, raw ops.
pub open spec fn vdot(a: Vec2<Rational>, b: Vec2<Rational>) -> Rational {
    a.x.mul_spec(b.x).add_spec(a.y.mul_spec(b.y))
}

/// Vec2 zero.
pub open spec fn vzero() -> Vec2<Rational> {
    Vec2 { x: Rational::from_int_spec(0), y: Rational::from_int_spec(0) }
}

/// Shoelace partial sum over edges (0,1)..(i−1,i) — the non-closing part.
pub open spec fn chain_cross_sum(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 0 <= i <= vs.len() - 1
    decreases i
{
    if i <= 0 {
        Rational::from_int_spec(0)
    } else {
        chain_cross_sum(vs, i - 1).add_spec(vcross2(vs[i - 1], vs[i]))
    }
}

/// Twice the signed area: chain sum plus the closing edge (n−1, 0).
pub open spec fn cross_sum(vs: Seq<Vec2<Rational>>) -> Rational
    recommends vs.len() >= 1
{
    chain_cross_sum(vs, vs.len() - 1).add_spec(vcross2(vs[vs.len() - 1], vs[0]))
}

/// Fan partial sum: Σ_{j=1}^{i−1} orient(v_0, v_j, v_{j+1}).
pub open spec fn fan_sum_upto(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 1 <= i <= vs.len() - 1
    decreases i
{
    if i <= 1 {
        Rational::from_int_spec(0)
    } else {
        fan_sum_upto(vs, i - 1).add_spec(crate::shape::orient(vs[0], vs[i - 1], vs[i]))
    }
}

/// The full fan sum (twice the area, fan-triangle form).
pub open spec fn fan_area2(vs: Seq<Vec2<Rational>>) -> Rational
    recommends vs.len() >= 1
{
    fan_sum_upto(vs, vs.len() - 1)
}

/// Centroid numerator partial sum: Σ (v_{j−1} + v_j)·cross(v_{j−1}, v_j).
pub open spec fn centroid_num_chain(vs: Seq<Vec2<Rational>>, i: int) -> Vec2<Rational>
    recommends 0 <= i <= vs.len() - 1
    decreases i
{
    if i <= 0 {
        vzero()
    } else {
        crate::shape::vadd(
            centroid_num_chain(vs, i - 1),
            vscale(vcross2(vs[i - 1], vs[i]), crate::shape::vadd(vs[i - 1], vs[i])),
        )
    }
}

/// Centroid numerator with the closing edge.
pub open spec fn centroid_num(vs: Seq<Vec2<Rational>>) -> Vec2<Rational>
    recommends vs.len() >= 1
{
    crate::shape::vadd(
        centroid_num_chain(vs, vs.len() - 1),
        vscale(vcross2(vs[vs.len() - 1], vs[0]), crate::shape::vadd(vs[vs.len() - 1], vs[0])),
    )
}

/// The exact centroid: (1/(3·area2))·centroid_num (3·area2 = 6A).
pub open spec fn centroid_spec(vs: Seq<Vec2<Rational>>) -> Vec2<Rational>
    recommends vs.len() >= 1, !cross_sum(vs).eqv_spec(Rational::from_int_spec(0))
{
    vscale(
        Rational::from_int_spec(3).mul_spec(cross_sum(vs)).reciprocal_spec(),
        centroid_num(vs),
    )
}

/// Per-edge inertia term: cross(v_i, v_j)·(v_i·v_i + v_i·v_j + v_j·v_j).
pub open spec fn inertia_edge_term(a: Vec2<Rational>, b: Vec2<Rational>) -> Rational {
    vcross2(a, b).mul_spec(
        vdot(a, a).add_spec(vdot(a, b)).add_spec(vdot(b, b)),
    )
}

/// Inertia numerator partial sum over edges (0,1)..(i−1,i).
pub open spec fn inertia_num_chain(vs: Seq<Vec2<Rational>>, i: int) -> Rational
    recommends 0 <= i <= vs.len() - 1
    decreases i
{
    if i <= 0 {
        Rational::from_int_spec(0)
    } else {
        inertia_num_chain(vs, i - 1).add_spec(inertia_edge_term(vs[i - 1], vs[i]))
    }
}

/// Inertia-about-origin numerator (12·I₀) with the closing edge.
pub open spec fn inertia_num(vs: Seq<Vec2<Rational>>) -> Rational
    recommends vs.len() >= 1
{
    inertia_num_chain(vs, vs.len() - 1).add_spec(inertia_edge_term(vs[vs.len() - 1], vs[0]))
}

/// Exact inertia about the origin: I₀ = (1/12)·inertia_num.
pub open spec fn inertia0_spec(vs: Seq<Vec2<Rational>>) -> Rational
    recommends vs.len() >= 1
{
    inertia_num(vs).mul_spec(Rational::from_int_spec(12).reciprocal_spec())
}

} // verus!

verus! {

/// cross of two runtime vectors (model form).
fn vcross2_exec(a: &crate::types::SVec2, b: &crate::types::SVec2) -> (out: Scalar)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == vcross2(a.model@, b.model@),
{
    let t1 = a.x.mul(&b.y);
    let t2 = a.y.mul(&b.x);
    t1.sub(&t2)
}

/// Exact area2 evaluator, with the strict-positivity guarantee (ccw
/// convex invariant via the fan argument in proofs/massprops.rs).
pub fn poly_area2_exec(p: &ConvexPoly) -> (out: Scalar)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cross_sum(p.model_verts()),
        q_pos(out@),
{
    let n = p.verts.len();
    let mut acc = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            n == p.verts@.len(),
            n >= 3,
            i + 1 <= n,
            p.wf_spec(),
            acc.wf_spec(),
            acc@ == chain_cross_sum(p.model_verts(), i as int),
        decreases n - i,
    {
        let c = vcross2_exec(&p.verts[i], &p.verts[i + 1]);
        proof {
            let m = p.model_verts();
            assert(m[i as int] == p.verts@[i as int].model@);
            assert(m[(i + 1) as int] == p.verts@[(i + 1) as int].model@);
            assert(c@ == vcross2(m[i as int], m[(i + 1) as int]));
            assert(chain_cross_sum(m, (i + 1) as int)
                == chain_cross_sum(m, i as int).add_spec(vcross2(m[i as int], m[(i + 1) as int])));
        }
        acc = acc.add(&c);
        i = i + 1;
    }
    let closing = vcross2_exec(&p.verts[n - 1], &p.verts[0]);
    proof {
        let m = p.model_verts();
        assert(m.len() == n as int);
        assert(m[(n - 1) as int] == p.verts@[(n - 1) as int].model@);
        assert(m[0] == p.verts@[0].model@);
        assert(closing@ == vcross2(m[m.len() - 1], m[0]));
        assert(cross_sum(m) == chain_cross_sum(m, m.len() - 1).add_spec(closing@));
        crate::proofs::massprops::lemma_area2_pos(m);
        assert(q_pos(cross_sum(m)));
    }
    acc.add(&closing)
}

/// Exact centroid evaluator.
pub fn centroid_exec(p: &ConvexPoly) -> (out: crate::types::SVec2)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == centroid_spec(p.model_verts()),
{
    let n = p.verts.len();
    let mut accx = RuntimeRational::from_int(0);
    let mut accy = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            n == p.verts@.len(),
            n >= 3,
            i + 1 <= n,
            p.wf_spec(),
            accx.wf_spec(),
            accy.wf_spec(),
            accx@ == centroid_num_chain(p.model_verts(), i as int).x,
            accy@ == centroid_num_chain(p.model_verts(), i as int).y,
        decreases n - i,
    {
        let c = vcross2_exec(&p.verts[i], &p.verts[i + 1]);
        let sx = p.verts[i].x.add(&p.verts[i + 1].x);
        let sy = p.verts[i].y.add(&p.verts[i + 1].y);
        let tx = c.mul(&sx);
        let ty = c.mul(&sy);
        proof {
            let m = p.model_verts();
            let term = vscale(vcross2(m[i as int], m[(i + 1) as int]),
                crate::shape::vadd(m[i as int], m[(i + 1) as int]));
            assert(m[i as int] == p.verts@[i as int].model@);
            assert(m[(i + 1) as int] == p.verts@[(i + 1) as int].model@);
            assert(tx@ == term.x);
            assert(ty@ == term.y);
            assert(centroid_num_chain(m, (i + 1) as int) == crate::shape::vadd(
                centroid_num_chain(m, i as int), term));
            assert(centroid_num_chain(m, (i + 1) as int).x
                == centroid_num_chain(m, i as int).x.add_spec(term.x));
            assert(centroid_num_chain(m, (i + 1) as int).y
                == centroid_num_chain(m, i as int).y.add_spec(term.y));
        }
        accx = accx.add(&tx);
        accy = accy.add(&ty);
        i = i + 1;
    }
    let c = vcross2_exec(&p.verts[n - 1], &p.verts[0]);
    let sx = p.verts[n - 1].x.add(&p.verts[0].x);
    let sy = p.verts[n - 1].y.add(&p.verts[0].y);
    let tx = c.mul(&sx);
    let ty = c.mul(&sy);
    accx = accx.add(&tx);
    accy = accy.add(&ty);
    let area2 = poly_area2_exec(p);
    let three = RuntimeRational::from_int(3);
    let d = three.mul(&area2);
    proof {
        let m = p.model_verts();
        let term = vscale(vcross2(m[m.len() - 1], m[0]),
            crate::shape::vadd(m[m.len() - 1], m[0]));
        assert(m.len() == n as int);
        assert(m[(n - 1) as int] == p.verts@[(n - 1) as int].model@);
        assert(m[0] == p.verts@[0].model@);
        assert(tx@ == term.x);
        assert(ty@ == term.y);
        assert(centroid_num(m) == crate::shape::vadd(
            centroid_num_chain(m, m.len() - 1), term));
        assert(accx@ == centroid_num(m).x);
        assert(accy@ == centroid_num(m).y);
        // divisor: 3·area2 > 0 (raw num form), so div is safe and exact
        crate::proofs::massprops::lemma_area2_pos(m);
        let three_spec = Rational::from_int_spec(3);
        let ds = three_spec.mul_spec(cross_sum(m));
        Rational::lemma_mul_denom_product_int(three_spec, cross_sum(m));
        assert(three_spec.num == 3);
        assert(three_spec.denom() == 1);
        assert(ds.num == 3 * cross_sum(m).num);
        assert(d@ == ds);
        assert(Rational::from_int_spec(0).lt_spec(cross_sum(m)));
        assert(Rational::from_int_spec(0).num == 0);
        assert(Rational::from_int_spec(0).denom() == 1);
        assert(Rational::from_int_spec(0).lt_spec(cross_sum(m)) == (
            Rational::from_int_spec(0).num * cross_sum(m).denom()
                < cross_sum(m).num * Rational::from_int_spec(0).denom()));
        assert(cross_sum(m).num > 0);
        assert(ds.num > 0);
        assert(!ds.eqv_spec(Rational::from_int_spec(0)));
    }
    let one = RuntimeRational::from_int(1);
    let inv = one.div(&d);
    proof {
        let m = p.model_verts();
        let ds = Rational::from_int_spec(3).mul_spec(cross_sum(m));
        assert(one@ == Rational::from_int_spec(1));
        assert(inv@ == one@.div_spec(ds));
        assert(one@.div_spec(ds) == ds.reciprocal_spec());
        assert(inv@ == ds.reciprocal_spec());
        assert(centroid_spec(m) == vscale(ds.reciprocal_spec(), centroid_num(m)));
    }
    let outx = inv.mul(&accx);
    let outy = inv.mul(&accy);
    proof {
        assert(outx@ == centroid_spec(p.model_verts()).x);
        assert(outy@ == centroid_spec(p.model_verts()).y);
    }
    RuntimeVec2::new(outx, outy)
}

/// Exact inertia-about-origin evaluator.
pub fn inertia0_exec(p: &ConvexPoly) -> (out: Scalar)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == inertia0_spec(p.model_verts()),
{
    let n = p.verts.len();
    let mut acc = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            n == p.verts@.len(),
            n >= 3,
            i + 1 <= n,
            p.wf_spec(),
            acc.wf_spec(),
            acc@ == inertia_num_chain(p.model_verts(), i as int),
        decreases n - i,
    {
        let term = inertia_edge_term_exec(&p.verts[i], &p.verts[i + 1]);
        proof {
            let m = p.model_verts();
            assert(m[i as int] == p.verts@[i as int].model@);
            assert(m[(i + 1) as int] == p.verts@[(i + 1) as int].model@);
            assert(term@ == inertia_edge_term(m[i as int], m[(i + 1) as int]));
            assert(inertia_num_chain(m, (i + 1) as int)
                == inertia_num_chain(m, i as int).add_spec(term@));
        }
        acc = acc.add(&term);
        i = i + 1;
    }
    let term = inertia_edge_term_exec(&p.verts[n - 1], &p.verts[0]);
    proof {
        let m = p.model_verts();
        assert(m.len() == n as int);
        assert(m[(n - 1) as int] == p.verts@[(n - 1) as int].model@);
        assert(m[0] == p.verts@[0].model@);
        assert(term@ == inertia_edge_term(m[m.len() - 1], m[0]));
        assert(inertia_num(m) == inertia_num_chain(m, m.len() - 1).add_spec(term@));
        let twelve = Rational::from_int_spec(12);
        assert(twelve.num == 12);
        assert(twelve.num > 0);
        assert(twelve.reciprocal_spec().num == twelve.denom());
        assert(twelve.reciprocal_spec().denom() == twelve.num);
    }
    acc = acc.add(&term);
    let twelve = RuntimeRational::from_int(12);
    proof {
        assert(twelve@ == Rational::from_int_spec(12));
        assert(Rational::from_int_spec(12).num == 12);
        assert(!Rational::from_int_spec(12).eqv_spec(Rational::from_int_spec(0)));
    }
    let one = RuntimeRational::from_int(1);
    let inv = one.div(&twelve);
    let out = acc.mul(&inv);
    proof {
        assert(one@ == Rational::from_int_spec(1));
        assert(Rational::from_int_spec(1).div_spec(Rational::from_int_spec(12))
            == Rational::from_int_spec(12).reciprocal_spec());
        assert(inv@ == Rational::from_int_spec(12).reciprocal_spec());
        assert(acc@ == inertia_num(p.model_verts()));
        assert(out@ == inertia0_spec(p.model_verts()));
    }
    out
}

/// Per-edge inertia term, exec.
fn inertia_edge_term_exec(a: &crate::types::SVec2, b: &crate::types::SVec2) -> (out: Scalar)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == inertia_edge_term(a.model@, b.model@),
{
    let c = vcross2_exec(a, b);
    let aa = vdot_exec(a, a);
    let ab = vdot_exec(a, b);
    let bb = vdot_exec(b, b);
    let s = aa.add(&ab).add(&bb);
    c.mul(&s)
}

/// Dot product, exec.
fn vdot_exec(a: &crate::types::SVec2, b: &crate::types::SVec2) -> (out: Scalar)
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

} // verus!
