//! The untrusted solver (phys-06, SPEC §6): row building from manifolds
//! and the PGS velocity sweep. D8: everything here is wf-only — all deep
//! content lives in the certificate checker and its lemmas. A weak solver
//! can only cause Reject, never a wrong accept.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::body::Body;
use crate::broadphase::{Aabb, broadphase_pairs, compute_aabb, world_verts_exec};
use crate::narrowphase::{
    build_manifold, sat_classify, SatResult,
};
use crate::row::{
    apply_impulse_exec, bounds_consistent, contact_row_exec, eff_mass_exec, eff_mass_spec,
    solve_row_lambda_exec, BoundQ, Row,
};
use crate::shape::ConvexPoly;
use crate::types::{copy_svec2, SVec2, Scalar};

verus! {

/// Copy a BoundQ (BigInt witnesses aren't Copy).
pub fn copy_bound(b: &BoundQ) -> (out: BoundQ)
    requires
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out.val() == b.val(),
{
    match b {
        BoundQ::Finite(x) => BoundQ::Finite(verus_rational::runtime_rational::copy_rational(x)),
        BoundQ::Inf => BoundQ::Inf,
    }
}

/// Copy a Row with a fresh lambda (the only field PGS mutates).
pub fn row_with_lambda(r: &Row, lam: &Scalar) -> (out: Row)
    requires
        r.wf_spec(),
        lam.wf_spec(),
    ensures
        out.wf_spec(),
        out.a == r.a,
        out.b == r.b,
        out.jla.model@ == r.jla.model@,
        out.jaa@ == r.jaa@,
        out.jlb.model@ == r.jlb.model@,
        out.jab@ == r.jab@,
        out.lo.val() == r.lo.val(),
        out.hi.val() == r.hi.val(),
        out.bias@ == r.bias@,
        out.lambda@ == lam@,
{
    Row {
        a: r.a,
        b: r.b,
        jla: copy_svec2(&r.jla),
        jaa: verus_rational::runtime_rational::copy_rational(&r.jaa),
        jlb: copy_svec2(&r.jlb),
        jab: verus_rational::runtime_rational::copy_rational(&r.jab),
        lo: copy_bound(&r.lo),
        hi: copy_bound(&r.hi),
        bias: verus_rational::runtime_rational::copy_rational(&r.bias),
        lambda: verus_rational::runtime_rational::copy_rational(lam),
    }
}

/// Copy a Row (PGS sweep works on copies).
pub fn copy_row(r: &Row) -> (out: Row)
    requires
        r.wf_spec(),
    ensures
        out.wf_spec(),
        out.a == r.a,
        out.b == r.b,
        out.jla.model@ == r.jla.model@,
        out.jaa@ == r.jaa@,
        out.jlb.model@ == r.jlb.model@,
        out.jab@ == r.jab@,
        out.lo.val() == r.lo.val(),
        out.hi.val() == r.hi.val(),
        out.bias@ == r.bias@,
        out.lambda@ == r.lambda@,
{
    row_with_lambda(r, &r.lambda)
}

/// World-space AABB of one body (all parts). Solver-side filter input;
/// wf-only (the checker runs its own broadphase, D8).
pub fn body_aabb_exec(b: &Body) -> (out: Aabb)
    requires
        b.wf_spec(),
        b.shape.parts@.len() >= 1,
    ensures
        out.wf_spec(),
{
    let mut all: Vec<SVec2> = Vec::new();
    let mut pi: usize = 0;
    while pi < b.shape.parts.len()
        invariant
            pi <= b.shape.parts@.len(),
            b.wf_spec(),
            forall|k: int| 0 <= k < all@.len() ==> (#[trigger] all@[k]).wf_spec(),
            all@.len() >= 3 * pi as int,
        decreases b.shape.parts.len() - pi,
    {
        let wv = world_verts_exec(&b.pos, &b.rot, &b.shape.parts[pi]);
        let mut k: usize = 0;
        while k < wv.len()
            invariant
                k <= wv@.len(),
                forall|j: int| 0 <= j < wv@.len() ==> (#[trigger] wv@[j]).wf_spec(),
                forall|j: int| 0 <= j < all@.len() ==> (#[trigger] all@[j]).wf_spec(),
                wv@.len() >= 3,
                all@.len() >= 3 * pi as int + k as int,
            decreases wv.len() - k,
        {
            all.push(copy_svec2(&wv[k]));
            k = k + 1;
        }
        pi = pi + 1;
    }
    compute_aabb(&all)
}

/// Row building (SPEC §6 pipeline step 3): broadphase pairs, per part-pair
/// SAT, per Touching a manifold, per contact point a row. mEff computed
/// once per row; rows with mEff ≡ 0 are dropped (SPEC §6). Canonical
/// order: pairs lex (broadphase), then parts, then manifold points lex
/// (E6). Untrusted — the certificate re-checks everything.
pub fn build_rows_exec(bodies: &Vec<Body>, aabbs: &Vec<Aabb>) -> (out: (Vec<Row>, Vec<Scalar>))
    requires
        forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
        forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).shape.parts@.len() >= 1,
        forall|i: int| 0 <= i < aabbs@.len() ==> (#[trigger] aabbs@[i]).wf_spec(),
        aabbs@.len() == bodies@.len(),
    ensures
        out.0@.len() == out.1@.len(),
        forall|k: int|
            0 <= k < out.0@.len() ==> {
                let r = #[trigger] out.0@[k];
                &&& r.wf_spec()
                &&& r.a < bodies@.len()
                &&& r.b < bodies@.len()
                &&& r.a != r.b
                &&& bounds_consistent(r.lo.val(), r.hi.val())
                &&& out.1@[k].wf_spec()
                &&& Rational::from_int_spec(0).lt_spec(out.1@[k]@)
                &&& out.1@[k]@ == eff_mass_spec(
                        r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                        bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                        bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
            },
{
    let pairs = broadphase_pairs(aabbs);
    let mut rows: Vec<Row> = Vec::new();
    let mut meffs: Vec<Scalar> = Vec::new();
    let zero = RuntimeRational::from_int(0);
    let mut p: usize = 0;
    while p < pairs.len()
        invariant
            p <= pairs@.len(),
            rows@.len() == meffs@.len(),
            forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
            forall|i: int|
                0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).shape.parts@.len() >= 1,
            zero.wf_spec(),
            zero@ == Rational::from_int_spec(0),
            forall|k: int|
                0 <= k < rows@.len() ==> {
                    let r = #[trigger] rows@[k];
                    &&& r.wf_spec()
                    &&& r.a < bodies@.len()
                    &&& r.b < bodies@.len()
                    &&& r.a != r.b
                    &&& bounds_consistent(r.lo.val(), r.hi.val())
                    &&& meffs@[k].wf_spec()
                    &&& Rational::from_int_spec(0).lt_spec(meffs@[k]@)
                    &&& meffs@[k]@ == eff_mass_spec(
                            r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                            bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                            bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
                },
        decreases pairs.len() - p,
    {
        let (i, j) = pairs[p];
        if i >= bodies.len() || j >= bodies.len() || i == j {
            p = p + 1;
            continue;
        }
        let mut pi: usize = 0;
        while pi < bodies[i].shape.parts.len()
            invariant
                pi <= bodies@[i as int].shape.parts@.len(),
                rows@.len() == meffs@.len(),
                i < bodies@.len(),
                j < bodies@.len(),
                i != j,
                forall|bi: int| 0 <= bi < bodies@.len() ==> (#[trigger] bodies@[bi]).wf_spec(),
                forall|bi: int|
                    0 <= bi < bodies@.len() ==> (#[trigger] bodies@[bi]).shape.parts@.len() >= 1,
                zero.wf_spec(),
                zero@ == Rational::from_int_spec(0),
                forall|k: int|
                    0 <= k < rows@.len() ==> {
                        let r = #[trigger] rows@[k];
                        &&& r.wf_spec()
                        &&& r.a < bodies@.len()
                        &&& r.b < bodies@.len()
                        &&& r.a != r.b
                        &&& bounds_consistent(r.lo.val(), r.hi.val())
                        &&& meffs@[k].wf_spec()
                        &&& Rational::from_int_spec(0).lt_spec(meffs@[k]@)
                        &&& meffs@[k]@ == eff_mass_spec(
                                r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                                bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                                bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
                    },
            decreases bodies@[i as int].shape.parts@.len() - pi as int,
        {
            let mut pj: usize = 0;
            while pj < bodies[j].shape.parts.len()
                invariant
                    pj <= bodies@[j as int].shape.parts@.len(),
                    pi < bodies@[i as int].shape.parts@.len(),
                    rows@.len() == meffs@.len(),
                    i < bodies@.len(),
                    j < bodies@.len(),
                    i != j,
                    forall|bi: int| 0 <= bi < bodies@.len() ==> (#[trigger] bodies@[bi]).wf_spec(),
                    forall|bi: int|
                        0 <= bi < bodies@.len() ==> (#[trigger] bodies@[bi]).shape.parts@.len()
                            >= 1,
                    zero.wf_spec(),
                    zero@ == Rational::from_int_spec(0),
                    forall|k: int|
                        0 <= k < rows@.len() ==> {
                            let r = #[trigger] rows@[k];
                            &&& r.wf_spec()
                            &&& r.a < bodies@.len()
                            &&& r.b < bodies@.len()
                            &&& r.a != r.b
                            &&& bounds_consistent(r.lo.val(), r.hi.val())
                            &&& meffs@[k].wf_spec()
                            &&& Rational::from_int_spec(0).lt_spec(meffs@[k]@)
                            &&& meffs@[k]@ == eff_mass_spec(
                                    r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                                    bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                                    bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
                        },
                decreases bodies@[j as int].shape.parts@.len() - pj as int,
            {
                let wvi = world_verts_exec(
                    &bodies[i].pos, &bodies[i].rot, &bodies[i].shape.parts[pi]);
                let wvj = world_verts_exec(
                    &bodies[j].pos, &bodies[j].rot, &bodies[j].shape.parts[pj]);
                let pi_opt = ConvexPoly::new_checked(wvi);
                let pj_opt = ConvexPoly::new_checked(wvj);
                if pi_opt.is_some() && pj_opt.is_some() {
                    let poly_i = pi_opt.unwrap();
                    let poly_j = pj_opt.unwrap();
                    let sat = sat_classify(&poly_i, &poly_j);
                    match sat {
                        SatResult::Separated { .. } => {},
                        SatResult::Touching { from_a, edge } => {
                            let man = if from_a {
                                build_manifold(i, j, &poly_i, &poly_j, edge)
                            } else {
                                build_manifold(j, i, &poly_j, &poly_i, edge)
                            };
                            match man {
                                Option::None => {},
                                Option::Some(m) => {
                                    let mut cp: usize = 0;
                                    while cp < m.points.len()
                                        invariant
                                            cp <= m.points@.len(),
                                            m.normal.wf_spec(),
                                            rows@.len() == meffs@.len(),
                                            i < bodies@.len(),
                                            j < bodies@.len(),
                                            i != j,
                                            forall|bi: int|
                                                0 <= bi < bodies@.len()
                                                    ==> (#[trigger] bodies@[bi]).wf_spec(),
                                            zero.wf_spec(),
                                            zero@ == Rational::from_int_spec(0),
                                            forall|k: int|
                                                0 <= k < m.points@.len() ==> {
                                                    let pt = #[trigger] m.points@[k];
                                                    &&& pt.point.wf_spec()
                                                },
                                            forall|k: int|
                                                0 <= k < rows@.len() ==> {
                                                    let r = #[trigger] rows@[k];
                                                    &&& r.wf_spec()
                                                    &&& r.a < bodies@.len()
                                                    &&& r.b < bodies@.len()
                                                    &&& r.a != r.b
                                                    &&& bounds_consistent(r.lo.val(), r.hi.val())
                                                    &&& meffs@[k].wf_spec()
                                                    &&& Rational::from_int_spec(0).lt_spec(
                                                            meffs@[k]@)
                                                    &&& meffs@[k]@ == eff_mass_spec(
                                                            r.jla.model@, r.jaa@, r.jlb.model@,
                                                            r.jab@,
                                                            bodies@[r.a as int].inv_mass@,
                                                            bodies@[r.a as int].inv_inertia@,
                                                            bodies@[r.b as int].inv_mass@,
                                                            bodies@[r.b as int].inv_inertia@)
                                                },
                                        decreases m.points.len() - cp,
                                    {
                                        let pt = &m.points[cp];
                                        let n_row = if from_a {
                                            copy_svec2(&m.normal)
                                        } else {
                                            m.normal.neg()
                                        };
                                        let ra = pt.point.sub(&bodies[i].pos);
                                        let rb = pt.point.sub(&bodies[j].pos);
                                        let r = contact_row_exec(i, j, &n_row, &ra, &rb);
                                        let meff = eff_mass_exec(&r, &bodies[i], &bodies[j]);
                                        let keep = zero.lt(&meff);
                                        if keep {
                                            proof {
                                                assert(r.a == i && r.b == j);
                                                assert(r.lo.val() == Option::Some(
                                                    Rational::from_int_spec(0)));
                                                assert(r.hi is Inf);
                                                assert(meff@ == eff_mass_spec(
                                                    r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                                                    bodies@[i as int].inv_mass@,
                                                    bodies@[i as int].inv_inertia@,
                                                    bodies@[j as int].inv_mass@,
                                                    bodies@[j as int].inv_inertia@));
                                            }
                                            rows.push(r);
                                            meffs.push(meff);
                                        }
                                        cp = cp + 1;
                                    }
                                },
                            }
                        },
                    }
                }
                pj = pj + 1;
            }
            pi = pi + 1;
        }
        p = p + 1;
    }
    (rows, meffs)
}

/// PGS velocity sweep (SPEC §6/§7): `iters` fixed-count iterations over
/// the rows in construction order. wf-only: bodies stay wf, row J/bounds
/// unchanged (only λ mutates), lengths constant. The certificate is the
/// claim — nothing else is proved here.
pub fn pgs_sweep_exec(
    bodies: &Vec<Body>,
    rows: &Vec<Row>,
    meffs: &Vec<Scalar>,
    iters: usize,
) -> (out: (Vec<Body>, Vec<Row>))
    requires
        rows@.len() == meffs@.len(),
        forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
        forall|k: int| 0 <= k < meffs@.len() ==> (#[trigger] meffs@[k]).wf_spec(),
        forall|k: int|
            0 <= k < rows@.len() ==> {
                let r = #[trigger] rows@[k];
                &&& r.wf_spec()
                &&& r.a < bodies@.len()
                &&& r.b < bodies@.len()
                &&& r.a != r.b
                &&& bounds_consistent(r.lo.val(), r.hi.val())
                &&& meffs@[k].wf_spec()
                &&& Rational::from_int_spec(0).lt_spec(meffs@[k]@)
                &&& meffs@[k]@ == eff_mass_spec(
                        r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                        bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                        bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
            },
    ensures
        out.0@.len() == bodies@.len(),
        out.1@.len() == rows@.len(),
        forall|i: int| 0 <= i < out.0@.len() ==> (#[trigger] out.0@[i]).wf_spec(),
        forall|i: int|
            0 <= i < out.0@.len() ==> {
                let b = #[trigger] out.0@[i];
                &&& b.pos.model@ == bodies@[i].pos.model@
                &&& b.rot.c@ == bodies@[i].rot.c@
                &&& b.rot.s@ == bodies@[i].rot.s@
                &&& b.inv_mass@ == bodies@[i].inv_mass@
                &&& b.inv_inertia@ == bodies@[i].inv_inertia@
                &&& b.shape.model_parts() == bodies@[i].shape.model_parts()
            },
        forall|k: int|
            0 <= k < out.1@.len() ==> {
                let r = #[trigger] out.1@[k];
                &&& r.wf_spec()
                &&& r.a == rows@[k].a
                &&& r.b == rows@[k].b
                &&& r.a < bodies@.len()
                &&& r.b < bodies@.len()
                &&& r.jla.model@ == rows@[k].jla.model@
                &&& r.jaa@ == rows@[k].jaa@
                &&& r.jlb.model@ == rows@[k].jlb.model@
                &&& r.jab@ == rows@[k].jab@
                &&& r.lo.val() == rows@[k].lo.val()
                &&& r.hi.val() == rows@[k].hi.val()
                &&& r.bias@ == rows@[k].bias@
            },
{
    let mut bs: Vec<Body> = Vec::new();
    let mut bi: usize = 0;
    while bi < bodies.len()
        invariant
            bi <= bodies@.len(),
            bs@.len() == bi as int,
            forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
            forall|i: int| 0 <= i < bi as int ==> {
                let b = #[trigger] bs@[i];
                &&& b.wf_spec()
                &&& b.pos.model@ == bodies@[i].pos.model@
                &&& b.rot.c@ == bodies@[i].rot.c@
                &&& b.rot.s@ == bodies@[i].rot.s@
                &&& b.inv_mass@ == bodies@[i].inv_mass@
                &&& b.inv_inertia@ == bodies@[i].inv_inertia@
                &&& b.shape.model_parts() == bodies@[i].shape.model_parts()
            },
        decreases bodies.len() - bi,
    {
        bs.push(bodies[bi].copy_body());
        bi = bi + 1;
    }
    let mut rs: Vec<Row> = Vec::new();
    let mut ri: usize = 0;
    while ri < rows.len()
        invariant
            ri <= rows@.len(),
            rs@.len() == ri as int,
            forall|k: int| 0 <= k < rows@.len() ==> (#[trigger] rows@[k]).wf_spec(),
            forall|k: int| 0 <= k < ri as int ==> {
                let r = #[trigger] rs@[k];
                &&& r.wf_spec()
                &&& r.a == rows@[k].a
                &&& r.b == rows@[k].b
                &&& r.jla.model@ == rows@[k].jla.model@
                &&& r.jaa@ == rows@[k].jaa@
                &&& r.jlb.model@ == rows@[k].jlb.model@
                &&& r.jab@ == rows@[k].jab@
                &&& r.lo.val() == rows@[k].lo.val()
                &&& r.hi.val() == rows@[k].hi.val()
                &&& r.bias@ == rows@[k].bias@
            },
        decreases rows.len() - ri,
    {
        rs.push(copy_row(&rows[ri]));
        ri = ri + 1;
    }
    let mut iter: usize = 0;
    while iter < iters
        invariant
            iter <= iters,
            rows@.len() == meffs@.len(),
            bs@.len() == bodies@.len(),
            rs@.len() == rows@.len(),
            forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
            forall|i: int| 0 <= i < bs@.len() ==> {
                let b = #[trigger] bs@[i];
                &&& b.wf_spec()
                &&& b.pos.model@ == bodies@[i].pos.model@
                &&& b.rot.c@ == bodies@[i].rot.c@
                &&& b.rot.s@ == bodies@[i].rot.s@
                &&& b.inv_mass@ == bodies@[i].inv_mass@
                &&& b.inv_inertia@ == bodies@[i].inv_inertia@
                &&& b.shape.model_parts() == bodies@[i].shape.model_parts()
            },
            forall|k: int| 0 <= k < meffs@.len() ==> (#[trigger] meffs@[k]).wf_spec(),
            forall|k: int| 0 <= k < rows@.len() ==> {
                let r = #[trigger] rows@[k];
                &&& r.wf_spec()
                &&& r.a < bodies@.len()
                &&& r.b < bodies@.len()
                &&& bounds_consistent(r.lo.val(), r.hi.val())
                &&& Rational::from_int_spec(0).lt_spec(meffs@[k]@)
                &&& meffs@[k]@ == eff_mass_spec(
                        r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                        bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                        bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
            },
            forall|k: int| 0 <= k < rs@.len() ==> {
                let r = #[trigger] rs@[k];
                &&& r.wf_spec()
                &&& r.a == rows@[k].a
                &&& r.b == rows@[k].b
                &&& r.jla.model@ == rows@[k].jla.model@
                &&& r.jaa@ == rows@[k].jaa@
                &&& r.jlb.model@ == rows@[k].jlb.model@
                &&& r.jab@ == rows@[k].jab@
                &&& r.lo.val() == rows@[k].lo.val()
                &&& r.hi.val() == rows@[k].hi.val()
                &&& r.bias@ == rows@[k].bias@
            },
        decreases iters - iter,
    {
        let mut ri2: usize = 0;
        while ri2 < rs.len()
            invariant
                ri2 <= rs@.len(),
                iter < iters,
                rows@.len() == meffs@.len(),
                bs@.len() == bodies@.len(),
                rs@.len() == rows@.len(),
                forall|i: int| 0 <= i < bodies@.len() ==> (#[trigger] bodies@[i]).wf_spec(),
                forall|i: int| 0 <= i < bs@.len() ==> {
                    let b = #[trigger] bs@[i];
                    &&& b.wf_spec()
                    &&& b.pos.model@ == bodies@[i].pos.model@
                    &&& b.rot.c@ == bodies@[i].rot.c@
                    &&& b.rot.s@ == bodies@[i].rot.s@
                    &&& b.inv_mass@ == bodies@[i].inv_mass@
                    &&& b.inv_inertia@ == bodies@[i].inv_inertia@
                    &&& b.shape.model_parts() == bodies@[i].shape.model_parts()
                },
                forall|k: int| 0 <= k < meffs@.len() ==> (#[trigger] meffs@[k]).wf_spec(),
                forall|k: int| 0 <= k < rows@.len() ==> {
                    let r = #[trigger] rows@[k];
                    &&& r.wf_spec()
                    &&& r.a < bodies@.len()
                    &&& r.b < bodies@.len()
                    &&& bounds_consistent(r.lo.val(), r.hi.val())
                    &&& Rational::from_int_spec(0).lt_spec(meffs@[k]@)
                    &&& meffs@[k]@ == eff_mass_spec(
                            r.jla.model@, r.jaa@, r.jlb.model@, r.jab@,
                            bodies@[r.a as int].inv_mass@, bodies@[r.a as int].inv_inertia@,
                            bodies@[r.b as int].inv_mass@, bodies@[r.b as int].inv_inertia@)
                },
                forall|k: int| 0 <= k < rs@.len() ==> {
                    let r = #[trigger] rs@[k];
                    &&& r.wf_spec()
                    &&& r.a == rows@[k].a
                    &&& r.b == rows@[k].b
                    &&& r.jla.model@ == rows@[k].jla.model@
                    &&& r.jaa@ == rows@[k].jaa@
                    &&& r.jlb.model@ == rows@[k].jlb.model@
                    &&& r.jab@ == rows@[k].jab@
                    &&& r.lo.val() == rows@[k].lo.val()
                    &&& r.hi.val() == rows@[k].hi.val()
                    &&& r.bias@ == rows@[k].bias@
                },
            decreases rs.len() - ri2,
        {
            let r = &rs[ri2];
            let ra_idx = r.a;
            let rb_idx = r.b;
            let lam = solve_row_lambda_exec(r, &bs[ra_idx], &bs[rb_idx], &meffs[ri2]);
            let dlam = lam.sub(&r.lambda);
            let jla = copy_svec2(&r.jla);
            let jaa = verus_rational::runtime_rational::copy_rational(&r.jaa);
            let jlb = copy_svec2(&r.jlb);
            let jab = verus_rational::runtime_rational::copy_rational(&r.jab);
            let new_r = row_with_lambda(r, &lam);
            let new_a = apply_impulse_exec(&bs[ra_idx], &jla, &jaa, &dlam);
            let new_b = apply_impulse_exec(&bs[rb_idx], &jlb, &jab, &dlam);
            proof {
                assert(bs@[ra_idx as int].inv_mass@ == bodies@[ra_idx as int].inv_mass@);
                assert(bs@[ra_idx as int].inv_inertia@ == bodies@[ra_idx as int].inv_inertia@);
                assert(bs@[rb_idx as int].inv_mass@ == bodies@[rb_idx as int].inv_mass@);
                assert(bs@[rb_idx as int].inv_inertia@ == bodies@[rb_idx as int].inv_inertia@);
            }
            bs.set(ra_idx, new_a);
            bs.set(rb_idx, new_b);
            rs.set(ri2, new_r);
            ri2 = ri2 + 1;
        }
        iter = iter + 1;
    }
    (bs, rs)
}

} // verus!
