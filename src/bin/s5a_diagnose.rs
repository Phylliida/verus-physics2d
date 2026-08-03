//! Diagnosis for the first contact step (107): advance to its pre-state,
//! replicate the pipeline with per-phase timing and witness sizes.

use std::time::Instant;

use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_physics2d::body::Body;
use verus_physics2d::rotq::RotQ;
use verus_physics2d::shape::{Compound, ConvexPoly};
use verus_physics2d::solver::{body_aabb_exec, build_rows_exec, pgs_sweep_exec};
use verus_physics2d::step::{
    apply_gravity_exec, canonicalize_bodies_exec, step, StepResult,
};
use verus_physics2d::world::World;
use verus_rational::RuntimeRational;

fn ri(x: i64) -> RuntimeRational {
    RuntimeRational::from_int(x)
}

fn v2(x: i64, y: i64) -> RuntimeVec2<RuntimeRational, verus_rational::Rational> {
    RuntimeVec2::new(ri(x), ri(y))
}

fn side2_square() -> Compound {
    let verts = vec![v2(-1, -1), v2(1, -1), v2(1, 1), v2(-1, 1)];
    let poly = ConvexPoly::new_checked(verts).expect("square is convex");
    Compound::new(vec![poly])
}

fn limbs(r: &RuntimeRational) -> (usize, usize) {
    (r.numerator.magnitude.limbs_le.len(), r.denominator.limbs_le.len())
}

fn main() {
    let gravity = v2(0, -10);
    let dt = RuntimeRational::from_frac(1, 240);
    let mut w = World::new(gravity, dt, 8);
    w.add_body(Body::new_static(v2(0, 0), RotQ::identity(), side2_square()));
    w.add_body(Body::new_dynamic(v2(0, 3), RotQ::identity(), v2(0, 0), ri(0), ri(1), ri(1), side2_square()));

    let tol_v = RuntimeRational::from_frac(1, 1000);
    let tol_p = RuntimeRational::from_frac(1, 100);
    let tol_j = ri(0);

    // advance to the failing step's pre-state
    for i in 0..108 {
        match step(&w, &tol_v, &tol_p, &tol_j) {
            StepResult::Ok(w2, _) => w = w2,
            StepResult::Reject(_) => panic!("unexpected reject at {}", i),
        }
    }
    println!("at contact-step pre-state; box vel.y limbs = {:?}", limbs(&w.bodies[1].vel.y));

    let t = Instant::now();
    let gb = apply_gravity_exec(&w);
    println!("gravity: {:.1}ms", t.elapsed().as_secs_f64() * 1000.0);

    let t = Instant::now();
    let aabbs: Vec<_> = (0..gb.len()).map(|i| body_aabb_exec(&gb[i])).collect();
    let (rows, meffs) = build_rows_exec(&gb, &aabbs);
    println!("rows: {:.1}ms, rows built: {}", t.elapsed().as_secs_f64() * 1000.0, rows.len());
    for r in rows.iter() {
        println!("  row a={} b={} jaa={:?} jab={:?}", r.a, r.b, limbs(&r.jaa), limbs(&r.jab));
    }

    for iters in [1usize, 2, 4, 8, 16] {
        let t = Instant::now();
        let (pb, prows) = pgs_sweep_exec(&gb, &rows, &meffs, iters);
        let ms = t.elapsed().as_secs_f64() * 1000.0;
        print!("pgs x{:2}: {:9.1}ms  vy={:?}", iters, ms, limbs(&pb[1].vel.y));
        if !prows.is_empty() {
            print!("  lam0={:?}", limbs(&prows[0].lambda));
        }
        println!();
    }

    let t = Instant::now();
    let (_pb, prows) = pgs_sweep_exec(&gb, &rows, &meffs, 16);
    let mut pb2 = _pb;
    canonicalize_bodies_exec(&mut pb2);
    println!("canonicalize: {:.1}ms", t.elapsed().as_secs_f64() * 1000.0);

    let t = Instant::now();
    let r = verus_physics2d::step::integrate_exec(&w, pb2);
    let ms = t.elapsed().as_secs_f64() * 1000.0;
    let (nb, errs, ts, entries) = match r {
        Ok(t) => t,
        Err(i) => {
            println!("integrate rejected at body {} ({:.1}ms)", i, ms);
            return;
        },
    };
    let mut nb2 = nb;
    canonicalize_bodies_exec(&mut nb2);
    let post = World {
        bodies: nb2,
        joints: Vec::<verus_physics2d::joints::Joint>::new(),
        gravity: verus_physics2d::types::copy_svec2(&w.gravity),
        dt: verus_rational::runtime_rational::copy_rational(&w.dt),
        series_k: w.series_k,
        angle_err: errs,
    };
    let cert = verus_physics2d::certificate::StepCert {
        rows: prows,
        tan_halfs: ts,
        snaps: Vec::new(),
        angle_entries: entries,
    };
    use verus_physics2d::certificate::*;
    println!("c1: {}", check_c1_rows(&w, &post, &cert));
    println!("c2: {}", check_c2_rows(&cert));
    println!("c3: {}", check_c3_rows(&post, &cert, &tol_v));
    println!("c4: {}", check_c4_world(&post, &tol_p));
    println!("c5: {}", check_c5_joints(&post, &tol_j));
    println!("c7: {}", check_c7_energy(&w, &post));
}
