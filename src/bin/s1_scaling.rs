//! Scaling harness for pre-flight check 2 (SPEC-phys06 §3).
//! Replicates scene_s1's world with a configurable step count and times
//! N = 1, 10, 100, 1000 steps to distinguish a bad per-step constant from
//! witness-size blowup. Not part of the verified build.

use std::time::Instant;

use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_physics2d::body::Body;
use verus_physics2d::rotq::RotQ;
use verus_physics2d::scenes::unit_square_compound;
use verus_physics2d::step::{step_free_flight, StepResult};
use verus_physics2d::world::World;
use verus_rational::RuntimeRational;

fn from_int(x: i64) -> RuntimeRational {
    RuntimeRational::from_int(x)
}

fn from_frac(n: i64, d: i64) -> RuntimeRational {
    RuntimeRational::from_frac(n, d)
}

fn build_world() -> World {
    let gravity = RuntimeVec2::new(from_int(0), from_int(0));
    let dt = from_frac(1, 240);
    let mut w = World::new(gravity, dt, 8);

    let b1 = Body::new_dynamic(
        RuntimeVec2::new(from_int(0), from_int(0)),
        RotQ::identity(),
        RuntimeVec2::new(from_int(1), from_int(2)),
        from_int(0),
        from_int(1),
        from_int(1),
        unit_square_compound(),
    );
    let b2 = Body::new_dynamic(
        RuntimeVec2::new(from_int(3), from_int(-1)),
        RotQ::identity(),
        RuntimeVec2::new(from_int(-1), from_frac(1, 2)),
        from_int(0),
        from_frac(1, 2),
        from_int(1),
        unit_square_compound(),
    );
    w.add_body(b1);
    w.add_body(b2);
    w
}

fn run_steps(n: usize) -> f64 {
    let mut w = build_world();
    let t0 = Instant::now();
    for _ in 0..n {
        match step_free_flight(&w) {
            StepResult::Ok(w2, _cert) => w = w2,
            StepResult::Reject(_) => panic!("unexpected reject"),
        }
    }
    t0.elapsed().as_secs_f64() * 1000.0
}

fn bl(r: &RuntimeRational) -> (usize, usize) {
    (r.numerator.magnitude.limbs_le.len(), r.denominator.limbs_le.len())
}

fn main() {
    let mut w = build_world();
    println!(
        "init: vel.x={:?} pos.x={:?} omega={:?} rot.c={:?} err={:?}",
        bl(&w.bodies[0].vel.x),
        bl(&w.bodies[0].pos.x),
        bl(&w.bodies[0].omega),
        bl(&w.bodies[0].rot.c),
        bl(&w.angle_err[0]),
    );
    for i in 0..15 {
        let t0 = Instant::now();
        match step_free_flight(&w) {
            StepResult::Ok(w2, _cert) => w = w2,
            StepResult::Reject(_) => panic!("unexpected reject"),
        }
        let step_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let t1 = Instant::now();
        for b in w.bodies.iter_mut() {
            b.rot.c = b.rot.c.normalize();
            b.rot.s = b.rot.s.normalize();
            b.pos.x = b.pos.x.normalize();
            b.pos.y = b.pos.y.normalize();
            b.vel.x = b.vel.x.normalize();
            b.vel.y = b.vel.y.normalize();
            b.omega = b.omega.normalize();
        }
        for e in w.angle_err.iter_mut() {
            *e = e.normalize();
        }
        let norm_ms = t1.elapsed().as_secs_f64() * 1000.0;

        println!(
            "step {:3}: {:10.1} ms (normalize {:6.2} ms)  rot.c={:?} err={:?}",
            i,
            step_ms,
            norm_ms,
            bl(&w.bodies[0].rot.c),
            bl(&w.angle_err[0]),
        );
    }
}
