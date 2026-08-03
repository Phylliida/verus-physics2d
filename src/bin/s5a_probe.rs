//! Exec probe for the phys-06a pipeline (pre-S5a sanity):
//! side-2 box dropped from height 1 onto a static side-2 ground box,
//! gravity (0,−10), dt = 1/240. Prints per-step Ok/Reject and the final
//! state. Not part of the verified build.

use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_physics2d::body::Body;
use verus_physics2d::rotq::RotQ;
use verus_physics2d::shape::{Compound, ConvexPoly};
use verus_physics2d::step::{step, RejectReason, StepResult};
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

fn main() {
    let gravity = v2(0, -10);
    let dt = RuntimeRational::from_frac(1, 240);
    let mut w = World::new(gravity, dt, 8);

    let ground = Body::new_static(v2(0, 0), RotQ::identity(), side2_square());
    w.add_body(ground);
    let bx = Body::new_dynamic(
        v2(0, 3),
        RotQ::identity(),
        v2(0, 0),
        ri(0),
        ri(1),
        ri(1),
        side2_square(),
    );
    w.add_body(bx);

    let tol_v = RuntimeRational::from_frac(1, 1000);
    let tol_p = RuntimeRational::from_frac(1, 100);
    let tol_j = ri(0);

    for i in 0..140 {
        let t0 = std::time::Instant::now();
        let r = step(&w, &tol_v, &tol_p, &tol_j);
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        if i >= 100 {
            let b = &w.bodies[1];
            println!(
                "pre {:3}: {:.1}ms  vel=({},{}) om=({},{})",
                i, ms,
                b.vel.y.numerator.magnitude.limbs_le.len(),
                b.vel.y.denominator.limbs_le.len(),
                b.omega.numerator.magnitude.limbs_le.len(),
                b.omega.denominator.limbs_le.len(),
            );
        }
        match r {
            StepResult::Ok(w2, cert) => {
                if i % 20 == 0 || (i > 100 && i < 120) {
                    let y = &w2.bodies[1].pos.y;
                    let vy = &w2.bodies[1].vel.y;
                    println!(
                        "step {:3}: Ok  rows={} box.y=({},{}) box.vy=({},{})",
                        i,
                        cert.rows.len(),
                        y.numerator.magnitude.limbs_le.len(),
                        y.denominator.limbs_le.len(),
                        vy.numerator.magnitude.limbs_le.len(),
                        vy.denominator.limbs_le.len(),
                    );
                }
                w = w2;
            }
            StepResult::Reject(r) => {
                let why = match r {
                    RejectReason::AngleOutOfRange(i) => format!("AngleOutOfRange({})", i),
                    RejectReason::CertFailed => "CertFailed".to_string(),
                    RejectReason::DenomOverflow => "DenomOverflow".to_string(),
                    RejectReason::ManifoldFailed => "ManifoldFailed".to_string(),
                };
                println!("step {:3}: REJECT {}", i, why);
                return;
            }
        }
    }
    println!("done: 140 steps, all Ok");
}
