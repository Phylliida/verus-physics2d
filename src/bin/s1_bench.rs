//! Timing harness for pre-flight check 2 (SPEC-phys06 §3).
//! Runs scene_s1 (1000 free-flight steps) compiled, reports wall time.
//! Not part of the verified build — plain exec timing only.

use std::time::Instant;

fn main() {
    for run in 0..3 {
        let t0 = Instant::now();
        let ok = verus_physics2d::scenes::scene_s1();
        let elapsed = t0.elapsed();
        println!(
            "run {}: scene_s1 -> {} in {:.3} ms",
            run,
            ok,
            elapsed.as_secs_f64() * 1000.0
        );
    }
}
