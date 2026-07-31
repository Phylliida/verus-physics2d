//! Micro-benchmark isolating the S1 slowdown: repeated `x + 0/240`
//! (the zero-gravity velocity update) with and without normalize().
//! Not part of the verified build.

use std::time::Instant;

use verus_rational::RuntimeRational;

fn main() {
    let n = 200;

    // Without normalize: denominators multiply every step.
    let t0 = Instant::now();
    let mut x = RuntimeRational::from_frac(1, 2);
    let zero_dt = RuntimeRational::from_frac(0, 240);
    for _ in 0..n {
        x = x.add(&zero_dt);
    }
    let ms_raw = t0.elapsed().as_secs_f64() * 1000.0;
    println!("raw:       {:8.1} ms for {} adds ({:.2} ms/add)", ms_raw, n, ms_raw / n as f64);

    // With normalize each step: value-preserving reduction.
    let t0 = Instant::now();
    let mut x = RuntimeRational::from_frac(1, 2);
    let zero_dt = RuntimeRational::from_frac(0, 240);
    for _ in 0..n {
        x = x.add(&zero_dt).normalize();
    }
    let ms_norm = t0.elapsed().as_secs_f64() * 1000.0;
    println!("normalize: {:8.1} ms for {} adds ({:.2} ms/add)", ms_norm, n, ms_norm / n as f64);

    // normalize cost on a large unreduced value (denominator ~ 240^n bits).
    let big = RuntimeRational::from_frac(1, 2);
    let mut y = big;
    let zero_dt = RuntimeRational::from_frac(0, 240);
    for _ in 0..n {
        y = y.add(&zero_dt);
    }
    let t0 = Instant::now();
    let _z = y.normalize();
    println!("one normalize on step-{}-sized value: {:8.1} ms", n, t0.elapsed().as_secs_f64() * 1000.0);
}
