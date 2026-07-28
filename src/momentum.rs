//! Momentum: spec folds + exact exec evaluators (phys-03).
//!
//! Linear momentum P = Σ m_i·v_i and angular momentum
//! L = Σ (m_i·(x_i × v_i) + I_i·ω_i), exact rationals, statics contribute
//! zero (they never move). mass = 1/inv_mass for dynamic bodies — never
//! divides by zero (guarded on body_dynamic).

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::body::Body;
use crate::step::body_dynamic;
use crate::types::{SVec2, Scalar};
use crate::world::World;

verus! {

/// m = 1/inv_mass (meaningful for dynamic bodies only).
pub open spec fn mass_of(b: Body) -> Rational {
    Rational::from_int_spec(1).div_spec(b.inv_mass@)
}

/// I = 1/inv_inertia (meaningful for dynamic bodies only).
pub open spec fn inertia_of(b: Body) -> Rational {
    Rational::from_int_spec(1).div_spec(b.inv_inertia@)
}

/// z-component of a × b (raw ops).
pub open spec fn vcross(a: Vec2<Rational>, b: Vec2<Rational>) -> Rational {
    a.x.mul_spec(b.y).sub_spec(a.y.mul_spec(b.x))
}

/// Linear momentum contribution (zero for statics).
pub open spec fn lin_contrib(b: Body) -> Vec2<Rational> {
    if body_dynamic(b) {
        Vec2 {
            x: mass_of(b).mul_spec(b.vel.model@.x),
            y: mass_of(b).mul_spec(b.vel.model@.y),
        }
    } else {
        Vec2 {
            x: Rational::from_int_spec(0),
            y: Rational::from_int_spec(0),
        }
    }
}

/// Angular momentum contribution about the origin (zero for statics;
/// point masses with inv_inertia == 0 contribute no spin term).
pub open spec fn ang_contrib(b: Body) -> Rational {
    if body_dynamic(b) {
        mass_of(b).mul_spec(vcross(b.pos.model@, b.vel.model@)).add_spec(
            if b.inv_inertia@.num != 0 {
                inertia_of(b).mul_spec(b.omega@)
            } else {
                Rational::from_int_spec(0)
            },
        )
    } else {
        Rational::from_int_spec(0)
    }
}

/// Partial sums over the first i bodies (canonical order, E6).
pub open spec fn lin_mom_x(bs: Seq<Body>, i: nat) -> Rational
    decreases i
{
    if i == 0 {
        Rational::from_int_spec(0)
    } else {
        lin_mom_x(bs, (i - 1) as nat).add_spec(lin_contrib(bs[(i - 1) as int]).x)
    }
}

pub open spec fn lin_mom_y(bs: Seq<Body>, i: nat) -> Rational
    decreases i
{
    if i == 0 {
        Rational::from_int_spec(0)
    } else {
        lin_mom_y(bs, (i - 1) as nat).add_spec(lin_contrib(bs[(i - 1) as int]).y)
    }
}

pub open spec fn ang_mom(bs: Seq<Body>, i: nat) -> Rational
    decreases i
{
    if i == 0 {
        Rational::from_int_spec(0)
    } else {
        ang_mom(bs, (i - 1) as nat).add_spec(ang_contrib(bs[(i - 1) as int]))
    }
}

/// Exact linear-momentum evaluator over the whole world.
pub fn lin_mom_exec(w: &World) -> (out: SVec2)
    requires
        w.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@.x == lin_mom_x(w.bodies@, w.bodies@.len()),
        out.model@.y == lin_mom_y(w.bodies@, w.bodies@.len()),
{
    let zero = RuntimeRational::from_int(0);
    let one = RuntimeRational::from_int(1);
    let mut px = RuntimeRational::from_int(0);
    let mut py = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < w.bodies.len()
        invariant
            i <= w.bodies@.len(),
            w.wf_spec(),
            zero.wf_spec(),
            one.wf_spec(),
            zero@ == Rational::from_int_spec(0),
            one@ == Rational::from_int_spec(1),
            px.wf_spec(),
            py.wf_spec(),
            px@ == lin_mom_x(w.bodies@, i as nat),
            py@ == lin_mom_y(w.bodies@, i as nat),
        decreases w.bodies.len() - i,
    {
        let is_dynamic = !w.bodies[i].inv_mass.eq(&zero);
        proof {
            assert(w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0))
                == (w.bodies@[i as int].inv_mass@.num == 0));
            assert(is_dynamic == body_dynamic(w.bodies@[i as int]));
        }
        if is_dynamic {
            proof {
                assert(!w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0)));
            }
            let mass = one.div(&w.bodies[i].inv_mass);
            let cx = mass.mul(&w.bodies[i].vel.x);
            let cy = mass.mul(&w.bodies[i].vel.y);
            let new_px = px.add(&cx);
            let new_py = py.add(&cy);
            proof {
                assert(lin_mom_x(w.bodies@, (i + 1) as nat)
                    == lin_mom_x(w.bodies@, i as nat).add_spec(
                        lin_contrib(w.bodies@[i as int]).x)) by {
                    reveal_with_fuel(lin_mom_x, 2);
                }
                assert(lin_mom_y(w.bodies@, (i + 1) as nat)
                    == lin_mom_y(w.bodies@, i as nat).add_spec(
                        lin_contrib(w.bodies@[i as int]).y)) by {
                    reveal_with_fuel(lin_mom_y, 2);
                }
            }
            px = new_px;
            py = new_py;
        } else {
            // static: zero contribution, momentum fold still advances
            let cx = RuntimeRational::from_int(0);
            let new_px = px.add(&cx);
            let new_py = py.add(&cx);
            proof {
                assert(lin_contrib(w.bodies@[i as int]).x == Rational::from_int_spec(0));
                assert(lin_contrib(w.bodies@[i as int]).y == Rational::from_int_spec(0));
                assert(lin_mom_x(w.bodies@, (i + 1) as nat)
                    == lin_mom_x(w.bodies@, i as nat).add_spec(
                        lin_contrib(w.bodies@[i as int]).x)) by {
                    reveal_with_fuel(lin_mom_x, 2);
                }
                assert(lin_mom_y(w.bodies@, (i + 1) as nat)
                    == lin_mom_y(w.bodies@, i as nat).add_spec(
                        lin_contrib(w.bodies@[i as int]).y)) by {
                    reveal_with_fuel(lin_mom_y, 2);
                }
            }
            px = new_px;
            py = new_py;
        }
        i = i + 1;
    }
    proof {
        assert(px.wf_spec());
        assert(py.wf_spec());
    }
    verus_linalg::runtime::vec2::RuntimeVec2::new(px, py)
}

/// Exact angular-momentum evaluator over the whole world.
pub fn ang_mom_exec(w: &World) -> (out: Scalar)
    requires
        w.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == ang_mom(w.bodies@, w.bodies@.len()),
{
    let zero = RuntimeRational::from_int(0);
    let one = RuntimeRational::from_int(1);
    let mut l = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < w.bodies.len()
        invariant
            i <= w.bodies@.len(),
            w.wf_spec(),
            zero.wf_spec(),
            one.wf_spec(),
            zero@ == Rational::from_int_spec(0),
            one@ == Rational::from_int_spec(1),
            l.wf_spec(),
            l@ == ang_mom(w.bodies@, i as nat),
        decreases w.bodies.len() - i,
    {
        let is_dynamic = !w.bodies[i].inv_mass.eq(&zero);
        proof {
            assert(w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0))
                == (w.bodies@[i as int].inv_mass@.num == 0));
            assert(is_dynamic == body_dynamic(w.bodies@[i as int]));
        }
        if is_dynamic {
            proof {
                assert(!w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0)));
            }
            let mass = one.div(&w.bodies[i].inv_mass);
            let cross_xy = w.bodies[i].pos.x.mul(&w.bodies[i].vel.y);
            let cross_yx = w.bodies[i].pos.y.mul(&w.bodies[i].vel.x);
            let cross = cross_xy.sub(&cross_yx);
            let orbital = mass.mul(&cross);
            let has_inertia = !w.bodies[i].inv_inertia.eq(&zero);
            proof {
                assert(w.bodies@[i as int].inv_inertia@.eqv_spec(Rational::from_int_spec(0))
                    == (w.bodies@[i as int].inv_inertia@.num == 0));
            }
            let spin = if has_inertia {
                proof {
                    assert(!w.bodies@[i as int].inv_inertia@.eqv_spec(
                        Rational::from_int_spec(0)));
                }
                let inertia = one.div(&w.bodies[i].inv_inertia);
                inertia.mul(&w.bodies[i].omega)
            } else {
                RuntimeRational::from_int(0)
            };
            let contrib = orbital.add(&spin);
            let new_l = l.add(&contrib);
            proof {
                assert(ang_mom(w.bodies@, (i + 1) as nat)
                    == ang_mom(w.bodies@, i as nat).add_spec(
                        ang_contrib(w.bodies@[i as int]))) by {
                    reveal_with_fuel(ang_mom, 2);
                }
            }
            l = new_l;
        } else {
            let cz = RuntimeRational::from_int(0);
            let new_l = l.add(&cz);
            proof {
                assert(ang_contrib(w.bodies@[i as int]) == Rational::from_int_spec(0));
                assert(ang_mom(w.bodies@, (i + 1) as nat)
                    == ang_mom(w.bodies@, i as nat).add_spec(
                        ang_contrib(w.bodies@[i as int]))) by {
                    reveal_with_fuel(ang_mom, 2);
                }
            }
            l = new_l;
        }
        i = i + 1;
    }
    l
}

} // verus!
