//! Momentum conservation for free flight (phys-03): with zero gravity,
//! the symplectic-Euler step preserves total linear and angular momentum
//! EXACTLY (eqv of exact rationals).
//!
//! Per body: vel is unchanged (g ≡ 0) and pos advances along vel, and
//! cross(pos + vel·dt, vel) ≡ cross(pos, vel) because cross(vel, vel) ≡ 0 —
//! the telescoping that makes symplectic Euler momentum-exact here.
//! All component algebra is raw (*_spec) with the canonical bridges from
//! proofs/rational_raw.rs.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::scale;
use verus_rational::Rational;

use crate::body::Body;
use crate::momentum::{ang_contrib, ang_mom, lin_contrib, lin_mom_x, lin_mom_y, mass_of, vcross};
use crate::proofs::rational_raw::{
    lemma_q_add_raw, lemma_q_add_zero_right_raw, lemma_q_mul_raw, lemma_q_mul_zero_right_raw,
    lemma_raw_add_zero_right,
};
use crate::step::{body_dynamic, body_step_rel};
use crate::types::{q_add, q_mul};
use crate::types::Scalar;
use crate::world::World;

verus! {

/// Gravity is zero (componentwise eqv).
pub open spec fn grav_zero(g: Vec2<Rational>) -> bool {
    &&& g.x.eqv_spec(Rational::from_int_spec(0))
    &&& g.y.eqv_spec(Rational::from_int_spec(0))
}

/// vel' ≡ vel componentwise when g ≡ 0.
pub proof fn lemma_step_vel_preserved_x(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
    ensures
        post.vel.model@.x.eqv_spec(pre.vel.model@.x),
{
    if body_dynamic(pre) {
        let vel1 = pre.vel.model@.add(scale(dt, g));
        assert(post.vel.model@ == vel1);
        assert(vel1.x == q_add(pre.vel.model@.x, scale(dt, g).x));
        assert(scale(dt, g).x == q_mul(dt, g.x));
        lemma_q_mul_zero_right_raw(dt, g.x);
        lemma_q_add_zero_right_raw(pre.vel.model@.x, q_mul(dt, g.x));
    } else {
        assert(post.vel.model@ == pre.vel.model@);
        Rational::lemma_eqv_reflexive(post.vel.model@.x);
    }
}

pub proof fn lemma_step_vel_preserved_y(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
    ensures
        post.vel.model@.y.eqv_spec(pre.vel.model@.y),
{
    if body_dynamic(pre) {
        let vel1 = pre.vel.model@.add(scale(dt, g));
        assert(post.vel.model@ == vel1);
        assert(vel1.y == q_add(pre.vel.model@.y, scale(dt, g).y));
        assert(scale(dt, g).y == q_mul(dt, g.y));
        lemma_q_mul_zero_right_raw(dt, g.y);
        lemma_q_add_zero_right_raw(pre.vel.model@.y, q_mul(dt, g.y));
    } else {
        assert(post.vel.model@ == pre.vel.model@);
        Rational::lemma_eqv_reflexive(post.vel.model@.y);
    }
}

/// pos' ≡ pos + vel·dt componentwise when g ≡ 0 (dynamic bodies only).
pub proof fn lemma_step_pos_form_x(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
        body_dynamic(pre),
    ensures
        post.pos.model@.x.eqv_spec(
            pre.pos.model@.x.add_spec(dt.mul_spec(pre.vel.model@.x))),
{
    lemma_step_vel_preserved_x(pre, post, g, dt, t);
    let vel1 = pre.vel.model@.add(scale(dt, g));
    let pos1 = pre.pos.model@.add(scale(dt, vel1));
    assert(post.pos.model@ == pos1);
    assert(pos1.x == q_add(pre.pos.model@.x, scale(dt, vel1).x));
    assert(scale(dt, vel1).x == q_mul(dt, vel1.x));
    // q_mul(dt, vel1.x) ≡ mul_spec(dt, vel1.x) ≡ mul_spec(dt, vel.x)
    lemma_q_mul_raw(dt, vel1.x);
    Rational::lemma_eqv_reflexive(dt);
    Rational::lemma_eqv_mul_congruence(dt, dt, vel1.x, pre.vel.model@.x);
    Rational::lemma_eqv_transitive(
        q_mul(dt, vel1.x), dt.mul_spec(vel1.x), dt.mul_spec(pre.vel.model@.x));
    // q_add(pos.x, ·) ≡ add_spec(pos.x, mul_spec(dt, vel.x))
    lemma_q_add_raw(pre.pos.model@.x, q_mul(dt, vel1.x));
    Rational::lemma_eqv_reflexive(pre.pos.model@.x);
    Rational::lemma_eqv_add_congruence(
        pre.pos.model@.x, pre.pos.model@.x,
        q_mul(dt, vel1.x), dt.mul_spec(pre.vel.model@.x));
    Rational::lemma_eqv_transitive(
        post.pos.model@.x,
        pre.pos.model@.x.add_spec(q_mul(dt, vel1.x)),
        pre.pos.model@.x.add_spec(dt.mul_spec(pre.vel.model@.x)));
}

pub proof fn lemma_step_pos_form_y(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
        body_dynamic(pre),
    ensures
        post.pos.model@.y.eqv_spec(
            pre.pos.model@.y.add_spec(dt.mul_spec(pre.vel.model@.y))),
{
    lemma_step_vel_preserved_y(pre, post, g, dt, t);
    let vel1 = pre.vel.model@.add(scale(dt, g));
    let pos1 = pre.pos.model@.add(scale(dt, vel1));
    assert(post.pos.model@ == pos1);
    assert(pos1.y == q_add(pre.pos.model@.y, scale(dt, vel1).y));
    assert(scale(dt, vel1).y == q_mul(dt, vel1.y));
    lemma_q_mul_raw(dt, vel1.y);
    Rational::lemma_eqv_reflexive(dt);
    Rational::lemma_eqv_mul_congruence(dt, dt, vel1.y, pre.vel.model@.y);
    Rational::lemma_eqv_transitive(
        q_mul(dt, vel1.y), dt.mul_spec(vel1.y), dt.mul_spec(pre.vel.model@.y));
    lemma_q_add_raw(pre.pos.model@.y, q_mul(dt, vel1.y));
    Rational::lemma_eqv_reflexive(pre.pos.model@.y);
    Rational::lemma_eqv_add_congruence(
        pre.pos.model@.y, pre.pos.model@.y,
        q_mul(dt, vel1.y), dt.mul_spec(pre.vel.model@.y));
    Rational::lemma_eqv_transitive(
        post.pos.model@.y,
        pre.pos.model@.y.add_spec(q_mul(dt, vel1.y)),
        pre.pos.model@.y.add_spec(dt.mul_spec(pre.vel.model@.y)));
}

/// The telescoping identity (raw): (px + dt·vx)·vy − (py + dt·vy)·vx
/// ≡ px·vy − py·vx.
pub proof fn lemma_raw_cross_telescope(
    px: Rational, py: Rational, vx: Rational, vy: Rational, dt: Rational,
)
    ensures
        px.add_spec(dt.mul_spec(vx)).mul_spec(vy).sub_spec(
            py.add_spec(dt.mul_spec(vy)).mul_spec(vx))
            .eqv_spec(vcross(Vec2 { x: px, y: py }, Vec2 { x: vx, y: vy })),
{
    let dvx = dt.mul_spec(vx);
    let dvy = dt.mul_spec(vy);
    let lhs1 = px.add_spec(dvx).mul_spec(vy);
    let lhs2 = py.add_spec(dvy).mul_spec(vx);
    // distribute (comm to put the sum on the right, distribute, comm back)
    Rational::lemma_mul_commutative(px.add_spec(dvx), vy);
    Rational::lemma_mul_distributes_over_add(vy, px, dvx);
    Rational::lemma_mul_commutative(vy, px);
    Rational::lemma_mul_commutative(vy, dvx);
    assert(lhs1.eqv_spec(px.mul_spec(vy).add_spec(dvx.mul_spec(vy))));
    Rational::lemma_mul_commutative(py.add_spec(dvy), vx);
    Rational::lemma_mul_distributes_over_add(vx, py, dvy);
    Rational::lemma_mul_commutative(vx, py);
    Rational::lemma_mul_commutative(vx, dvy);
    assert(lhs2.eqv_spec(py.mul_spec(vx).add_spec(dvy.mul_spec(vx))));
    // regroup: (A + X) − (B + Y) ≡ (A − B) + (X − Y)
    Rational::lemma_sub_add_distributes(
        px.mul_spec(vy), dvx.mul_spec(vy), py.mul_spec(vx), dvy.mul_spec(vx));
    // dvx·vy ≡ dt·(vx·vy) and dvy·vx ≡ dt·(vy·vx) == dt·(vx·vy)
    Rational::lemma_mul_associative(dt, vx, vy);
    Rational::lemma_mul_associative(dt, vy, vx);
    Rational::lemma_mul_commutative(vy, vx);
    assert(dvx.mul_spec(vy).eqv_spec(dt.mul_spec(vx.mul_spec(vy))));
    assert(dvy.mul_spec(vx).eqv_spec(dt.mul_spec(vx.mul_spec(vy))));
    // X − Y ≡ 0 (both ≡ dt·(vx·vy))
    Rational::lemma_eqv_symmetric(dvx.mul_spec(vy), dt.mul_spec(vx.mul_spec(vy)));
    Rational::lemma_eqv_transitive(
        dvx.mul_spec(vy), dt.mul_spec(vx.mul_spec(vy)), dvy.mul_spec(vx));
    Rational::lemma_sub_eqv_zero_iff_eqv(dvx.mul_spec(vy), dvy.mul_spec(vx));
    assert(dvx.mul_spec(vy).sub_spec(dvy.mul_spec(vx)).eqv_spec(Rational::from_int_spec(0)));

    // lhs1 − lhs2 ≡ (A + X) − (B + Y) ≡ (A − B) + (X − Y)
    Rational::lemma_sub_add_distributes(
        px.mul_spec(vy), dvx.mul_spec(vy), py.mul_spec(vx), dvy.mul_spec(vx));
    Rational::lemma_eqv_sub_congruence(
        lhs1, px.mul_spec(vy).add_spec(dvx.mul_spec(vy)),
        lhs2, py.mul_spec(vx).add_spec(dvy.mul_spec(vx)));

    // (A − B) + (X − Y) ≡ (A − B) + 0 ≡ A − B
    Rational::lemma_eqv_reflexive(px.mul_spec(vy).sub_spec(py.mul_spec(vx)));
    Rational::lemma_eqv_add_congruence(
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)),
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)),
        dvx.mul_spec(vy).sub_spec(dvy.mul_spec(vx)),
        Rational::from_int_spec(0));
    lemma_raw_add_zero_right(px.mul_spec(vy).sub_spec(py.mul_spec(vx)));

    // full chain
    Rational::lemma_eqv_transitive(
        lhs1.sub_spec(lhs2),
        px.mul_spec(vy).add_spec(dvx.mul_spec(vy)).sub_spec(
            py.mul_spec(vx).add_spec(dvy.mul_spec(vx))),
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)).add_spec(
            dvx.mul_spec(vy).sub_spec(dvy.mul_spec(vx))));
    Rational::lemma_eqv_transitive(
        lhs1.sub_spec(lhs2),
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)).add_spec(
            dvx.mul_spec(vy).sub_spec(dvy.mul_spec(vx))),
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)).add_spec(Rational::from_int_spec(0)));
    Rational::lemma_eqv_transitive(
        lhs1.sub_spec(lhs2),
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)).add_spec(Rational::from_int_spec(0)),
        px.mul_spec(vy).sub_spec(py.mul_spec(vx)));
}

/// cross(pos', vel') ≡ cross(pos, vel) when g ≡ 0.
pub proof fn lemma_step_cross_preserved(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
    ensures
        vcross(post.pos.model@, post.vel.model@).eqv_spec(
            vcross(pre.pos.model@, pre.vel.model@)),
{
    if body_dynamic(pre) {
        lemma_step_vel_preserved_x(pre, post, g, dt, t);
        lemma_step_vel_preserved_y(pre, post, g, dt, t);
        lemma_step_pos_form_x(pre, post, g, dt, t);
        lemma_step_pos_form_y(pre, post, g, dt, t);
        let px = pre.pos.model@.x;
        let py = pre.pos.model@.y;
        let vx = pre.vel.model@.x;
        let vy = pre.vel.model@.y;
        lemma_raw_cross_telescope(px, py, vx, vy, dt);
        // substitute pos'/vel' forms into the telescope identity
        Rational::lemma_eqv_mul_congruence(
            post.pos.model@.x, px.add_spec(dt.mul_spec(vx)), post.vel.model@.y, vy);
        Rational::lemma_eqv_mul_congruence(
            post.pos.model@.y, py.add_spec(dt.mul_spec(vy)), post.vel.model@.x, vx);
        Rational::lemma_eqv_sub_congruence(
            post.pos.model@.x.mul_spec(post.vel.model@.y),
            px.add_spec(dt.mul_spec(vx)).mul_spec(vy),
            post.pos.model@.y.mul_spec(post.vel.model@.x),
            py.add_spec(dt.mul_spec(vy)).mul_spec(vx));
        Rational::lemma_eqv_transitive(
            vcross(post.pos.model@, post.vel.model@),
            px.add_spec(dt.mul_spec(vx)).mul_spec(vy).sub_spec(
                py.add_spec(dt.mul_spec(vy)).mul_spec(vx)),
            vcross(pre.pos.model@, pre.vel.model@));
    } else {
        assert(post.pos.model@ == pre.pos.model@);
        assert(post.vel.model@ == pre.vel.model@);
        Rational::lemma_eqv_reflexive(vcross(post.pos.model@, post.vel.model@));
    }
}

/// Per-body linear-momentum contribution is preserved (g ≡ 0).
pub proof fn lemma_lin_contrib_preserved(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
    ensures
        lin_contrib(post).x.eqv_spec(lin_contrib(pre).x),
        lin_contrib(post).y.eqv_spec(lin_contrib(pre).y),
{
    lemma_step_vel_preserved_x(pre, post, g, dt, t);
    lemma_step_vel_preserved_y(pre, post, g, dt, t);
    if body_dynamic(pre) {
        assert(body_dynamic(post));
        assert(mass_of(post) == mass_of(pre));
        Rational::lemma_eqv_reflexive(mass_of(pre));
        Rational::lemma_eqv_mul_congruence(
            mass_of(post), mass_of(pre), post.vel.model@.x, pre.vel.model@.x);
        Rational::lemma_eqv_mul_congruence(
            mass_of(post), mass_of(pre), post.vel.model@.y, pre.vel.model@.y);
    } else {
        assert(!body_dynamic(post));
        Rational::lemma_eqv_reflexive(lin_contrib(post).x);
        Rational::lemma_eqv_reflexive(lin_contrib(post).y);
    }
}

/// Per-body angular-momentum contribution is preserved (g ≡ 0).
pub proof fn lemma_ang_contrib_preserved(
    pre: Body, post: Body, g: Vec2<Rational>, dt: Rational, t: Rational,
)
    requires
        body_step_rel(pre, post, g, dt, t),
        grav_zero(g),
    ensures
        ang_contrib(post).eqv_spec(ang_contrib(pre)),
{
    lemma_step_cross_preserved(pre, post, g, dt, t);
    if body_dynamic(pre) {
        assert(body_dynamic(post));
        assert(mass_of(post) == mass_of(pre));
        assert(post.omega@ == pre.omega@);
        assert(post.inv_inertia@ == pre.inv_inertia@);
        Rational::lemma_eqv_reflexive(mass_of(pre));
        Rational::lemma_eqv_mul_congruence(
            mass_of(post), mass_of(pre),
            vcross(post.pos.model@, post.vel.model@),
            vcross(pre.pos.model@, pre.vel.model@));
        Rational::lemma_eqv_reflexive(
            if post.inv_inertia@.num != 0 {
                crate::momentum::inertia_of(post).mul_spec(post.omega@)
            } else {
                Rational::from_int_spec(0)
            });
        Rational::lemma_eqv_add_congruence(
            mass_of(post).mul_spec(vcross(post.pos.model@, post.vel.model@)),
            mass_of(pre).mul_spec(vcross(pre.pos.model@, pre.vel.model@)),
            if post.inv_inertia@.num != 0 {
                crate::momentum::inertia_of(post).mul_spec(post.omega@)
            } else {
                Rational::from_int_spec(0)
            },
            if pre.inv_inertia@.num != 0 {
                crate::momentum::inertia_of(pre).mul_spec(pre.omega@)
            } else {
                Rational::from_int_spec(0)
            });
    } else {
        assert(!body_dynamic(post));
        Rational::lemma_eqv_reflexive(ang_contrib(post));
    }
}

// ── fold inductions ──────────────────────────────────────────────────

pub proof fn lemma_lin_mom_x_preserved(
    pre: Seq<Body>, post: Seq<Body>, g: Vec2<Rational>, dt: Rational, ts: Seq<Scalar>, i: nat,
)
    requires
        pre.len() == post.len(),
        ts.len() == pre.len(),
        i <= pre.len(),
        grav_zero(g),
        forall|j: int|
            0 <= j < i ==> body_step_rel(
                #[trigger] pre[j], post[j], g, dt, ts[j]@),
    ensures
        lin_mom_x(post, i).eqv_spec(lin_mom_x(pre, i)),
    decreases i
{
    if i > 0 {
        lemma_lin_mom_x_preserved(pre, post, g, dt, ts, (i - 1) as nat);
        lemma_lin_contrib_preserved(pre[(i - 1) as int], post[(i - 1) as int], g, dt, ts[(i - 1) as int]@);
        assert(lin_mom_x(post, i)
            == lin_mom_x(post, (i - 1) as nat).add_spec(lin_contrib(post[(i - 1) as int]).x)) by {
            reveal_with_fuel(lin_mom_x, 2);
        }
        assert(lin_mom_x(pre, i)
            == lin_mom_x(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).x)) by {
            reveal_with_fuel(lin_mom_x, 2);
        }
        Rational::lemma_eqv_add_congruence(
            lin_mom_x(post, (i - 1) as nat), lin_mom_x(pre, (i - 1) as nat),
            lin_contrib(post[(i - 1) as int]).x, lin_contrib(pre[(i - 1) as int]).x);
        Rational::lemma_eqv_transitive(
            lin_mom_x(post, i),
            lin_mom_x(post, (i - 1) as nat).add_spec(lin_contrib(post[(i - 1) as int]).x),
            lin_mom_x(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).x));
        Rational::lemma_eqv_symmetric(
            lin_mom_x(pre, i),
            lin_mom_x(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).x));
        Rational::lemma_eqv_transitive(
            lin_mom_x(post, i),
            lin_mom_x(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).x),
            lin_mom_x(pre, i));
    } else {
        Rational::lemma_eqv_reflexive(lin_mom_x(post, 0));
    }
}

pub proof fn lemma_lin_mom_y_preserved(
    pre: Seq<Body>, post: Seq<Body>, g: Vec2<Rational>, dt: Rational, ts: Seq<Scalar>, i: nat,
)
    requires
        pre.len() == post.len(),
        ts.len() == pre.len(),
        i <= pre.len(),
        grav_zero(g),
        forall|j: int|
            0 <= j < i ==> body_step_rel(
                #[trigger] pre[j], post[j], g, dt, ts[j]@),
    ensures
        lin_mom_y(post, i).eqv_spec(lin_mom_y(pre, i)),
    decreases i
{
    if i > 0 {
        lemma_lin_mom_y_preserved(pre, post, g, dt, ts, (i - 1) as nat);
        lemma_lin_contrib_preserved(pre[(i - 1) as int], post[(i - 1) as int], g, dt, ts[(i - 1) as int]@);
        assert(lin_mom_y(post, i)
            == lin_mom_y(post, (i - 1) as nat).add_spec(lin_contrib(post[(i - 1) as int]).y)) by {
            reveal_with_fuel(lin_mom_y, 2);
        }
        assert(lin_mom_y(pre, i)
            == lin_mom_y(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).y)) by {
            reveal_with_fuel(lin_mom_y, 2);
        }
        Rational::lemma_eqv_add_congruence(
            lin_mom_y(post, (i - 1) as nat), lin_mom_y(pre, (i - 1) as nat),
            lin_contrib(post[(i - 1) as int]).y, lin_contrib(pre[(i - 1) as int]).y);
        Rational::lemma_eqv_transitive(
            lin_mom_y(post, i),
            lin_mom_y(post, (i - 1) as nat).add_spec(lin_contrib(post[(i - 1) as int]).y),
            lin_mom_y(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).y));
        Rational::lemma_eqv_symmetric(
            lin_mom_y(pre, i),
            lin_mom_y(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).y));
        Rational::lemma_eqv_transitive(
            lin_mom_y(post, i),
            lin_mom_y(pre, (i - 1) as nat).add_spec(lin_contrib(pre[(i - 1) as int]).y),
            lin_mom_y(pre, i));
    } else {
        Rational::lemma_eqv_reflexive(lin_mom_y(post, 0));
    }
}

pub proof fn lemma_ang_mom_preserved(
    pre: Seq<Body>, post: Seq<Body>, g: Vec2<Rational>, dt: Rational, ts: Seq<Scalar>, i: nat,
)
    requires
        pre.len() == post.len(),
        ts.len() == pre.len(),
        i <= pre.len(),
        grav_zero(g),
        forall|j: int|
            0 <= j < i ==> body_step_rel(
                #[trigger] pre[j], post[j], g, dt, ts[j]@),
    ensures
        ang_mom(post, i).eqv_spec(ang_mom(pre, i)),
    decreases i
{
    if i > 0 {
        lemma_ang_mom_preserved(pre, post, g, dt, ts, (i - 1) as nat);
        lemma_ang_contrib_preserved(pre[(i - 1) as int], post[(i - 1) as int], g, dt, ts[(i - 1) as int]@);
        assert(ang_mom(post, i)
            == ang_mom(post, (i - 1) as nat).add_spec(ang_contrib(post[(i - 1) as int]))) by {
            reveal_with_fuel(ang_mom, 2);
        }
        assert(ang_mom(pre, i)
            == ang_mom(pre, (i - 1) as nat).add_spec(ang_contrib(pre[(i - 1) as int]))) by {
            reveal_with_fuel(ang_mom, 2);
        }
        Rational::lemma_eqv_add_congruence(
            ang_mom(post, (i - 1) as nat), ang_mom(pre, (i - 1) as nat),
            ang_contrib(post[(i - 1) as int]), ang_contrib(pre[(i - 1) as int]));
        Rational::lemma_eqv_transitive(
            ang_mom(post, i),
            ang_mom(post, (i - 1) as nat).add_spec(ang_contrib(post[(i - 1) as int])),
            ang_mom(pre, (i - 1) as nat).add_spec(ang_contrib(pre[(i - 1) as int])));
        Rational::lemma_eqv_symmetric(
            ang_mom(pre, i),
            ang_mom(pre, (i - 1) as nat).add_spec(ang_contrib(pre[(i - 1) as int])));
        Rational::lemma_eqv_transitive(
            ang_mom(post, i),
            ang_mom(pre, (i - 1) as nat).add_spec(ang_contrib(pre[(i - 1) as int])),
            ang_mom(pre, i));
    } else {
        Rational::lemma_eqv_reflexive(ang_mom(post, 0));
    }
}

/// Top level: zero-gravity free flight preserves P and L exactly.
pub proof fn lemma_step_preserves_momentum(w: World, w2: World, ts: Seq<Scalar>)
    requires
        w.wf_spec(),
        w2.bodies@.len() == w.bodies@.len(),
        ts.len() == w.bodies@.len(),
        grav_zero(w.gravity.model@),
        forall|i: int|
            0 <= i < w.bodies@.len() ==> body_step_rel(
                w.bodies@[i], #[trigger] w2.bodies@[i], w.gravity.model@, w.dt@, ts[i]@),
    ensures
        lin_mom_x(w2.bodies@, w2.bodies@.len()).eqv_spec(
            lin_mom_x(w.bodies@, w.bodies@.len())),
        lin_mom_y(w2.bodies@, w2.bodies@.len()).eqv_spec(
            lin_mom_y(w.bodies@, w.bodies@.len())),
        ang_mom(w2.bodies@, w2.bodies@.len()).eqv_spec(
            ang_mom(w.bodies@, w.bodies@.len())),
{
    lemma_lin_mom_x_preserved(
        w.bodies@, w2.bodies@, w.gravity.model@, w.dt@, ts, w.bodies@.len());
    lemma_lin_mom_y_preserved(
        w.bodies@, w2.bodies@, w.gravity.model@, w.dt@, ts, w.bodies@.len());
    lemma_ang_mom_preserved(
        w.bodies@, w2.bodies@, w.gravity.model@, w.dt@, ts, w.bodies@.len());
}

} // verus!
