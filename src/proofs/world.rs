//! World-transform geometry (phys-05d, for the C4 certificate re-check):
//! rigid transforms preserve orient values up to eqv, hence preserve the
//! global convexity invariant. This is the phys-06 C4 workhorse too —
//! the certificate re-runs SAT on world_verts of post bodies.
//!
//! Proof route (all raw *_spec, R1–R5 discipline):
//!   translation cancels in differences (sub_add_distributes),
//!   rotation is linear (vrot(b) − vrot(a) ≡ vrot(b − a)),
//!   cross(vrot u, vrot v) ≡ (c² + s²)·cross(u, v) via bilinearity of
//!   cross and the vperp identities, and c² + s² ≡ 1 (unit norm) closes.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::broadphase::{world_vert, world_verts};
use crate::massprops::vdot;
use crate::proofs::rational_raw::{
    lemma_raw_neg_mul_left, lemma_raw_neg_mul_right, unit_norm_raw,
};
use crate::proofs::row::lemma_add_pair_swap;
use crate::shape::{convex_poly_inv, orient, vadd, vcross2, vsub};

verus! {

/// 90° counter-clockwise rotation: v⊥ = (−v.y, v.x).
pub open spec fn vperp(v: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 { x: v.y.neg_spec(), y: v.x }
}

/// The rotation part of world_vert: R(v) = (c·vx − s·vy, s·vx + c·vy).
pub open spec fn vrot(c: Rational, s: Rational, v: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 {
        x: c.mul_spec(v.x).sub_spec(s.mul_spec(v.y)),
        y: s.mul_spec(v.x).add_spec(c.mul_spec(v.y)),
    }
}

/// Scalar-vector product, raw ops (local mirror of massprops::vscale).
pub open spec fn vscl(t: Rational, v: Vec2<Rational>) -> Vec2<Rational> {
    Vec2 { x: t.mul_spec(v.x), y: t.mul_spec(v.y) }
}

// ── cross congruence and bilinearity ───────────────────────────────────

/// cross respects componentwise eqv.
pub proof fn lemma_vcross2_congr(
    x: Vec2<Rational>,
    x2: Vec2<Rational>,
    z: Vec2<Rational>,
    z2: Vec2<Rational>,
)
    requires
        x.x.eqv_spec(x2.x),
        x.y.eqv_spec(x2.y),
        z.x.eqv_spec(z2.x),
        z.y.eqv_spec(z2.y),
    ensures
        vcross2(x, z).eqv_spec(vcross2(x2, z2)),
{
    Rational::lemma_eqv_mul_congruence(x.x, x2.x, z.y, z2.y);
    Rational::lemma_eqv_mul_congruence(x.y, x2.y, z.x, z2.x);
    Rational::lemma_eqv_sub_congruence(
        x.x.mul_spec(z.y), x2.x.mul_spec(z2.y),
        x.y.mul_spec(z.x), x2.y.mul_spec(z2.x));
}

/// cross(x + y, z) ≡ cross(x, z) + cross(y, z).
pub proof fn lemma_vcross2_add_left(x: Vec2<Rational>, y: Vec2<Rational>, z: Vec2<Rational>)
    ensures
        vcross2(vadd(x, y), z).eqv_spec(
            vcross2(x, z).add_spec(vcross2(y, z))),
{
    // (x.x+y.x)·z.y ≡ x.x·z.y + y.x·z.y  [comm, distrib, comm]
    Rational::lemma_mul_commutative(x.x.add_spec(y.x), z.y);
    Rational::lemma_mul_distributes_over_add(z.y, x.x, y.x);
    Rational::lemma_mul_commutative(z.y, x.x);
    Rational::lemma_mul_commutative(z.y, y.x);
    Rational::lemma_eqv_reflexive(z.y.mul_spec(y.x));
    Rational::lemma_eqv_add_congruence(
        z.y.mul_spec(x.x).add_spec(z.y.mul_spec(y.x)),
        x.x.mul_spec(z.y).add_spec(z.y.mul_spec(y.x)),
        z.y.mul_spec(y.x), y.x.mul_spec(z.y));
    Rational::lemma_eqv_transitive(
        z.y.mul_spec(x.x).add_spec(z.y.mul_spec(y.x)),
        x.x.mul_spec(z.y).add_spec(z.y.mul_spec(y.x)),
        x.x.mul_spec(z.y).add_spec(y.x.mul_spec(z.y)));
    Rational::lemma_eqv_transitive(
        x.x.add_spec(y.x).mul_spec(z.y),
        z.y.mul_spec(x.x.add_spec(y.x)),
        z.y.mul_spec(x.x).add_spec(z.y.mul_spec(y.x)));
    Rational::lemma_eqv_transitive(
        x.x.add_spec(y.x).mul_spec(z.y),
        z.y.mul_spec(x.x).add_spec(z.y.mul_spec(y.x)),
        x.x.mul_spec(z.y).add_spec(y.x.mul_spec(z.y)));
    // (x.y+y.y)·z.x ≡ x.y·z.x + y.y·z.x  [same]
    Rational::lemma_mul_commutative(x.y.add_spec(y.y), z.x);
    Rational::lemma_mul_distributes_over_add(z.x, x.y, y.y);
    Rational::lemma_mul_commutative(z.x, x.y);
    Rational::lemma_mul_commutative(z.x, y.y);
    Rational::lemma_eqv_reflexive(z.x.mul_spec(y.y));
    Rational::lemma_eqv_add_congruence(
        z.x.mul_spec(x.y).add_spec(z.x.mul_spec(y.y)),
        x.y.mul_spec(z.x).add_spec(z.x.mul_spec(y.y)),
        z.x.mul_spec(y.y), y.y.mul_spec(z.x));
    Rational::lemma_eqv_transitive(
        z.x.mul_spec(x.y).add_spec(z.x.mul_spec(y.y)),
        x.y.mul_spec(z.x).add_spec(z.x.mul_spec(y.y)),
        x.y.mul_spec(z.x).add_spec(y.y.mul_spec(z.x)));
    Rational::lemma_eqv_transitive(
        x.y.add_spec(y.y).mul_spec(z.x),
        z.x.mul_spec(x.y.add_spec(y.y)),
        z.x.mul_spec(x.y).add_spec(z.x.mul_spec(y.y)));
    Rational::lemma_eqv_transitive(
        x.y.add_spec(y.y).mul_spec(z.x),
        z.x.mul_spec(x.y).add_spec(z.x.mul_spec(y.y)),
        x.y.mul_spec(z.x).add_spec(y.y.mul_spec(z.x)));
    // (A1 + A2) − (B1 + B2) ≡ (A1 − B1) + (A2 − B2)
    Rational::lemma_eqv_sub_congruence(
        x.x.add_spec(y.x).mul_spec(z.y),
        x.x.mul_spec(z.y).add_spec(y.x.mul_spec(z.y)),
        x.y.add_spec(y.y).mul_spec(z.x),
        x.y.mul_spec(z.x).add_spec(y.y.mul_spec(z.x)));
    Rational::lemma_sub_add_distributes(
        x.x.mul_spec(z.y), y.x.mul_spec(z.y),
        x.y.mul_spec(z.x), y.y.mul_spec(z.x));
    Rational::lemma_eqv_transitive(
        vcross2(vadd(x, y), z),
        x.x.mul_spec(z.y).add_spec(y.x.mul_spec(z.y)).sub_spec(
            x.y.mul_spec(z.x).add_spec(y.y.mul_spec(z.x))),
        vcross2(x, z).add_spec(vcross2(y, z)));
}

/// cross(z, x + y) ≡ cross(z, x) + cross(z, y).
pub proof fn lemma_vcross2_add_right(z: Vec2<Rational>, x: Vec2<Rational>, y: Vec2<Rational>)
    ensures
        vcross2(z, vadd(x, y)).eqv_spec(
            vcross2(z, x).add_spec(vcross2(z, y))),
{
    Rational::lemma_mul_distributes_over_add(z.x, x.y, y.y);
    Rational::lemma_mul_distributes_over_add(z.y, x.x, y.x);
    Rational::lemma_eqv_sub_congruence(
        z.x.mul_spec(x.y.add_spec(y.y)),
        z.x.mul_spec(x.y).add_spec(z.x.mul_spec(y.y)),
        z.y.mul_spec(x.x.add_spec(y.x)),
        z.y.mul_spec(x.x).add_spec(z.y.mul_spec(y.x)));
    Rational::lemma_sub_add_distributes(
        z.x.mul_spec(x.y), z.x.mul_spec(y.y),
        z.y.mul_spec(x.x), z.y.mul_spec(y.x));
    Rational::lemma_eqv_transitive(
        vcross2(z, vadd(x, y)),
        z.x.mul_spec(x.y).add_spec(z.x.mul_spec(y.y)).sub_spec(
            z.y.mul_spec(x.x).add_spec(z.y.mul_spec(y.x))),
        vcross2(z, x).add_spec(vcross2(z, y)));
}

/// cross(t·x, z) ≡ t·cross(x, z).
pub proof fn lemma_vcross2_scale_left(t: Rational, x: Vec2<Rational>, z: Vec2<Rational>)
    ensures
        vcross2(vscl(t, x), z).eqv_spec(t.mul_spec(vcross2(x, z))),
{
    // (t·x.x)·z.y ≡ t·(x.x·z.y); (t·x.y)·z.x ≡ t·(x.y·z.x)  [assoc]
    Rational::lemma_mul_associative(t, x.x, z.y);
    Rational::lemma_mul_associative(t, x.y, z.x);
    Rational::lemma_eqv_sub_congruence(
        t.mul_spec(x.x).mul_spec(z.y), t.mul_spec(x.x.mul_spec(z.y)),
        t.mul_spec(x.y).mul_spec(z.x), t.mul_spec(x.y.mul_spec(z.x)));
    // t·A − t·B ≡ t·(A − B)  [comm + sub_mul_right + comm]
    Rational::lemma_mul_commutative(t, x.x.mul_spec(z.y));
    Rational::lemma_mul_commutative(t, x.y.mul_spec(z.x));
    Rational::lemma_eqv_sub_congruence(
        t.mul_spec(x.x.mul_spec(z.y)), x.x.mul_spec(z.y).mul_spec(t),
        t.mul_spec(x.y.mul_spec(z.x)), x.y.mul_spec(z.x).mul_spec(t));
    Rational::lemma_sub_mul_right(
        x.x.mul_spec(z.y), x.y.mul_spec(z.x), t);
    Rational::lemma_eqv_transitive(
        t.mul_spec(x.x.mul_spec(z.y)).sub_spec(t.mul_spec(x.y.mul_spec(z.x))),
        x.x.mul_spec(z.y).mul_spec(t).sub_spec(x.y.mul_spec(z.x).mul_spec(t)),
        vcross2(x, z).mul_spec(t));
    Rational::lemma_mul_commutative(vcross2(x, z), t);
    Rational::lemma_eqv_transitive(
        t.mul_spec(x.x.mul_spec(z.y)).sub_spec(t.mul_spec(x.y.mul_spec(z.x))),
        vcross2(x, z).mul_spec(t),
        t.mul_spec(vcross2(x, z)));
    Rational::lemma_eqv_transitive(
        vcross2(vscl(t, x), z),
        t.mul_spec(x.x.mul_spec(z.y)).sub_spec(t.mul_spec(x.y.mul_spec(z.x))),
        t.mul_spec(vcross2(x, z)));
}

/// cross(z, t·x) ≡ t·cross(z, x).
pub proof fn lemma_vcross2_scale_right(t: Rational, z: Vec2<Rational>, x: Vec2<Rational>)
    ensures
        vcross2(z, vscl(t, x)).eqv_spec(t.mul_spec(vcross2(z, x))),
{
    // z.x·(t·x.y) ≡ t·(z.x·x.y)  [assoc⁻¹, comm, assoc]
    Rational::lemma_mul_associative(z.x, t, x.y);
    Rational::lemma_eqv_symmetric(
        z.x.mul_spec(t).mul_spec(x.y), z.x.mul_spec(t.mul_spec(x.y)));
    Rational::lemma_mul_commutative(z.x, t);
    Rational::lemma_eqv_reflexive(x.y);
    Rational::lemma_eqv_mul_congruence(z.x.mul_spec(t), t.mul_spec(z.x), x.y, x.y);
    Rational::lemma_mul_associative(t, z.x, x.y);
    Rational::lemma_eqv_transitive(
        z.x.mul_spec(t.mul_spec(x.y)),
        z.x.mul_spec(t).mul_spec(x.y),
        t.mul_spec(z.x).mul_spec(x.y));
    Rational::lemma_eqv_transitive(
        z.x.mul_spec(t.mul_spec(x.y)),
        t.mul_spec(z.x).mul_spec(x.y),
        t.mul_spec(z.x.mul_spec(x.y)));
    // z.y·(t·x.x) ≡ t·(z.y·x.x)  [same]
    Rational::lemma_mul_associative(z.y, t, x.x);
    Rational::lemma_eqv_symmetric(
        z.y.mul_spec(t).mul_spec(x.x), z.y.mul_spec(t.mul_spec(x.x)));
    Rational::lemma_mul_commutative(z.y, t);
    Rational::lemma_eqv_reflexive(x.x);
    Rational::lemma_eqv_mul_congruence(z.y.mul_spec(t), t.mul_spec(z.y), x.x, x.x);
    Rational::lemma_mul_associative(t, z.y, x.x);
    Rational::lemma_eqv_transitive(
        z.y.mul_spec(t.mul_spec(x.x)),
        z.y.mul_spec(t).mul_spec(x.x),
        t.mul_spec(z.y).mul_spec(x.x));
    Rational::lemma_eqv_transitive(
        z.y.mul_spec(t.mul_spec(x.x)),
        t.mul_spec(z.y).mul_spec(x.x),
        t.mul_spec(z.y.mul_spec(x.x)));
    // sub congr + factor (same pattern as scale_left)
    Rational::lemma_eqv_sub_congruence(
        z.x.mul_spec(t.mul_spec(x.y)), t.mul_spec(z.x.mul_spec(x.y)),
        z.y.mul_spec(t.mul_spec(x.x)), t.mul_spec(z.y.mul_spec(x.x)));
    Rational::lemma_mul_commutative(t, z.x.mul_spec(x.y));
    Rational::lemma_mul_commutative(t, z.y.mul_spec(x.x));
    Rational::lemma_eqv_sub_congruence(
        t.mul_spec(z.x.mul_spec(x.y)), z.x.mul_spec(x.y).mul_spec(t),
        t.mul_spec(z.y.mul_spec(x.x)), z.y.mul_spec(x.x).mul_spec(t));
    Rational::lemma_sub_mul_right(
        z.x.mul_spec(x.y), z.y.mul_spec(x.x), t);
    Rational::lemma_eqv_transitive(
        t.mul_spec(z.x.mul_spec(x.y)).sub_spec(t.mul_spec(z.y.mul_spec(x.x))),
        z.x.mul_spec(x.y).mul_spec(t).sub_spec(z.y.mul_spec(x.x).mul_spec(t)),
        vcross2(z, x).mul_spec(t));
    Rational::lemma_mul_commutative(vcross2(z, x), t);
    Rational::lemma_eqv_transitive(
        t.mul_spec(z.x.mul_spec(x.y)).sub_spec(t.mul_spec(z.y.mul_spec(x.x))),
        vcross2(z, x).mul_spec(t),
        t.mul_spec(vcross2(z, x)));
    Rational::lemma_eqv_transitive(
        vcross2(z, vscl(t, x)),
        t.mul_spec(z.x.mul_spec(x.y)).sub_spec(t.mul_spec(z.y.mul_spec(x.x))),
        t.mul_spec(vcross2(z, x)));
}

// ── vperp identities (all structural) ──────────────────────────────────

/// cross(u, v⊥) == dot(u, v) (structural).
pub proof fn lemma_vcross2_vperp_right(u: Vec2<Rational>, v: Vec2<Rational>)
    ensures
        vcross2(u, vperp(v)) == vdot(u, v),
{
    lemma_raw_neg_mul_right(u.y, v.y);
    assert(u.y.mul_spec(v.y.neg_spec()) == u.y.mul_spec(v.y).neg_spec());
    Rational::lemma_sub_neg(u.x.mul_spec(v.x), u.y.mul_spec(v.y));
}

/// cross(u⊥, v) ≡ −dot(u, v).
pub proof fn lemma_vcross2_vperp_left(u: Vec2<Rational>, v: Vec2<Rational>)
    ensures
        vcross2(vperp(u), v).eqv_spec(vdot(u, v).neg_spec()),
{
    lemma_raw_neg_mul_left(u.y, v.y);
    assert(u.y.neg_spec().mul_spec(v.y) == u.y.mul_spec(v.y).neg_spec());
    // −(uy·vy) − (ux·vx) == −((uy·vy) + (ux·vx))  [neg_add reversed]
    Rational::lemma_neg_add(u.y.mul_spec(v.y), u.x.mul_spec(v.x));
    assert(u.y.mul_spec(v.y).neg_spec().sub_spec(u.x.mul_spec(v.x))
        == u.y.mul_spec(v.y).add_spec(u.x.mul_spec(v.x)).neg_spec());
    // ≡ −(ux·vx + uy·vy) = −dot  [add comm + neg congr]
    Rational::lemma_add_commutative(u.y.mul_spec(v.y), u.x.mul_spec(v.x));
    Rational::lemma_eqv_neg_congruence(
        u.y.mul_spec(v.y).add_spec(u.x.mul_spec(v.x)),
        u.x.mul_spec(v.x).add_spec(u.y.mul_spec(v.y)));
    Rational::lemma_eqv_transitive(
        vcross2(vperp(u), v),
        u.y.mul_spec(v.y).add_spec(u.x.mul_spec(v.x)).neg_spec(),
        vdot(u, v).neg_spec());
}

/// cross(u⊥, v⊥) == cross(u, v) (structural).
pub proof fn lemma_vcross2_vperp_both(u: Vec2<Rational>, v: Vec2<Rational>)
    ensures
        vcross2(vperp(u), vperp(v)) == vcross2(u, v),
{
    lemma_raw_neg_mul_left(u.y, v.x);
    lemma_raw_neg_mul_right(u.x, v.y);
    assert(u.y.neg_spec().mul_spec(v.x) == u.y.mul_spec(v.x).neg_spec());
    assert(u.x.mul_spec(v.y.neg_spec()) == u.x.mul_spec(v.y).neg_spec());
    // (−P) − (−Q) == (P − Q).neg ... then (uy·vx − ux·vy).neg == cross
    Rational::lemma_sub_neg_both(u.y.mul_spec(v.x), u.x.mul_spec(v.y));
    assert(vcross2(vperp(u), vperp(v))
        == u.y.mul_spec(v.x).sub_spec(u.x.mul_spec(v.y)).neg_spec());
    Rational::lemma_neg_sub(u.y.mul_spec(v.x), u.x.mul_spec(v.y));
}

// ── translation and rotation linearity ─────────────────────────────────

/// (rb.x + px) − (ra.x + px) ≡ rb.x − ra.x (translation cancels).
pub proof fn lemma_trans_sub_cancel(px: Rational, rbx: Rational, rax: Rational)
    ensures
        rbx.add_spec(px).sub_spec(rax.add_spec(px)).eqv_spec(rbx.sub_spec(rax)),
{
    // (a+b)−(c+d) ≡ (a−c)+(b−d)
    Rational::lemma_sub_add_distributes(rbx, px, rax, px);
    Rational::lemma_sub_self(px);
    Rational::lemma_eqv_reflexive(rbx.sub_spec(rax));
    Rational::lemma_eqv_add_congruence(
        rbx.sub_spec(rax), rbx.sub_spec(rax),
        px.sub_spec(px), Rational::from_int_spec(0));
    Rational::lemma_add_zero_identity(rbx.sub_spec(rax));
    Rational::lemma_eqv_reflexive(rbx.sub_spec(rax).add_spec(Rational::from_int_spec(0)));
    Rational::lemma_eqv_transitive(
        rbx.sub_spec(rax).add_spec(px.sub_spec(px)),
        rbx.sub_spec(rax).add_spec(Rational::from_int_spec(0)),
        rbx.sub_spec(rax));
    Rational::lemma_eqv_transitive(
        rbx.add_spec(px).sub_spec(rax.add_spec(px)),
        rbx.sub_spec(rax).add_spec(px.sub_spec(px)),
        rbx.sub_spec(rax));
}

/// Rotation is linear: vrot(b) − vrot(a) ≡vec vrot(b − a), x component.
pub proof fn lemma_vrot_sub_x(c: Rational, s: Rational, b: Vec2<Rational>, a: Vec2<Rational>)
    ensures
        vrot(c, s, b).x.sub_spec(vrot(c, s, a).x).eqv_spec(vrot(c, s, vsub(b, a)).x),
{
    let lhs = c.mul_spec(b.x).sub_spec(s.mul_spec(b.y)).sub_spec(
        c.mul_spec(a.x).sub_spec(s.mul_spec(a.y)));
    // (A + B) − (C + D) form with B = −(s·by), D = −(s·ay)
    Rational::lemma_sub_add_distributes(
        c.mul_spec(b.x), s.mul_spec(b.y).neg_spec(),
        c.mul_spec(a.x), s.mul_spec(a.y).neg_spec());
    assert(lhs.eqv_spec(
        c.mul_spec(b.x).sub_spec(c.mul_spec(a.x)).add_spec(
            s.mul_spec(b.y).neg_spec().sub_spec(s.mul_spec(a.y).neg_spec()))));
    // c·bx − c·ax ≡ c·(bx − ax)  [comm ×2, sub_mul_right, comm]
    Rational::lemma_mul_commutative(c, b.x);
    Rational::lemma_mul_commutative(c, a.x);
    Rational::lemma_eqv_sub_congruence(
        c.mul_spec(b.x), b.x.mul_spec(c),
        c.mul_spec(a.x), a.x.mul_spec(c));
    Rational::lemma_sub_mul_right(b.x, a.x, c);
    Rational::lemma_eqv_transitive(
        c.mul_spec(b.x).sub_spec(c.mul_spec(a.x)),
        b.x.mul_spec(c).sub_spec(a.x.mul_spec(c)),
        b.x.sub_spec(a.x).mul_spec(c));
    Rational::lemma_mul_commutative(b.x.sub_spec(a.x), c);
    Rational::lemma_eqv_transitive(
        c.mul_spec(b.x).sub_spec(c.mul_spec(a.x)),
        b.x.sub_spec(a.x).mul_spec(c),
        c.mul_spec(b.x.sub_spec(a.x)));
    // (−s·by) − (−s·ay) == (s·by − s·ay).neg  [sub_neg_both structural]
    Rational::lemma_sub_neg_both(s.mul_spec(b.y), s.mul_spec(a.y));
    // s·by − s·ay ≡ s·(by−ay)  [same factor chain]
    Rational::lemma_mul_commutative(s, b.y);
    Rational::lemma_mul_commutative(s, a.y);
    Rational::lemma_eqv_sub_congruence(
        s.mul_spec(b.y), b.y.mul_spec(s),
        s.mul_spec(a.y), a.y.mul_spec(s));
    Rational::lemma_sub_mul_right(b.y, a.y, s);
    Rational::lemma_eqv_transitive(
        s.mul_spec(b.y).sub_spec(s.mul_spec(a.y)),
        b.y.mul_spec(s).sub_spec(a.y.mul_spec(s)),
        b.y.sub_spec(a.y).mul_spec(s));
    Rational::lemma_mul_commutative(b.y.sub_spec(a.y), s);
    Rational::lemma_eqv_transitive(
        s.mul_spec(b.y).sub_spec(s.mul_spec(a.y)),
        b.y.sub_spec(a.y).mul_spec(s),
        s.mul_spec(b.y.sub_spec(a.y)));
    Rational::lemma_eqv_neg_congruence(
        s.mul_spec(b.y).sub_spec(s.mul_spec(a.y)),
        s.mul_spec(b.y.sub_spec(a.y)));
    // add congruence closes
    Rational::lemma_eqv_add_congruence(
        c.mul_spec(b.x).sub_spec(c.mul_spec(a.x)),
        c.mul_spec(b.x.sub_spec(a.x)),
        s.mul_spec(b.y).neg_spec().sub_spec(s.mul_spec(a.y).neg_spec()),
        s.mul_spec(b.y.sub_spec(a.y)).neg_spec());
    Rational::lemma_eqv_transitive(
        lhs,
        c.mul_spec(b.x).sub_spec(c.mul_spec(a.x)).add_spec(
            s.mul_spec(b.y).neg_spec().sub_spec(s.mul_spec(a.y).neg_spec())),
        c.mul_spec(b.x.sub_spec(a.x)).add_spec(s.mul_spec(b.y.sub_spec(a.y)).neg_spec()));
    assert(c.mul_spec(b.x.sub_spec(a.x)).add_spec(s.mul_spec(b.y.sub_spec(a.y)).neg_spec())
        == vrot(c, s, vsub(b, a)).x);
}

/// Rotation is linear: vrot(b) − vrot(a) ≡vec vrot(b − a), y component.
pub proof fn lemma_vrot_sub_y(c: Rational, s: Rational, b: Vec2<Rational>, a: Vec2<Rational>)
    ensures
        vrot(c, s, b).y.sub_spec(vrot(c, s, a).y).eqv_spec(vrot(c, s, vsub(b, a)).y),
{
    let lhs = s.mul_spec(b.x).add_spec(c.mul_spec(b.y)).sub_spec(
        s.mul_spec(a.x).add_spec(c.mul_spec(a.y)));
    Rational::lemma_sub_add_distributes(
        s.mul_spec(b.x), c.mul_spec(b.y),
        s.mul_spec(a.x), c.mul_spec(a.y));
    assert(lhs.eqv_spec(
        s.mul_spec(b.x).sub_spec(s.mul_spec(a.x)).add_spec(
            c.mul_spec(b.y).sub_spec(c.mul_spec(a.y)))));
    // s·bx − s·ax ≡ s·(bx − ax)
    Rational::lemma_mul_commutative(s, b.x);
    Rational::lemma_mul_commutative(s, a.x);
    Rational::lemma_eqv_sub_congruence(
        s.mul_spec(b.x), b.x.mul_spec(s),
        s.mul_spec(a.x), a.x.mul_spec(s));
    Rational::lemma_sub_mul_right(b.x, a.x, s);
    Rational::lemma_eqv_transitive(
        s.mul_spec(b.x).sub_spec(s.mul_spec(a.x)),
        b.x.mul_spec(s).sub_spec(a.x.mul_spec(s)),
        b.x.sub_spec(a.x).mul_spec(s));
    Rational::lemma_mul_commutative(b.x.sub_spec(a.x), s);
    Rational::lemma_eqv_transitive(
        s.mul_spec(b.x).sub_spec(s.mul_spec(a.x)),
        b.x.sub_spec(a.x).mul_spec(s),
        s.mul_spec(b.x.sub_spec(a.x)));
    // c·by − c·ay ≡ c·(by − ay)
    Rational::lemma_mul_commutative(c, b.y);
    Rational::lemma_mul_commutative(c, a.y);
    Rational::lemma_eqv_sub_congruence(
        c.mul_spec(b.y), b.y.mul_spec(c),
        c.mul_spec(a.y), a.y.mul_spec(c));
    Rational::lemma_sub_mul_right(b.y, a.y, c);
    Rational::lemma_eqv_transitive(
        c.mul_spec(b.y).sub_spec(c.mul_spec(a.y)),
        b.y.mul_spec(c).sub_spec(a.y.mul_spec(c)),
        b.y.sub_spec(a.y).mul_spec(c));
    Rational::lemma_mul_commutative(b.y.sub_spec(a.y), c);
    Rational::lemma_eqv_transitive(
        c.mul_spec(b.y).sub_spec(c.mul_spec(a.y)),
        b.y.sub_spec(a.y).mul_spec(c),
        c.mul_spec(b.y.sub_spec(a.y)));
    // add congruence closes
    Rational::lemma_eqv_add_congruence(
        s.mul_spec(b.x).sub_spec(s.mul_spec(a.x)),
        s.mul_spec(b.x.sub_spec(a.x)),
        c.mul_spec(b.y).sub_spec(c.mul_spec(a.y)),
        c.mul_spec(b.y.sub_spec(a.y)));
    Rational::lemma_eqv_transitive(
        lhs,
        s.mul_spec(b.x).sub_spec(s.mul_spec(a.x)).add_spec(
            c.mul_spec(b.y).sub_spec(c.mul_spec(a.y))),
        vrot(c, s, vsub(b, a)).y);
}

// ── the rotation-cross identity ────────────────────────────────────────

/// Helper: cross(t·w, z1 + z2) ≡ t·cross(w, z1) + t·cross(w, z2).
pub proof fn lemma_vcross2_scl_add_right(
    t: Rational,
    w: Vec2<Rational>,
    z1: Vec2<Rational>,
    z2: Vec2<Rational>,
)
    ensures
        vcross2(vscl(t, w), vadd(z1, z2)).eqv_spec(
            t.mul_spec(vcross2(w, z1)).add_spec(t.mul_spec(vcross2(w, z2)))),
{
    lemma_vcross2_scale_left(t, w, vadd(z1, z2));
    lemma_vcross2_add_right(w, z1, z2);
    Rational::lemma_eqv_reflexive(t);
    Rational::lemma_eqv_mul_congruence(
        t, t, vcross2(w, vadd(z1, z2)), vcross2(w, z1).add_spec(vcross2(w, z2)));
    Rational::lemma_mul_distributes_over_add(t, vcross2(w, z1), vcross2(w, z2));
    Rational::lemma_eqv_transitive(
        vcross2(vscl(t, w), vadd(z1, z2)),
        t.mul_spec(vcross2(w, vadd(z1, z2))),
        t.mul_spec(vcross2(w, z1).add_spec(vcross2(w, z2))));
    Rational::lemma_eqv_transitive(
        vcross2(vscl(t, w), vadd(z1, z2)),
        t.mul_spec(vcross2(w, z1).add_spec(vcross2(w, z2))),
        t.mul_spec(vcross2(w, z1)).add_spec(t.mul_spec(vcross2(w, z2))));
}

/// Bilinearity expansion: cross(Ru, Rv) ≡ (cc·X + cs·D) + (sc·(−D) + ss·X)
/// where X = cross(u, v), D = dot(u, v).
pub proof fn lemma_vrot_cross_expanded(c: Rational, s: Rational, u: Vec2<Rational>, v: Vec2<Rational>)
    ensures {
        let x = vcross2(u, v);
        let d = vdot(u, v);
        vcross2(vrot(c, s, u), vrot(c, s, v)).eqv_spec(
            c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(d)).add_spec(
                s.mul_spec(c).mul_spec(d.neg_spec()).add_spec(s.mul_spec(s).mul_spec(x))))
    },
{
    let ru = vrot(c, s, u);
    let rv = vrot(c, s, v);
    let du = vadd(vscl(c, u), vscl(s, vperp(u)));
    let dv = vadd(vscl(c, v), vscl(s, vperp(v)));
    let x = vcross2(u, v);
    let d = vdot(u, v);
    // R == c·self + s·self⊥ componentwise (x structural, y by comm)
    lemma_raw_neg_mul_right(s, u.y);
    assert(du.x == ru.x);
    Rational::lemma_add_commutative(s.mul_spec(u.x), c.mul_spec(u.y));
    lemma_raw_neg_mul_right(s, v.y);
    assert(dv.x == rv.x);
    Rational::lemma_add_commutative(s.mul_spec(v.x), c.mul_spec(v.y));
    Rational::lemma_eqv_reflexive(du.x);
    Rational::lemma_eqv_reflexive(du.y);
    Rational::lemma_eqv_reflexive(dv.x);
    Rational::lemma_eqv_reflexive(dv.y);
    lemma_vcross2_congr(ru, du, rv, dv);
    // bilinearity: cross(du, dv) ≡ cross(c·u, dv) + cross(s·u⊥, dv)
    lemma_vcross2_add_left(vscl(c, u), vscl(s, vperp(u)), dv);
    // each side via the helper + scale_right + assoc
    lemma_vcross2_scl_add_right(c, u, vscl(c, v), vscl(s, vperp(v)));
    lemma_vcross2_scl_add_right(s, vperp(u), vscl(c, v), vscl(s, vperp(v)));
    lemma_vcross2_scale_right(c, u, v);
    lemma_vcross2_scale_right(s, u, vperp(v));
    lemma_vcross2_scale_right(c, vperp(u), v);
    lemma_vcross2_scale_right(s, vperp(u), vperp(v));
    // c-side: cross(cu, dv) ≡ (c·c)·X + (c·s)·Xr
    Rational::lemma_eqv_reflexive(c);
    Rational::lemma_eqv_mul_congruence(c, c, vcross2(u, vscl(c, v)), c.mul_spec(x));
    Rational::lemma_eqv_mul_congruence(
        c, c, vcross2(u, vscl(s, vperp(v))), s.mul_spec(vcross2(u, vperp(v))));
    Rational::lemma_eqv_add_congruence(
        c.mul_spec(vcross2(u, vscl(c, v))), c.mul_spec(c.mul_spec(x)),
        c.mul_spec(vcross2(u, vscl(s, vperp(v)))), c.mul_spec(s.mul_spec(vcross2(u, vperp(v)))));
    Rational::lemma_mul_associative(c, c, x);
    Rational::lemma_eqv_symmetric(c.mul_spec(c).mul_spec(x), c.mul_spec(c.mul_spec(x)));
    Rational::lemma_mul_associative(c, s, vcross2(u, vperp(v)));
    Rational::lemma_eqv_symmetric(
        c.mul_spec(s).mul_spec(vcross2(u, vperp(v))),
        c.mul_spec(s.mul_spec(vcross2(u, vperp(v)))));
    Rational::lemma_eqv_add_congruence(
        c.mul_spec(c.mul_spec(x)), c.mul_spec(c).mul_spec(x),
        c.mul_spec(s.mul_spec(vcross2(u, vperp(v)))),
        c.mul_spec(s).mul_spec(vcross2(u, vperp(v))));
    Rational::lemma_eqv_transitive(
        c.mul_spec(vcross2(u, vscl(c, v))).add_spec(c.mul_spec(vcross2(u, vscl(s, vperp(v))))),
        c.mul_spec(c.mul_spec(x)).add_spec(c.mul_spec(s.mul_spec(vcross2(u, vperp(v))))),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(vcross2(u, vperp(v)))));
    // s-side: cross(su⊥, dv) ≡ (s·c)·Xl + (s·s)·Xb
    Rational::lemma_eqv_reflexive(s);
    Rational::lemma_eqv_mul_congruence(
        s, s, vcross2(vperp(u), vscl(c, v)), c.mul_spec(vcross2(vperp(u), v)));
    Rational::lemma_eqv_mul_congruence(
        s, s, vcross2(vperp(u), vscl(s, vperp(v))), s.mul_spec(vcross2(vperp(u), vperp(v))));
    Rational::lemma_eqv_add_congruence(
        s.mul_spec(vcross2(vperp(u), vscl(c, v))), s.mul_spec(c.mul_spec(vcross2(vperp(u), v))),
        s.mul_spec(vcross2(vperp(u), vscl(s, vperp(v)))),
        s.mul_spec(s.mul_spec(vcross2(vperp(u), vperp(v)))));
    Rational::lemma_mul_associative(s, c, vcross2(vperp(u), v));
    Rational::lemma_eqv_symmetric(
        s.mul_spec(c).mul_spec(vcross2(vperp(u), v)),
        s.mul_spec(c.mul_spec(vcross2(vperp(u), v))));
    Rational::lemma_mul_associative(s, s, vcross2(vperp(u), vperp(v)));
    Rational::lemma_eqv_symmetric(
        s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v))),
        s.mul_spec(s.mul_spec(vcross2(vperp(u), vperp(v)))));
    Rational::lemma_eqv_add_congruence(
        s.mul_spec(c.mul_spec(vcross2(vperp(u), v))), s.mul_spec(c).mul_spec(vcross2(vperp(u), v)),
        s.mul_spec(s.mul_spec(vcross2(vperp(u), vperp(v)))),
        s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v))));
    Rational::lemma_eqv_transitive(
        s.mul_spec(vcross2(vperp(u), vscl(c, v))).add_spec(
            s.mul_spec(vcross2(vperp(u), vscl(s, vperp(v))))),
        s.mul_spec(c.mul_spec(vcross2(vperp(u), v))).add_spec(
            s.mul_spec(s.mul_spec(vcross2(vperp(u), vperp(v))))),
        s.mul_spec(c).mul_spec(vcross2(vperp(u), v)).add_spec(
            s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v)))));
    // side splits fold to their expanded forms
    Rational::lemma_eqv_transitive(
        vcross2(vscl(c, u), dv),
        c.mul_spec(vcross2(u, vscl(c, v))).add_spec(c.mul_spec(vcross2(u, vscl(s, vperp(v))))),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(vcross2(u, vperp(v)))));
    Rational::lemma_eqv_transitive(
        vcross2(vscl(s, vperp(u)), dv),
        s.mul_spec(vcross2(vperp(u), vscl(c, v))).add_spec(
            s.mul_spec(vcross2(vperp(u), vscl(s, vperp(v))))),
        s.mul_spec(c).mul_spec(vcross2(vperp(u), v)).add_spec(
            s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v)))));
    // sum congruence
    Rational::lemma_eqv_add_congruence(
        vcross2(vscl(c, u), dv),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(vcross2(u, vperp(v)))),
        vcross2(vscl(s, vperp(u)), dv),
        s.mul_spec(c).mul_spec(vcross2(vperp(u), v)).add_spec(
            s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v)))));
    // perp identities: Xr == D, Xb == X (structural), Xl ≡ −D
    lemma_vcross2_vperp_right(u, v);
    lemma_vcross2_vperp_both(u, v);
    lemma_vcross2_vperp_left(u, v);
    Rational::lemma_eqv_reflexive(c.mul_spec(s));
    Rational::lemma_eqv_mul_congruence(c.mul_spec(s), c.mul_spec(s), vcross2(u, vperp(v)), d);
    Rational::lemma_eqv_reflexive(s.mul_spec(s));
    Rational::lemma_eqv_mul_congruence(s.mul_spec(s), s.mul_spec(s), vcross2(vperp(u), vperp(v)), x);
    Rational::lemma_eqv_reflexive(s.mul_spec(c));
    Rational::lemma_eqv_mul_congruence(
        s.mul_spec(c), s.mul_spec(c), vcross2(vperp(u), v), d.neg_spec());
    Rational::lemma_eqv_reflexive(c.mul_spec(c).mul_spec(x));
    Rational::lemma_eqv_add_congruence(
        c.mul_spec(c).mul_spec(x), c.mul_spec(c).mul_spec(x),
        c.mul_spec(s).mul_spec(vcross2(u, vperp(v))), c.mul_spec(s).mul_spec(d));
    Rational::lemma_eqv_add_congruence(
        s.mul_spec(c).mul_spec(vcross2(vperp(u), v)), s.mul_spec(c).mul_spec(d.neg_spec()),
        s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v))), s.mul_spec(s).mul_spec(x));
    Rational::lemma_eqv_add_congruence(
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(vcross2(u, vperp(v)))),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(d)),
        s.mul_spec(c).mul_spec(vcross2(vperp(u), v)).add_spec(
            s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v)))),
        s.mul_spec(c).mul_spec(d.neg_spec()).add_spec(s.mul_spec(s).mul_spec(x)));
    // final chain
    Rational::lemma_eqv_transitive(
        vcross2(ru, rv),
        vcross2(du, dv),
        vcross2(vscl(c, u), dv).add_spec(vcross2(vscl(s, vperp(u)), dv)));
    Rational::lemma_eqv_transitive(
        vcross2(ru, rv),
        vcross2(vscl(c, u), dv).add_spec(vcross2(vscl(s, vperp(u)), dv)),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(vcross2(u, vperp(v)))).add_spec(
            s.mul_spec(c).mul_spec(vcross2(vperp(u), v)).add_spec(
                s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v))))));
    Rational::lemma_eqv_transitive(
        vcross2(ru, rv),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(vcross2(u, vperp(v)))).add_spec(
            s.mul_spec(c).mul_spec(vcross2(vperp(u), v)).add_spec(
                s.mul_spec(s).mul_spec(vcross2(vperp(u), vperp(v))))),
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(d)).add_spec(
            s.mul_spec(c).mul_spec(d.neg_spec()).add_spec(s.mul_spec(s).mul_spec(x))));
}

/// Fold: (cc·X + cs·D) + (sc·(−D) + ss·X) ≡ (cc + ss)·X.
pub proof fn lemma_vrot_cross_fold(c: Rational, s: Rational, u: Vec2<Rational>, v: Vec2<Rational>)
    ensures {
        let x = vcross2(u, v);
        let d = vdot(u, v);
        c.mul_spec(c).mul_spec(x).add_spec(c.mul_spec(s).mul_spec(d)).add_spec(
            s.mul_spec(c).mul_spec(d.neg_spec()).add_spec(s.mul_spec(s).mul_spec(x)))
            .eqv_spec(c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(x))
    },
{
    let x = vcross2(u, v);
    let d = vdot(u, v);
    let cc = c.mul_spec(c);
    let ss = s.mul_spec(s);
    let cs = c.mul_spec(s);
    let sc = s.mul_spec(c);
    // sc·(−D) == −(sc·D) ≡ −(cs·D)
    lemma_raw_neg_mul_right(sc, d);
    assert(sc.mul_spec(d.neg_spec()) == sc.mul_spec(d).neg_spec());
    Rational::lemma_mul_commutative(s, c);
    Rational::lemma_eqv_reflexive(d);
    Rational::lemma_eqv_mul_congruence(sc, cs, d, d);
    Rational::lemma_eqv_neg_congruence(sc.mul_spec(d), cs.mul_spec(d));
    Rational::lemma_eqv_transitive(
        sc.mul_spec(d.neg_spec()), sc.mul_spec(d).neg_spec(), cs.mul_spec(d).neg_spec());
    // swap the second pair, then pair-swap the 4-term sum
    Rational::lemma_add_commutative(sc.mul_spec(d.neg_spec()), ss.mul_spec(x));
    Rational::lemma_eqv_reflexive(cc.mul_spec(x).add_spec(cs.mul_spec(d)));
    Rational::lemma_eqv_add_congruence(
        cc.mul_spec(x).add_spec(cs.mul_spec(d)), cc.mul_spec(x).add_spec(cs.mul_spec(d)),
        sc.mul_spec(d.neg_spec()).add_spec(ss.mul_spec(x)),
        ss.mul_spec(x).add_spec(sc.mul_spec(d.neg_spec())));
    lemma_add_pair_swap(cc.mul_spec(x), cs.mul_spec(d), ss.mul_spec(x), sc.mul_spec(d.neg_spec()));
    Rational::lemma_eqv_transitive(
        cc.mul_spec(x).add_spec(cs.mul_spec(d)).add_spec(
            sc.mul_spec(d.neg_spec()).add_spec(ss.mul_spec(x))),
        cc.mul_spec(x).add_spec(cs.mul_spec(d)).add_spec(
            ss.mul_spec(x).add_spec(sc.mul_spec(d.neg_spec()))),
        cc.mul_spec(x).add_spec(ss.mul_spec(x)).add_spec(
            cs.mul_spec(d).add_spec(sc.mul_spec(d.neg_spec()))));
    // cc·X + ss·X ≡ (cc + ss)·X  [comm, distrib, comm ×2, symmetric]
    Rational::lemma_mul_commutative(cc.add_spec(ss), x);
    Rational::lemma_mul_distributes_over_add(x, cc, ss);
    Rational::lemma_mul_commutative(x, cc);
    Rational::lemma_mul_commutative(x, ss);
    Rational::lemma_eqv_reflexive(x.mul_spec(ss));
    Rational::lemma_eqv_add_congruence(
        x.mul_spec(cc).add_spec(x.mul_spec(ss)),
        cc.mul_spec(x).add_spec(x.mul_spec(ss)),
        x.mul_spec(ss), ss.mul_spec(x));
    Rational::lemma_eqv_transitive(
        x.mul_spec(cc).add_spec(x.mul_spec(ss)),
        cc.mul_spec(x).add_spec(x.mul_spec(ss)),
        cc.mul_spec(x).add_spec(ss.mul_spec(x)));
    Rational::lemma_eqv_transitive(
        cc.add_spec(ss).mul_spec(x),
        x.mul_spec(cc.add_spec(ss)),
        x.mul_spec(cc).add_spec(x.mul_spec(ss)));
    Rational::lemma_eqv_transitive(
        cc.add_spec(ss).mul_spec(x),
        x.mul_spec(cc).add_spec(x.mul_spec(ss)),
        cc.mul_spec(x).add_spec(ss.mul_spec(x)));
    Rational::lemma_eqv_symmetric(
        cc.add_spec(ss).mul_spec(x), cc.mul_spec(x).add_spec(ss.mul_spec(x)));
    // cs·D + sc·(−D) ≡ cs·D + (−(cs·D)) ≡ 0
    Rational::lemma_eqv_reflexive(cs.mul_spec(d));
    Rational::lemma_eqv_add_congruence(
        cs.mul_spec(d), cs.mul_spec(d),
        sc.mul_spec(d.neg_spec()), cs.mul_spec(d).neg_spec());
    assert(cs.mul_spec(d).add_spec(cs.mul_spec(d).neg_spec())
        == cs.mul_spec(d).sub_spec(cs.mul_spec(d)));
    Rational::lemma_sub_self(cs.mul_spec(d));
    Rational::lemma_eqv_transitive(
        cs.mul_spec(d).add_spec(sc.mul_spec(d.neg_spec())),
        cs.mul_spec(d).sub_spec(cs.mul_spec(d)),
        Rational::from_int_spec(0));
    // sum: ≡ (cc+ss)·X + 0 == (cc+ss)·X
    Rational::lemma_eqv_add_congruence(
        cc.mul_spec(x).add_spec(ss.mul_spec(x)), cc.add_spec(ss).mul_spec(x),
        cs.mul_spec(d).add_spec(sc.mul_spec(d.neg_spec())), Rational::from_int_spec(0));
    Rational::lemma_add_zero_identity(cc.add_spec(ss).mul_spec(x));
    Rational::lemma_eqv_reflexive(
        cc.add_spec(ss).mul_spec(x).add_spec(Rational::from_int_spec(0)));
    Rational::lemma_eqv_transitive(
        cc.mul_spec(x).add_spec(ss.mul_spec(x)).add_spec(
            cs.mul_spec(d).add_spec(sc.mul_spec(d.neg_spec()))),
        cc.add_spec(ss).mul_spec(x).add_spec(Rational::from_int_spec(0)),
        cc.add_spec(ss).mul_spec(x));
    Rational::lemma_eqv_transitive(
        cc.mul_spec(x).add_spec(cs.mul_spec(d)).add_spec(
            sc.mul_spec(d.neg_spec()).add_spec(ss.mul_spec(x))),
        cc.mul_spec(x).add_spec(ss.mul_spec(x)).add_spec(
            cs.mul_spec(d).add_spec(sc.mul_spec(d.neg_spec()))),
        cc.add_spec(ss).mul_spec(x));
}

/// cross(Ru, Rv) ≡ (c² + s²)·cross(u, v).
pub proof fn lemma_vcross2_vrot(c: Rational, s: Rational, u: Vec2<Rational>, v: Vec2<Rational>)
    ensures
        vcross2(vrot(c, s, u), vrot(c, s, v)).eqv_spec(
            c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(vcross2(u, v))),
{
    lemma_vrot_cross_expanded(c, s, u, v);
    lemma_vrot_cross_fold(c, s, u, v);
    Rational::lemma_eqv_transitive(
        vcross2(vrot(c, s, u), vrot(c, s, v)),
        c.mul_spec(c).mul_spec(vcross2(u, v)).add_spec(
            c.mul_spec(s).mul_spec(vdot(u, v))).add_spec(
                s.mul_spec(c).mul_spec(vdot(u, v).neg_spec()).add_spec(
                    s.mul_spec(s).mul_spec(vcross2(u, v)))),
        c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(vcross2(u, v)));
}

/// orient of world-transformed points ≡ orient of locals (unit rotation).
pub proof fn lemma_orient_world(
    pos: Vec2<Rational>,
    c: Rational,
    s: Rational,
    a: Vec2<Rational>,
    b: Vec2<Rational>,
    w: Vec2<Rational>,
)
    requires
        unit_norm_raw(c, s),
    ensures
        orient(
            world_vert(pos, c, s, a),
            world_vert(pos, c, s, b),
            world_vert(pos, c, s, w),
        ).eqv_spec(orient(a, b, w)),
{
    let wa = world_vert(pos, c, s, a);
    let wb = world_vert(pos, c, s, b);
    let ww = world_vert(pos, c, s, w);
    let ra = vrot(c, s, a);
    let rb = vrot(c, s, b);
    let rw = vrot(c, s, w);
    // wa == vadd(ra, pos) structurally; translation cancels in differences
    lemma_trans_sub_cancel(pos.x, rb.x, ra.x);
    lemma_trans_sub_cancel(pos.y, rb.y, ra.y);
    lemma_trans_sub_cancel(pos.x, rw.x, ra.x);
    lemma_trans_sub_cancel(pos.y, rw.y, ra.y);
    // rotation is linear
    lemma_vrot_sub_x(c, s, b, a);
    lemma_vrot_sub_y(c, s, b, a);
    lemma_vrot_sub_x(c, s, w, a);
    lemma_vrot_sub_y(c, s, w, a);
    // cross congruence twice, then the rotation-cross identity
    lemma_vcross2_congr(vsub(wb, wa), vsub(rb, ra), vsub(ww, wa), vsub(rw, ra));
    lemma_vcross2_congr(
        vsub(rb, ra), vrot(c, s, vsub(b, a)),
        vsub(rw, ra), vrot(c, s, vsub(w, a)));
    Rational::lemma_eqv_transitive(
        orient(wa, wb, ww),
        vcross2(vsub(rb, ra), vsub(rw, ra)),
        vcross2(vrot(c, s, vsub(b, a)), vrot(c, s, vsub(w, a))));
    lemma_vcross2_vrot(c, s, vsub(b, a), vsub(w, a));
    Rational::lemma_eqv_transitive(
        orient(wa, wb, ww),
        vcross2(vrot(c, s, vsub(b, a)), vrot(c, s, vsub(w, a))),
        c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(orient(a, b, w)));
    // (c² + s²)·X ≡ 1·X ≡ X·1 ≡ X
    let one = Rational::from_int_spec(1);
    Rational::lemma_eqv_reflexive(orient(a, b, w));
    Rational::lemma_eqv_mul_congruence(
        c.mul_spec(c).add_spec(s.mul_spec(s)), one, orient(a, b, w), orient(a, b, w));
    Rational::lemma_mul_commutative(one, orient(a, b, w));
    Rational::lemma_mul_one_identity(orient(a, b, w));
    Rational::lemma_eqv_transitive(
        c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(orient(a, b, w)),
        one.mul_spec(orient(a, b, w)),
        orient(a, b, w).mul_spec(one));
    Rational::lemma_eqv_transitive(
        c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(orient(a, b, w)),
        orient(a, b, w).mul_spec(one),
        orient(a, b, w));
    Rational::lemma_eqv_transitive(
        orient(wa, wb, ww),
        c.mul_spec(c).add_spec(s.mul_spec(s)).mul_spec(orient(a, b, w)),
        orient(a, b, w));
}

/// Rigid transforms preserve the global convexity invariant: this is what
/// lets the certificate re-run SAT on world-space polys (C4, phys-06 too).
pub proof fn lemma_convex_poly_inv_world(
    pos: Vec2<Rational>,
    c: Rational,
    s: Rational,
    vs: Seq<Vec2<Rational>>,
)
    requires
        convex_poly_inv(vs),
        unit_norm_raw(c, s),
    ensures
        convex_poly_inv(world_verts(pos, c, s, vs)),
{
    let w = world_verts(pos, c, s, vs);
    let n = vs.len();
    assert(w.len() == n);
    assert(n >= 3);
    assert forall|i: int, j: int|
        (0 <= i < n && 0 <= j < n) implies {
            let o = #[trigger] orient(w[i], w[(i + 1) % (n as int)], w[j]);
            if j == i || j == (i + 1) % (n as int) {
                true
            } else {
                Rational::from_int_spec(0).lt_spec(o)
            }
        }
    by {
        assert(w[i] == world_vert(pos, c, s, vs[i]));
        assert(w[(i + 1) % (n as int)] == world_vert(pos, c, s, vs[(i + 1) % (n as int)]));
        assert(w[j] == world_vert(pos, c, s, vs[j]));
        lemma_orient_world(pos, c, s, vs[i], vs[(i + 1) % (n as int)], vs[j]);
        if !(j == i || j == (i + 1) % (n as int)) {
            let oo = orient(vs[i], vs[(i + 1) % (n as int)], vs[j]);
            assert(Rational::from_int_spec(0).lt_spec(oo));
            Rational::lemma_eqv_implies_le(oo, orient(w[i], w[(i + 1) % (n as int)], w[j]));
            Rational::lemma_lt_le_transitive(
                Rational::from_int_spec(0), oo, orient(w[i], w[(i + 1) % (n as int)], w[j]));
        }
    }
}

} // verus!
