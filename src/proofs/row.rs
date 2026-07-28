//! Impulse lemmas for the ONE row type (phys-05c, SPEC §6): effective-mass
//! sign theory, the J·v′ ≡ J·v + λ·mEff workhorse, exact momentum exchange
//! for contact rows, and the C3 restitution inequality for the single-row
//! PGS update. Raw *_spec discipline (R1–R5 in rational_raw.rs) throughout.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::massprops::{vdot, vscale};
use crate::proofs::rational_raw::{
    lemma_raw_mul_zero_left, lemma_raw_neg_mul_left, lemma_raw_neg_mul_neg,
    lemma_raw_neg_mul_right, lemma_raw_neg_one_mul,
};
use crate::row::{clamp_spec, eff_mass_spec, row_vel_spec, vel_after_impulse};
use crate::shape::vadd;

verus! {

// ── dot-self sign theory ───────────────────────────────────────────────

/// 0 ≤ j·j (sum of squares).
pub proof fn lemma_vdot_self_nonneg(j: Vec2<Rational>)
    ensures
        Rational::from_int_spec(0).le_spec(vdot(j, j)),
{
    let z = Rational::from_int_spec(0);
    Rational::lemma_square_le_nonneg(j.x);
    Rational::lemma_square_le_nonneg(j.y);
    Rational::lemma_le_add_both(z, j.x.mul_spec(j.x), z, j.y.mul_spec(j.y));
    Rational::lemma_add_zero_identity(z);
    assert(z.add_spec(z) == z);
    Rational::lemma_eqv_reflexive(z);
    Rational::lemma_eqv_implies_le(z, z.add_spec(z));
    Rational::lemma_le_transitive(z, z.add_spec(z), vdot(j, j));
}

/// j ≠ 0 (some component num nonzero) ⟹ 0 < j·j.
pub proof fn lemma_vdot_self_pos(j: Vec2<Rational>)
    requires
        j.x.num != 0 || j.y.num != 0,
    ensures
        Rational::from_int_spec(0).lt_spec(vdot(j, j)),
{
    let z = Rational::from_int_spec(0);
    Rational::lemma_square_le_nonneg(j.x);
    Rational::lemma_square_le_nonneg(j.y);
    if j.x.num != 0 {
        Rational::lemma_trichotomy(z, j.x);
        Rational::lemma_eqv_zero_iff_num_zero(j.x);
        Rational::lemma_eqv_symmetric(z, j.x);
        if z.lt_spec(j.x) {
            Rational::lemma_pos_mul_pos(j.x, j.x);
        } else {
            assert(j.x.lt_spec(z));
            Rational::lemma_neg_mul_neg(j.x, j.x);
        }
        assert(z.lt_spec(j.x.mul_spec(j.x)));
        // jx² = jx² + 0 ≤ jx² + jy²
        Rational::lemma_le_add_both(j.x.mul_spec(j.x), j.x.mul_spec(j.x), z, j.y.mul_spec(j.y));
        Rational::lemma_add_zero_identity(j.x.mul_spec(j.x));
        Rational::lemma_eqv_reflexive(j.x.mul_spec(j.x));
        Rational::lemma_eqv_implies_le(
            j.x.mul_spec(j.x), j.x.mul_spec(j.x).add_spec(z));
        Rational::lemma_le_transitive(
            j.x.mul_spec(j.x), j.x.mul_spec(j.x).add_spec(z), vdot(j, j));
        Rational::lemma_lt_le_transitive(z, j.x.mul_spec(j.x), vdot(j, j));
    } else {
        assert(j.y.num != 0);
        Rational::lemma_trichotomy(z, j.y);
        Rational::lemma_eqv_zero_iff_num_zero(j.y);
        Rational::lemma_eqv_symmetric(z, j.y);
        if z.lt_spec(j.y) {
            Rational::lemma_pos_mul_pos(j.y, j.y);
        } else {
            assert(j.y.lt_spec(z));
            Rational::lemma_neg_mul_neg(j.y, j.y);
        }
        assert(z.lt_spec(j.y.mul_spec(j.y)));
        // jy² = 0 + jy² ≤ jx² + jy²
        Rational::lemma_le_add_both(z, j.x.mul_spec(j.x), j.y.mul_spec(j.y), j.y.mul_spec(j.y));
        Rational::lemma_add_zero_identity(j.y.mul_spec(j.y));
        assert(z.add_spec(j.y.mul_spec(j.y)) == j.y.mul_spec(j.y));
        Rational::lemma_eqv_reflexive(j.y.mul_spec(j.y));
        Rational::lemma_eqv_implies_le(
            j.y.mul_spec(j.y), z.add_spec(j.y.mul_spec(j.y)));
        Rational::lemma_le_transitive(
            j.y.mul_spec(j.y), z.add_spec(j.y.mul_spec(j.y)), vdot(j, j));
        Rational::lemma_lt_le_transitive(z, j.y.mul_spec(j.y), vdot(j, j));
    }
}

/// dot(−n, −n) == dot(n, n) (structural), with −n = vscale(−1, n).
pub proof fn lemma_vdot_neg_self(n: Vec2<Rational>)
    ensures
        vdot(
            vscale(Rational::from_int_spec(-1), n),
            vscale(Rational::from_int_spec(-1), n),
        ) == vdot(n, n),
{
    lemma_raw_neg_one_mul(n.x);
    lemma_raw_neg_one_mul(n.y);
    lemma_raw_neg_mul_neg(n.x, n.x);
    lemma_raw_neg_mul_neg(n.y, n.y);
}

/// q_nonneg(x) ∧ x.num ≠ 0 ⟹ 0 < x.
pub proof fn lemma_nonneg_num_nonzero_pos(x: Rational)
    requires
        Rational::from_int_spec(0).le_spec(x),
        x.num != 0,
    ensures
        Rational::from_int_spec(0).lt_spec(x),
{
    let z = Rational::from_int_spec(0);
    Rational::lemma_le_iff_lt_or_eqv(z, x);
    Rational::lemma_eqv_zero_iff_num_zero(x);
    Rational::lemma_eqv_symmetric(z, x);
}

// ── effective-mass sign theory ─────────────────────────────────────────

/// mEff ≥ 0 whenever every inverse mass/inertia is ≥ 0 (body wf).
pub proof fn lemma_eff_mass_nonneg(
    jla: Vec2<Rational>,
    jaa: Rational,
    jlb: Vec2<Rational>,
    jab: Rational,
    inv_ma: Rational,
    inv_ia: Rational,
    inv_mb: Rational,
    inv_ib: Rational,
)
    requires
        Rational::from_int_spec(0).le_spec(inv_ma),
        Rational::from_int_spec(0).le_spec(inv_ia),
        Rational::from_int_spec(0).le_spec(inv_mb),
        Rational::from_int_spec(0).le_spec(inv_ib),
    ensures
        Rational::from_int_spec(0).le_spec(eff_mass_spec(
            jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib)),
{
    let z = Rational::from_int_spec(0);
    let t1 = vdot(jla, jla).mul_spec(inv_ma);
    let t2 = jaa.mul_spec(jaa).mul_spec(inv_ia);
    let t3 = vdot(jlb, jlb).mul_spec(inv_mb);
    let t4 = jab.mul_spec(jab).mul_spec(inv_ib);
    lemma_vdot_self_nonneg(jla);
    lemma_vdot_self_nonneg(jlb);
    Rational::lemma_square_le_nonneg(jaa);
    Rational::lemma_square_le_nonneg(jab);
    Rational::lemma_le_mul_nonneg(z, vdot(jla, jla), inv_ma);
    Rational::lemma_le_mul_nonneg(z, jaa.mul_spec(jaa), inv_ia);
    Rational::lemma_le_mul_nonneg(z, vdot(jlb, jlb), inv_mb);
    Rational::lemma_le_mul_nonneg(z, jab.mul_spec(jab), inv_ib);
    lemma_raw_mul_zero_left(inv_ma);
    lemma_raw_mul_zero_left(inv_ia);
    lemma_raw_mul_zero_left(inv_mb);
    lemma_raw_mul_zero_left(inv_ib);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_ma), z);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_ia), z);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_mb), z);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_ib), z);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_ma), t1);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_ia), t2);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_mb), t3);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_ib), t4);
    // z ≤ t1+t2 ≤ (t1+t2)+t3 ≤ mEff (folded adds of nonnegs)
    Rational::lemma_le_add_both(z, t1, z, t2);
    Rational::lemma_add_zero_identity(z);
    Rational::lemma_eqv_reflexive(z);
    Rational::lemma_eqv_implies_le(z, z.add_spec(z));
    Rational::lemma_le_transitive(z, z.add_spec(z), t1.add_spec(t2));
    Rational::lemma_le_add_both(z, t1.add_spec(t2), z, t3);
    Rational::lemma_le_transitive(z, z.add_spec(z), t1.add_spec(t2).add_spec(t3));
    Rational::lemma_le_add_both(z, t1.add_spec(t2).add_spec(t3), z, t4);
    Rational::lemma_le_transitive(
        z, z.add_spec(z),
        eff_mass_spec(jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib));
}

/// mEff > 0 when the body-a linear term is strictly positive (nonzero
/// linear J block on a dynamic body) and the rest are ≥ 0.
pub proof fn lemma_eff_mass_pos_linear_a(
    jla: Vec2<Rational>,
    jaa: Rational,
    jlb: Vec2<Rational>,
    jab: Rational,
    inv_ma: Rational,
    inv_ia: Rational,
    inv_mb: Rational,
    inv_ib: Rational,
)
    requires
        Rational::from_int_spec(0).lt_spec(vdot(jla, jla)),
        Rational::from_int_spec(0).lt_spec(inv_ma),
        Rational::from_int_spec(0).le_spec(inv_ia),
        Rational::from_int_spec(0).le_spec(inv_mb),
        Rational::from_int_spec(0).le_spec(inv_ib),
    ensures
        Rational::from_int_spec(0).lt_spec(eff_mass_spec(
            jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib)),
{
    let z = Rational::from_int_spec(0);
    let t1 = vdot(jla, jla).mul_spec(inv_ma);
    let t2 = jaa.mul_spec(jaa).mul_spec(inv_ia);
    let t3 = vdot(jlb, jlb).mul_spec(inv_mb);
    let t4 = jab.mul_spec(jab).mul_spec(inv_ib);
    // 0 < t1
    Rational::lemma_pos_mul_pos(vdot(jla, jla), inv_ma);
    // 0 ≤ t2, t3, t4
    lemma_vdot_self_nonneg(jlb);
    Rational::lemma_square_le_nonneg(jaa);
    Rational::lemma_square_le_nonneg(jab);
    Rational::lemma_le_mul_nonneg(z, jaa.mul_spec(jaa), inv_ia);
    Rational::lemma_le_mul_nonneg(z, vdot(jlb, jlb), inv_mb);
    Rational::lemma_le_mul_nonneg(z, jab.mul_spec(jab), inv_ib);
    lemma_raw_mul_zero_left(inv_ia);
    lemma_raw_mul_zero_left(inv_mb);
    lemma_raw_mul_zero_left(inv_ib);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_ia), z);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_mb), z);
    Rational::lemma_eqv_implies_le(z.mul_spec(inv_ib), z);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_ia), t2);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_mb), t3);
    Rational::lemma_le_transitive(z, z.mul_spec(inv_ib), t4);
    // 0 < t1 = t1 + 0 ≤ t1 + t2
    Rational::lemma_le_add_both(t1, t1, z, t2);
    Rational::lemma_add_zero_identity(t1);
    Rational::lemma_eqv_reflexive(t1);
    Rational::lemma_eqv_implies_le(t1, t1.add_spec(z));
    Rational::lemma_le_transitive(t1, t1.add_spec(z), t1.add_spec(t2));
    Rational::lemma_lt_le_transitive(z, t1, t1.add_spec(t2));
    // ... ≤ (t1+t2) + t3
    let s12 = t1.add_spec(t2);
    Rational::lemma_le_add_both(s12, s12, z, t3);
    Rational::lemma_add_zero_identity(s12);
    Rational::lemma_eqv_reflexive(s12);
    Rational::lemma_eqv_implies_le(s12, s12.add_spec(z));
    Rational::lemma_le_transitive(s12, s12.add_spec(z), s12.add_spec(t3));
    Rational::lemma_lt_le_transitive(z, s12, s12.add_spec(t3));
    // ... ≤ ((t1+t2)+t3) + t4 == mEff
    let s123 = s12.add_spec(t3);
    Rational::lemma_le_add_both(s123, s123, z, t4);
    Rational::lemma_add_zero_identity(s123);
    Rational::lemma_eqv_reflexive(s123);
    Rational::lemma_eqv_implies_le(s123, s123.add_spec(z));
    Rational::lemma_le_transitive(s123, s123.add_spec(z), s123.add_spec(t4));
    Rational::lemma_lt_le_transitive(z, s123, s123.add_spec(t4));
    assert(s123.add_spec(t4) == eff_mass_spec(
        jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib));
}

// ── add regrouping ─────────────────────────────────────────────────────

/// (a + x) + (b + y) ≡ (a + b) + (x + y).
pub proof fn lemma_add_pair_swap(a: Rational, x: Rational, b: Rational, y: Rational)
    ensures
        a.add_spec(x).add_spec(b.add_spec(y)).eqv_spec(
            a.add_spec(b).add_spec(x.add_spec(y))),
{
    // (a+x)+(b+y) ≡ a+(x+(b+y))           [assoc]
    Rational::lemma_add_associative(a, x, b.add_spec(y));
    // x+(b+y) ≡ (x+b)+y                   [assoc, symmetric]
    Rational::lemma_add_associative(x, b, y);
    Rational::lemma_eqv_symmetric(
        x.add_spec(b).add_spec(y), x.add_spec(b.add_spec(y)));
    // (x+b)+y ≡ (b+x)+y                   [comm + congr]
    Rational::lemma_add_commutative(x, b);
    Rational::lemma_eqv_reflexive(y);
    Rational::lemma_eqv_add_congruence(x.add_spec(b), b.add_spec(x), y, y);
    // (b+x)+y ≡ b+(x+y)                   [assoc]
    Rational::lemma_add_associative(b, x, y);
    // x+(b+y) ≡ b+(x+y)                   [chain of 3]
    Rational::lemma_eqv_transitive(
        x.add_spec(b.add_spec(y)),
        x.add_spec(b).add_spec(y),
        b.add_spec(x).add_spec(y));
    Rational::lemma_eqv_transitive(
        x.add_spec(b.add_spec(y)),
        b.add_spec(x).add_spec(y),
        b.add_spec(x.add_spec(y)));
    // a+(x+(b+y)) ≡ a+(b+(x+y))           [congr]
    Rational::lemma_eqv_reflexive(a);
    Rational::lemma_eqv_add_congruence(
        a, a, x.add_spec(b.add_spec(y)), b.add_spec(x.add_spec(y)));
    // a+(b+(x+y)) ≡ (a+b)+(x+y)           [assoc, symmetric]
    Rational::lemma_add_associative(a, b, x.add_spec(y));
    Rational::lemma_eqv_symmetric(
        a.add_spec(b).add_spec(x.add_spec(y)),
        a.add_spec(b.add_spec(x.add_spec(y))));
    // full chain
    Rational::lemma_eqv_transitive(
        a.add_spec(x).add_spec(b.add_spec(y)),
        a.add_spec(x.add_spec(b.add_spec(y))),
        a.add_spec(b.add_spec(x.add_spec(y))));
    Rational::lemma_eqv_transitive(
        a.add_spec(x).add_spec(b.add_spec(y)),
        a.add_spec(b.add_spec(x.add_spec(y))),
        a.add_spec(b).add_spec(x.add_spec(y)));
}

// ── per-term impulse algebra ───────────────────────────────────────────

/// vdot(j, v + c·j) ≡ vdot(j, v) + c·vdot(j, j) (linearity of dot).
pub proof fn lemma_vdot_vadd_scale(j: Vec2<Rational>, v: Vec2<Rational>, c: Rational)
    ensures
        vdot(j, vadd(v, vscale(c, j))).eqv_spec(
            vdot(j, v).add_spec(c.mul_spec(vdot(j, j)))),
{
    let tx = j.x.mul_spec(v.x.add_spec(c.mul_spec(j.x)));
    let ty = j.y.mul_spec(v.y.add_spec(c.mul_spec(j.y)));
    // distribute per component
    Rational::lemma_mul_distributes_over_add(j.x, v.x, c.mul_spec(j.x));
    Rational::lemma_mul_distributes_over_add(j.y, v.y, c.mul_spec(j.y));
    Rational::lemma_eqv_add_congruence(
        tx, j.x.mul_spec(v.x).add_spec(j.x.mul_spec(c.mul_spec(j.x))),
        ty, j.y.mul_spec(v.y).add_spec(j.y.mul_spec(c.mul_spec(j.y))));
    // swap pairs
    lemma_add_pair_swap(
        j.x.mul_spec(v.x), j.x.mul_spec(c.mul_spec(j.x)),
        j.y.mul_spec(v.y), j.y.mul_spec(c.mul_spec(j.y)));
    // j·(c·j) ≡ c·(j·j) per component
    Rational::lemma_mul_commutative(j.x, c.mul_spec(j.x));
    Rational::lemma_mul_associative(c, j.x, j.x);
    Rational::lemma_eqv_transitive(
        j.x.mul_spec(c.mul_spec(j.x)),
        c.mul_spec(j.x).mul_spec(j.x),
        c.mul_spec(j.x.mul_spec(j.x)));
    Rational::lemma_mul_commutative(j.y, c.mul_spec(j.y));
    Rational::lemma_mul_associative(c, j.y, j.y);
    Rational::lemma_eqv_transitive(
        j.y.mul_spec(c.mul_spec(j.y)),
        c.mul_spec(j.y).mul_spec(j.y),
        c.mul_spec(j.y.mul_spec(j.y)));
    Rational::lemma_eqv_add_congruence(
        j.x.mul_spec(c.mul_spec(j.x)), c.mul_spec(j.x.mul_spec(j.x)),
        j.y.mul_spec(c.mul_spec(j.y)), c.mul_spec(j.y.mul_spec(j.y)));
    // c·jx² + c·jy² ≡ c·(jx² + jy²)   [distributes, symmetric]
    Rational::lemma_mul_distributes_over_add(c, j.x.mul_spec(j.x), j.y.mul_spec(j.y));
    Rational::lemma_eqv_symmetric(
        c.mul_spec(j.x.mul_spec(j.x).add_spec(j.y.mul_spec(j.y))),
        c.mul_spec(j.x.mul_spec(j.x)).add_spec(c.mul_spec(j.y.mul_spec(j.y))));
    // chain: lhs ≡ (jx·vx + jy·vy) + (jx(cjx) + jy(cjy))
    Rational::lemma_eqv_transitive(
        vdot(j, vadd(v, vscale(c, j))),
        j.x.mul_spec(v.x).add_spec(j.x.mul_spec(c.mul_spec(j.x))).add_spec(
            j.y.mul_spec(v.y).add_spec(j.y.mul_spec(c.mul_spec(j.y)))),
        vdot(j, v).add_spec(
            j.x.mul_spec(c.mul_spec(j.x)).add_spec(j.y.mul_spec(c.mul_spec(j.y)))));
    // ≡ vdot + (c·jx² + c·jy²)
    Rational::lemma_eqv_reflexive(vdot(j, v));
    Rational::lemma_eqv_add_congruence(
        vdot(j, v), vdot(j, v),
        j.x.mul_spec(c.mul_spec(j.x)).add_spec(j.y.mul_spec(c.mul_spec(j.y))),
        c.mul_spec(j.x.mul_spec(j.x)).add_spec(c.mul_spec(j.y.mul_spec(j.y))));
    // ≡ vdot + c·vdot(j, j)
    Rational::lemma_eqv_add_congruence(
        vdot(j, v), vdot(j, v),
        c.mul_spec(j.x.mul_spec(j.x)).add_spec(c.mul_spec(j.y.mul_spec(j.y))),
        c.mul_spec(vdot(j, j)));
    Rational::lemma_eqv_transitive(
        vdot(j, vadd(v, vscale(c, j))),
        vdot(j, v).add_spec(
            j.x.mul_spec(c.mul_spec(j.x)).add_spec(j.y.mul_spec(c.mul_spec(j.y)))),
        vdot(j, v).add_spec(
            c.mul_spec(j.x.mul_spec(j.x)).add_spec(c.mul_spec(j.y.mul_spec(j.y)))));
    Rational::lemma_eqv_transitive(
        vdot(j, vadd(v, vscale(c, j))),
        vdot(j, v).add_spec(
            c.mul_spec(j.x.mul_spec(j.x)).add_spec(c.mul_spec(j.y.mul_spec(j.y)))),
        vdot(j, v).add_spec(c.mul_spec(vdot(j, j))));
}

/// ja·(w + (inv_i·λ)·ja) ≡ ja·w + λ·(ja²·inv_i).
pub proof fn lemma_ang_after_impulse(
    ja: Rational,
    w: Rational,
    inv_i: Rational,
    lambda: Rational,
)
    ensures
        ja.mul_spec(w.add_spec(inv_i.mul_spec(lambda).mul_spec(ja))).eqv_spec(
            ja.mul_spec(w).add_spec(
                lambda.mul_spec(ja.mul_spec(ja).mul_spec(inv_i)))),
{
    let ci = inv_i.mul_spec(lambda);
    let j2 = ja.mul_spec(ja);
    Rational::lemma_mul_distributes_over_add(ja, w, ci.mul_spec(ja));
    // ja·(ci·ja) ≡ (ci·ja)·ja ≡ ci·ja²
    Rational::lemma_mul_commutative(ja, ci.mul_spec(ja));
    Rational::lemma_mul_associative(ci, ja, ja);
    Rational::lemma_eqv_transitive(
        ja.mul_spec(ci.mul_spec(ja)),
        ci.mul_spec(ja).mul_spec(ja),
        ci.mul_spec(j2));
    // ci·ja² ≡ (λ·inv_i)·ja² ≡ λ·(inv_i·ja²)
    Rational::lemma_mul_commutative(inv_i, lambda);
    Rational::lemma_eqv_reflexive(j2);
    Rational::lemma_eqv_mul_congruence(ci, lambda.mul_spec(inv_i), j2, j2);
    Rational::lemma_mul_associative(lambda, inv_i, j2);
    Rational::lemma_eqv_transitive(
        ci.mul_spec(j2),
        lambda.mul_spec(inv_i).mul_spec(j2),
        lambda.mul_spec(inv_i.mul_spec(j2)));
    // λ·(inv_i·ja²) ≡ λ·(ja²·inv_i)
    Rational::lemma_mul_commutative(inv_i, j2);
    Rational::lemma_eqv_reflexive(lambda);
    Rational::lemma_eqv_mul_congruence(
        lambda, lambda, inv_i.mul_spec(j2), j2.mul_spec(inv_i));
    // chain: ja·(ci·ja) ≡ λ·(ja²·inv_i)
    Rational::lemma_eqv_transitive(
        ja.mul_spec(ci.mul_spec(ja)),
        ci.mul_spec(j2),
        lambda.mul_spec(inv_i.mul_spec(j2)));
    Rational::lemma_eqv_transitive(
        ja.mul_spec(ci.mul_spec(ja)),
        lambda.mul_spec(inv_i.mul_spec(j2)),
        lambda.mul_spec(j2.mul_spec(inv_i)));
    // add congruence with the reflexive ja·w
    Rational::lemma_eqv_reflexive(ja.mul_spec(w));
    Rational::lemma_eqv_add_congruence(
        ja.mul_spec(w), ja.mul_spec(w),
        ja.mul_spec(ci.mul_spec(ja)),
        lambda.mul_spec(j2.mul_spec(inv_i)));
    Rational::lemma_eqv_transitive(
        ja.mul_spec(w.add_spec(ci.mul_spec(ja))),
        ja.mul_spec(w).add_spec(ja.mul_spec(ci.mul_spec(ja))),
        ja.mul_spec(w).add_spec(lambda.mul_spec(j2.mul_spec(inv_i))));
}

/// (inv_m·λ)·dot ≡ λ·(dot·inv_m).
pub proof fn lemma_impulse_lin_term(inv_m: Rational, lambda: Rational, dot: Rational)
    ensures
        inv_m.mul_spec(lambda).mul_spec(dot).eqv_spec(
            lambda.mul_spec(dot.mul_spec(inv_m))),
{
    Rational::lemma_mul_commutative(inv_m, lambda);
    Rational::lemma_eqv_reflexive(dot);
    Rational::lemma_eqv_mul_congruence(
        inv_m.mul_spec(lambda), lambda.mul_spec(inv_m), dot, dot);
    Rational::lemma_mul_associative(lambda, inv_m, dot);
    Rational::lemma_eqv_transitive(
        inv_m.mul_spec(lambda).mul_spec(dot),
        lambda.mul_spec(inv_m).mul_spec(dot),
        lambda.mul_spec(inv_m.mul_spec(dot)));
    Rational::lemma_mul_commutative(inv_m, dot);
    Rational::lemma_eqv_reflexive(lambda);
    Rational::lemma_eqv_mul_congruence(
        lambda, lambda, inv_m.mul_spec(dot), dot.mul_spec(inv_m));
    Rational::lemma_eqv_transitive(
        inv_m.mul_spec(lambda).mul_spec(dot),
        lambda.mul_spec(inv_m.mul_spec(dot)),
        lambda.mul_spec(dot.mul_spec(inv_m)));
}

/// U = ((u1+u2)+u3)+u4 ≡ λ·(((m1+m2)+m3)+m4) from per-term λ-forms.
pub proof fn lemma_sum4_lambda_meff(
    u1: Rational,
    u2: Rational,
    u3: Rational,
    u4: Rational,
    m1: Rational,
    m2: Rational,
    m3: Rational,
    m4: Rational,
    lambda: Rational,
)
    requires
        u1.eqv_spec(lambda.mul_spec(m1)),
        u2.eqv_spec(lambda.mul_spec(m2)),
        u3.eqv_spec(lambda.mul_spec(m3)),
        u4.eqv_spec(lambda.mul_spec(m4)),
    ensures
        u1.add_spec(u2).add_spec(u3).add_spec(u4).eqv_spec(
            lambda.mul_spec(m1.add_spec(m2).add_spec(m3).add_spec(m4))),
{
    let l1 = lambda.mul_spec(m1);
    let l2 = lambda.mul_spec(m2);
    let l3 = lambda.mul_spec(m3);
    let l4 = lambda.mul_spec(m4);
    // U ≡ ((l1+l2)+l3)+l4
    Rational::lemma_eqv_add_congruence(u1, l1, u2, l2);
    Rational::lemma_eqv_add_congruence(u1.add_spec(u2), l1.add_spec(l2), u3, l3);
    Rational::lemma_eqv_add_congruence(
        u1.add_spec(u2).add_spec(u3), l1.add_spec(l2).add_spec(l3), u4, l4);
    // λ-sum ≡ λ·mEff via distributes (each step symmetric)
    Rational::lemma_mul_distributes_over_add(lambda, m1, m2);
    Rational::lemma_mul_distributes_over_add(lambda, m1.add_spec(m2), m3);
    Rational::lemma_mul_distributes_over_add(lambda, m1.add_spec(m2).add_spec(m3), m4);
    Rational::lemma_eqv_symmetric(lambda.mul_spec(m1.add_spec(m2)), l1.add_spec(l2));
    Rational::lemma_eqv_symmetric(
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3)),
        lambda.mul_spec(m1.add_spec(m2)).add_spec(l3));
    Rational::lemma_eqv_symmetric(
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3).add_spec(m4)),
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3)).add_spec(l4));
    // chain: (l1+l2)+l3 ≡ λ(m12) + l3 ≡ λ(m123)
    Rational::lemma_eqv_reflexive(l3);
    Rational::lemma_eqv_add_congruence(
        l1.add_spec(l2), lambda.mul_spec(m1.add_spec(m2)), l3, l3);
    Rational::lemma_eqv_transitive(
        l1.add_spec(l2).add_spec(l3),
        lambda.mul_spec(m1.add_spec(m2)).add_spec(l3),
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3)));
    // + l4 ≡ λ·mEff
    Rational::lemma_eqv_reflexive(l4);
    Rational::lemma_eqv_add_congruence(
        l1.add_spec(l2).add_spec(l3), lambda.mul_spec(m1.add_spec(m2).add_spec(m3)), l4, l4);
    Rational::lemma_eqv_transitive(
        l1.add_spec(l2).add_spec(l3).add_spec(l4),
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3)).add_spec(l4),
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3).add_spec(m4)));
    // U ≡ λ·mEff
    Rational::lemma_eqv_transitive(
        u1.add_spec(u2).add_spec(u3).add_spec(u4),
        l1.add_spec(l2).add_spec(l3).add_spec(l4),
        lambda.mul_spec(m1.add_spec(m2).add_spec(m3).add_spec(m4)));
}

// ── the workhorse: J·v′ ≡ J·v + λ·mEff ────────────────────────────────

/// Applying impulse λ through a row's J blocks to both endpoints changes
/// the row rate by exactly λ·mEff (SPEC §6 PGS identity, exact rationals).
pub proof fn lemma_row_vel_after_impulse(
    jla: Vec2<Rational>,
    jaa: Rational,
    jlb: Vec2<Rational>,
    jab: Rational,
    inv_ma: Rational,
    inv_ia: Rational,
    inv_mb: Rational,
    inv_ib: Rational,
    va: Vec2<Rational>,
    wa: Rational,
    vb: Vec2<Rational>,
    wb: Rational,
    lambda: Rational,
)
    ensures
        row_vel_spec(
            jla, jaa, jlb, jab,
            vel_after_impulse(inv_ma, inv_ia, jla, jaa, lambda, va, wa).0,
            vel_after_impulse(inv_ma, inv_ia, jla, jaa, lambda, va, wa).1,
            vel_after_impulse(inv_mb, inv_ib, jlb, jab, lambda, vb, wb).0,
            vel_after_impulse(inv_mb, inv_ib, jlb, jab, lambda, vb, wb).1,
        ).eqv_spec(
            row_vel_spec(jla, jaa, jlb, jab, va, wa, vb, wb).add_spec(
                lambda.mul_spec(eff_mass_spec(
                    jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib)))),
{
    let t1 = vdot(jla, va);
    let t2 = jaa.mul_spec(wa);
    let t3 = vdot(jlb, vb);
    let t4 = jab.mul_spec(wb);
    let m1 = vdot(jla, jla).mul_spec(inv_ma);
    let m2 = jaa.mul_spec(jaa).mul_spec(inv_ia);
    let m3 = vdot(jlb, jlb).mul_spec(inv_mb);
    let m4 = jab.mul_spec(jab).mul_spec(inv_ib);
    let ca = inv_ma.mul_spec(lambda);
    let cb = inv_mb.mul_spec(lambda);
    let u1 = ca.mul_spec(vdot(jla, jla));
    let u2 = lambda.mul_spec(m2);
    let u3 = cb.mul_spec(vdot(jlb, jlb));
    let u4 = lambda.mul_spec(m4);
    // per-term: ti′ ≡ ti + ui
    lemma_vdot_vadd_scale(jla, va, ca);
    lemma_impulse_lin_term(inv_ma, lambda, vdot(jla, jla));
    lemma_ang_after_impulse(jaa, wa, inv_ia, lambda);
    lemma_vdot_vadd_scale(jlb, vb, cb);
    lemma_impulse_lin_term(inv_mb, lambda, vdot(jlb, jlb));
    lemma_ang_after_impulse(jab, wb, inv_ib, lambda);
    let t1p = vdot(jla, vadd(va, vscale(ca, jla)));
    let t2p = jaa.mul_spec(wa.add_spec(inv_ia.mul_spec(lambda).mul_spec(jaa)));
    let t3p = vdot(jlb, vadd(vb, vscale(cb, jlb)));
    let t4p = jab.mul_spec(wb.add_spec(inv_ib.mul_spec(lambda).mul_spec(jab)));
    // ui ≡ λ·mi
    assert(u1.eqv_spec(lambda.mul_spec(m1)));
    assert(u3.eqv_spec(lambda.mul_spec(m3)));
    Rational::lemma_eqv_reflexive(u2);
    Rational::lemma_eqv_reflexive(u4);
    // Jv′ ≡ ((t1+u1)+(t2+u2))+(t3+u3))+(t4+u4) via add congruence
    Rational::lemma_eqv_add_congruence(t1p, t1.add_spec(u1), t2p, t2.add_spec(u2));
    Rational::lemma_eqv_add_congruence(
        t1p.add_spec(t2p), t1.add_spec(u1).add_spec(t2.add_spec(u2)), t3p, t3.add_spec(u3));
    Rational::lemma_eqv_add_congruence(
        t1p.add_spec(t2p).add_spec(t3p),
        t1.add_spec(u1).add_spec(t2.add_spec(u2)).add_spec(t3.add_spec(u3)),
        t4p, t4.add_spec(u4));
    // pair swaps: (t+u) sums ≡ (t-sums) + (u-sums)
    lemma_add_pair_swap(t1, u1, t2, u2);
    Rational::lemma_eqv_transitive(
        t1p.add_spec(t2p),
        t1.add_spec(u1).add_spec(t2.add_spec(u2)),
        t1.add_spec(t2).add_spec(u1.add_spec(u2)));
    Rational::lemma_eqv_reflexive(t3.add_spec(u3));
    Rational::lemma_eqv_add_congruence(
        t1.add_spec(u1).add_spec(t2.add_spec(u2)),
        t1.add_spec(t2).add_spec(u1.add_spec(u2)),
        t3.add_spec(u3), t3.add_spec(u3));
    lemma_add_pair_swap(t1.add_spec(t2), u1.add_spec(u2), t3, u3);
    Rational::lemma_eqv_transitive(
        t1p.add_spec(t2p).add_spec(t3p),
        t1.add_spec(u1).add_spec(t2.add_spec(u2)).add_spec(t3.add_spec(u3)),
        t1.add_spec(t2).add_spec(u1.add_spec(u2)).add_spec(t3.add_spec(u3)));
    Rational::lemma_eqv_transitive(
        t1p.add_spec(t2p).add_spec(t3p),
        t1.add_spec(t2).add_spec(u1.add_spec(u2)).add_spec(t3.add_spec(u3)),
        t1.add_spec(t2).add_spec(t3).add_spec(u1.add_spec(u2).add_spec(u3)));
    Rational::lemma_eqv_transitive(
        t1.add_spec(u1).add_spec(t2.add_spec(u2)).add_spec(t3.add_spec(u3)),
        t1.add_spec(t2).add_spec(u1.add_spec(u2)).add_spec(t3.add_spec(u3)),
        t1.add_spec(t2).add_spec(t3).add_spec(u1.add_spec(u2).add_spec(u3)));
    Rational::lemma_eqv_reflexive(t4.add_spec(u4));
    Rational::lemma_eqv_add_congruence(
        t1.add_spec(u1).add_spec(t2.add_spec(u2)).add_spec(t3.add_spec(u3)),
        t1.add_spec(t2).add_spec(t3).add_spec(u1.add_spec(u2).add_spec(u3)),
        t4.add_spec(u4), t4.add_spec(u4));
    lemma_add_pair_swap(
        t1.add_spec(t2).add_spec(t3), u1.add_spec(u2).add_spec(u3), t4, u4);
    Rational::lemma_eqv_transitive(
        t1p.add_spec(t2p).add_spec(t3p).add_spec(t4p),
        t1.add_spec(u1).add_spec(t2.add_spec(u2)).add_spec(t3.add_spec(u3)).add_spec(
            t4.add_spec(u4)),
        t1.add_spec(t2).add_spec(t3).add_spec(u1.add_spec(u2).add_spec(u3)).add_spec(
            t4.add_spec(u4)));
    Rational::lemma_eqv_transitive(
        t1p.add_spec(t2p).add_spec(t3p).add_spec(t4p),
        t1.add_spec(t2).add_spec(t3).add_spec(u1.add_spec(u2).add_spec(u3)).add_spec(
            t4.add_spec(u4)),
        t1.add_spec(t2).add_spec(t3).add_spec(t4).add_spec(
            u1.add_spec(u2).add_spec(u3).add_spec(u4)));
    // U ≡ λ·mEff, then congruence under Jv +
    lemma_sum4_lambda_meff(u1, u2, u3, u4, m1, m2, m3, m4, lambda);
    let jv = row_vel_spec(jla, jaa, jlb, jab, va, wa, vb, wb);
    Rational::lemma_eqv_reflexive(jv);
    Rational::lemma_eqv_add_congruence(
        jv, jv,
        u1.add_spec(u2).add_spec(u3).add_spec(u4),
        lambda.mul_spec(eff_mass_spec(jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib)));
    Rational::lemma_eqv_transitive(
        t1p.add_spec(t2p).add_spec(t3p).add_spec(t4p),
        jv.add_spec(u1.add_spec(u2).add_spec(u3).add_spec(u4)),
        jv.add_spec(lambda.mul_spec(eff_mass_spec(
            jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib))));
    assert(t1p.add_spec(t2p).add_spec(t3p).add_spec(t4p) == row_vel_spec(
        jla, jaa, jlb, jab,
        vel_after_impulse(inv_ma, inv_ia, jla, jaa, lambda, va, wa).0,
        vel_after_impulse(inv_ma, inv_ia, jla, jaa, lambda, va, wa).1,
        vel_after_impulse(inv_mb, inv_ib, jlb, jab, lambda, vb, wb).0,
        vel_after_impulse(inv_mb, inv_ib, jlb, jab, lambda, vb, wb).1,
    ));
}

// ── momentum exchange ──────────────────────────────────────────────────

/// m·((inv_m·λ)·j) ≡ λ·j where m = 1/inv_m (dynamic body): the linear-
/// momentum transfer of one impulse application is EXACTLY λ·j.
pub proof fn lemma_impulse_momentum_transfer(
    inv_m: Rational,
    lambda: Rational,
    j: Rational,
)
    requires
        inv_m.num != 0,
    ensures
        Rational::from_int_spec(1).div_spec(inv_m).mul_spec(
            inv_m.mul_spec(lambda).mul_spec(j)).eqv_spec(lambda.mul_spec(j)),
{
    let m = Rational::from_int_spec(1).div_spec(inv_m);
    // m ≡ inv_m.reciprocal_spec():  div is mul by recip; 1·recip ≡ recip
    let recip = Rational::lemma_reciprocal_spec_inverse(inv_m);
    assert(m == Rational::from_int_spec(1).mul_spec(recip));
    Rational::lemma_mul_commutative(Rational::from_int_spec(1), recip);
    Rational::lemma_mul_one_identity(recip);
    Rational::lemma_eqv_transitive(
        m, Rational::from_int_spec(1).mul_spec(recip), recip.mul_spec(Rational::from_int_spec(1)));
    Rational::lemma_eqv_transitive(
        m, recip.mul_spec(Rational::from_int_spec(1)), recip);
    // m·inv_m ≡ 1
    Rational::lemma_eqv_reflexive(inv_m);
    Rational::lemma_eqv_mul_congruence(m, recip, inv_m, inv_m);
    assert(recip.mul_spec(inv_m).eqv_spec(Rational::from_int_spec(1)));
    Rational::lemma_eqv_transitive(
        m.mul_spec(inv_m), recip.mul_spec(inv_m), Rational::from_int_spec(1));
    // m·((inv·λ)·j) ≡ (m·(inv·λ))·j ≡ ((m·inv)·λ)·j
    Rational::lemma_mul_associative(m, inv_m.mul_spec(lambda), j);
    Rational::lemma_mul_associative(m, inv_m, lambda);
    Rational::lemma_eqv_symmetric(
        m.mul_spec(inv_m).mul_spec(lambda), m.mul_spec(inv_m.mul_spec(lambda)));
    Rational::lemma_eqv_reflexive(j);
    Rational::lemma_eqv_mul_congruence(
        m.mul_spec(inv_m.mul_spec(lambda)), m.mul_spec(inv_m).mul_spec(lambda), j, j);
    // ((m·inv)·λ)·j ≡ (1·λ)·j ≡ (λ·1)·j ≡ λ·j
    Rational::lemma_eqv_reflexive(lambda);
    Rational::lemma_eqv_mul_congruence(
        m.mul_spec(inv_m), Rational::from_int_spec(1), lambda, lambda);
    Rational::lemma_eqv_reflexive(j);
    Rational::lemma_eqv_mul_congruence(
        m.mul_spec(inv_m).mul_spec(lambda),
        Rational::from_int_spec(1).mul_spec(lambda), j, j);
    Rational::lemma_mul_commutative(Rational::from_int_spec(1), lambda);
    Rational::lemma_eqv_reflexive(j);
    Rational::lemma_eqv_mul_congruence(
        Rational::from_int_spec(1).mul_spec(lambda), lambda.mul_spec(Rational::from_int_spec(1)),
        j, j);
    Rational::lemma_mul_one_identity(lambda);
    Rational::lemma_eqv_reflexive(j);
    Rational::lemma_eqv_mul_congruence(
        lambda.mul_spec(Rational::from_int_spec(1)), lambda, j, j);
    // full chain
    Rational::lemma_eqv_transitive(
        m.mul_spec(inv_m.mul_spec(lambda).mul_spec(j)),
        m.mul_spec(inv_m.mul_spec(lambda)).mul_spec(j),
        m.mul_spec(inv_m).mul_spec(lambda).mul_spec(j));
    Rational::lemma_eqv_transitive(
        m.mul_spec(inv_m.mul_spec(lambda).mul_spec(j)),
        m.mul_spec(inv_m).mul_spec(lambda).mul_spec(j),
        Rational::from_int_spec(1).mul_spec(lambda).mul_spec(j));
    Rational::lemma_eqv_transitive(
        m.mul_spec(inv_m.mul_spec(lambda).mul_spec(j)),
        Rational::from_int_spec(1).mul_spec(lambda).mul_spec(j),
        lambda.mul_spec(Rational::from_int_spec(1)).mul_spec(j));
    Rational::lemma_eqv_transitive(
        m.mul_spec(inv_m.mul_spec(lambda).mul_spec(j)),
        lambda.mul_spec(Rational::from_int_spec(1)).mul_spec(j),
        lambda.mul_spec(j));
}

/// Exact momentum exchange for a contact impulse, both bodies dynamic:
/// m_a·Δv_a + m_b·Δv_b ≡ λ·(−n) + λ·n ≡ 0 per component — the transfer is
/// equal and opposite (the C1 corollary shape of SPEC §7).
pub proof fn lemma_contact_momentum_exchange(
    n: Vec2<Rational>,
    inv_ma: Rational,
    inv_mb: Rational,
    lambda: Rational,
)
    requires
        inv_ma.num != 0,
        inv_mb.num != 0,
    ensures {
        let jla = vscale(Rational::from_int_spec(-1), n);
        let ma = Rational::from_int_spec(1).div_spec(inv_ma);
        let mb = Rational::from_int_spec(1).div_spec(inv_mb);
        &&& ma.mul_spec(inv_ma.mul_spec(lambda).mul_spec(jla.x)).add_spec(
                mb.mul_spec(inv_mb.mul_spec(lambda).mul_spec(n.x)))
            .eqv_spec(Rational::from_int_spec(0))
        &&& ma.mul_spec(inv_ma.mul_spec(lambda).mul_spec(jla.y)).add_spec(
                mb.mul_spec(inv_mb.mul_spec(lambda).mul_spec(n.y)))
            .eqv_spec(Rational::from_int_spec(0))
    },
{
    let z = Rational::from_int_spec(0);
    let jla = vscale(Rational::from_int_spec(-1), n);
    let ma = Rational::from_int_spec(1).div_spec(inv_ma);
    let mb = Rational::from_int_spec(1).div_spec(inv_mb);
    // x component
    lemma_impulse_momentum_transfer(inv_ma, lambda, jla.x);
    lemma_impulse_momentum_transfer(inv_mb, lambda, n.x);
    // λ·jla.x == −(λ·n.x) (structural: jla.x == −n.x, neg-mul-right)
    lemma_raw_neg_one_mul(n.x);
    assert(jla.x == n.x.neg_spec());
    lemma_raw_neg_mul_right(lambda, n.x);
    assert(lambda.mul_spec(jla.x) == lambda.mul_spec(n.x).neg_spec());
    // sum ≡ (−λnx) + λnx ≡ λnx + (−λnx) == λnx − λnx ≡ 0
    Rational::lemma_eqv_reflexive(lambda.mul_spec(n.x));
    Rational::lemma_eqv_add_congruence(
        ma.mul_spec(inv_ma.mul_spec(lambda).mul_spec(jla.x)),
        lambda.mul_spec(jla.x),
        mb.mul_spec(inv_mb.mul_spec(lambda).mul_spec(n.x)),
        lambda.mul_spec(n.x));
    Rational::lemma_add_commutative(
        lambda.mul_spec(n.x).neg_spec(), lambda.mul_spec(n.x));
    Rational::lemma_eqv_transitive(
        lambda.mul_spec(n.x).neg_spec().add_spec(lambda.mul_spec(n.x)),
        lambda.mul_spec(n.x).add_spec(lambda.mul_spec(n.x).neg_spec()),
        lambda.mul_spec(n.x).sub_spec(lambda.mul_spec(n.x)));
    Rational::lemma_sub_self(lambda.mul_spec(n.x));
    Rational::lemma_eqv_transitive(
        lambda.mul_spec(n.x).neg_spec().add_spec(lambda.mul_spec(n.x)),
        lambda.mul_spec(n.x).sub_spec(lambda.mul_spec(n.x)),
        z);
    Rational::lemma_eqv_transitive(
        ma.mul_spec(inv_ma.mul_spec(lambda).mul_spec(jla.x)).add_spec(
            mb.mul_spec(inv_mb.mul_spec(lambda).mul_spec(n.x))),
        lambda.mul_spec(n.x).neg_spec().add_spec(lambda.mul_spec(n.x)),
        z);
    // y component (same shape)
    lemma_impulse_momentum_transfer(inv_ma, lambda, jla.y);
    lemma_impulse_momentum_transfer(inv_mb, lambda, n.y);
    lemma_raw_neg_one_mul(n.y);
    assert(jla.y == n.y.neg_spec());
    lemma_raw_neg_mul_right(lambda, n.y);
    assert(lambda.mul_spec(jla.y) == lambda.mul_spec(n.y).neg_spec());
    Rational::lemma_eqv_reflexive(lambda.mul_spec(n.y));
    Rational::lemma_eqv_add_congruence(
        ma.mul_spec(inv_ma.mul_spec(lambda).mul_spec(jla.y)),
        lambda.mul_spec(jla.y),
        mb.mul_spec(inv_mb.mul_spec(lambda).mul_spec(n.y)),
        lambda.mul_spec(n.y));
    Rational::lemma_add_commutative(
        lambda.mul_spec(n.y).neg_spec(), lambda.mul_spec(n.y));
    Rational::lemma_eqv_transitive(
        lambda.mul_spec(n.y).neg_spec().add_spec(lambda.mul_spec(n.y)),
        lambda.mul_spec(n.y).add_spec(lambda.mul_spec(n.y).neg_spec()),
        lambda.mul_spec(n.y).sub_spec(lambda.mul_spec(n.y)));
    Rational::lemma_sub_self(lambda.mul_spec(n.y));
    Rational::lemma_eqv_transitive(
        lambda.mul_spec(n.y).neg_spec().add_spec(lambda.mul_spec(n.y)),
        lambda.mul_spec(n.y).sub_spec(lambda.mul_spec(n.y)),
        z);
    Rational::lemma_eqv_transitive(
        ma.mul_spec(inv_ma.mul_spec(lambda).mul_spec(jla.y)).add_spec(
            mb.mul_spec(inv_mb.mul_spec(lambda).mul_spec(n.y))),
        lambda.mul_spec(n.y).neg_spec().add_spec(lambda.mul_spec(n.y)),
        z);
}

// ── C3: restitution/no-suck for the single fresh-row update ───────────

/// C3 (SPEC §7, e = 0): after a single PGS update of a fresh contact row
/// (λ = 0, bias = 0, lo = 0, hi = ∞), the post relative normal velocity
/// is ≥ 0 — and exactly ≡ 0 when the update is unclamped (perfectly
/// inelastic: the contact neither sucks in nor gains energy).
pub proof fn lemma_solve_row_c3(
    jla: Vec2<Rational>,
    jaa: Rational,
    jlb: Vec2<Rational>,
    jab: Rational,
    inv_ma: Rational,
    inv_ia: Rational,
    inv_mb: Rational,
    inv_ib: Rational,
    va: Vec2<Rational>,
    wa: Rational,
    vb: Vec2<Rational>,
    wb: Rational,
    lam: Rational,
)
    requires
        Rational::from_int_spec(0).lt_spec(eff_mass_spec(
            jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib)),
        lam == clamp_spec(
            Rational::from_int_spec(0).sub_spec(
                row_vel_spec(jla, jaa, jlb, jab, va, wa, vb, wb)
                    .add_spec(Rational::from_int_spec(0)).div_spec(eff_mass_spec(
                        jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib))),
            Option::Some(Rational::from_int_spec(0)),
            Option::None),
    ensures
        Rational::from_int_spec(0).le_spec(row_vel_spec(
            jla, jaa, jlb, jab,
            vel_after_impulse(inv_ma, inv_ia, jla, jaa, lam, va, wa).0,
            vel_after_impulse(inv_ma, inv_ia, jla, jaa, lam, va, wa).1,
            vel_after_impulse(inv_mb, inv_ib, jlb, jab, lam, vb, wb).0,
            vel_after_impulse(inv_mb, inv_ib, jlb, jab, lam, vb, wb).1,
        )),
{
    let z = Rational::from_int_spec(0);
    let meff = eff_mass_spec(jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib);
    let vrel = row_vel_spec(jla, jaa, jlb, jab, va, wa, vb, wb);
    let x = z.sub_spec(vrel.add_spec(z).div_spec(meff));
    let vrel1 = row_vel_spec(
        jla, jaa, jlb, jab,
        vel_after_impulse(inv_ma, inv_ia, jla, jaa, lam, va, wa).0,
        vel_after_impulse(inv_ma, inv_ia, jla, jaa, lam, va, wa).1,
        vel_after_impulse(inv_mb, inv_ib, jlb, jab, lam, vb, wb).0,
        vel_after_impulse(inv_mb, inv_ib, jlb, jab, lam, vb, wb).1,
    );
    // meff ≢ 0 (needed by div_cancel)
    Rational::lemma_trichotomy(z, meff);
    Rational::lemma_eqv_symmetric(z, meff);
    assert(!meff.eqv_spec(z));
    // vrel + 0 == vrel; x = 0 − (vrel/meff) == −(vrel/meff) (both structural)
    Rational::lemma_add_zero_identity(vrel);
    assert(vrel.add_spec(z) == vrel);
    Rational::lemma_add_zero_identity(vrel.div_spec(meff).neg_spec());
    assert(x == vrel.div_spec(meff).neg_spec());
    // J·v′ ≡ vrel + λ·meff
    lemma_row_vel_after_impulse(
        jla, jaa, jlb, jab, inv_ma, inv_ia, inv_mb, inv_ib, va, wa, vb, wb, lam);
    // clamp with lo = 0, hi = ∞: lam = if x < 0 then 0 else x
    assert(lam == (if x.lt_spec(z) { z } else { x }));
    if x.lt_spec(z) {
        // λ = 0: vrel′ ≡ vrel. x < 0 ⟹ vrel/meff > 0 ⟹ vrel > 0.
        assert(lam == z);
        Rational::lemma_neg_reverses_lt(x, z);
        assert(z.neg_spec() == z);
        assert(z.lt_spec(x.neg_spec()));
        assert(x.neg_spec() == vrel.div_spec(meff));
        Rational::lemma_div_cancel(meff, vrel);
        Rational::lemma_pos_mul_pos(meff, vrel.div_spec(meff));
        Rational::lemma_eqv_implies_le(meff.mul_spec(vrel.div_spec(meff)), vrel);
        Rational::lemma_lt_le_transitive(z, meff.mul_spec(vrel.div_spec(meff)), vrel);
        Rational::lemma_lt_implies_le(z, vrel);
        // vrel′ ≡ vrel + 0·meff ≡ vrel + 0 == vrel
        Rational::lemma_mul_zero(meff);
        Rational::lemma_mul_commutative(z, meff);
        Rational::lemma_eqv_transitive(z.mul_spec(meff), meff.mul_spec(z), z);
        Rational::lemma_eqv_reflexive(vrel);
        Rational::lemma_eqv_add_congruence(vrel, vrel, lam.mul_spec(meff), z);
        Rational::lemma_add_zero_identity(vrel);
        Rational::lemma_eqv_transitive(
            vrel.add_spec(lam.mul_spec(meff)), vrel.add_spec(z), vrel);
        Rational::lemma_eqv_transitive(vrel1, vrel.add_spec(lam.mul_spec(meff)), vrel);
        Rational::lemma_eqv_symmetric(vrel1, vrel);
        Rational::lemma_eqv_implies_le(vrel, vrel1);
        Rational::lemma_le_transitive(z, vrel, vrel1);
    } else {
        // λ = −(vrel/meff): vrel′ ≡ vrel + (−vrel) ≡ 0.
        assert(lam == x);
        assert(lam == vrel.div_spec(meff).neg_spec());
        // λ·meff ≡ −vrel:  structural neg-mul-left, comm, div_cancel, neg congr
        lemma_raw_neg_mul_left(vrel.div_spec(meff), meff);
        assert(lam.mul_spec(meff) == vrel.div_spec(meff).mul_spec(meff).neg_spec());
        Rational::lemma_mul_commutative(vrel.div_spec(meff), meff);
        Rational::lemma_eqv_neg_congruence(
            vrel.div_spec(meff).mul_spec(meff), meff.mul_spec(vrel.div_spec(meff)));
        Rational::lemma_div_cancel(meff, vrel);
        Rational::lemma_eqv_neg_congruence(meff.mul_spec(vrel.div_spec(meff)), vrel);
        Rational::lemma_eqv_transitive(
            lam.mul_spec(meff),
            vrel.div_spec(meff).mul_spec(meff).neg_spec(),
            meff.mul_spec(vrel.div_spec(meff)).neg_spec());
        Rational::lemma_eqv_transitive(
            lam.mul_spec(meff),
            meff.mul_spec(vrel.div_spec(meff)).neg_spec(),
            vrel.neg_spec());
        // vrel′ ≡ vrel + (−vrel) == vrel − vrel ≡ 0
        Rational::lemma_eqv_reflexive(vrel);
        Rational::lemma_eqv_add_congruence(vrel, vrel, lam.mul_spec(meff), vrel.neg_spec());
        Rational::lemma_eqv_transitive(
            vrel1, vrel.add_spec(lam.mul_spec(meff)), vrel.add_spec(vrel.neg_spec()));
        assert(vrel.add_spec(vrel.neg_spec()) == vrel.sub_spec(vrel));
        Rational::lemma_sub_self(vrel);
        Rational::lemma_eqv_transitive(vrel1, vrel.sub_spec(vrel), z);
        Rational::lemma_eqv_symmetric(vrel1, z);
        Rational::lemma_eqv_implies_le(z, vrel1);
    }
}

} // verus!
