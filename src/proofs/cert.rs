//! Proof helpers for the certificate checker (phys-05d): the touching-case
//! depth reasoning, extracted from check_c4 to keep Z3 contexts small.

use vstd::prelude::*;

use verus_linalg::vec2::Vec2;
use verus_rational::Rational;

use crate::certificate::c4_touch_witness;
use crate::narrowphase::axis_separates;
use crate::proofs::shape::lemma_min_sep_attained;
use crate::shape::{edge_normal, min_sep};

verus! {

/// If every edge's min_sep ≤ 0, no axis separates (the classify_side None
/// case implies the negation of C4 disjuncts 1/2).
pub proof fn lemma_no_sep_witness_of_all_nonpos(
    owner: Seq<Vec2<Rational>>,
    other: Seq<Vec2<Rational>>,
)
    requires
        owner.len() >= 1,
        other.len() >= 1,
        forall|e: int|
            0 <= e < owner.len() ==> #[trigger] min_sep(
                edge_normal(owner[e], owner[(e + 1) % (owner.len() as int)]),
                owner[e], other, 0).le_spec(Rational::from_int_spec(0)),
    ensures
        !(exists|e: int| axis_separates(owner, other, e)),
{
    if exists|e: int| axis_separates(owner, other, e) {
        let e = choose|e: int| axis_separates(owner, other, e);
        // axis_separates: every axis_sep > 0; min is attained at some j,
        // so min_sep > 0 — contradicting the ≤ 0 hypothesis.
        lemma_min_sep_attained(
            edge_normal(owner[e], owner[(e + 1) % (owner.len() as int)]),
            owner[e], other, 0);
        assert(min_sep(
            edge_normal(owner[e], owner[(e + 1) % (owner.len() as int)]),
            owner[e], other, 0).le_spec(Rational::from_int_spec(0)));
        assert(false);
    }
}

/// The depth check passing yields the touching witness: the reported edge
/// of the greater side has min_sep ≥ −tol_p.
pub proof fn lemma_c4_witness_of_depth(
    wva: Seq<Vec2<Rational>>,
    wvb: Seq<Vec2<Rational>>,
    ms_a: Rational,
    ms_b: Rational,
    e_a: int,
    e_b: int,
    tol_p: Rational,
    a_ge_b: bool,
)
    requires
        0 <= e_a < wva.len(),
        0 <= e_b < wvb.len(),
        ms_a.eqv_spec(min_sep(
            edge_normal(wva[e_a], wva[(e_a + 1) % (wva.len() as int)]), wva[e_a], wvb, 0)),
        ms_b.eqv_spec(min_sep(
            edge_normal(wvb[e_b], wvb[(e_b + 1) % (wvb.len() as int)]), wvb[e_b], wva, 0)),
        a_ge_b ==> ms_b.le_spec(ms_a),
        !a_ge_b ==> ms_a.le_spec(ms_b),
        a_ge_b ==> tol_p.neg_spec().le_spec(ms_a),
        !a_ge_b ==> tol_p.neg_spec().le_spec(ms_b),
    ensures
        c4_touch_witness(wva, wvb, tol_p, a_ge_b, if a_ge_b { e_a } else { e_b }),
{
    if a_ge_b {
        Rational::lemma_eqv_implies_le(
            min_sep(edge_normal(wva[e_a], wva[(e_a + 1) % (wva.len() as int)]), wva[e_a], wvb, 0),
            ms_a);
        Rational::lemma_le_transitive(
            tol_p.neg_spec(),
            ms_a,
            min_sep(edge_normal(wva[e_a], wva[(e_a + 1) % (wva.len() as int)]), wva[e_a], wvb, 0));
    } else {
        Rational::lemma_eqv_implies_le(
            min_sep(edge_normal(wvb[e_b], wvb[(e_b + 1) % (wvb.len() as int)]), wvb[e_b], wva, 0),
            ms_b);
        Rational::lemma_le_transitive(
            tol_p.neg_spec(),
            ms_b,
            min_sep(edge_normal(wvb[e_b], wvb[(e_b + 1) % (wvb.len() as int)]), wvb[e_b], wva, 0));
    }
}

/// The depth check failing rules out every touching witness: any edge's
/// min_sep is ≤ its side's max, which is < −tol_p.
pub proof fn lemma_c4_no_witness_of_shallow(
    wva: Seq<Vec2<Rational>>,
    wvb: Seq<Vec2<Rational>>,
    ms_a: Rational,
    ms_b: Rational,
    tol_p: Rational,
    a_ge_b: bool,
)
    requires
        forall|e: int|
            0 <= e < wva.len() ==> #[trigger] min_sep(
                edge_normal(wva[e], wva[(e + 1) % (wva.len() as int)]), wva[e], wvb, 0).le_spec(
                ms_a),
        forall|e: int|
            0 <= e < wvb.len() ==> #[trigger] min_sep(
                edge_normal(wvb[e], wvb[(e + 1) % (wvb.len() as int)]), wvb[e], wva, 0).le_spec(
                ms_b),
        a_ge_b ==> (ms_b.le_spec(ms_a) && !tol_p.neg_spec().le_spec(ms_a)),
        !a_ge_b ==> (ms_a.le_spec(ms_b) && !tol_p.neg_spec().le_spec(ms_b)),
    ensures
        !(exists|fa: bool, e: int| c4_touch_witness(wva, wvb, tol_p, fa, e)),
{
    assert forall|fa: bool, e: int| !c4_touch_witness(wva, wvb, tol_p, fa, e) by {
        if c4_touch_witness(wva, wvb, tol_p, fa, e) {
            if fa {
                Rational::lemma_le_transitive(
                    tol_p.neg_spec(),
                    min_sep(edge_normal(wva[e], wva[(e + 1) % (wva.len() as int)]), wva[e], wvb, 0),
                    ms_a);
                if a_ge_b {
                    assert(false);
                } else {
                    Rational::lemma_le_transitive(tol_p.neg_spec(), ms_a, ms_b);
                    assert(false);
                }
            } else {
                Rational::lemma_le_transitive(
                    tol_p.neg_spec(),
                    min_sep(edge_normal(wvb[e], wvb[(e + 1) % (wvb.len() as int)]), wvb[e], wva, 0),
                    ms_b);
                if a_ge_b {
                    Rational::lemma_le_transitive(tol_p.neg_spec(), ms_b, ms_a);
                    assert(false);
                } else {
                    assert(false);
                }
            }
        }
    }
}

} // verus!
