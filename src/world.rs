//! World: the full simulation state (SPEC §1). Stepping (phys-03) is a
//! PURE function World -> StepResult (Ok | Reject, SPEC §1/A9); nothing
//! here mutates during a step except through the constructors below.

use vstd::prelude::*;

use verus_algebra::traits::*;

use crate::body::Body;
use crate::joints::Joint;
use crate::types::{q_nonneg, q_pos, SVec2, Scalar};

verus! {

pub struct World {
    pub bodies: Vec<Body>,
    pub joints: Vec<Joint>,
    pub gravity: SVec2,
    pub dt: Scalar,
    /// Arctan series truncation index for the angle ledger (SPEC §3).
    pub series_k: usize,
    /// Per-body accumulated angle-enclosure width (E2 ledger, phys-03).
    pub angle_err: Vec<Scalar>,
}

impl World {
    pub open spec fn wf_spec(&self) -> bool {
        &&& forall|i: int|
                0 <= i < self.bodies@.len() ==> (#[trigger] self.bodies@[i]).wf_spec()
        &&& forall|j: int|
                0 <= j < self.joints@.len() ==> {
                    let jj = #[trigger] self.joints@[j];
                    &&& jj.wf_spec()
                    &&& (jj.a as int) < self.bodies@.len()
                    &&& (jj.b as int) < self.bodies@.len()
                }
        &&& self.gravity.wf_spec()
        &&& self.dt.wf_spec()
        &&& q_pos(self.dt@)
        &&& self.series_k < 1_000_000
        &&& self.angle_err@.len() == self.bodies@.len()
        &&& forall|i: int|
                0 <= i < self.angle_err@.len() ==> {
                    let e = #[trigger] self.angle_err@[i];
                    e.wf_spec() && q_nonneg(e@)
                }
    }

    pub fn new(gravity: SVec2, dt: Scalar, series_k: usize) -> (out: Self)
        requires
            gravity.wf_spec(),
            dt.wf_spec(),
            q_pos(dt@),
            series_k < 1_000_000,
        ensures
            out.wf_spec(),
            out.bodies@.len() == 0,
            out.joints@.len() == 0,
            out.angle_err@.len() == 0,
            out.gravity == gravity,
            out.dt == dt,
            out.series_k == series_k,
    {
        World { bodies: Vec::new(), joints: Vec::new(), gravity, dt, series_k, angle_err: Vec::new() }
    }

    /// Canonical body identity = index in `bodies` (E6: canonical order).
    pub fn add_body(&mut self, b: Body) -> (id: usize)
        requires
            old(self).wf_spec(),
            b.wf_spec(),
        ensures
            self.wf_spec(),
            id == old(self).bodies@.len(),
            self.bodies@.len() == old(self).bodies@.len() + 1,
            self.bodies@[id as int] == b,
            forall|i: int|
                0 <= i < old(self).bodies@.len()
                    ==> self.bodies@[i] == old(self).bodies@[i],
            self.joints@ == old(self).joints@,
            forall|i: int|
                0 <= i < old(self).angle_err@.len()
                    ==> self.angle_err@[i] == old(self).angle_err@[i],
            self.angle_err@[id as int]@ == verus_rational::Rational::from_int_spec(0),
            self.gravity == old(self).gravity,
            self.dt == old(self).dt,
            self.series_k == old(self).series_k,
    {
        let id = self.bodies.len();
        self.bodies.push(b);
        self.angle_err.push(Scalar::from_int(0));
        proof {
            crate::types::lemma_zero_nonneg();
        }
        id
    }
}

} // verus!
