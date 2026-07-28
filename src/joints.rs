//! Joints (phys-05c: datatype only; SPEC §6). Row generation for revolute
//! and prismatic joints is phys-07/phys-22 work — this module lands the
//! `Joint` datatype in the SAME crate-wide change as `Body.shape` and
//! `StepResult` (DESIGN §3.7(a): one cache invalidation, not three).

use vstd::prelude::*;

use crate::types::{copy_svec2, SVec2};

verus! {

/// Revolute (pin) joint: local anchor points on bodies a and b. The
/// constraint (two rows: x and y anchor coincidence) is generated in
/// phys-07; phys-05c only carries the data.
pub struct Joint {
    pub a: usize,
    pub b: usize,
    pub anchor_a: SVec2,
    pub anchor_b: SVec2,
}

impl Joint {
    /// Self-contained well-formedness. Index bounds (a, b < bodies.len())
    /// are a WORLD invariant, not part of this spec.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.anchor_a.wf_spec()
        &&& self.anchor_b.wf_spec()
    }

    pub fn new(a: usize, b: usize, anchor_a: SVec2, anchor_b: SVec2) -> (out: Self)
        requires
            anchor_a.wf_spec(),
            anchor_b.wf_spec(),
        ensures
            out.wf_spec(),
            out.a == a,
            out.b == b,
            out.anchor_a == anchor_a,
            out.anchor_b == anchor_b,
    {
        Joint { a, b, anchor_a, anchor_b }
    }

    /// Deep copy (BigInt witnesses aren't Copy).
    pub fn copy_joint(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.a == self.a,
            out.b == self.b,
            out.anchor_a.model@ == self.anchor_a.model@,
            out.anchor_b.model@ == self.anchor_b.model@,
    {
        Joint {
            a: self.a,
            b: self.b,
            anchor_a: copy_svec2(&self.anchor_a),
            anchor_b: copy_svec2(&self.anchor_b),
        }
    }
}

} // verus!
