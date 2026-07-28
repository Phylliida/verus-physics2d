//! Rigid body state (SPEC §1). inv_mass/inv_inertia form: statics are 0 —
//! no division by mass anywhere in the engine.

use vstd::prelude::*;

use verus_rational::{Rational, RuntimeRational};

use crate::rotq::RotQ;
use crate::shape::Compound;
use crate::types::{q_nonneg, SVec2, Scalar};

verus! {

pub struct Body {
    pub pos: SVec2,
    pub rot: RotQ,
    pub vel: SVec2,
    pub omega: Scalar,
    pub inv_mass: Scalar,
    pub inv_inertia: Scalar,
    pub shape: Compound,
}

impl Body {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.pos.wf_spec()
        &&& self.rot.wf_spec()
        &&& self.vel.wf_spec()
        &&& self.omega.wf_spec()
        &&& self.inv_mass.wf_spec()
        &&& self.inv_inertia.wf_spec()
        &&& q_nonneg(self.inv_mass@)
        &&& q_nonneg(self.inv_inertia@)
        &&& self.shape.wf_spec()
    }

    /// A body is static iff its inverse mass is (exactly, structurally)
    /// the canonical zero — constructors only ever store from_int(0).
    pub open spec fn is_static_spec(&self) -> bool {
        self.inv_mass@ == Rational::from_int_spec(0)
    }

    /// Dynamic body from explicit inverse mass/inertia.
    pub fn new_dynamic(
        pos: SVec2, rot: RotQ, vel: SVec2, omega: Scalar,
        inv_mass: Scalar, inv_inertia: Scalar, shape: Compound,
    ) -> (out: Self)
        requires
            pos.wf_spec(), rot.wf_spec(), vel.wf_spec(), omega.wf_spec(),
            inv_mass.wf_spec(), inv_inertia.wf_spec(),
            q_nonneg(inv_mass@), q_nonneg(inv_inertia@),
            shape.wf_spec(),
        ensures
            out.wf_spec(),
            out.pos == pos, out.rot == rot, out.vel == vel,
            out.omega == omega, out.inv_mass == inv_mass,
            out.inv_inertia == inv_inertia, out.shape == shape,
    {
        Body { pos, rot, vel, omega, inv_mass, inv_inertia, shape }
    }

    /// Static body: zero inverse mass/inertia, zero velocity.
    pub fn new_static(pos: SVec2, rot: RotQ, shape: Compound) -> (out: Self)
        requires pos.wf_spec(), rot.wf_spec(), shape.wf_spec(),
        ensures out.wf_spec(), out.is_static_spec(),
    {
        let vel = pos.zero();
        let omega = RuntimeRational::from_int(0);
        let inv_mass = RuntimeRational::from_int(0);
        let inv_inertia = RuntimeRational::from_int(0);
        proof {
            crate::types::lemma_zero_nonneg();
            assert(inv_mass@ == Rational::from_int_spec(0));
        }
        Body { pos, rot, vel, omega, inv_mass, inv_inertia, shape }
    }

    /// Deep copy (BigInt witnesses aren't Copy).
    pub fn copy_body(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.pos.model@ == self.pos.model@,
            out.rot.c@ == self.rot.c@,
            out.rot.s@ == self.rot.s@,
            out.vel.model@ == self.vel.model@,
            out.omega@ == self.omega@,
            out.inv_mass@ == self.inv_mass@,
            out.inv_inertia@ == self.inv_inertia@,
            out.shape.model_parts() == self.shape.model_parts(),
    {
        let pos = crate::types::copy_svec2(&self.pos);
        let rot = self.rot.copy();
        let vel = crate::types::copy_svec2(&self.vel);
        let omega = verus_rational::runtime_rational::copy_rational(&self.omega);
        let inv_mass = verus_rational::runtime_rational::copy_rational(&self.inv_mass);
        let inv_inertia = verus_rational::runtime_rational::copy_rational(&self.inv_inertia);
        let shape = self.shape.copy_compound();
        Body { pos, rot, vel, omega, inv_mass, inv_inertia, shape }
    }
}

} // verus!
