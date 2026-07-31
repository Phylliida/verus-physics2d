//! verus-physics2d — formally verified 2D rigid-body physics engine.
//!
//! Master plan: ../physics-gears/DESIGN.md (v1.3)
//! Implementation spec: ../physics-gears/SPEC-phase1.md
//!
//! Layer L1: exact rational engine core. All positions, shapes, velocities
//! and impulses are exact rationals; orientation is an exact rational point
//! on the unit circle (RotQ). No f32/f64 anywhere in this crate.

#[cfg(verus_keep_ghost)]
pub mod types;

#[cfg(verus_keep_ghost)]
pub mod rotq;

#[cfg(verus_keep_ghost)]
pub mod body;

#[cfg(verus_keep_ghost)]
pub mod world;

#[cfg(verus_keep_ghost)]
pub mod proofs;

#[cfg(verus_keep_ghost)]
pub mod angle_ledger;

#[cfg(verus_keep_ghost)]
pub mod step;

#[cfg(verus_keep_ghost)]
pub mod momentum;

#[cfg(verus_keep_ghost)]
pub mod scenes;

#[cfg(verus_keep_ghost)]
pub mod shape;

#[cfg(verus_keep_ghost)]
pub mod joints;

#[cfg(verus_keep_ghost)]
pub mod narrowphase;

#[cfg(verus_keep_ghost)]
pub mod massprops;

#[cfg(verus_keep_ghost)]
pub mod broadphase;

#[cfg(verus_keep_ghost)]
pub mod row;

#[cfg(verus_keep_ghost)]
pub mod certificate;
