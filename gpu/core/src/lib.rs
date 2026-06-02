//! GPU substrate: static device/host allocators + CUDA primitives
//! (device_structures, DeviceMatrix family, accessors, field, callbacks,
//! device_tracing, machine_type, nvtx, static_host, utils). Extracted from
//! circuit_prover; pure-Rust substrate over era_cudart/fft + cs/field.

#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(btree_cursors)]
#![feature(generic_const_exprs)]
#![feature(pointer_is_aligned_to)]
// `UnsafeMutAccessor::get_mut(&self) -> &mut T` is the documented contract
// scaffolding for stream-scheduled callbacks — see primitives/context.rs.
#![allow(clippy::mut_from_ref)]

mod upstream;

pub mod allocator;
pub mod primitives;

#[cfg(feature = "bench")]
pub mod bench;
