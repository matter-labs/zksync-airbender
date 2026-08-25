#![allow(incomplete_features)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// `UnsafeMutAccessor::get_mut(&self) -> &mut T` is the documented contract
// scaffolding for stream-scheduled callbacks — see gpu_core primitives.
#![allow(clippy::mut_from_ref)]

mod context;
pub mod transfer;
pub(crate) mod upstream;

pub use context::{
    DeviceAllocatorGeometry, DeviceMemoryHighWaterObserver, PoolMemoryHighWaterReport,
    PoolMemoryHighWaterSnapshot, PoolMemoryUsage, ProverContext, ProverContextConfig,
};

#[cfg(test)]
gpu_core::force_serial_libtest!();
