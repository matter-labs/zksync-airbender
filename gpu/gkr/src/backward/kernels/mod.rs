mod dim_reducing;
mod encoding;
mod fused_tail;
mod launchers;
mod main_layer;
mod shared;

pub(crate) use dim_reducing::*;
pub(crate) use encoding::*;
pub(crate) use fused_tail::*;
pub(crate) use launchers::*;
pub(crate) use main_layer::*;
pub(crate) use shared::*;

// `pub` re-exports (not `pub(crate)`): the apex proof/whir layer and the apex
// e2e tests consume these through `gpu_gkr::backward::…` (backward/mod.rs
// re-exports them again). Pinned public API of the gpu_gkr split.
pub use dim_reducing::GpuGKRDimensionReducingBackwardState;
pub use launchers::{
    eq_group_count, eq_group_tables_len, gkr_dim_reducing_launch_config,
    launch_build_eq_values_from_point, make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN,
    GKR_EQ_HIGH_SLOTS,
};
pub(crate) use shared::DeviceClaimPointAndBatching;
pub use shared::{ClaimBufferLayout, GpuGKRBackwardScheduledExecution};

#[cfg(test)]
mod tests;
