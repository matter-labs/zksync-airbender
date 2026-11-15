// `pub` re-exports (not `pub(crate)`): the apex proof/whir layer and the apex
// e2e tests consume these through `gpu_gkr::backward::…` (backward/mod.rs
// re-exports them again). Pinned public API of the gpu_gkr split.
pub use crate::baby_bear::backward::kernels::{
    dim_reducing::GpuGKRDimensionReducingBackwardState,
    launchers::launch_build_eq_values_from_point, shared::GpuGKRBackwardScheduledExecution,
};
pub(crate) use crate::baby_bear::backward::kernels::{
    dim_reducing::*, encoding::*, eq::*, launchers::*, main_layer::*,
    shared::DeviceClaimPointAndBatching,
};

pub(crate) mod dim_reducing;
pub(crate) mod encoding;
pub(crate) mod eq;
pub(crate) mod launchers;
pub(crate) mod main_layer;
pub(crate) mod shared;
