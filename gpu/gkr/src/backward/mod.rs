pub use crate::backward::kernels::{
    eq_group_count, eq_group_tables_len, gkr_dim_reducing_launch_config, make_eq_sizes,
    ClaimBufferLayout, GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
#[doc(hidden)]
pub use crate::backward::stage_snapshots::GKRBackwardStageSnapshot;
#[doc(hidden)]
pub use crate::backward::stage_snapshots::GKRBackwardStageSnapshotSink;
pub(crate) use crate::backward::{
    dr_tail::{
        dr_tail_device_optin_cap_bytes, kernel_attributes as dr_tail_kernel_attributes,
        kernel_occupancy as dr_tail_kernel_occupancy, launch_dr_tail_state,
        resources::DrTailRawAttributes,
        set_kernel_max_dynamic_smem as dr_tail_set_kernel_max_dynamic_smem,
    },
    kernels::*,
    main_layer::extras::derive_dimension_reducing_inputs,
    stage_snapshots::schedule_stage_snapshot_fields,
};

pub(crate) mod coefficient_chunks;
pub(crate) mod dr_tail;
pub mod kernels;
pub mod main_continuation;
pub(crate) mod main_layer;
pub(crate) mod stage_snapshots;
pub mod window;
pub(crate) mod window_dr;

#[cfg(test)]
pub(crate) mod tests;
