pub(crate) use crate::backward::dr_tail::kernels::{
    dr_tail_device_optin_cap_bytes, kernel_attributes, kernel_occupancy, launch_dr_tail_state,
    set_kernel_max_dynamic_smem, DrTailSlot, DR_TAIL_MAX_SOURCES, DR_TAIL_SLOTS,
};

pub(crate) mod kernels;
pub(crate) mod resources;
