pub(crate) mod capacity;
pub(crate) use crate::backward::dr_tail::kernels::{
    dr_tail_device_optin_cap_bytes, kernel_attributes, kernel_occupancy, launch_dr_tail_state,
    set_kernel_max_dynamic_smem, DR_TAIL_MAX_SOURCES,
};

pub(crate) mod kernels;
pub(crate) mod resources;
