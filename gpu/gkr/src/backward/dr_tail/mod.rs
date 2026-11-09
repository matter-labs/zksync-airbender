pub(crate) mod capacity;
mod kernels;
pub(crate) mod resources;

pub(crate) use kernels::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc, DrTailSlot, DR_TAIL_MAX_SOURCES,
    DR_TAIL_SLOTS,
};

pub(crate) use kernels::{
    dr_tail_device_optin_cap_bytes, kernel_attributes, kernel_occupancy, launch_dr_tail_state,
    set_kernel_max_dynamic_smem,
};
