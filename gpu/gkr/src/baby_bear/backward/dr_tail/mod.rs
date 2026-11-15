pub(crate) use crate::baby_bear::backward::dr_tail::kernels::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc,
};

pub(crate) mod capacity;
pub(crate) mod kernels;
pub(crate) mod resources;
