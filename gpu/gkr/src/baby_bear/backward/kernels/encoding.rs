use std::{ffi::c_void, ptr::null_mut};

use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_core::primitives::field::E4;

use crate::backward::kernels::encoding::*;

cuda_struct_and_stub! {
    static ab_gkr_main_layer_claim_point: [E4; MAX_MAIN_LAYER_CLAIM_POINT_LEN];
}

pub(crate) fn get_main_layer_claim_point_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_main_layer_claim_point as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_main_layer_claim_point");
    ptr.cast()
}
