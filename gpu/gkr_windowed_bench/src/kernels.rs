use std::ffi::c_void;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{
    cudaFuncSetAttribute, cudaGetSymbolAddress, cuda_struct_and_stub, CudaFuncAttribute,
};

use crate::abi::{WindowVmDesc, BF, E4, THREADS_PER_BLOCK, WINDOW_CELLS};

pub const COEFFICIENT_CAPACITY: usize = 80;
pub const EQ_HIGH_SLOTS: usize = 2;
pub const EQ_GROUP_TABLE_LEN: usize = 256;
pub const EQ_HIGH_ELEMENTS: usize = EQ_HIGH_SLOTS * EQ_GROUP_TABLE_LEN;
pub const WINDOW_VM_SHARED_CARVEOUT_PERCENT: i32 = 60;

cuda_struct_and_stub! {
    static ab_gkr_windowed_coeff_bank: [E4; COEFFICIENT_CAPACITY];
}

cuda_struct_and_stub! {
    static ab_gkr_windowed_eq_high: [E4; EQ_HIGH_ELEMENTS];
}

cuda_kernel_signature_arguments_and_function!(
    InitBf,
    values: *mut BF,
    count: u64,
    seed: u32,
);

cuda_kernel_declaration!(ab_gkr_windowed_init_bf_kernel(
    values: *mut BF,
    count: u64,
    seed: u32,
));

cuda_kernel_signature_arguments_and_function!(
    InitE4,
    values: *mut E4,
    count: u64,
    seed: u32,
);

cuda_kernel_declaration!(ab_gkr_windowed_init_e4_kernel(
    values: *mut E4,
    count: u64,
    seed: u32,
));

cuda_kernel_signature_arguments_and_function!(WindowVm, desc: WindowVmDesc,);

cuda_kernel_declaration!(ab_gkr_windowed_vm_kernel(desc: WindowVmDesc,));

cuda_kernel_signature_arguments_and_function!(
    Finalize,
    partials: *const E4,
    output: *mut E4,
    num_blocks: u32,
);

cuda_kernel_declaration!(ab_gkr_windowed_finalize_kernel(
    partials: *const E4,
    output: *mut E4,
    num_blocks: u32,
));

pub fn launch_init_bf(
    values: &mut DeviceSlice<BF>,
    seed: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    if values.is_empty() {
        return Ok(());
    }
    let config = init_config(values.len(), stream);
    let args = InitBfArguments::new(values.as_mut_ptr(), values.len() as u64, seed);
    InitBfFunction(ab_gkr_windowed_init_bf_kernel).launch(&config, &args)
}

pub fn launch_init_e4(
    values: &mut DeviceSlice<E4>,
    seed: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    if values.is_empty() {
        return Ok(());
    }
    let config = init_config(values.len(), stream);
    let args = InitE4Arguments::new(values.as_mut_ptr(), values.len() as u64, seed);
    InitE4Function(ab_gkr_windowed_init_e4_kernel).launch(&config, &args)
}

pub fn launch_window_vm(
    desc: WindowVmDesc,
    num_blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(num_blocks, THREADS_PER_BLOCK, stream);
    let args = WindowVmArguments::new(desc);
    WindowVmFunction(ab_gkr_windowed_vm_kernel).launch(&config, &args)
}

pub fn configure_window_vm_shared_carveout() -> CudaResult<()> {
    let function = WindowVmFunction(ab_gkr_windowed_vm_kernel);
    unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            WINDOW_VM_SHARED_CARVEOUT_PERCENT,
        )
    }
    .wrap()
}

pub fn launch_finalize(
    partials: *const E4,
    output: *mut E4,
    num_blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(WINDOW_CELLS, 256, stream);
    let args = FinalizeArguments::new(partials, output, num_blocks);
    FinalizeFunction(ab_gkr_windowed_finalize_kernel).launch(&config, &args)
}

pub fn coefficient_bank_device_ptr() -> CudaResult<*mut E4> {
    unsafe { symbol_device_ptr(&ab_gkr_windowed_coeff_bank) }
}

pub fn eq_high_device_ptr() -> CudaResult<*mut E4> {
    unsafe { symbol_device_ptr(&ab_gkr_windowed_eq_high) }
}

fn init_config(count: usize, stream: &CudaStream) -> CudaLaunchConfig<'_> {
    let blocks = count.div_ceil(256).min(65_535) as u32;
    CudaLaunchConfig::basic(blocks, 256, stream)
}

fn symbol_device_ptr<T>(symbol: *const T) -> CudaResult<*mut E4> {
    let mut ptr: *mut c_void = core::ptr::null_mut();
    unsafe { cudaGetSymbolAddress(&mut ptr, symbol.cast()) }.wrap()?;
    Ok(ptr.cast())
}
