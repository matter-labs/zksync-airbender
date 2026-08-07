//! Kernel declarations, `__constant__` symbol uploads and safe launchers.
//!
//! The device tracks a window's backing as `bf *` / `e4 *`; the host tracks it as
//! a `u32` word array (one word per `bf`, four per `e4`), so every pointer that
//! crosses here is a `*mut u32`.

use std::ffi::c_void;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaMemcpyToSymbol, cuda_struct_and_stub, CudaMemoryCopyKind};

use crate::abi::{UniskipVmDesc, UNISKIP_EQ_HIGH, UNISKIP_TAPS, UNISKIP_THREADS_PER_BLOCK};

cuda_struct_and_stub! { static ab_gkr_uniskip_eq_high: [[u32; 4]; 2 * UNISKIP_EQ_HIGH]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_lde_matrix: [u32; UNISKIP_TAPS * UNISKIP_TAPS]; }

/// Blocks a grid-stride launch may use. The kernels loop, so this only bounds the
/// launch; every configuration above it is covered by the stride.
const MAX_BLOCKS: u64 = 1 << 16;

cuda_kernel!(
    InitBf,
    ab_gkr_uniskip_init_bf_kernel(dst: *mut u32, count: u64, seed: u32)
);
cuda_kernel!(
    InitE4,
    ab_gkr_uniskip_init_e4_kernel(dst: *mut u32, count: u64, seed: u32)
);
cuda_kernel!(
    LdeBf,
    ab_gkr_uniskip_lde_bf_kernel(desc: UniskipVmDesc, jobs: *const u16, num_jobs: u32)
);
cuda_kernel!(
    LdeE4,
    ab_gkr_uniskip_lde_e4_kernel(desc: UniskipVmDesc, jobs: *const u16, num_jobs: u32)
);

fn grid(total: u64) -> u32 {
    total
        .div_ceil(u64::from(UNISKIP_THREADS_PER_BLOCK as u32))
        .clamp(1, MAX_BLOCKS) as u32
}

fn config<'a>(total: u64, stream: &'a CudaStream) -> CudaLaunchConfig<'a> {
    CudaLaunchConfig::basic(grid(total), UNISKIP_THREADS_PER_BLOCK as u32, stream)
}

/// # Safety
///
/// `symbol` must name a `__device__ __constant__` array of exactly `size_of::<T>()`
/// bytes; it is only ever addressed on the host, never dereferenced.
unsafe fn memcpy_to_symbol<T>(symbol: &T, src: &T) -> CudaResult<()> {
    cudaMemcpyToSymbol(
        symbol as *const T as *const c_void,
        src as *const T as *const c_void,
        size_of::<T>(),
        0,
        CudaMemoryCopyKind::HostToDevice,
    )
    .wrap()
}

/// Upload the flattened coset LDE matrix. Entry `[c * UNISKIP_TAPS + t]` is
/// `L_t(gamma * omega^c)`, i.e. row `c` of [`crate::domain::lde_matrix`], which the
/// LDE kernels write into coset plane `c` — the plane [`crate::abi::cell_for_coset_row`]
/// names device cell `UNISKIP_TAPS + c`.
pub fn upload_lde_matrix(matrix: &[u32; UNISKIP_TAPS * UNISKIP_TAPS]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_lde_matrix, matrix) }
}

/// Upload both eq high tables. Table 0 occupies `[0, UNISKIP_EQ_HIGH)`, table 1 the
/// remainder — one allocation as far as the init generator is concerned.
pub fn upload_eq_high(tables: &[[u32; 4]; 2 * UNISKIP_EQ_HIGH]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_eq_high, tables) }
}

/// Fill a `bf` backing with the deterministic init generator; `dst` is one word
/// per element.
pub fn init_bf(dst: &mut DeviceSlice<u32>, seed: u32, stream: &CudaStream) -> CudaResult<()> {
    let count = dst.len() as u64;
    let args = InitBfArguments::new(dst.as_mut_ptr(), count, seed);
    InitBfFunction::default().launch(&config(count, stream), &args)
}

/// Fill an `e4` backing with the deterministic init generator; `dst` is four words
/// per element.
pub fn init_e4(dst: &mut DeviceSlice<u32>, seed: u32, stream: &CudaStream) -> CudaResult<()> {
    assert_eq!(dst.len() % 4, 0, "an e4 backing is four words per element");
    let count = (dst.len() / 4) as u64;
    let args = InitE4Arguments::new(dst.as_mut_ptr(), count, seed);
    InitE4Function::default().launch(&config(count, stream), &args)
}

fn lde_total(desc: &UniskipVmDesc, num_jobs: usize) -> u64 {
    (1u64 << desc.log_rows) * num_jobs as u64 * UNISKIP_TAPS as u64
}

/// One coset cell per (job, cell, row) over the `bf` source records in `jobs`.
pub fn lde_bf(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = lde_total(desc, num_jobs);
    let args = LdeBfArguments::new(*desc, jobs.as_ptr(), num_jobs as u32);
    LdeBfFunction::default().launch(&config(total, stream), &args)
}

/// The `e4` counterpart of [`lde_bf`].
pub fn lde_e4(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = lde_total(desc, num_jobs);
    let args = LdeE4Arguments::new(*desc, jobs.as_ptr(), num_jobs as u32);
    LdeE4Function::default().launch(&config(total, stream), &args)
}
