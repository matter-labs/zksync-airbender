use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;

use gpu_core::primitives::field::PR;

use crate::keccak256::Digest;

cuda_kernel!(
    Bench,
    bench,
    bytes: u32,
    count: u64,
    out: *mut Digest
);

bench!(ab_keccak256_bench_unroll_kernel);
bench!(ab_keccak256_bench_loop_kernel);

pub fn bench_hash_count() -> CudaResult<usize> {
    let count = device_get_attribute(MultiProcessorCount, get_device()?)? as usize;
    Ok(count
        .checked_mul(2048 * 4)
        .expect("keccak256::bench_hash_count: count overflow"))
}

pub fn bench_keccak256(
    bytes: u32,
    round_loop: bool,
    out: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        matches!(bytes, 40 | 64 | 256 | 448),
        "keccak256::bench_keccak256: unsupported bytes"
    );
    let count = bench_hash_count()?;
    assert_eq!(
        out.len(),
        count,
        "keccak256::bench_keccak256: out.len() == count"
    );
    let grid =
        u32::try_from(count.div_ceil(128)).expect("keccak256::bench_keccak256: grid overflow");
    let function = if round_loop {
        ab_keccak256_bench_loop_kernel
    } else {
        ab_keccak256_bench_unroll_kernel
    };
    let args = BenchArguments::new(bytes, count as u64, out.as_mut_ptr());
    BenchFunction(function).launch(&CudaLaunchConfig::basic(grid, 128, stream), &args)
}

cuda_kernel!(
    Chain,
    chain,
    chain: u32,
    threads: u64,
    out: *mut u64
);

chain!(ab_keccak_f_chain_unroll_kernel);
chain!(ab_keccak_f_chain_loop_kernel);

pub fn bench_keccak_f_chain(
    chain: u32,
    round_loop: bool,
    block: u32,
    out: &mut DeviceSlice<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let threads = out.len();
    let grid = u32::try_from(threads.div_ceil(block as usize))
        .expect("keccak256::bench_keccak_f_chain: grid overflow");
    let function = if round_loop {
        ab_keccak_f_chain_loop_kernel
    } else {
        ab_keccak_f_chain_unroll_kernel
    };
    let args = ChainArguments::new(chain, threads as u64, out.as_mut_ptr());
    ChainFunction(function).launch(&CudaLaunchConfig::basic(grid, block, stream), &args)
}

cuda_kernel!(
    PartialRoots,
    ab_keccak256_partial_roots_kernel(
        values: *const PR,
        log_domain: u32,
        log_v: u32,
        columns: u32,
        skip_bottom: u32,
        cosets_in_tile: u32,
        values_stride: u64,
        retained_stride: u64,
        retained: *mut Digest,
    )
);

cuda_kernel!(
    Nodes,
    ab_keccak256_nodes_kernel(
        src: *const Digest,
        count: u64,
        cosets_in_tile: u32,
        src_stride: u64,
        dst_stride: u64,
        dst: *mut Digest,
    )
);

pub fn bench_partial_roots(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_v: u32,
    columns: u32,
    skip_bottom: u32,
    retained: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(values.len(), (columns as usize) << log_domain);
    let leaves = 1usize << (log_domain - log_v);
    assert_eq!(retained.len(), leaves >> skip_bottom);
    let grid =
        u32::try_from(leaves.div_ceil(256)).expect("keccak256::bench_partial_roots: grid overflow");
    let args = PartialRootsArguments::new(
        values.as_ptr(),
        log_domain,
        log_v,
        columns,
        skip_bottom,
        1,
        values.len() as u64,
        retained.len() as u64,
        retained.as_mut_ptr(),
    );
    PartialRootsFunction::default().launch(&CudaLaunchConfig::basic(grid, 256, stream), &args)
}

pub fn bench_nodes(
    src: &DeviceSlice<Digest>,
    dst: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src.len(), 2 * dst.len());
    let count = dst.len();
    let grid = u32::try_from(count.div_ceil(128)).expect("keccak256::bench_nodes: grid overflow");
    let args = NodesArguments::new(src.as_ptr(), count as u64, 1, 0, 0, dst.as_mut_ptr());
    NodesFunction::default().launch(&CudaLaunchConfig::basic(grid, 128, stream), &args)
}
