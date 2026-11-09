use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;

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
    Pow,
    ab_keccak256_pow_kernel(
        seed: *const u8,
        bits: u32,
        max_nonce: u64,
        chunk_steps: u32,
        counter: *mut u64,
        result: *mut u64
    )
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PowArm {
    GridStrideMin,
    GridStrideFirst,
    CounterMin,
}

impl PowArm {
    pub fn uses_counter(self) -> bool {
        self == PowArm::CounterMin
    }

    pub fn is_min(self) -> bool {
        self != PowArm::GridStrideFirst
    }
}

cuda_kernel!(
    PowGridStride,
    pow_grid_stride,
    seed: *const u8,
    bits: u32,
    max_nonce: u64,
    result: *mut u64
);

pow_grid_stride!(ab_keccak256_pow_grid_stride_min_bench_kernel);
pow_grid_stride!(ab_keccak256_pow_grid_stride_first_bench_kernel);
pow_grid_stride!(ab_blake2s_pow_grid_stride_min_bench_kernel);
pow_grid_stride!(ab_blake2s_pow_grid_stride_first_bench_kernel);

cuda_kernel!(
    PowCounter,
    pow_counter,
    seed: *const u8,
    bits: u32,
    max_nonce: u64,
    chunk_steps: u32,
    counter: *mut u64,
    result: *mut u64
);

pow_counter!(ab_keccak256_pow_counter_min_bench_kernel);
pow_counter!(ab_blake2s_pow_counter_min_bench_kernel);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PowHash {
    Keccak,
    Blake2s,
}

enum PowKernel {
    GridStride(PowGridStrideSignature),
    Counter(PowCounterSignature),
}

fn pow_kernel(hash: PowHash, arm: PowArm) -> PowKernel {
    match (hash, arm) {
        (PowHash::Keccak, PowArm::GridStrideMin) => {
            PowKernel::GridStride(ab_keccak256_pow_grid_stride_min_bench_kernel)
        }
        (PowHash::Keccak, PowArm::GridStrideFirst) => {
            PowKernel::GridStride(ab_keccak256_pow_grid_stride_first_bench_kernel)
        }
        (PowHash::Keccak, PowArm::CounterMin) => {
            PowKernel::Counter(ab_keccak256_pow_counter_min_bench_kernel)
        }
        (PowHash::Blake2s, PowArm::GridStrideMin) => {
            PowKernel::GridStride(ab_blake2s_pow_grid_stride_min_bench_kernel)
        }
        (PowHash::Blake2s, PowArm::GridStrideFirst) => {
            PowKernel::GridStride(ab_blake2s_pow_grid_stride_first_bench_kernel)
        }
        (PowHash::Blake2s, PowArm::CounterMin) => {
            PowKernel::Counter(ab_blake2s_pow_counter_min_bench_kernel)
        }
    }
}

pub fn bench_pow_arm_blocks(hash: PowHash, arm: PowArm) -> CudaResult<u32> {
    let mpc = device_get_attribute(MultiProcessorCount, get_device()?)?;
    let active = match pow_kernel(hash, arm) {
        PowKernel::GridStride(f) => {
            max_active_blocks_per_multiprocessor(&PowGridStrideFunction(f), 128, 0)?
        }
        PowKernel::Counter(f) => {
            max_active_blocks_per_multiprocessor(&PowCounterFunction(f), 128, 0)?
        }
    };
    Ok(u32::try_from(mpc * active).expect("bench_pow_arm_blocks: grid overflow"))
}

/// The arm's kernel at the production grid; `result` (and `counter`) must hold their start values.
#[allow(clippy::too_many_arguments)]
pub fn bench_pow_arm_kernel(
    hash: PowHash,
    arm: PowArm,
    seed: *const u8,
    bits: u32,
    max_nonce: u64,
    blocks: u32,
    counter: &mut DeviceVariable<u64>,
    result: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(blocks, 128, stream);
    match pow_kernel(hash, arm) {
        PowKernel::GridStride(f) => {
            let args = PowGridStrideArguments::new(seed, bits, max_nonce, result.as_mut_ptr());
            PowGridStrideFunction(f).launch(&config, &args)
        }
        PowKernel::Counter(f) => {
            let args = PowCounterArguments::new(
                seed,
                bits,
                max_nonce,
                crate::pow::pow_chunk_steps(bits, blocks),
                counter.as_mut_ptr(),
                result.as_mut_ptr(),
            );
            PowCounterFunction(f).launch(&config, &args)
        }
    }
}

/// Mirrors `keccak256_pow` (bits > 0: occupancy query, then resets) or `blake2s_pow` (resets, then
/// occupancy query) for one arm, kernel with `max_nonce = u64::MAX`, Keccak finalize.
pub fn bench_pow_arm_launcher(
    hash: PowHash,
    arm: PowArm,
    seed: &mut DeviceSlice<u8>,
    bits: u32,
    counter: &mut DeviceVariable<u64>,
    result: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(bits > 0);
    assert_eq!(seed.len(), 32);
    let reset = |result: &mut DeviceVariable<u64>, counter: &mut DeviceVariable<u64>| unsafe {
        era_cudart::memory::memory_set_async(result.transmute_mut(), 0xff, stream)?;
        if arm.uses_counter() {
            era_cudart::memory::memory_set_async(counter.transmute_mut(), 0, stream)?;
        }
        CudaResult::Ok(())
    };
    let blocks = match hash {
        PowHash::Keccak => {
            let blocks = bench_pow_arm_blocks(hash, arm)?;
            reset(result, counter)?;
            blocks
        }
        PowHash::Blake2s => {
            reset(result, counter)?;
            bench_pow_arm_blocks(hash, arm)?
        }
    };
    bench_pow_arm_kernel(
        hash,
        arm,
        seed.as_ptr(),
        bits,
        u64::MAX,
        blocks,
        counter,
        result,
        stream,
    )?;
    if hash == PowHash::Keccak {
        crate::keccak256::pow_finalize(seed, bits, result, stream)?;
    }
    Ok(())
}

cuda_kernel!(
    ProductionBlake2sPow,
    ab_blake2s_pow_kernel(
        seed: *const u64,
        bits_count: u32,
        max_nonce: u64,
        chunk_steps: u32,
        counter: *mut u64,
        result: *mut u64,
    )
);

/// The production launchers' grid for their compiled kernel.
pub fn bench_production_pow_blocks(hash: PowHash) -> CudaResult<u32> {
    let mpc = device_get_attribute(MultiProcessorCount, get_device()?)?;
    let active = match hash {
        PowHash::Keccak => max_active_blocks_per_multiprocessor(&PowFunction::default(), 128, 0)?,
        PowHash::Blake2s => {
            max_active_blocks_per_multiprocessor(&ProductionBlake2sPowFunction::default(), 128, 0)?
        }
    };
    Ok(u32::try_from(mpc * active).expect("bench_production_pow_blocks: grid overflow"))
}
