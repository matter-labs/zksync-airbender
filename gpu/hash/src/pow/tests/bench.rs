//! Production PoW search kernels at the wrap bit counts, timed without copies.
use super::{Blake2s, Hash, Keccak};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

// Reuse the production native symbols; no benchmark-only GPU kernel or production API.
era_cudart::cuda_kernel!(BenchKeccakPow, ab_keccak256_pow_kernel(
    seed: *const u8, bits: u32, max_nonce: u64, chunk_steps: u32,
    counter: *mut u64, result: *mut u64
));
era_cudart::cuda_kernel!(BenchBlakePow, ab_blake2s_pow_kernel(
    seed: *const u64, bits_count: u32, max_nonce: u64, chunk_steps: u32,
    counter: *mut u64, result: *mut u64
));

fn benchmark_pow_kernel<const KECCAK: bool>(warmups: usize, samples: usize) {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart::event::{elapsed_time, CudaEvent};
    use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
    use era_cudart::memory::memory_set_async;
    use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
    use era_cudart_sys::CudaDeviceAttr;

    let hash = if KECCAK { "keccak256" } else { "blake2s" };
    let stream = CudaStream::create().unwrap();
    let mpc =
        device_get_attribute(CudaDeviceAttr::MultiProcessorCount, get_device().unwrap()).unwrap();
    let active = if KECCAK {
        max_active_blocks_per_multiprocessor(&BenchKeccakPowFunction::default(), 128, 0).unwrap()
    } else {
        max_active_blocks_per_multiprocessor(&BenchBlakePowFunction::default(), 128, 0).unwrap()
    };
    assert!(mpc > 0 && active > 0);
    let blocks = u32::try_from(mpc * active).unwrap();
    let mut device_seed = DeviceAllocation::<u8>::alloc(32).unwrap();
    let mut counter = DeviceAllocation::<u64>::alloc(1).unwrap();
    let mut result = DeviceAllocation::<u64>::alloc(1).unwrap();
    let start = CudaEvent::create().unwrap();
    let stop = CudaEvent::create().unwrap();
    // Synthetic fixed seeds, production bit counts; IDs distinguish the two 30-bit rounds.
    for (case, bits) in [13u32, 20, 30, 27, 30, 20, 17].into_iter().enumerate() {
        let seed: [u8; 32] =
            std::array::from_fn(|i| (case as u8).wrapping_mul(37).wrapping_add(i as u8));
        let seed_hex: String = seed.iter().map(|b| format!("{b:02x}")).collect();
        memory_copy_async(&mut device_seed, &seed, &stream).unwrap();
        let steps = crate::pow::pow_chunk_steps(bits, blocks);
        let mut expected_nonce = None;
        for sample in 0..warmups + samples {
            // Reset work is outside the event interval. The timed interval encloses one native search launch.
            unsafe {
                memory_set_async(counter.transmute_mut(), 0, &stream).unwrap();
                memory_set_async(result.transmute_mut(), 0xff, &stream).unwrap();
            }
            let config = CudaLaunchConfig::basic(blocks, 128u32, &stream);
            start.record(&stream).unwrap();
            if KECCAK {
                BenchKeccakPowFunction::default()
                    .launch(
                        &config,
                        &BenchKeccakPowArguments::new(
                            device_seed.as_ptr(),
                            bits,
                            u64::MAX,
                            steps,
                            counter.as_mut_ptr(),
                            result.as_mut_ptr(),
                        ),
                    )
                    .unwrap();
            } else {
                BenchBlakePowFunction::default()
                    .launch(
                        &config,
                        &BenchBlakePowArguments::new(
                            device_seed.as_ptr().cast(),
                            bits,
                            u64::MAX,
                            steps,
                            counter.as_mut_ptr(),
                            result.as_mut_ptr(),
                        ),
                    )
                    .unwrap();
            }
            stop.record(&stream).unwrap();
            let mut nonce = [u64::MAX];
            let mut raw_counter = [0u64];
            memory_copy_async(&mut nonce, &result, &stream).unwrap();
            memory_copy_async(&mut raw_counter, &counter, &stream).unwrap();
            stream.synchronize().unwrap();
            assert_ne!(nonce[0], u64::MAX);
            assert_ne!(
                raw_counter[0] & (1u64 << 63),
                0,
                "benchmark must execute counter-search mode"
            );
            assert!(if KECCAK {
                Keccak::matches(&seed, nonce[0], bits)
            } else {
                Blake2s::matches(&seed, nonce[0], bits)
            });
            if let Some(expected) = expected_nonce {
                assert_eq!(nonce[0], expected);
            } else {
                expected_nonce = Some(nonce[0]);
            }
            let phase = if sample < warmups { "warmup" } else { "sample" };
            let ms = elapsed_time(&start, &stop).unwrap();
            println!("pow_kernel,{hash},{case},{bits},{seed_hex},{phase},{sample},{},{},{blocks},128,{steps},{ms:.9}", nonce[0], raw_counter[0]);
        }
    }
}

/// Kernel-only timing with stable case seeds; the measurement driver compares nonces across A/B artifacts.
#[test]
#[ignore = "local GPU measurement gate: R-M5 production PoW bit counts"]
fn pow_kernel_production_bits_benchmark() {
    fn count(name: &str, default: usize) -> usize {
        std::env::var(name)
            .map(|value| value.parse().expect("benchmark count must be an integer"))
            .unwrap_or(default)
    }
    let warmups = count("AB_POW_BENCH_WARMUPS", 2);
    let samples = count("AB_POW_BENCH_SAMPLES", 8);
    assert!(samples > 0);
    println!("record,hash,case,bits,seed,phase,sample,nonce,counter_value,blocks,threads,chunk_steps,kernel_ms");
    benchmark_pow_kernel::<true>(warmups, samples);
    benchmark_pow_kernel::<false>(warmups, samples);
}
