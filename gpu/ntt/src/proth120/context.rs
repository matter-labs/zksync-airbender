use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;

// Matches the literal in twiddle_build.cu; no runtime host table generation/upload.
const _: () = assert!(PR::TWO_ADICITY_GENERATORS[32].0 == 0x05cc132e8eb2e1d9da222838592e34f4);

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct TwiddleDescriptor {
    forward_low: *const PR,
    forward_high: *const PR,
    log_max_domain: u32,
    low_bits: u32,
}

impl TwiddleDescriptor {
    pub fn log_max_domain(&self) -> u32 {
        self.log_max_domain
    }
}

const _: () = {
    assert!(core::mem::size_of::<TwiddleDescriptor>() == 24);
    assert!(core::mem::align_of::<TwiddleDescriptor>() == 8);
    assert!(core::mem::offset_of!(TwiddleDescriptor, forward_low) == 0);
    assert!(core::mem::offset_of!(TwiddleDescriptor, forward_high) == 8);
    assert!(core::mem::offset_of!(TwiddleDescriptor, log_max_domain) == 16);
    assert!(core::mem::offset_of!(TwiddleDescriptor, low_bits) == 20);
};

era_cudart::cuda_kernel!(BuildFactors, ab_pr_ntt_build_factors_kernel(factors: *mut PR));
era_cudart::cuda_kernel!(BuildTables, ab_pr_ntt_build_tables_kernel(factors: *const PR, output: *mut PR));

pub const LOG_MAX_DOMAIN: u32 = u32::BITS;
const LOW_BITS: u32 = LOG_MAX_DOMAIN / 2;
pub const LOW_TABLE_LEN: usize = 1 << LOW_BITS;
pub const TABLE_LEN: usize = LOW_TABLE_LEN + (1 << (LOG_MAX_DOMAIN - LOW_BITS));
pub(crate) const TABLE_BYTES: usize = TABLE_LEN * size_of::<PR>();
const FACTOR_BITS: u32 = 4;
const FACTOR_COUNT: usize = (LOG_MAX_DOMAIN / FACTOR_BITS) as usize;
pub const FACTOR_LEN: usize = FACTOR_COUNT * (1 << FACTOR_BITS);

/// Build both forward tables once for a proof or an explicit setup/test scope.
/// Scratch can retire after this call; tables must cover all scheduled descriptor uses.
pub fn prepare_proof_twiddles(
    tables: &mut DeviceSlice<PR>,
    factors: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<TwiddleDescriptor> {
    assert_eq!(tables.len(), TABLE_LEN, "Proth120 twiddle table length");
    assert_eq!(factors.len(), FACTOR_LEN, "Proth120 twiddle factor length");
    let config = CudaLaunchConfig::basic(FACTOR_COUNT as u32, 1u32 << FACTOR_BITS.max(5), stream);
    BuildFactorsFunction::default()
        .launch(&config, &BuildFactorsArguments::new(factors.as_mut_ptr()))?;
    let config = CudaLaunchConfig::basic((TABLE_LEN / 256) as u32, 256u32, stream);
    BuildTablesFunction::default().launch(
        &config,
        &BuildTablesArguments::new(factors.as_ptr(), tables.as_mut_ptr()),
    )?;
    Ok(TwiddleDescriptor {
        forward_low: tables.as_ptr(),
        forward_high: tables[LOW_TABLE_LEN..].as_ptr(),
        log_max_domain: LOG_MAX_DOMAIN,
        low_bits: LOW_BITS,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        prepare_proof_twiddles, TwiddleDescriptor, FACTOR_BITS, FACTOR_COUNT, FACTOR_LEN,
        LOG_MAX_DOMAIN, LOW_BITS, LOW_TABLE_LEN, TABLE_LEN,
    };
    use crate::upstream::{domain_generator_for_size, Field, PrimeField};
    use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
    use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use gpu_core::primitives::field::PR;

    era_cudart::cuda_kernel!(TestRootPowers, ab_pr_ntt_test_root_powers_kernel(
        descriptor: TwiddleDescriptor, exponents: *const u64, powers: *mut PR, reversed: *mut u32,
    ));
    era_cudart::cuda_kernel!(TestInverseLeaf, ab_pr_ntt_test_inverse_leaf_kernel(
        descriptor: TwiddleDescriptor, exponent: u32, values: *mut PR,
    ));

    fn assert_powers(table: &[PR], base: PR, step_log: u32) {
        let mut step = base;
        step.exp_power_of_2(step_log as usize);
        for (j, value) in table.iter().enumerate() {
            let expected = step.pow(j as u32);
            assert!(value.0 < PR::CHARACTERISTICS_U128);
            assert_eq!(value.0, expected.0, "power {j} of w^(2^{step_log})");
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    fn pr_context_roots_cpu_parity() {
        let stream = CudaStream::create().unwrap();
        let mut tables = DeviceAllocation::<PR>::alloc(TABLE_LEN).unwrap();
        let mut factors = DeviceAllocation::<PR>::alloc(FACTOR_LEN).unwrap();
        let descriptor = prepare_proof_twiddles(&mut tables, &mut factors, &stream).unwrap();
        assert_eq!(descriptor.forward_low, tables.as_ptr());
        assert_eq!(descriptor.forward_high, tables[LOW_TABLE_LEN..].as_ptr());
        assert_eq!(descriptor.log_max_domain, 32);
        assert_eq!(descriptor.low_bits, LOW_BITS);
        let mut host = vec![PR::ZERO; TABLE_LEN];
        let mut factor_host = vec![PR::ZERO; FACTOR_LEN];
        memory_copy_async(&mut host, &tables, &stream).unwrap();
        memory_copy_async(&mut factor_host, &factors, &stream).unwrap();
        stream.synchronize().unwrap();
        let (forward_low, forward_high) = host.split_at(LOW_TABLE_LEN);
        let omega = domain_generator_for_size::<PR>(1u64 << LOG_MAX_DOMAIN);
        assert_powers(forward_low, omega, 0);
        assert_powers(forward_high, omega, LOW_BITS);
        for factor in 0..FACTOR_COUNT {
            let start = factor * (1 << FACTOR_BITS);
            let len = 1 << FACTOR_BITS;
            assert_powers(
                &factor_host[start..start + len],
                omega,
                FACTOR_BITS * factor as u32,
            );
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    fn pr_context_domain32_powers_and_bit_reversal() {
        let stream = CudaStream::create().unwrap();
        let mut tables = DeviceAllocation::alloc(TABLE_LEN).unwrap();
        let mut factors = DeviceAllocation::alloc(FACTOR_LEN).unwrap();
        let descriptor = prepare_proof_twiddles(&mut tables, &mut factors, &stream).unwrap();
        let exponents = [
            0,
            1,
            0xffff,
            0x10000,
            0x40000000,
            0x7fffffff,
            1 << 31,
            u32::MAX as u64,
            1 << 32,
        ];
        let mut device_exponents = DeviceAllocation::alloc(exponents.len()).unwrap();
        memory_copy(&mut device_exponents, &exponents[..]).unwrap();
        let mut device_powers = DeviceAllocation::alloc(3 * exponents.len()).unwrap();
        let mut device_reversed = DeviceAllocation::alloc(exponents.len()).unwrap();
        TestRootPowersFunction::default()
            .launch(
                &CudaLaunchConfig::basic(1, exponents.len() as u32, &stream),
                &TestRootPowersArguments::new(
                    descriptor,
                    device_exponents.as_ptr(),
                    device_powers.as_mut_ptr(),
                    device_reversed.as_mut_ptr(),
                ),
            )
            .unwrap();
        let mut powers = [PR::ZERO; 3 * 9];
        let mut reversed = [0u32; 9];
        memory_copy_async(&mut powers[..], &device_powers, &stream).unwrap();
        memory_copy_async(&mut reversed[..], &device_reversed, &stream).unwrap();
        stream.synchronize().unwrap();
        let omega = domain_generator_for_size::<PR>(1u64 << 32);
        let omega_inv = omega.inverse().unwrap();
        for (i, exponent) in exponents.into_iter().enumerate() {
            let expected = [
                omega.pow_u128(exponent as u128),
                omega_inv.pow_u128(exponent as u128),
                omega.pow((exponent as u32).reverse_bits() >> 1),
            ];
            assert_eq!(powers[3 * i..3 * i + 3], expected, "exponent {exponent:#x}");
            assert_eq!(reversed[i], (exponent as u32).reverse_bits());
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    fn pr_context_domain32_inverse_leaf_matches_cpu() {
        let stream = CudaStream::create().unwrap();
        let mut tables = DeviceAllocation::alloc(TABLE_LEN).unwrap();
        let mut factors = DeviceAllocation::alloc(FACTOR_LEN).unwrap();
        let descriptor = prepare_proof_twiddles(&mut tables, &mut factors, &stream).unwrap();
        let omega = domain_generator_for_size::<PR>(1u64 << 32);
        let worker = crate::upstream::Worker::new_with_num_threads(1);
        let twiddles = crate::upstream::Twiddles::<PR, std::alloc::Global>::new(16, &worker);
        let coeffs: [PR; 16] = std::array::from_fn(|i| PR::new((i as u128 + 1).pow(3)));
        let mut leaf = DeviceAllocation::alloc(coeffs.len()).unwrap();
        for exponent in [1, 1 << 31, u32::MAX] {
            let offset = omega.pow(exponent);
            let evaluations = crate::upstream::lde_coset_lazy_r8(
                &coeffs,
                offset,
                &twiddles.forward_twiddles[..8],
            );
            let bitreversed: [PR; 16] =
                std::array::from_fn(|i| evaluations[i.reverse_bits() >> (usize::BITS - 4)]);
            memory_copy(&mut leaf, &bitreversed[..]).unwrap();
            TestInverseLeafFunction::default()
                .launch(
                    &CudaLaunchConfig::basic(1, 1, &stream),
                    &TestInverseLeafArguments::new(descriptor, exponent, leaf.as_mut_ptr()),
                )
                .unwrap();
            let mut actual = [PR::ZERO; 16];
            memory_copy_async(&mut actual[..], &leaf, &stream).unwrap();
            stream.synchronize().unwrap();
            assert_eq!(actual, coeffs, "inverse leaf at exponent {exponent:#x}");
        }
    }
}
