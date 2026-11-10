use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;

// Matches the literal in twiddle_build.cu; no runtime host table generation/upload.
const _: () = assert!(PR::TWO_ADICITY_GENERATORS[31].0 == 0x00c1d7c223510c85e4a2ec2eeea02be9);

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

pub const LOG_MAX_DOMAIN: u32 = 31;
pub const LOW_TABLE_LEN: usize = 1 << 16;
pub const TABLE_LEN: usize = LOW_TABLE_LEN + (1 << 15);
pub(crate) const TABLE_BYTES: usize = TABLE_LEN * size_of::<PR>();
const FACTOR_BITS: u32 = 4;
const FACTOR_COUNT: usize = 32 / FACTOR_BITS as usize;
// The final 3-bit factor is padded to 16 entries.
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
        low_bits: 16,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        prepare_proof_twiddles, FACTOR_BITS, FACTOR_COUNT, FACTOR_LEN, LOG_MAX_DOMAIN,
        LOW_TABLE_LEN, TABLE_LEN,
    };
    use crate::upstream::{domain_generator_for_size, Field, PrimeField};
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use gpu_core::primitives::field::PR;

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
        assert_eq!(descriptor.log_max_domain, 31);
        assert_eq!(descriptor.low_bits, 16);
        let mut host = vec![PR::ZERO; TABLE_LEN];
        let mut factor_host = vec![PR::ZERO; FACTOR_LEN];
        memory_copy_async(&mut host, &tables, &stream).unwrap();
        memory_copy_async(&mut factor_host, &factors, &stream).unwrap();
        stream.synchronize().unwrap();
        let (forward_low, forward_high) = host.split_at(LOW_TABLE_LEN);
        let omega = domain_generator_for_size::<PR>(1u64 << LOG_MAX_DOMAIN);
        assert_powers(forward_low, omega, 0);
        assert_powers(forward_high, omega, 16);
        for exponent in [0u32, 1, 255, 256, 65535, 65536, 1 << 24, 0x7fffffff] {
            let reflected = 0u32.wrapping_sub(exponent) & 0x7fffffff;
            let mut value = forward_low[(reflected & 65535) as usize];
            value.mul_assign(&forward_high[(reflected >> 16) as usize]);
            assert_eq!(value, omega.inverse().unwrap().pow(exponent));
        }
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
}
