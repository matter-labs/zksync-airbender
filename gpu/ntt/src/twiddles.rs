//! Field-independent host construction of device power tables.
use crate::upstream::{bitreverse_enumeration_inplace, distribute_powers_serial, Field};
use era_cudart::{memory::memory_copy, result::CudaResult, slice::DeviceSlice};

pub(crate) fn generate_powers_dev<F: Field>(
    base: F,
    powers_dev: &mut DeviceSlice<F>,
    bit_reverse: bool,
    swizzle: bool,
) -> CudaResult<()> {
    let mut powers_host = vec![F::ONE; powers_dev.len()];
    distribute_powers_serial::<F, F>(&mut powers_host, F::ONE, base);
    if bit_reverse {
        bitreverse_enumeration_inplace(&mut powers_host);
    }
    let linear_to_swizzled = |i: usize| -> usize {
        const LOG_BANKS: usize = 5;
        const BANKS: usize = 1 << LOG_BANKS;
        const BANK_MASK: usize = BANKS - 1;
        let x = i & BANK_MASK;
        let y = i >> LOG_BANKS;
        y * BANKS + ((y & BANK_MASK) ^ x)
    };
    if swizzle {
        let mut powers_swizzled_host = vec![F::ZERO; powers_dev.len()];
        for i in 0..powers_dev.len() {
            powers_swizzled_host[i] = powers_host[linear_to_swizzled(i)];
        }
        memory_copy(powers_dev, &powers_swizzled_host)?;
        return Ok(());
    }
    memory_copy(powers_dev, &powers_host)
}
