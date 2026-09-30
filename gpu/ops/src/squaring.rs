use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use gpu_core::primitives::field::E4;

cuda_kernel_signature_arguments_and_function!(
    SquaringSequenceE4,
    base: *const E4,
    result: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_squaring_sequence_e4_kernel(
        base: *const E4,
        result: *mut E4,
        count: u32,
    )
);

pub fn squaring_sequence_e4(
    base: &DeviceVariable<E4>,
    result: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(result.len() <= u32::MAX as usize);
    let count = result.len() as u32;
    // The kernel runs as a single-thread sequential loop because the squaring
    // chain has serial data dependency and `count == log_n` is small (~25).
    let config = CudaLaunchConfig::basic(1, 1, stream);
    let args = SquaringSequenceE4Arguments::new(base.as_ptr(), result.as_mut_ptr(), count);
    SquaringSequenceE4Function(ab_squaring_sequence_e4_kernel).launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::{Field, FieldExtension};
    use gpu_core::primitives::field::BF;

    #[test]
    fn squaring_sequence_e4_matches_host() {
        let count = 10usize;
        // Pick a non-trivial E4 value.
        let mut base = E4::from_base(BF::TWO);
        base.add_assign(&E4::ONE);
        // Add a non-trivial c1 component so all 4 lanes are exercised.
        let mut c1_seed = E4::from_base(BF::TWO);
        c1_seed.mul_assign(&E4::TWO);
        base.add_assign(&c1_seed);

        let mut host_seq: Vec<E4> = Vec::with_capacity(count);
        let mut p = base;
        for _ in 0..count {
            host_seq.push(p);
            let mut sq = p;
            sq.square();
            p = sq;
        }

        let stream = CudaStream::default();
        let mut d_base = DeviceAllocation::alloc(1).unwrap();
        memory_copy_async(&mut d_base[..], &[base], &stream).unwrap();
        let mut d_result = DeviceAllocation::alloc(count).unwrap();
        squaring_sequence_e4(&d_base[0], &mut d_result[..], &stream).unwrap();
        let mut h_result = vec![E4::ZERO; count];
        memory_copy_async(&mut h_result[..], &d_result[..], &stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(host_seq, h_result);
    }
}
