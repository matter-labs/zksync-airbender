use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;

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

cuda_kernel_signature_arguments_and_function!(
    QuerySquaringSequencesBfToE4,
    domain_generator: BF,
    query_indexes: *const u32,
    result: *mut E4,
    count_per_query: u32,
    num_queries: u32,
);

cuda_kernel_declaration!(
    ab_query_squaring_sequences_bf_to_e4_kernel(
        domain_generator: BF,
        query_indexes: *const u32,
        result: *mut E4,
        count_per_query: u32,
        num_queries: u32,
    )
);

pub fn query_squaring_sequences_bf_to_e4(
    domain_generator: BF,
    query_indexes: &DeviceSlice<u32>,
    result: &mut DeviceSlice<E4>,
    count_per_query: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_queries = query_indexes.len();
    assert_eq!(result.len(), num_queries * count_per_query as usize);
    assert!(num_queries <= u32::MAX as usize);
    if num_queries == 0 {
        return Ok(());
    }
    // One thread per query; each thread runs a serial squaring loop of length
    // `count_per_query` (~log_n, small). Pick a modest block size and grid-cover.
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(64, num_queries as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = QuerySquaringSequencesBfToE4Arguments::new(
        domain_generator,
        query_indexes.as_ptr(),
        result.as_mut_ptr(),
        count_per_query,
        num_queries as u32,
    );
    QuerySquaringSequencesBfToE4Function(ab_query_squaring_sequences_bf_to_e4_kernel)
        .launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::{Field, FieldExtension};
    use serial_test::serial;

    #[test]
    #[serial]
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

    #[test]
    #[serial]
    fn query_squaring_sequences_matches_host() {
        let count_per_query = 8usize;
        let query_indexes: Vec<u32> = vec![3, 7, 11, 15, 42, 100];
        let num_queries = query_indexes.len();
        // Pick a non-trivial BF generator.
        let mut domain_generator = BF::TWO;
        domain_generator.add_assign(&BF::ONE);

        // Host reference.
        let mut host_ref: Vec<E4> = Vec::with_capacity(count_per_query * num_queries);
        for &qi in &query_indexes {
            let bf_pow = domain_generator.pow(qi);
            let mut p = E4::from_base(bf_pow);
            for _ in 0..count_per_query {
                host_ref.push(p);
                let mut sq = p;
                sq.square();
                p = sq;
            }
        }

        let stream = CudaStream::default();
        let mut d_indexes = DeviceAllocation::alloc(num_queries).unwrap();
        memory_copy_async(&mut d_indexes[..], &query_indexes, &stream).unwrap();
        let mut d_result = DeviceAllocation::alloc(count_per_query * num_queries).unwrap();
        query_squaring_sequences_bf_to_e4(
            domain_generator,
            &d_indexes[..],
            &mut d_result[..],
            count_per_query as u32,
            &stream,
        )
        .unwrap();
        let mut h_result = vec![E4::ZERO; count_per_query * num_queries];
        memory_copy_async(&mut h_result[..], &d_result[..], &stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(host_ref, h_result);
    }
}
