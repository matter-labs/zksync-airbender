use super::*;

#[test]
fn cpu_natural_register_resident_v32_respects_threshold_and_width() {
    assert!(!use_register_resident_natural_v32(5, (1 << 16) - 1));
    assert!(use_register_resident_natural_v32(5, 1 << 16));
    assert!(!use_register_resident_natural_v32(4, 1 << 20));
}

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use field::{Field, Rand};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_structures::DeviceMatrix;
use itertools::Itertools;
use rand::{rng, Rng};

/// `partially_evaluate_monomials_by_ref` evaluates NATURAL-order monomial
/// coefficients: coefficient `i` carries `z^i`, matching the CPU authority
/// `evaluate_monomial_form` (prover/src/gkr/whir/mod.rs:3030-3095). The Horner
/// loop below is that definition, so the device array is loaded with the same
/// order production stores.
fn run_partially_evaluate_monomials_by_ref(log_count: usize) {
    let count = 1 << log_count;
    let stride = 2 * count;
    let bf_elems = 4 * stride;
    let vectorized_src = (0..bf_elems)
        .map(|_| BF::random_element(&mut rng()))
        .collect_vec();

    let h_monomials = (0..count)
        .map(|i| {
            let coeffs = std::array::from_fn(|j| vectorized_src[i + stride * j]);
            E4::from_array_of_base(coeffs)
        })
        .collect_vec();
    let z = E4::random_element(&mut rng());
    let mut cpu_result = h_monomials[count - 1];
    for i in 2..=count {
        cpu_result.mul_assign(&z);
        cpu_result.add_assign(&h_monomials[count - i]);
    }

    let stream = CudaStream::default();
    let mut d_src = DeviceAllocation::alloc(bf_elems).unwrap();
    let mut d_z = DeviceAllocation::alloc(1).unwrap();
    let mut scratch0 = DeviceAllocation::alloc(stride / 2).unwrap(); // like GpuWhirState
    let mut scratch1 = DeviceAllocation::alloc(1).unwrap();
    memory_copy_async(&mut d_src, &vectorized_src[..], &stream).unwrap();
    memory_copy_async(&mut d_z, &[z], &stream).unwrap();
    let d_src_matrix = DeviceMatrix::new(&d_src, stride);
    let partials_count = partially_evaluate_monomials_by_ref(
        &d_src_matrix,
        &mut scratch0[..],
        &mut scratch1[..],
        &d_z[..],
        count,
        &stream,
    )
    .unwrap();

    let mut sum_partials = DeviceAllocation::alloc(partials_count.div_ceil(256).max(1)).unwrap();
    let mut reduce_result = DeviceAllocation::alloc(1).unwrap();

    whir_sum(
        &scratch0[..partials_count],
        &mut sum_partials[..],
        &mut reduce_result[0],
        &stream,
    )
    .unwrap();

    let mut gpu_result = [E4::ZERO; 1];
    memory_copy_async(&mut gpu_result[..], &reduce_result[..], &stream).unwrap();
    stream.synchronize().unwrap();
    assert_eq!(cpu_result, gpu_result[0]);
}

#[test]
#[cfg(not(no_cuda))]
fn test_partially_evaluate_monomials_by_ref_small() {
    run_partially_evaluate_monomials_by_ref(6);
}

#[test]
#[cfg(not(no_cuda))]
fn test_partially_evaluate_monomials_by_ref() {
    run_partially_evaluate_monomials_by_ref(23);
}

fn run_blake2s_leaves_from_ntt_matches_pack_then_blake(
    log_trace_len: usize,
    log_lde_factor: usize,
    log_values_per_leaf: usize,
    coset_index_base: u32,
) {
    use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use gpu_hash::blake2s::{hash_leaves_from_ntt_multi_coset, hash_leaves_multi_coset, Digest};

    const EXT4_DEGREE: usize = 4;
    let trace_len = 1usize << log_trace_len;
    let lde_factor = 1usize << log_lde_factor;
    let values_per_leaf = 1usize << log_values_per_leaf;
    let packed_leaf_count = trace_len / values_per_leaf;
    let total_leaf_count = packed_leaf_count * lde_factor;
    let cosets_in_tile = lde_factor; // tile = all cosets in this test
    assert!(
        (coset_index_base as usize) + cosets_in_tile <= lde_factor,
        "coset_index_base ({coset_index_base}) + cosets_in_tile ({cosets_in_tile}) > lde_factor ({lde_factor}); reduce cosets_in_tile or base"
    );

    let stream = CudaStream::default();
    // Deterministic NTT-output input
    let natural_bf: Vec<BF> = (0..(lde_factor * trace_len * EXT4_DEGREE))
        .map(|_| BF::random_element(&mut rng()))
        .collect_vec();
    let mut d_natural: DeviceAllocation<BF> = DeviceAllocation::alloc(natural_bf.len()).unwrap();
    memory_copy_async(&mut d_natural[..], &natural_bf[..], &stream).unwrap();

    // Reference path: pack into packed layout, then run existing blake leaves.
    let mut d_packed: DeviceAllocation<BF> =
        DeviceAllocation::alloc(lde_factor * trace_len * EXT4_DEGREE).unwrap();
    // pack expects src as (rows=trace_len, cols=lde_factor*EXT4_DEGREE), dst as
    // (rows=packed_leaf_count*lde_factor, cols=EXT4_DEGREE*values_per_leaf).
    {
        let natural_matrix = DeviceMatrix::new(&d_natural[..], trace_len);
        let mut packed_matrix =
            DeviceMatrixMut::new(&mut d_packed[..], packed_leaf_count << log_lde_factor);
        pack_rows_for_whir_leaves_multi_coset(
            &natural_matrix,
            &mut packed_matrix,
            log_values_per_leaf as u32,
            packed_leaf_count,
            log_lde_factor as u32,
            coset_index_base,
            cosets_in_tile,
            EXT4_DEGREE,
            &stream,
        )
        .unwrap();
    }
    let mut d_ref_digests: DeviceAllocation<Digest> =
        DeviceAllocation::alloc(total_leaf_count).unwrap();
    // Existing kernel hashes one flat coset (cosets_in_tile = 1) covering all
    // `total_leaf_count` leaves; cols_count = EXT4_DEGREE * values_per_leaf.
    hash_leaves_multi_coset(
        &d_packed[..],
        &mut d_ref_digests[..],
        /*log_rows_per_hash=*/ 0,
        /*cosets_in_tile=*/ 1,
        /*per_coset_leaves_count=*/ total_leaf_count,
        /*per_coset_values_stride_bf=*/ EXT4_DEGREE * values_per_leaf * total_leaf_count,
        /*per_coset_results_stride_digests=*/ total_leaf_count,
        /*cols_count=*/ EXT4_DEGREE * values_per_leaf,
        &stream,
    )
    .unwrap();
    let mut ref_digests_host = vec![Digest::default(); total_leaf_count];
    memory_copy_async(&mut ref_digests_host[..], &d_ref_digests[..], &stream).unwrap();

    // New path: directly hash from natural NTT output.
    let mut d_new_digests: DeviceAllocation<Digest> =
        DeviceAllocation::alloc(total_leaf_count).unwrap();
    hash_leaves_from_ntt_multi_coset(
        &d_natural[..],
        &mut d_new_digests[..],
        log_values_per_leaf as u32,
        EXT4_DEGREE as u32,
        log_lde_factor as u32,
        coset_index_base,
        cosets_in_tile,
        packed_leaf_count,
        trace_len as u32,
        &stream,
    )
    .unwrap();
    let mut new_digests_host = vec![Digest::default(); total_leaf_count];
    memory_copy_async(&mut new_digests_host[..], &d_new_digests[..], &stream).unwrap();

    stream.synchronize().unwrap();

    assert_eq!(
        ref_digests_host, new_digests_host,
        "blake2s_leaves_from_ntt digest mismatch at log_trace_len={log_trace_len}, log_lde_factor={log_lde_factor}, log_values_per_leaf={log_values_per_leaf}, coset_index_base={coset_index_base}"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn test_blake2s_leaves_from_ntt_small() {
    // packed_leaf_count = 32 (= warp size); 16 cosets fits comfortably in
    // unit-test memory while still exercising multi-coset behavior.
    run_blake2s_leaves_from_ntt_matches_pack_then_blake(8, 4, 3, 0);
}

#[test]
#[cfg(not(no_cuda))]
fn test_blake2s_leaves_from_ntt_medium() {
    // packed_leaf_count = 256; warps fully within one coset.
    run_blake2s_leaves_from_ntt_matches_pack_then_blake(12, 6, 4, 0);
}

#[test]
#[cfg(not(no_cuda))]
fn test_blake2s_leaves_from_ntt_large() {
    // packed_leaf_count = 1024; large enough for warp coalescing analysis.
    run_blake2s_leaves_from_ntt_matches_pack_then_blake(15, 8, 5, 0);
}

#[test]
#[cfg(not(no_cuda))]
fn test_reduce_staged_whir_subtrees_matches_generic_tree() {
    use gpu_hash::blake2s::{build_merkle_tree_nodes, Digest};

    fn reference_roots(leaves: &[Digest], stream: &CudaStream) -> Vec<Digest> {
        let mut leaves_device = DeviceAllocation::alloc(leaves.len()).unwrap();
        let mut nodes_device = DeviceAllocation::alloc(leaves.len()).unwrap();
        memory_copy_async(&mut leaves_device, leaves, stream).unwrap();
        build_merkle_tree_nodes(&leaves_device, &mut nodes_device, 5, stream).unwrap();
        let roots_count = leaves.len() / 32;
        let roots_offset = 15 * leaves.len() / 16;
        let mut roots = vec![Digest::default(); roots_count];
        memory_copy_async(
            &mut roots,
            &nodes_device[roots_offset..roots_offset + roots_count],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();
        roots
    }

    let stream = CudaStream::default();
    let random_digest = || std::array::from_fn(|_| rng().random());

    let flat_leaves = (0..1usize << 12).map(|_| random_digest()).collect_vec();
    let flat_expected = reference_roots(&flat_leaves, &stream);
    let mut flat_staged = DeviceAllocation::alloc(flat_leaves.len()).unwrap();
    let mut flat_roots = DeviceAllocation::alloc(flat_expected.len()).unwrap();
    memory_copy_async(&mut flat_staged, &flat_leaves, &stream).unwrap();
    reduce_staged_whir_subtrees_flat(&flat_staged, &mut flat_roots, &stream).unwrap();
    let mut flat_actual = vec![Digest::default(); flat_expected.len()];
    memory_copy_async(&mut flat_actual, &flat_roots, &stream).unwrap();

    const LOG_PACKED_LEAF_COUNT: u32 = 6;
    const LOG_LDE_FACTOR: u32 = 3;
    let packed_leaf_count = 1usize << LOG_PACKED_LEAF_COUNT;
    let natural_leaves = (0..packed_leaf_count << LOG_LDE_FACTOR)
        .map(|_| random_digest())
        .collect_vec();
    let natural_expected = reference_roots(&natural_leaves, &stream);
    let stage_cosets = |cosets: &[usize]| {
        cosets
            .iter()
            .flat_map(|&natural_coset| {
                let bitrev_coset = natural_coset.reverse_bits() >> (usize::BITS - LOG_LDE_FACTOR);
                let start = bitrev_coset * packed_leaf_count;
                natural_leaves[start..start + packed_leaf_count]
                    .iter()
                    .copied()
            })
            .collect_vec()
    };
    let natural_stage_a = stage_cosets(&[0, 1, 4, 5]);
    let natural_stage_b = stage_cosets(&[2, 3, 6, 7]);
    let mut natural_stage_a_device = DeviceAllocation::alloc(natural_stage_a.len()).unwrap();
    let mut natural_stage_b_device = DeviceAllocation::alloc(natural_stage_b.len()).unwrap();
    let mut natural_roots = DeviceAllocation::alloc(natural_expected.len()).unwrap();
    memory_copy_async(&mut natural_stage_a_device, &natural_stage_a, &stream).unwrap();
    memory_copy_async(&mut natural_stage_b_device, &natural_stage_b, &stream).unwrap();
    reduce_staged_whir_subtrees_natural_tiles(
        &natural_stage_a_device,
        &mut natural_roots,
        LOG_PACKED_LEAF_COUNT,
        LOG_LDE_FACTOR,
        0,
        (2 * packed_leaf_count) as u32,
        2,
        4,
        &stream,
    )
    .unwrap();
    reduce_staged_whir_subtrees_natural_tiles(
        &natural_stage_b_device,
        &mut natural_roots,
        LOG_PACKED_LEAF_COUNT,
        LOG_LDE_FACTOR,
        2,
        (2 * packed_leaf_count) as u32,
        2,
        4,
        &stream,
    )
    .unwrap();
    let mut natural_actual = vec![Digest::default(); natural_expected.len()];
    memory_copy_async(&mut natural_actual, &natural_roots, &stream).unwrap();
    stream.synchronize().unwrap();

    assert_eq!(flat_actual, flat_expected);
    assert_eq!(natural_actual, natural_expected);
}

fn run_gather_leaves_for_queries_from_ntt_matches_packed(
    log_trace_len: usize,
    log_lde_factor: usize,
    log_values_per_leaf: usize,
) {
    use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use gpu_hash::blake2s::{
        gather_leaves_for_queries, gather_leaves_for_queries_from_ntt, OracleGatherDesc,
    };

    const EXT4_DEGREE: usize = 4;
    assert_eq!(1u32 << crate::LOG_SRC_COLS_PER_COSET, EXT4_DEGREE as u32);
    let trace_len = 1usize << log_trace_len;
    let lde_factor = 1usize << log_lde_factor;
    let values_per_leaf = 1usize << log_values_per_leaf;
    let packed_leaf_count = trace_len / values_per_leaf;
    let total_leaf_count = packed_leaf_count * lde_factor;
    let dst_cols = EXT4_DEGREE * values_per_leaf;

    let stream = CudaStream::default();

    // Deterministic NTT-output input.
    let natural_bf: Vec<BF> = (0..(lde_factor * trace_len * EXT4_DEGREE))
        .map(|_| BF::random_element(&mut rng()))
        .collect_vec();
    let mut d_natural: DeviceAllocation<BF> = DeviceAllocation::alloc(natural_bf.len()).unwrap();
    memory_copy_async(&mut d_natural[..], &natural_bf[..], &stream).unwrap();

    // Pack into packed layout for the reference path.
    let mut d_packed: DeviceAllocation<BF> =
        DeviceAllocation::alloc(lde_factor * trace_len * EXT4_DEGREE).unwrap();
    {
        let natural_matrix = DeviceMatrix::new(&d_natural[..], trace_len);
        let mut packed_matrix =
            DeviceMatrixMut::new(&mut d_packed[..], packed_leaf_count << log_lde_factor);
        pack_rows_for_whir_leaves_multi_coset(
            &natural_matrix,
            &mut packed_matrix,
            log_values_per_leaf as u32,
            packed_leaf_count,
            log_lde_factor as u32,
            /*coset_index_base=*/ 0,
            lde_factor,
            EXT4_DEGREE,
            &stream,
        )
        .unwrap();
    }

    // Build a query-index set covering boundary cases. Stay in [0, total_leaf_count).
    let queries: Vec<u32> = vec![
        0,
        1,
        (total_leaf_count - 1) as u32,
        (total_leaf_count / 2) as u32,
        (packed_leaf_count - 1) as u32,
        packed_leaf_count as u32,
        (packed_leaf_count + 3) as u32,
        ((lde_factor / 2) * packed_leaf_count) as u32,
    ];
    let mut d_queries: DeviceAllocation<u32> = DeviceAllocation::alloc(queries.len()).unwrap();
    memory_copy_async(&mut d_queries[..], &queries[..], &stream).unwrap();

    // Reference: gather against the packed buffer using the existing kernel.
    let mut d_ref_slab: DeviceAllocation<BF> =
        DeviceAllocation::alloc(queries.len() * dst_cols).unwrap();
    let ref_desc = OracleGatherDesc {
        cosets_ptr: d_packed.as_ptr() as u64,
        columns_count: dst_cols as u32,
        _pad: 0,
        slab_dst_ptr: d_ref_slab.as_mut_ptr() as u64,
    };
    let descs = [
        ref_desc,
        OracleGatherDesc::default(),
        OracleGatherDesc::default(),
    ];
    // Packed-layout call mirrors what `schedule_query_leaves_into` does for
    // the WHIR oracle today: log_lde_factor = 0, log_rows_per_leaf = 0,
    // log_domain_size = total_leaf_count.trailing_zeros().
    let log_total_leaf_count = total_leaf_count.trailing_zeros();
    gather_leaves_for_queries(
        &descs,
        1,
        /*log_lde_factor=*/ 0,
        /*log_domain_size=*/ log_total_leaf_count,
        /*log_rows_per_leaf=*/ 0,
        &d_queries[..],
        &stream,
    )
    .unwrap();
    let mut ref_slab_host = vec![BF::ZERO; queries.len() * dst_cols];
    memory_copy_async(&mut ref_slab_host[..], &d_ref_slab[..], &stream).unwrap();

    // New: gather against the natural-NTT buffer using the new kernel.
    let mut d_new_slab: DeviceAllocation<BF> =
        DeviceAllocation::alloc(queries.len() * dst_cols).unwrap();
    gather_leaves_for_queries_from_ntt(
        &d_natural[..],
        &mut d_new_slab[..],
        log_lde_factor as u32,
        (log_trace_len - log_values_per_leaf) as u32,
        log_values_per_leaf as u32,
        crate::LOG_SRC_COLS_PER_COSET,
        trace_len as u32,
        &d_queries[..],
        &stream,
    )
    .unwrap();
    let mut new_slab_host = vec![BF::ZERO; queries.len() * dst_cols];
    memory_copy_async(&mut new_slab_host[..], &d_new_slab[..], &stream).unwrap();

    stream.synchronize().unwrap();

    assert_eq!(
        ref_slab_host, new_slab_host,
        "gather_leaves_for_queries_from_ntt slab mismatch at log_trace_len={log_trace_len}, log_lde_factor={log_lde_factor}, log_values_per_leaf={log_values_per_leaf}"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn test_gather_leaves_for_queries_from_ntt_small() {
    run_gather_leaves_for_queries_from_ntt_matches_packed(8, 4, 3);
}

#[test]
#[cfg(not(no_cuda))]
fn test_gather_leaves_for_queries_from_ntt_medium() {
    run_gather_leaves_for_queries_from_ntt_matches_packed(12, 6, 4);
}

#[test]
#[cfg(not(no_cuda))]
fn test_gather_leaves_for_queries_from_ntt_large() {
    run_gather_leaves_for_queries_from_ntt_matches_packed(15, 8, 5);
}

// ---------------------------------------------------------------------------
// Bounds tripwires on the split-eq table builder
// ---------------------------------------------------------------------------
//
// `launch_build_split_eq_table` writes `num_queries << bits` E4 into its
// destination and reads claim coordinates `claim_offset..claim_offset + bits`
// out of each query's `log_n`-coordinate point. Both bounds are set by a bit
// split computed in the caller, and until these asserts existed neither was
// checked: an over-large `bits` wrote past the destination slab while staying
// inside the pool (no CUDA error, only a value comparison would notice), and
// `claim_offset + bits > log_n` read into the next query's coordinates, or past
// the buffer on the last query.

#[test]
#[cfg(not(no_cuda))]
#[should_panic(expected = "claim_offset + bits <= log_n")]
fn split_eq_table_rejects_claim_range_past_log_n() {
    let context = crate::test_utils::make_test_context(256, 32);
    let log_n = 8usize;
    let num_queries = 2usize;
    let (high_bits, low_bits) = split_eq_bits(log_n);
    let claim_points = context
        .alloc::<E4>(num_queries * log_n, AllocationPlacement::BestFit)
        .unwrap();
    let mut out = context
        .alloc::<E4>(num_queries << high_bits, AllocationPlacement::BestFit)
        .unwrap();
    // `low_bits` is the high slab's legal offset; one past it walks off the end
    // of the query's coordinate run.
    launch_build_split_eq_table(
        claim_points.as_ptr(),
        std::ptr::null(),
        log_n,
        high_bits,
        low_bits + 1,
        num_queries,
        &mut out[..],
        &context,
    )
    .unwrap();
}

#[test]
#[cfg(not(no_cuda))]
#[should_panic(expected = "out_array.len() >= num_queries << bits")]
fn split_eq_table_rejects_undersized_destination() {
    let context = crate::test_utils::make_test_context(256, 32);
    let log_n = 8usize;
    let num_queries = 3usize;
    let (high_bits, low_bits) = split_eq_bits(log_n);
    let claim_points = context
        .alloc::<E4>(num_queries * log_n, AllocationPlacement::BestFit)
        .unwrap();
    // One bit short of the table the `high_bits` build will write: exactly the
    // shape Task 8's negative control hit (3x8 E4 written into a 3x4 slab).
    let mut out = context
        .alloc::<E4>(num_queries << (high_bits - 1), AllocationPlacement::BestFit)
        .unwrap();
    launch_build_split_eq_table(
        claim_points.as_ptr(),
        std::ptr::null(),
        log_n,
        high_bits,
        low_bits,
        num_queries,
        &mut out[..],
        &context,
    )
    .unwrap();
}
