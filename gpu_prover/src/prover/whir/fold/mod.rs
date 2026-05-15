use core::marker::PhantomData;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::{
    bitreverse_enumeration_inplace, domain_generator_for_size,
    materialize_powers_serial_starting_with_one,
};

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::{Digest, STATE_SIZE};
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::ops::ntt::{
    hypercube_coeffs_bitrev_to_bitrev_evals, hypercube_x1_msb_evals_to_x1_msb_monomials,
    natural_evals_to_bitreversed_monomials,
};
use crate::ops::simple::{add, add_into_y, mul, mul_into_x};
use crate::ops::transpose::transpose;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, UnsafeMutAccessor,
};
use crate::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixOwnsAllocation,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{eq_group_tables_len, launch_build_eq_values_from_point};
use crate::prover::pow::{schedule_pow_verify_and_query_indexes, PowAndQueryIndexesState};
use crate::prover::proof::layout::ProofLayout;
use crate::prover::trace::holder::TraceHolder;
use crate::prover::whir::kernels::{
    accumulate_whir_base_columns, deserialize_whir_e4_columns, partially_evaluate_monomials_by_ref,
    serialize_whir_e4_columns, whir_fold_split_half_in_place,
    whir_fold_split_half_in_place_vectorized,
};
use crate::prover::whir::GpuWhirExtensionOracle;
use crate::upstream::{
    add_whir_commitment_to_transcript, commit_field_els, draw_random_field_els,
    extension_field_from_base_coeffs, BaseFieldQuery, DefaultTreeConstructor, ExtensionFieldQuery,
    Field, FieldExtension, MerkleTreeCapVarLength, Seed, WhirBaseLayerCommitmentAndQueries,
    WhirCommitment, WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof, WhirSchedule,
};

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;

mod schedule;
mod slab_copies;

pub(crate) use schedule::schedule_gpu_whir_fold_with_sources;
use slab_copies::{
    copy_base_layer_cap_to_slab, copy_intermediate_cap_to_slab, copy_intermediate_query_to_slab,
    copy_ood_sample_to_slab, copy_pow_nonce_to_slab,
};

pub(super) struct GpuWhirState {
    sumchecked_poly_monomial_form: DeviceMatrixOwnsAllocation<BF>,
    sumchecked_poly_evaluation_form: DeviceAllocation<E4>,
    eq_poly: DeviceAllocation<E4>,
    eq_group_tables: DeviceAllocation<E4>,
    scratch0: DeviceAllocation<E4>,
    scratch1: DeviceAllocation<E4>,
    point_pows: DeviceAllocation<E4>,
    #[allow(dead_code)]
    scalar: DeviceAllocation<E4>,
    reduce_temp: DeviceAllocation<u8>,
    reduce_out: DeviceAllocation<E4>,
    current_len: usize,
    original_trace_len: usize,
}

// `device_internal_index` is a length-1 slice the caller pre-populated with
// `query_index / lde_factor`. Base-layer memory/witness/setup oracles share
// the same `log_lde_factor` (`ProverConfig` invariant; asserted by the
// scheduler), so one shared internal-index buffer is filled once per query
// and re-used across all three calls.
//
// After upstream efa7bbd3, CPU records `BaseFieldQuery.index = tree_index`
// and retrieves the merkle path at `tree_index` too (see
// prover/src/gkr/whir/mod.rs, `ColumnMajorBaseOracleForLDE::query_for_folded_index`).
// The combined CPU tree is laid out with bit-reversed coset order over
// per-coset buckets of `coset_tree_size` leaves, so `trees[lde_coset]` on GPU
// corresponds to CPU bucket `bitreverse(lde_coset)` and the path within it is
// at CPU's `internal_index = query_index / lde_factor`. We therefore use the
// same `internal_index` for both value and path lookups; the per-coset
// selection (value_leafs[coset_index], path_merkle_paths[coset_index]) is the
// LDE coset index.
pub(super) fn schedule_unknown_coset_base_field_query(
    trace_holder: &mut TraceHolder<BF>,
    device_internal_index: &DeviceSlice<u32>,
    context: &ProverContext,
) -> CudaResult<ScheduledUnknownCosetBaseFieldQuery> {
    let lde_factor = 1usize << trace_holder.log_lde_factor;
    let values_per_leaf = 1usize << trace_holder.log_rows_per_leaf;
    let coset_tree_size = (1usize << trace_holder.log_domain_size) / values_per_leaf;
    if trace_holder.columns_count == 0 {
        return Ok(ScheduledUnknownCosetBaseFieldQuery {
            value_leafs: Vec::new(),
            path_merkle_paths: Vec::new(),
            values_per_leaf,
            columns_count: 0,
            coset_tree_size,
            log_lde_factor: trace_holder.log_lde_factor,
        });
    }
    let mut value_leafs = Vec::with_capacity(lde_factor);
    let mut path_merkle_paths = Vec::with_capacity(lde_factor);
    for coset_index in 0..lde_factor {
        value_leafs.push(trace_holder.get_query_leafs(
            coset_index,
            device_internal_index,
            context,
        )?);
        path_merkle_paths.push(trace_holder.get_query_merkle_paths(
            coset_index,
            device_internal_index,
            context,
        )?);
    }

    Ok(ScheduledUnknownCosetBaseFieldQuery {
        value_leafs,
        path_merkle_paths,
        values_per_leaf,
        columns_count: trace_holder.columns_count,
        coset_tree_size,
        log_lde_factor: trace_holder.log_lde_factor,
    })
}

pub(super) type WhirHostUpload = Callbacks<'static>;

pub(super) struct ScheduledUnknownCosetBaseFieldQuery {
    value_leafs: Vec<HostAllocation<[BF]>>,
    path_merkle_paths: Vec<HostAllocation<[Digest]>>,
    values_per_leaf: usize,
    columns_count: usize,
    coset_tree_size: usize,
    log_lde_factor: u32,
}

pub(crate) struct ScheduledWhirProofState {
    proof: Option<WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>>,
    #[cfg(test)]
    pre_pow_seeds: Vec<Seed>,
}

// Per-fold-round-group buffers that back the device-side transcript path.
// Aggregated into one struct because they have a shared lifetime: every
// scheduled stream op holding into them remains in flight until the
// surrounding `GpuWhirFoldScheduledExecution` is dropped.
pub(super) struct FoldRoundGroupKeepalives {
    pub(super) device_seeds: Vec<DeviceAllocation<u32>>,
    pub(super) device_challenges: Vec<DeviceAllocation<E4>>,
    pub(super) device_coeffs: Vec<DeviceAllocation<E4>>,
    pub(super) host_seed_stagings: Vec<HostAllocation<[u32]>>,
    pub(super) host_seed_mirrors: Vec<HostAllocation<[u32]>>,
    pub(super) host_coeffs: Vec<HostAllocation<[E4]>>,
    pub(super) upload_callbacks: Vec<Callbacks<'static>>,
}

impl FoldRoundGroupKeepalives {
    pub(super) fn new() -> Self {
        Self {
            device_seeds: Vec::new(),
            device_challenges: Vec::new(),
            device_coeffs: Vec::new(),
            host_seed_stagings: Vec::new(),
            host_seed_mirrors: Vec::new(),
            host_coeffs: Vec::new(),
            upload_callbacks: Vec::new(),
        }
    }
}

pub(crate) struct GpuWhirFoldScheduledExecution {
    #[allow(dead_code)]
    _tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    _start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    _folding_challenges: Vec<WhirHostUpload>,
    #[allow(dead_code)]
    _fold_round_group_keepalives: FoldRoundGroupKeepalives,
    // Keepalives for the device-side PoW verify + query index assembly
    // (one entry per WHIR round that goes through schedule_pow_verify_and_query_indexes).
    #[allow(dead_code)]
    _pow_round_state: Vec<PowAndQueryIndexesState>,
    #[allow(dead_code)]
    _ood_points: Vec<WhirHostUpload>,
    #[allow(dead_code)]
    _query_index_callbacks: Vec<Callbacks<'static>>,
    #[allow(dead_code)]
    _delinearization_challenges: Vec<WhirHostUpload>,
    #[allow(dead_code)]
    _base_queries: Vec<[Vec<ScheduledUnknownCosetBaseFieldQuery>; 3]>,
    #[allow(dead_code)]
    _recursive_queries: Vec<Vec<crate::prover::whir::GpuWhirScheduledExtensionQueryKeepalive>>,
    // Pinned host buffers that back D2H readbacks of the base-layer unified
    // device caps and the per-round intermediate WHIR oracle caps. The
    // start_callbacks / final_callbacks copy from these into the host-side
    // `proof.*_commitment.commitment.cap.cap` fields, so they must outlive
    // those callbacks.
    #[allow(dead_code)]
    _witness_cap_host_for_proof: HostAllocation<[Digest]>,
    #[allow(dead_code)]
    _memory_cap_host_for_proof: HostAllocation<[Digest]>,
    #[allow(dead_code)]
    _setup_cap_host_for_proof: Option<HostAllocation<[Digest]>>,
    #[allow(dead_code)]
    _intermediate_oracle_cap_hosts: Vec<HostAllocation<[Digest]>>,
    // Trace holders of retired intermediate WHIR oracles — kept alive so any
    // scheduled D2D/D2H reads against their unified device cap remain valid.
    #[allow(dead_code)]
    _recursive_caps_keepalive: Vec<crate::prover::whir::GpuWhirExtensionOracleKeepalive>,
    // Host buffer that backs the final-round monomial-form readback. The callback
    // that commits it to the transcript and writes `proof.final_monomials` holds a
    // raw accessor into this allocation, so it must outlive `final_callbacks`.
    #[allow(dead_code)]
    _final_monomials_host: Option<HostAllocation<[E4]>>,
    #[allow(dead_code)]
    _final_callbacks: Callbacks<'static>,
    shared_state: Box<ScheduledWhirProofState>,
}

impl GpuWhirFoldScheduledExecution {
    pub(crate) fn shared_state_handle(&mut self) -> UnsafeMutAccessor<ScheduledWhirProofState> {
        UnsafeMutAccessor::new(self.shared_state.as_mut())
    }
}

pub(crate) fn take_scheduled_whir_proof(
    shared_state: UnsafeMutAccessor<ScheduledWhirProofState>,
) -> WhirPolyCommitProof<BF, E4, DefaultTreeConstructor> {
    unsafe { shared_state.get_mut() }
        .proof
        .take()
        .expect("scheduled WHIR proof must be available")
}

impl GpuWhirState {
    fn new(trace_len: usize, context: &ProverContext) -> CudaResult<Self> {
        assert!(trace_len.is_power_of_two());
        assert!(trace_len >= 2);
        let half_len = trace_len / 2;
        let max_log_n = trace_len.trailing_zeros() as usize;
        let reduce_temp_bytes =
            get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, half_len as i32)?;
        Ok(Self {
            sumchecked_poly_monomial_form: DeviceMatrixOwnsAllocation::new(
                context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?,
                trace_len,
            ),
            sumchecked_poly_evaluation_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_poly: context.alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_group_tables: context.alloc(
                eq_group_tables_len(max_log_n).max(1),
                AllocationPlacement::BestFit,
            )?,
            scratch0: context.alloc(half_len, AllocationPlacement::BestFit)?,
            scratch1: context.alloc(half_len, AllocationPlacement::BestFit)?,
            point_pows: context.alloc(
                trace_len.trailing_zeros() as usize,
                AllocationPlacement::BestFit,
            )?,
            scalar: context.alloc(1, AllocationPlacement::BestFit)?,
            reduce_temp: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduce_temp_bytes,
                    AllocationPlacement::BestFit,
                )?,
            reduce_out: context.alloc(3, AllocationPlacement::BestFit)?,
            current_len: trace_len,
            original_trace_len: trace_len,
        })
    }
}

pub(super) fn schedule_callback_populated_upload<T: Copy + 'static>(
    context: &ProverContext,
    len: usize,
    fill: impl Fn(&mut [T]) + Send + Sync + 'static,
) -> CudaResult<(WhirHostUpload, HostAllocation<[T]>, DeviceAllocation<T>)> {
    let mut callbacks = Callbacks::new();
    let mut host = unsafe { context.alloc_host_uninit_slice(len) };
    let host_accessor = host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            fill(host_accessor.get_mut());
        },
        context.get_exec_stream(),
    )?;
    let mut device = context.alloc(len, AllocationPlacement::BestFit)?;
    memory_copy_async(&mut device, &host, context.get_exec_stream())?;
    Ok((callbacks, host, device))
}

pub(super) fn schedule_reduce_outputs_readback(
    count: usize,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E4]>> {
    let mut host = unsafe { context.alloc_host_uninit_slice(count) };
    memory_copy_async(
        &mut host,
        &state.reduce_out[..count],
        context.get_exec_stream(),
    )?;
    Ok(host)
}

/// Schedules a D2H of the unified device cap into a freshly allocated pinned
/// host buffer on `exec_stream`. Returns the buffer; the caller captures an
/// accessor into a downstream callback that fills the host-side
/// `proof.*_commitment.commitment.cap.cap`. The host buffer outlives every
/// scheduled op holding into it via the proof-job keepalive.
pub(super) fn schedule_unified_cap_d2h(
    unified_device_cap: &DeviceAllocation<Digest>,
    context: &ProverContext,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<HostAllocation<[Digest]>> {
    let cap_size = unified_device_cap.len();
    let mut host = unsafe { context.alloc_host_uninit_slice::<Digest>(cap_size) };
    memory_copy_async(&mut host, unified_device_cap, stream)?;
    Ok(host)
}

pub(super) fn make_preallocated_base_queries(
    count: usize,
    leaf_values_len: usize,
    path_len: usize,
) -> Vec<BaseFieldQuery<BF, DefaultTreeConstructor>> {
    (0..count)
        .map(|_| BaseFieldQuery {
            index: 0,
            leaf_values_concatenated: vec![BF::ZERO; leaf_values_len],
            path: vec![Digest::default(); path_len],
            _marker: PhantomData,
        })
        .collect()
}

pub(super) fn make_preallocated_extension_queries(
    count: usize,
    values_per_leaf: usize,
    path_len: usize,
) -> Vec<ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>> {
    (0..count)
        .map(|_| ExtensionFieldQuery {
            index: 0,
            leaf_values_concatenated: vec![E4::ZERO; values_per_leaf],
            path: vec![Digest::default(); path_len],
            _marker: PhantomData,
        })
        .collect()
}

pub(super) fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        debug_assert_eq!(index, 0);
        return 0;
    }
    index.reverse_bits() >> (usize::BITS - num_bits)
}

pub(super) fn fill_unknown_coset_base_field_query_from_accessors(
    dst: &mut BaseFieldQuery<BF, DefaultTreeConstructor>,
    index: usize,
    coset_tree_size: usize,
    log_lde_factor: u32,
    values_per_leaf: usize,
    columns_count: usize,
    value_leafs: &[crate::primitives::context::UnsafeAccessor<[BF]>],
    path_merkle_paths: &[crate::primitives::context::UnsafeAccessor<[Digest]>],
) {
    // CPU stores the merkle-tree-space index on `BaseFieldQuery.index` (see
    // prover/src/gkr/whir/mod.rs `ColumnMajorBaseOracleForLDE::query_for_folded_index`):
    //   tree_index = bitreverse(coset_index) * coset_tree_size + internal_index
    // where `coset_index = index & (lde_factor - 1)` and
    // `internal_index = index / lde_factor`. Match that here.
    let lde_factor = 1usize << log_lde_factor;
    let coset_index = index & (lde_factor - 1);
    let internal_index = index / lde_factor;
    let coset_dest_index = bitreverse_index(coset_index, log_lde_factor);
    let tree_index = coset_dest_index * coset_tree_size + internal_index;
    if columns_count == 0 {
        dst.leaf_values_concatenated.clear();
        dst.path.clear();
        dst.index = tree_index;
        return;
    }
    // Both value and path per-coset buffers are indexed by the LDE coset index; see the
    // comment in `schedule_unknown_coset_base_field_query` for why this matches the new
    // CPU tree-index convention.
    let leafs = unsafe { value_leafs[coset_index].get() };
    let path = unsafe { path_merkle_paths[coset_index].get() };
    let expected_leaf_values = values_per_leaf * columns_count;
    assert_eq!(
        dst.leaf_values_concatenated.len(),
        expected_leaf_values,
        "base-field query leaf destination length mismatch"
    );
    assert_eq!(
        dst.path.len(),
        path.len(),
        "base-field query path destination length mismatch"
    );
    dst.index = tree_index;
    for value_index in 0..values_per_leaf {
        for column in 0..columns_count {
            dst.leaf_values_concatenated[value_index * columns_count + column] =
                leafs[column * values_per_leaf + value_index];
        }
    }
    dst.path.copy_from_slice(path);
}

pub(super) fn fill_extension_query_from_accessors(
    dst: &mut ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
    index: usize,
    coset_tree_size: usize,
    log_lde_factor: u32,
    values_per_leaf: usize,
    leafs_accessor: crate::primitives::context::UnsafeAccessor<[BF]>,
    path_accessor: crate::primitives::context::UnsafeAccessor<[Digest]>,
) {
    let leafs = unsafe { leafs_accessor.get() };
    let path = unsafe { path_accessor.get() };
    assert_eq!(
        leafs.len(),
        values_per_leaf * EXT4_DEGREE,
        "extension query leaf source length mismatch"
    );
    assert_eq!(
        dst.leaf_values_concatenated.len(),
        values_per_leaf,
        "extension query leaf destination length mismatch"
    );
    assert_eq!(
        dst.path.len(),
        path.len(),
        "extension query path destination length mismatch"
    );
    // Match CPU `ColumnMajorExtensionOracleForLDE::query_for_folded_index`:
    //   tree_index = bitreverse(coset_index) * coset_tree_size + internal_index
    let lde_factor = 1usize << log_lde_factor;
    let coset_index = index & (lde_factor - 1);
    let internal_index = index / lde_factor;
    let coset_dest_index = bitreverse_index(coset_index, log_lde_factor);
    dst.index = coset_dest_index * coset_tree_size + internal_index;
    for value_index in 0..values_per_leaf {
        let mut coeffs = [BF::ZERO; EXT4_DEGREE];
        for column in 0..EXT4_DEGREE {
            coeffs[column] = leafs[value_index * EXT4_DEGREE + column];
        }
        dst.leaf_values_concatenated[value_index] =
            extension_field_from_base_coeffs::<BF, E4>(coeffs);
    }
    dst.path.copy_from_slice(path);
}

pub(super) fn get_base_columns<'a>(
    trace_holder: &'a TraceHolder<BF>,
    rows: usize,
    use_hypercube_evals: bool,
) -> DeviceMatrix<'a, BF> {
    let values = if use_hypercube_evals {
        // Use the logical hypercube-evaluation view here. `raw_hypercube_backing`
        // preserves ownership only; WHIR needs the row-shaped evaluation slice
        // that `get_hypercube_evals` already exposes.
        DeviceMatrix::new(trace_holder.get_hypercube_evals(), rows)
    } else {
        assert!(
            trace_holder.are_cosets_materialized(),
            "{} {}",
            "Tried to build WHIR initial state from coset 0, ",
            "but cosets are not materialized",
        );
        DeviceMatrix::new(trace_holder.get_evaluations(), rows)
    };
    values
}

// Also initializes evaluation form if use_hypercube_evals_for_batching was false.
pub(super) fn initialize_batched_monomial_form(
    log_domain_size: usize,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = 1 << log_domain_size;
    let mut vectorized_scratch =
        context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    serialize_whir_e4_columns(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        &mut vectorized_scratch,
        stream,
    )?;
    let vectorized_batched_evals_matrix = DeviceMatrix::new(&vectorized_scratch, trace_len);

    if use_hypercube_evals_for_batching {
        hypercube_x1_msb_evals_to_x1_msb_monomials(
            &vectorized_batched_evals_matrix,
            &mut state.sumchecked_poly_monomial_form,
            log_domain_size,
            false, // transpsoed_monomials,
            stream,
            context.get_device_properties(),
        )?;
        // If we're in this branch, it means state.sumchecked_poly_evaluation_form was
        // directly created by batching base hypercube evaluation columns, so we're done.
    } else {
        natural_evals_to_bitreversed_monomials(
            &vectorized_batched_evals_matrix,
            &mut state.sumchecked_poly_monomial_form,
            log_domain_size,
            false, // transposed_monomials
            stream,
            context.get_device_properties(),
        )?;
        let monomials_slice = state.sumchecked_poly_monomial_form.slice();
        for column in 0..EXT4_DEGREE {
            let src = &monomials_slice[column * trace_len..(column + 1) * trace_len];
            let dst = &mut vectorized_scratch[column * trace_len..(column + 1) * trace_len];
            // Interestingly, both work (I think because addition is commutative).
            // hypercube_coeffs_natural_to_natural_evals(
            hypercube_coeffs_bitrev_to_bitrev_evals(src, dst, log_domain_size, stream)?;
        }
        deserialize_whir_e4_columns(
            &vectorized_scratch,
            &mut state.sumchecked_poly_evaluation_form[..trace_len],
            stream,
        )?;
    }

    Ok(())
}

pub(super) fn schedule_initialize_batched_forms(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge_source: impl Fn() -> E4 + Send + Sync + 'static,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    callbacks: &mut Callbacks<'static>,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = state.current_len;
    assert_eq!(
        memory_trace_holder.log_domain_size,
        witness_trace_holder.log_domain_size
    );
    assert_eq!(
        memory_trace_holder.log_domain_size,
        setup_trace_holder.log_domain_size
    );
    assert_eq!(trace_len, 1usize << memory_trace_holder.log_domain_size);

    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let stream = context.get_exec_stream();

    let mut challenge_powers_host = unsafe { context.alloc_host_uninit_slice(total_base_oracles) };
    let challenge_powers_accessor = challenge_powers_host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            let challenge_powers = materialize_powers_serial_starting_with_one::<
                E4,
                std::alloc::Global,
            >(batching_challenge_source(), total_base_oracles);
            challenge_powers_accessor
                .get_mut()
                .copy_from_slice(&challenge_powers);
        },
        stream,
    )?;
    let mut challenge_powers_device =
        context.alloc(total_base_oracles, AllocationPlacement::BestFit)?;
    memory_copy_async(&mut challenge_powers_device, &challenge_powers_host, stream)?;

    assert!(
        mem_polys_claims_len + wit_polys_claims_len + setup_polys_claims_len > 0,
        "WHIR base-folding needs at least one base column across memory/witness/setup",
    );

    let challenge_powers_device_slice = &mut challenge_powers_device[..];
    let (device_memory_weights, rest) =
        challenge_powers_device_slice.split_at_mut(mem_polys_claims_len);
    let (device_witness_weights, device_setup_weights) = rest.split_at_mut(wit_polys_claims_len);
    assert_eq!(device_setup_weights.len(), setup_polys_claims_len);

    let rows = state.sumchecked_poly_evaluation_form.len();
    let memory_values =
        get_base_columns(memory_trace_holder, rows, use_hypercube_evals_for_batching);
    let witness_values =
        get_base_columns(witness_trace_holder, rows, use_hypercube_evals_for_batching);
    let setup_values = get_base_columns(setup_trace_holder, rows, use_hypercube_evals_for_batching);

    accumulate_whir_base_columns(
        &memory_values,
        &witness_values,
        &setup_values,
        &device_memory_weights,
        &device_witness_weights,
        &device_setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        stream,
    )?;

    initialize_batched_monomial_form(
        memory_trace_holder.log_domain_size as usize,
        use_hypercube_evals_for_batching,
        state,
        context,
    )?;

    Ok(())
}

/// Computes the three sumcheck reductions needed per WHIR fold round into
/// `state.reduce_out[0..3]`. Output layout:
///   [0] = ⟨eval_low, eq_low⟩          = f(0)
///   [1] = ⟨eval_high, eq_high⟩        = f(1)
///   [2] = ⟨eval_low+eval_high, eq_low+eq_high⟩   (callers scale by 1/4 to get f(1/2))
///
/// Leaves the result on the device; callers that need a host copy must follow
/// up with `schedule_reduce_outputs_readback(3, ...)`.
pub(super) fn schedule_special_three_point_eval_device_compute(
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    let half = state.current_len / 2;
    assert!(half <= state.scratch0.len());
    let stream = context.get_exec_stream();

    {
        let (eval_low, _) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (eq_low, _) = state.eq_poly[..state.current_len].split_at(half);
        mul(eval_low, eq_low, &mut state.scratch0[..half], stream)?;
    }
    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..half],
        &mut state.reduce_out[0],
        stream,
    )?;

    {
        let (_, eval_high) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (_, eq_high) = state.eq_poly[..state.current_len].split_at(half);
        mul(eval_high, eq_high, &mut state.scratch0[..half], stream)?;
    }
    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..half],
        &mut state.reduce_out[1],
        stream,
    )?;

    {
        let (eval_low, eval_high) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (eq_low, eq_high) = state.eq_poly[..state.current_len].split_at(half);
        add(eval_low, eval_high, &mut state.scratch0[..half], stream)?;
        add(eq_low, eq_high, &mut state.scratch1[..half], stream)?;
    }
    mul_into_x(&mut state.scratch0[..half], &state.scratch1[..half], stream)?;
    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..half],
        &mut state.reduce_out[2],
        stream,
    )?;

    Ok(())
}

pub(super) fn schedule_monomial_eval_device_impl(
    state: &mut GpuWhirState,
    point: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();

    let partials_count = partially_evaluate_monomials_by_ref(
        &state.sumchecked_poly_monomial_form,
        &mut state.scratch0[..],
        &mut state.scratch1[..],
        point,
        state.current_len,
        stream,
    )?;

    let reduce_temp_bytes =
        get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, partials_count as i32)?;
    assert!(state.reduce_temp.len() >= reduce_temp_bytes);

    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..partials_count],
        &mut state.reduce_out[0],
        stream,
    )
}

pub(super) fn schedule_monomial_eval_device(
    state: &mut GpuWhirState,
    point: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<Vec<HostAllocation<[E4]>>> {
    schedule_monomial_eval_device_impl(state, point, context)?;

    let mut result = Vec::new();
    result.push(schedule_reduce_outputs_readback(1, state, context)?);

    Ok(result)
}

pub(super) fn schedule_accumulate_eq_sample_in_place_device(
    state: &mut GpuWhirState,
    fill_point_pows: impl Fn(&mut [E4]) + Send + Sync + 'static,
    challenge: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<(WhirHostUpload, HostAllocation<[E4]>)> {
    let log_n = state.current_len.trailing_zeros() as usize;
    let (point_pows_upload, _point_pows_host, point_pows_device) =
        schedule_callback_populated_upload(context, log_n, fill_point_pows)?;
    launch_build_eq_values_from_point(
        point_pows_device.as_ptr(),
        0,
        log_n,
        state.eq_group_tables.as_mut_ptr(),
        state.scratch0.as_mut_ptr(),
        state.current_len,
        context,
    )?;
    mul_into_x(
        &mut state.scratch0[..state.current_len],
        &challenge[0],
        context.get_exec_stream(),
    )?;
    add_into_y(
        &state.scratch0[..state.current_len],
        &mut state.eq_poly[..state.current_len],
        context.get_exec_stream(),
    )?;
    Ok((point_pows_upload, _point_pows_host))
}

#[cfg(test)]
pub(crate) use tests::{
    clone_scheduled_whir_pre_pow_seeds, debug_apply_initial_fold_challenge_for_test,
    debug_build_initial_batched_evals_for_test, debug_build_initial_fold_state_for_test,
    debug_build_initial_state_for_test, debug_build_initial_state_snapshots_for_test,
    debug_initial_round_checkpoint_for_test,
};

#[cfg(test)]
mod tests;
