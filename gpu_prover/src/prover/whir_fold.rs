use core::marker::PhantomData;

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::{
    batch_inverse_inplace, bitreverse_enumeration_inplace, domain_generator_for_size,
    materialize_powers_serial_starting_with_one,
};
use field::{Field, FieldExtension, FixedArrayConvertible, PrimeField};
use prover::definitions::Transcript;
use prover::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_query_bits, draw_random_field_els,
};
use prover::gkr::sumcheck::evaluate_small_univariate_poly;
use prover::gkr::whir::{
    BaseFieldQuery, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries, WhirCommitment,
    WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
use prover::prover_stages::query_producer::assemble_query_index;
use prover::transcript::Seed;
use prover::utils::extension_field_from_base_coeffs;
use worker::Worker;

use crate::allocator::tracker::AllocationPlacement;
use crate::ntt::{hypercube_coeffs_natural_to_natural_evals, natural_evals_to_bitreversed_coeffs};
use crate::ops::blake2s::Digest;
use crate::ops::complex::{
    accumulate_whir_base_columns, bit_reverse, bit_reverse_in_place, deserialize_whir_e4_columns,
    get_powers_by_ref, get_powers_by_val, serialize_whir_e4_columns, whir_fold_monomial,
    whir_fold_split_half_in_place,
};
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::ops::simple::{add, add_into_y, mul, mul_into_x, set_to_zero};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::{
    alloc_static_pinned_box_from_slice, alloc_static_pinned_box_uninit,
};
use crate::prover::gkr::backward::launch_build_eq_values;
use crate::prover::pow::search_pow_challenge;
use crate::prover::proof::{
    draw_query_bits_after_verified_pow, draw_query_bits_with_external_nonce,
};
use crate::prover::trace_holder::{get_tree_caps, TraceHolder};
use crate::prover::whir::{GpuWhirExtensionOracle, GpuWhirExtensionQuery};

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;
struct GpuWhirState {
    sumchecked_poly_monomial_form: DeviceAllocation<E4>,
    monomial_buffer: DeviceAllocation<E4>,
    sumchecked_poly_evaluation_form: DeviceAllocation<E4>,
    eq_poly: DeviceAllocation<E4>,
    scratch0: DeviceAllocation<E4>,
    scratch1: DeviceAllocation<E4>,
    point_pows: DeviceAllocation<E4>,
    scalar: DeviceAllocation<E4>,
    reduce_temp: DeviceAllocation<u8>,
    reduce_out: DeviceAllocation<E4>,
    current_len: usize,
}

pub(crate) struct GpuScheduledBaseFieldQuery {
    pub(crate) index: usize,
    pub(crate) coset_index: usize,
    // Keeps index-fill callbacks alive until the stream executes them.
    #[allow(dead_code)]
    callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    leafs: HostAllocation<[BF]>,
    #[allow(dead_code)]
    merkle_paths: HostAllocation<[Digest]>,
    values_per_leaf: usize,
    columns_count: usize,
}

impl GpuScheduledBaseFieldQuery {
    pub(crate) fn decode(&self) -> (Vec<Vec<BF>>, BaseFieldQuery<BF, DefaultTreeConstructor>) {
        let leafs_accessor = self.leafs.get_accessor();
        let path_accessor = self.merkle_paths.get_accessor();
        let leafs = unsafe { leafs_accessor.get() };
        let path = unsafe { path_accessor.get().to_vec() };
        let decoded = decode_base_leaf_values(leafs, self.values_per_leaf, self.columns_count);
        let cpu_query = BaseFieldQuery {
            index: self.index,
            leaf_values_concatenated: decoded.iter().flatten().copied().collect(),
            path,
            _marker: PhantomData,
        };

        (decoded, cpu_query)
    }
}

impl ScheduledUnknownCosetBaseFieldQuery {
    fn decode(
        &self,
    ) -> (
        usize,
        Vec<Vec<BF>>,
        BaseFieldQuery<BF, DefaultTreeConstructor>,
    ) {
        let index = unsafe { self.query_index.get_accessor().get()[0] as usize };
        let lde_factor = 1usize << self.log_lde_factor;
        let value_coset_index = index & (lde_factor - 1);
        let stage1_coset_index = index / self.coset_tree_size;
        let path_coset_index = bitreverse_index(stage1_coset_index, self.log_lde_factor);
        let leafs_accessor = self.value_leafs[value_coset_index].get_accessor();
        let leafs = unsafe { leafs_accessor.get() };
        let path = unsafe {
            self.path_merkle_paths[path_coset_index]
                .get_accessor()
                .get()
                .to_vec()
        };
        let decoded = decode_base_leaf_values(leafs, self.values_per_leaf, self.columns_count);
        let cpu_query = BaseFieldQuery {
            index,
            leaf_values_concatenated: decoded.iter().flatten().copied().collect(),
            path,
            _marker: PhantomData,
        };

        (value_coset_index, decoded, cpu_query)
    }
}

fn schedule_unknown_coset_base_field_query(
    trace_holder: &mut TraceHolder<BF>,
    query_index: HostAllocation<[u32]>,
    context: &ProverContext,
) -> CudaResult<ScheduledUnknownCosetBaseFieldQuery> {
    let lde_factor = 1usize << trace_holder.log_lde_factor;
    let values_per_leaf = 1usize << trace_holder.log_rows_per_leaf;
    let coset_tree_size = (1usize << trace_holder.log_domain_size) / values_per_leaf;
    let mut callbacks = Callbacks::new();
    let mut value_internal_index = unsafe { context.alloc_host_uninit_slice(1) };
    let value_internal_accessor = value_internal_index.get_mut_accessor();
    let query_index_accessor = query_index.get_accessor();
    callbacks.schedule(
        move || unsafe {
            value_internal_accessor.get_mut()[0] =
                query_index_accessor.get()[0] / (lde_factor as u32);
        },
        context.get_exec_stream(),
    )?;
    let mut path_internal_index = unsafe { context.alloc_host_uninit_slice(1) };
    let path_internal_accessor = path_internal_index.get_mut_accessor();
    let query_index_accessor = query_index.get_accessor();
    callbacks.schedule(
        move || unsafe {
            path_internal_accessor.get_mut()[0] =
                query_index_accessor.get()[0] % (coset_tree_size as u32);
        },
        context.get_exec_stream(),
    )?;
    let mut device_value_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_value_index,
        &value_internal_index,
        context.get_exec_stream(),
    )?;
    drop(value_internal_index);
    let mut device_path_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_path_index,
        &path_internal_index,
        context.get_exec_stream(),
    )?;
    drop(path_internal_index);

    let mut value_leafs = Vec::with_capacity(lde_factor);
    let mut path_merkle_paths = Vec::with_capacity(lde_factor);
    for coset_index in 0..lde_factor {
        value_leafs.push(
            trace_holder
                .get_leafs_and_merkle_paths(coset_index, &device_value_index, context)?
                .leafs,
        );
        path_merkle_paths.push(
            trace_holder
                .get_leafs_and_merkle_paths(coset_index, &device_path_index, context)?
                .merkle_paths,
        );
    }

    Ok(ScheduledUnknownCosetBaseFieldQuery {
        callbacks,
        query_index,
        value_leafs,
        path_merkle_paths,
        values_per_leaf,
        columns_count: trace_holder.columns_count,
        coset_tree_size,
        log_lde_factor: trace_holder.log_lde_factor,
    })
}

struct WhirHostUpload<T> {
    callbacks: Callbacks<'static>,
    host: HostAllocation<[T]>,
}

struct ScheduledUnknownCosetBaseFieldQuery {
    callbacks: Callbacks<'static>,
    query_index: HostAllocation<[u32]>,
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

pub(crate) struct GpuWhirFoldScheduledExecution {
    #[allow(dead_code)]
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    seed_host: HostAllocation<Seed>,
    #[allow(dead_code)]
    base_layer_point_host: HostAllocation<[E4]>,
    #[allow(dead_code)]
    base_caps_keepalive: [Vec<HostAllocation<[Digest]>>; 3],
    #[allow(dead_code)]
    fold_eval_readbacks: Vec<HostAllocation<[E4]>>,
    #[allow(dead_code)]
    folding_challenges: Vec<WhirHostUpload<E4>>,
    #[allow(dead_code)]
    recursive_caps_keepalive: Vec<Vec<HostAllocation<[Digest]>>>,
    #[allow(dead_code)]
    ood_points: Vec<WhirHostUpload<E4>>,
    #[allow(dead_code)]
    ood_partial_readbacks: Vec<Vec<HostAllocation<[E4]>>>,
    #[allow(dead_code)]
    ood_values: Vec<HostAllocation<[E4]>>,
    #[allow(dead_code)]
    query_index_callbacks: Vec<Callbacks<'static>>,
    #[allow(dead_code)]
    query_indexes: Vec<HostAllocation<[u32]>>,
    #[allow(dead_code)]
    delinearization_challenges: Vec<WhirHostUpload<E4>>,
    #[allow(dead_code)]
    pow_nonces: Vec<HostAllocation<u64>>,
    #[allow(dead_code)]
    base_queries: Vec<[Vec<ScheduledUnknownCosetBaseFieldQuery>; 3]>,
    #[allow(dead_code)]
    recursive_queries: Vec<Vec<crate::prover::whir::GpuWhirScheduledExtensionQuery>>,
    #[allow(dead_code)]
    final_callbacks: Callbacks<'static>,
    shared_state: std::sync::Arc<std::sync::Mutex<ScheduledWhirProofState>>,
}

impl GpuWhirFoldScheduledExecution {
    pub(crate) fn shared_state_handle(
        &self,
    ) -> std::sync::Arc<std::sync::Mutex<ScheduledWhirProofState>> {
        std::sync::Arc::clone(&self.shared_state)
    }

    pub(crate) fn wait(
        self,
        context: &ProverContext,
    ) -> CudaResult<WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>> {
        context.get_exec_stream().synchronize()?;
        self.shared_state
            .lock()
            .unwrap()
            .proof
            .take()
            .ok_or(era_cudart_sys::CudaError::ErrorInvalidValue)
    }
}

pub(crate) fn take_scheduled_whir_proof(
    shared_state: &std::sync::Arc<std::sync::Mutex<ScheduledWhirProofState>>,
) -> WhirPolyCommitProof<BF, E4, DefaultTreeConstructor> {
    shared_state
        .lock()
        .unwrap()
        .proof
        .take()
        .expect("scheduled WHIR proof must be available")
}

#[cfg(test)]
pub(crate) fn clone_scheduled_whir_pre_pow_seeds(
    shared_state: &std::sync::Arc<std::sync::Mutex<ScheduledWhirProofState>>,
) -> Vec<Seed> {
    shared_state.lock().unwrap().pre_pow_seeds.clone()
}

impl GpuWhirState {
    fn new(trace_len: usize, context: &ProverContext) -> CudaResult<Self> {
        assert!(trace_len.is_power_of_two());
        assert!(trace_len >= 2);
        let half_len = trace_len / 2;
        let reduce_temp_bytes =
            get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, half_len as i32)?;
        Ok(Self {
            sumchecked_poly_monomial_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            monomial_buffer: context.alloc(half_len, AllocationPlacement::BestFit)?,
            sumchecked_poly_evaluation_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_poly: context.alloc(trace_len, AllocationPlacement::BestFit)?,
            scratch0: context.alloc(half_len, AllocationPlacement::BestFit)?,
            scratch1: context.alloc(half_len, AllocationPlacement::BestFit)?,
            point_pows: context.alloc(
                trace_len.trailing_zeros() as usize,
                AllocationPlacement::BestFit,
            )?,
            scalar: context.alloc(1, AllocationPlacement::BestFit)?,
            reduce_temp: context.alloc(reduce_temp_bytes, AllocationPlacement::BestFit)?,
            reduce_out: context.alloc(3, AllocationPlacement::BestFit)?,
            current_len: trace_len,
        })
    }
}

fn schedule_callback_populated_upload<T: Copy + 'static>(
    context: &ProverContext,
    len: usize,
    fill: impl Fn(&mut [T]) + Send + Sync + 'static,
) -> CudaResult<(WhirHostUpload<T>, DeviceAllocation<T>)> {
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
    Ok((WhirHostUpload { callbacks, host }, device))
}

fn copy_small_to_device<T: Copy>(
    dst: &mut DeviceSlice<T>,
    values: &[T],
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(dst.len(), values.len());
    let host = alloc_static_pinned_box_from_slice(values)?;
    memory_copy_async(dst, &host[..], context.get_exec_stream())
}

fn schedule_copy_small_to_device<T: Copy + Send + Sync + 'static>(
    dst: &mut DeviceSlice<T>,
    values: &[T],
    callbacks: &mut Callbacks<'static>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(dst.len(), values.len());
    let values = values.to_vec();
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    let host_accessor = host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            // SAFETY: the callback owns the raw accessor into `host`, and both the callback and
            // the H2D copy are queued on exec_stream before `host` is dropped at the end of this
            // function, satisfying the stream-ordered host-lifetime contract.
            host_accessor.get_mut().copy_from_slice(&values);
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(dst, &host, context.get_exec_stream())
}

fn copy_scalar_to_device(
    value: E4,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_small_to_device(&mut state.scalar, &[value], context)
}

fn read_reduce_outputs(
    count: usize,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    let stream = context.get_exec_stream();
    let mut host = unsafe { context.alloc_host_uninit_slice(count) };
    memory_copy_async(&mut host, &state.reduce_out[..count], stream)?;
    stream.synchronize()?;
    Ok(unsafe { host.get_accessor().get().to_vec() })
}

fn schedule_reduce_outputs_readback(
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

fn full_cap_from_trace_holder(trace_holder: &TraceHolder<BF>) -> MerkleTreeCapVarLength {
    MerkleTreeCapVarLength {
        cap: trace_holder
            .get_tree_caps()
            .into_iter()
            .flat_map(|subcap| subcap.cap)
            .collect(),
    }
}

fn full_cap_from_host_caps(
    tree_caps: &[HostAllocation<[Digest]>],
    log_lde_factor: u32,
) -> MerkleTreeCapVarLength {
    MerkleTreeCapVarLength {
        cap: get_tree_caps(
            &tree_caps
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>(),
            log_lde_factor,
        )
        .into_iter()
        .flat_map(|subcap| subcap.cap)
        .collect(),
    }
}

fn full_cap_from_accessors(
    accessors: &[crate::primitives::context::UnsafeAccessor<[Digest]>],
    log_lde_factor: u32,
) -> MerkleTreeCapVarLength {
    MerkleTreeCapVarLength {
        cap: get_tree_caps(accessors, log_lde_factor)
            .into_iter()
            .flat_map(|subcap| subcap.cap)
            .collect(),
    }
}

fn cap_digest_count_from_accessors(
    accessors: &[crate::primitives::context::UnsafeAccessor<[Digest]>],
) -> usize {
    accessors
        .iter()
        .map(|accessor| unsafe { accessor.get().len() })
        .sum()
}

fn fill_full_cap_from_accessors(
    dst: &mut [Digest],
    accessors: &[crate::primitives::context::UnsafeAccessor<[Digest]>],
    log_lde_factor: u32,
) {
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(accessors.len(), lde_factor);
    let expected_len = accessors
        .iter()
        .map(|accessor| unsafe { accessor.get().len() })
        .sum::<usize>();
    assert_eq!(
        dst.len(),
        expected_len,
        "WHIR cap destination length mismatch"
    );
    let mut offset = 0;
    for stage1_pos in 0..lde_factor {
        let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
        let src = unsafe { accessors[natural_coset_index].get() };
        let len = src.len();
        dst[offset..offset + len].copy_from_slice(src);
        offset += len;
    }
}

fn make_preallocated_base_queries(
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

fn make_preallocated_extension_queries(
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

fn decode_base_leaf_values(
    leafs: &[BF],
    values_per_leaf: usize,
    columns_count: usize,
) -> Vec<Vec<BF>> {
    assert_eq!(leafs.len(), values_per_leaf * columns_count);
    let mut result = (0..values_per_leaf)
        .map(|_| Vec::with_capacity(columns_count))
        .collect::<Vec<_>>();
    for column in 0..columns_count {
        for slot in 0..values_per_leaf {
            result[slot].push(leafs[column * values_per_leaf + slot]);
        }
    }
    result
}

fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        debug_assert_eq!(index, 0);
        return 0;
    }
    index.reverse_bits() >> (usize::BITS - num_bits)
}

pub(crate) fn query_base_trace_holder_for_folded_index(
    trace_holder: &mut TraceHolder<BF>,
    index: usize,
    context: &ProverContext,
) -> CudaResult<(
    usize,
    Vec<Vec<BF>>,
    BaseFieldQuery<BF, DefaultTreeConstructor>,
)> {
    let scheduled =
        schedule_query_base_trace_holder_for_folded_index(trace_holder, index, context)?;
    context.get_exec_stream().synchronize()?;
    let (decoded, cpu_query) = scheduled.decode();
    Ok((scheduled.coset_index, decoded, cpu_query))
}

pub(crate) fn schedule_query_base_trace_holder_for_folded_index(
    trace_holder: &mut TraceHolder<BF>,
    index: usize,
    context: &ProverContext,
) -> CudaResult<GpuScheduledBaseFieldQuery> {
    let lde_factor = 1usize << trace_holder.log_lde_factor;
    let values_per_leaf = 1usize << trace_holder.log_rows_per_leaf;
    let coset_tree_size = (1usize << trace_holder.log_domain_size) / values_per_leaf;
    assert!(values_per_leaf.is_power_of_two());
    assert!(index < (1usize << trace_holder.log_domain_size) * lde_factor / values_per_leaf);
    let value_coset_index = index & (lde_factor - 1);
    let value_internal_index = index / lde_factor;
    let mut callbacks = Callbacks::new();
    let mut host_value_index = unsafe { context.alloc_host_uninit_slice(1) };
    let vi_accessor = host_value_index.get_mut_accessor();
    callbacks.schedule(
        move || unsafe { vi_accessor.get_mut()[0] = value_internal_index as u32 },
        context.get_exec_stream(),
    )?;
    let mut device_value_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_value_index,
        &host_value_index,
        context.get_exec_stream(),
    )?;
    drop(host_value_index);
    let value_query =
        trace_holder.get_leafs_and_merkle_paths(value_coset_index, &device_value_index, context)?;

    let stage1_coset_index = index / coset_tree_size;
    let path_coset_index = bitreverse_index(stage1_coset_index, trace_holder.log_lde_factor);
    let path_internal_index = index % coset_tree_size;
    let mut host_path_index = unsafe { context.alloc_host_uninit_slice(1) };
    let pi_accessor = host_path_index.get_mut_accessor();
    callbacks.schedule(
        move || unsafe { pi_accessor.get_mut()[0] = path_internal_index as u32 },
        context.get_exec_stream(),
    )?;
    let mut device_path_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_path_index,
        &host_path_index,
        context.get_exec_stream(),
    )?;
    drop(host_path_index);
    let path_query =
        trace_holder.get_leafs_and_merkle_paths(path_coset_index, &device_path_index, context)?;
    Ok(GpuScheduledBaseFieldQuery {
        index,
        coset_index: value_coset_index,
        callbacks,
        leafs: value_query.leafs,
        merkle_paths: path_query.merkle_paths,
        values_per_leaf,
        columns_count: trace_holder.columns_count,
    })
}

fn into_extension_query(
    query: GpuWhirExtensionQuery,
) -> ExtensionFieldQuery<BF, E4, DefaultTreeConstructor> {
    ExtensionFieldQuery {
        index: query.index,
        leaf_values_concatenated: query.leaf_values_concatenated,
        path: query.path,
        _marker: PhantomData,
    }
}

fn make_pows(mut point: E4, count: usize) -> Vec<E4> {
    let mut result = Vec::with_capacity(count);
    for _ in 0..count {
        result.push(point);
        point.square();
    }
    result
}

fn special_lagrange_interpolate(
    eval_at_0: E4,
    eval_at_1: E4,
    eval_at_random: E4,
    random_point: E4,
) -> [E4; 3] {
    let mut coeffs_for_0 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_0[1] = E4::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();
    coeffs_for_0[0] = random_point;

    let mut coeffs_for_1 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_1[1] = random_point;
    coeffs_for_1[1].negate();

    let mut coeffs_for_random = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_random[1] = E4::ONE;
    coeffs_for_random[1].negate();

    let mut dens = [E4::ONE, E4::ONE, E4::ONE];
    let mut t = E4::ZERO;
    t.sub_assign(&E4::ONE);
    dens[0].mul_assign(&t);
    let mut t = E4::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E4::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let mut t = random_point;
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E4::ONE);
    dens[2].mul_assign(&t);

    let mut buffer = [E4::ZERO; 3];
    batch_inverse_inplace(&mut dens, &mut buffer);

    let mut result = [E4::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random),
    ] {
        for (dst, coeff) in result.iter_mut().zip(coeffs.into_iter()) {
            let mut term = coeff;
            term.mul_assign(&den);
            term.mul_assign(&eval);
            dst.add_assign(&term);
        }
    }

    result
}

fn decode_unknown_coset_base_field_query_from_accessors(
    index: usize,
    coset_tree_size: usize,
    log_lde_factor: u32,
    values_per_leaf: usize,
    columns_count: usize,
    value_leafs: &[crate::primitives::context::UnsafeAccessor<[BF]>],
    path_merkle_paths: &[crate::primitives::context::UnsafeAccessor<[Digest]>],
) -> (
    usize,
    Vec<Vec<BF>>,
    BaseFieldQuery<BF, DefaultTreeConstructor>,
) {
    let lde_factor = 1usize << log_lde_factor;
    let value_coset_index = index & (lde_factor - 1);
    let stage1_coset_index = index / coset_tree_size;
    let path_coset_index = bitreverse_index(stage1_coset_index, log_lde_factor);
    let leafs = unsafe { value_leafs[value_coset_index].get() };
    let path = unsafe { path_merkle_paths[path_coset_index].get().to_vec() };
    let decoded = decode_base_leaf_values(leafs, values_per_leaf, columns_count);
    let cpu_query = BaseFieldQuery {
        index,
        leaf_values_concatenated: decoded.iter().flatten().copied().collect(),
        path,
        _marker: PhantomData,
    };

    (value_coset_index, decoded, cpu_query)
}

fn fill_unknown_coset_base_field_query_from_accessors(
    dst: &mut BaseFieldQuery<BF, DefaultTreeConstructor>,
    index: usize,
    coset_tree_size: usize,
    log_lde_factor: u32,
    values_per_leaf: usize,
    columns_count: usize,
    value_leafs: &[crate::primitives::context::UnsafeAccessor<[BF]>],
    path_merkle_paths: &[crate::primitives::context::UnsafeAccessor<[Digest]>],
) {
    let lde_factor = 1usize << log_lde_factor;
    let value_coset_index = index & (lde_factor - 1);
    let stage1_coset_index = index / coset_tree_size;
    let path_coset_index = bitreverse_index(stage1_coset_index, log_lde_factor);
    let leafs = unsafe { value_leafs[value_coset_index].get() };
    let path = unsafe { path_merkle_paths[path_coset_index].get() };
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
    dst.index = index;
    for value_index in 0..values_per_leaf {
        for column in 0..columns_count {
            dst.leaf_values_concatenated[value_index * columns_count + column] =
                leafs[column * values_per_leaf + value_index];
        }
    }
    dst.path.copy_from_slice(path);
}

fn decode_extension_query_from_accessors(
    index: usize,
    values_per_leaf: usize,
    leafs_accessor: crate::primitives::context::UnsafeAccessor<[BF]>,
    path_accessor: crate::primitives::context::UnsafeAccessor<[Digest]>,
) -> GpuWhirExtensionQuery {
    let leafs = unsafe { leafs_accessor.get() };
    assert_eq!(leafs.len(), values_per_leaf * EXT4_DEGREE);
    let mut leaf_values_concatenated = Vec::with_capacity(values_per_leaf);
    for value_index in 0..values_per_leaf {
        let mut coeffs = [BF::ZERO; EXT4_DEGREE];
        for column in 0..EXT4_DEGREE {
            coeffs[column] = leafs[value_index * EXT4_DEGREE + column];
        }
        leaf_values_concatenated.push(extension_field_from_base_coeffs::<BF, E4>(coeffs));
    }
    let path = unsafe { path_accessor.get().to_vec() };
    GpuWhirExtensionQuery {
        index,
        leaf_values_concatenated,
        path,
    }
}

fn fill_extension_query_from_accessors(
    dst: &mut ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
    index: usize,
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
    dst.index = index;
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

fn fold_coset(
    mut flattened_evals: Vec<E4>,
    num_folding_rounds: usize,
    folding_challenges: &[E4],
    base_root_inv: &BF,
    high_powers_offsets: &[BF],
    two_inv: &BF,
) -> E4 {
    let mut root_inv = *base_root_inv;
    let mut buffer = Vec::with_capacity(flattened_evals.len());
    for folding_step in 0..num_folding_rounds {
        let (src, dst) = if folding_step % 2 == 0 {
            (&flattened_evals[..], &mut buffer)
        } else {
            (&buffer[..], &mut flattened_evals)
        };
        dst.clear();
        for (set_idx, [a, b]) in src.as_chunks::<2>().0.iter().enumerate() {
            let mut t = *a;
            t.sub_assign(b);
            t.mul_assign(&folding_challenges[folding_step]);
            let mut root = root_inv;
            root.mul_assign(&high_powers_offsets[set_idx]);
            t.mul_assign_by_base(&root);
            t.add_assign(a);
            t.add_assign(b);
            t.mul_assign_by_base(two_inv);
            dst.push(t);
        }
        root_inv.square();
    }
    if num_folding_rounds % 2 == 1 {
        buffer[0]
    } else {
        flattened_evals[0]
    }
}

fn build_initial_batched_main_domain_poly_device_impl(
    memory_trace_holder: &TraceHolder<BF>,
    memory_weights: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    witness_weights: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_weights: &[E4],
    result: &mut DeviceSlice<E4>,
    mut upload_weights: impl FnMut(&mut DeviceSlice<E4>, &[E4], &ProverContext) -> CudaResult<()>,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<E4>>> {
    let stream = context.get_exec_stream();
    set_to_zero(result, stream)?;
    let mut weight_buffers = Vec::with_capacity(3);

    for (trace_holder, weights) in [
        (memory_trace_holder, memory_weights),
        (witness_trace_holder, witness_weights),
        (setup_trace_holder, setup_weights),
    ] {
        if weights.is_empty() {
            continue;
        }
        assert!(
            trace_holder.are_cosets_materialized(),
            "WHIR initial state requires materialized main-domain cosets",
        );
        let mut device_weights = context.alloc(weights.len(), AllocationPlacement::BestFit)?;
        upload_weights(&mut device_weights, weights, context)?;
        let values = DeviceMatrix::new(trace_holder.get_evaluations(), result.len());
        accumulate_whir_base_columns(&values, &device_weights, result, stream)?;
        weight_buffers.push(device_weights);
    }

    Ok(weight_buffers)
}

fn build_initial_batched_main_domain_poly_device(
    memory_trace_holder: &TraceHolder<BF>,
    memory_weights: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    witness_weights: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_weights: &[E4],
    result: &mut DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<E4>>> {
    build_initial_batched_main_domain_poly_device_impl(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        result,
        |dst, values, context| copy_small_to_device(dst, values, context),
        context,
    )
}

fn schedule_build_initial_batched_main_domain_poly_device(
    memory_trace_holder: &TraceHolder<BF>,
    memory_weights: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    witness_weights: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_weights: &[E4],
    result: &mut DeviceSlice<E4>,
    callbacks: &mut Callbacks<'static>,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<E4>>> {
    build_initial_batched_main_domain_poly_device_impl(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        result,
        |dst, values, context| schedule_copy_small_to_device(dst, values, callbacks, context),
        context,
    )
}

fn initialize_batched_forms_impl(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge: E4,
    state: &mut GpuWhirState,
    mut build_initial_form: impl FnMut(
        &TraceHolder<BF>,
        &[E4],
        &TraceHolder<BF>,
        &[E4],
        &TraceHolder<BF>,
        &[E4],
        &mut DeviceSlice<E4>,
        &ProverContext,
    ) -> CudaResult<Vec<DeviceAllocation<E4>>>,
    context: &ProverContext,
) -> CudaResult<[Vec<E4>; 3]> {
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
    let mut challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    challenge_powers[1..].fill(E4::ZERO);
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims_len);
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims_len);
    debug_assert_eq!(setup_weights.len(), setup_polys_claims_len);

    let _weight_buffers = build_initial_form(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        context,
    )?;

    let mut serialized = context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
    let mut bf_scratch = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    serialize_whir_e4_columns(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        &mut serialized,
        stream,
    )?;
    for column in 0..EXT4_DEGREE {
        let src = &serialized[column * trace_len..(column + 1) * trace_len];
        natural_evals_to_bitreversed_coeffs(
            src,
            &mut bf_scratch,
            trace_len.trailing_zeros() as usize,
            stream,
        )?;
        let dst = &mut serialized[column * trace_len..(column + 1) * trace_len];
        memory_copy_async(dst, &bf_scratch, stream)?;
    }
    {
        let mut coeffs_matrix = DeviceMatrixMut::new(&mut serialized, trace_len);
        bit_reverse_in_place(&mut coeffs_matrix, stream)?;
    }
    deserialize_whir_e4_columns(
        &serialized,
        &mut state.sumchecked_poly_monomial_form[..trace_len],
        stream,
    )?;
    for column in 0..EXT4_DEGREE {
        let src = &serialized[column * trace_len..(column + 1) * trace_len];
        hypercube_coeffs_natural_to_natural_evals(
            src,
            &mut bf_scratch,
            trace_len.trailing_zeros() as usize,
            stream,
        )?;
        let dst = &mut serialized[column * trace_len..(column + 1) * trace_len];
        memory_copy_async(dst, &bf_scratch, stream)?;
    }
    {
        let mut evals_matrix = DeviceMatrixMut::new(&mut serialized, trace_len);
        bit_reverse_in_place(&mut evals_matrix, stream)?;
    }
    deserialize_whir_e4_columns(
        &serialized,
        &mut state.sumchecked_poly_evaluation_form[..trace_len],
        stream,
    )?;

    Ok([
        memory_weights.to_vec(),
        witness_weights.to_vec(),
        setup_weights.to_vec(),
    ])
}

fn initialize_batched_forms(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge: E4,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<[Vec<E4>; 3]> {
    initialize_batched_forms_impl(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims_len,
        wit_polys_claims_len,
        setup_polys_claims_len,
        batching_challenge,
        state,
        |memory_trace_holder,
         memory_weights,
         witness_trace_holder,
         witness_weights,
         setup_trace_holder,
         setup_weights,
         result,
         context| {
            build_initial_batched_main_domain_poly_device(
                memory_trace_holder,
                memory_weights,
                witness_trace_holder,
                witness_weights,
                setup_trace_holder,
                setup_weights,
                result,
                context,
            )
        },
        context,
    )
}

fn schedule_initialize_batched_forms(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge: E4,
    state: &mut GpuWhirState,
    callbacks: &mut Callbacks<'static>,
    context: &ProverContext,
) -> CudaResult<[Vec<E4>; 3]> {
    initialize_batched_forms_impl(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims_len,
        wit_polys_claims_len,
        setup_polys_claims_len,
        batching_challenge,
        state,
        |memory_trace_holder,
         memory_weights,
         witness_trace_holder,
         witness_weights,
         setup_trace_holder,
         setup_weights,
         result,
         context| {
            schedule_build_initial_batched_main_domain_poly_device(
                memory_trace_holder,
                memory_weights,
                witness_trace_holder,
                witness_weights,
                setup_trace_holder,
                setup_weights,
                result,
                callbacks,
                context,
            )
        },
        context,
    )
}

fn build_initial_state(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<([Vec<E4>; 3], E4)> {
    let trace_len = state.current_len;
    assert_eq!(
        original_evaluation_point.len(),
        trace_len.trailing_zeros() as usize
    );

    let batch_challenges = initialize_batched_forms(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims.len(),
        wit_polys_claims.len(),
        setup_polys_claims.len(),
        batching_challenge,
        state,
        context,
    )?;

    copy_small_to_device(
        &mut state.point_pows[..original_evaluation_point.len()],
        original_evaluation_point,
        context,
    )?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        original_evaluation_point.len(),
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;
    context.get_exec_stream().synchronize()?;

    let mut batched_claim = E4::ZERO;
    for (weights, claims) in
        batch_challenges
            .iter()
            .zip([mem_polys_claims, wit_polys_claims, setup_polys_claims])
    {
        for (weight, claim) in weights.iter().zip(claims.iter()) {
            let mut term = *claim;
            term.mul_assign(weight);
            batched_claim.add_assign(&term);
        }
    }

    Ok((batch_challenges, batched_claim))
}

fn special_three_point_eval_device(
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<(E4, E4, E4)> {
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

    let mut outputs = read_reduce_outputs(3, state, context)?;
    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    outputs[2].mul_assign_by_base(&quart);
    Ok((outputs[0], outputs[1], outputs[2]))
}

fn schedule_special_three_point_eval_device(
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E4]>> {
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

    schedule_reduce_outputs_readback(3, state, context)
}

fn fold_monomial_form_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    let half = state.current_len / 2;
    whir_fold_monomial(
        &state.sumchecked_poly_monomial_form[..state.current_len],
        &state.scalar[0],
        &mut state.monomial_buffer[..half],
        context.get_exec_stream(),
    )?;
    core::mem::swap(
        &mut state.sumchecked_poly_monomial_form,
        &mut state.monomial_buffer,
    );
    Ok(())
}

fn fold_evaluation_form_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    whir_fold_split_half_in_place(
        &mut state.sumchecked_poly_evaluation_form[..state.current_len],
        &state.scalar[0],
        context.get_exec_stream(),
    )
}

fn fold_eq_poly_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    whir_fold_split_half_in_place(
        &mut state.eq_poly[..state.current_len],
        &state.scalar[0],
        context.get_exec_stream(),
    )
}

fn evaluate_monomial_form_device(
    state: &mut GpuWhirState,
    point: E4,
    context: &ProverContext,
) -> CudaResult<E4> {
    let stream = context.get_exec_stream();
    let chunk_size = state.scratch0.len().min(state.current_len);
    let mut result = E4::ZERO;

    for chunk_start in (0..state.current_len).step_by(chunk_size) {
        let chunk_len = chunk_size.min(state.current_len - chunk_start);
        let coeffs = &state.sumchecked_poly_monomial_form[chunk_start..chunk_start + chunk_len];
        let powers = &mut state.scratch0[..chunk_len];
        let products = &mut state.scratch1[..chunk_len];
        get_powers_by_val(point, chunk_start as u32, false, powers, stream)?;
        mul(coeffs, powers, products, stream)?;
        reduce(
            ReduceOperation::Sum,
            &mut state.reduce_temp,
            &state.scratch1[..chunk_len],
            &mut state.reduce_out[0],
            stream,
        )?;
        let partial = read_reduce_outputs(1, state, context)?[0];
        result.add_assign(&partial);
    }

    Ok(result)
}

fn schedule_monomial_eval_device(
    state: &mut GpuWhirState,
    point: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<Vec<HostAllocation<[E4]>>> {
    let stream = context.get_exec_stream();
    let chunk_size = state.scratch0.len().min(state.current_len);
    let mut partials = Vec::new();

    for chunk_start in (0..state.current_len).step_by(chunk_size) {
        let chunk_len = chunk_size.min(state.current_len - chunk_start);
        let coeffs = &state.sumchecked_poly_monomial_form[chunk_start..chunk_start + chunk_len];
        let powers = &mut state.scratch0[..chunk_len];
        let products = &mut state.scratch1[..chunk_len];
        get_powers_by_ref(&point[0], chunk_start as u32, false, powers, stream)?;
        mul(coeffs, powers, products, stream)?;
        reduce(
            ReduceOperation::Sum,
            &mut state.reduce_temp,
            &state.scratch1[..chunk_len],
            &mut state.reduce_out[0],
            stream,
        )?;
        partials.push(schedule_reduce_outputs_readback(1, state, context)?);
    }

    Ok(partials)
}

fn accumulate_eq_sample_in_place_device(
    state: &mut GpuWhirState,
    point: E4,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let log_n = state.current_len.trailing_zeros() as usize;
    assert!(state.current_len <= state.scratch0.len());
    let pows = make_pows(point, log_n);
    copy_small_to_device(&mut state.point_pows[..log_n], &pows, context)?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        log_n,
        state.scratch0.as_mut_ptr(),
        state.current_len,
        context,
    )?;
    copy_scalar_to_device(challenge, state, context)?;
    mul_into_x(
        &mut state.scratch0[..state.current_len],
        &state.scalar[0],
        context.get_exec_stream(),
    )?;
    add_into_y(
        &state.scratch0[..state.current_len],
        &mut state.eq_poly[..state.current_len],
        context.get_exec_stream(),
    )
}

fn schedule_accumulate_eq_sample_in_place_device(
    state: &mut GpuWhirState,
    fill_point_pows: impl Fn(&mut [E4]) + Send + Sync + 'static,
    challenge: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<WhirHostUpload<E4>> {
    let log_n = state.current_len.trailing_zeros() as usize;
    let (point_pows_upload, point_pows_device) =
        schedule_callback_populated_upload(context, log_n, fill_point_pows)?;
    launch_build_eq_values(
        point_pows_device.as_ptr(),
        0,
        log_n,
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
    Ok(point_pows_upload)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_gpu_whir_fold_with_sources(
    memory_trace_holder: &mut TraceHolder<BF>,
    memory_base_caps_keepalive: Vec<HostAllocation<[Digest]>>,
    fill_mem_polys_claims: impl Fn(&mut [E4]) + Send + Sync + 'static,
    witness_trace_holder: &mut TraceHolder<BF>,
    witness_base_caps_keepalive: Vec<HostAllocation<[Digest]>>,
    fill_wit_polys_claims: impl Fn(&mut [E4]) + Send + Sync + 'static,
    setup_trace_holder: &mut TraceHolder<BF>,
    setup_base_caps_keepalive: Vec<HostAllocation<[Digest]>>,
    fill_setup_polys_claims: impl Fn(&mut [E4]) + Send + Sync + 'static,
    base_layer_point_len: usize,
    fill_base_layer_point: impl Fn(&mut [E4]) + Send + Sync + 'static,
    original_lde_factor: usize,
    _batching_challenge_source: impl Fn() -> E4 + Send + Sync + 'static,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    seed_source: impl Fn() -> Seed + Send + Sync + 'static,
    tree_cap_size: usize,
    trace_len_log2: usize,
    external_pow_nonces: Option<Vec<u64>>,
    context: &ProverContext,
) -> CudaResult<GpuWhirFoldScheduledExecution> {
    let trace_len = 1usize << trace_len_log2;
    assert_eq!(memory_trace_holder.log_domain_size as usize, trace_len_log2);
    assert_eq!(
        witness_trace_holder.log_domain_size as usize,
        trace_len_log2
    );
    assert_eq!(setup_trace_holder.log_domain_size as usize, trace_len_log2);
    assert_eq!(
        1usize << memory_trace_holder.log_lde_factor,
        original_lde_factor
    );
    assert_eq!(
        1usize << memory_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(
        1usize << witness_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(
        1usize << setup_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(whir_steps_schedule.len(), whir_queries_schedule.len());
    assert_eq!(whir_steps_schedule.len(), whir_pow_schedule.len());
    assert_eq!(whir_steps_schedule.len(), whir_steps_lde_factors.len() + 1);
    if let Some(external_pow_nonces) = external_pow_nonces.as_ref() {
        assert_eq!(external_pow_nonces.len(), whir_pow_schedule.len());
    }

    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let materialize_cosets_range = Range::new("gkr.whir.materialize_cosets")?;
    materialize_cosets_range.start(stream)?;
    memory_trace_holder.ensure_cosets_materialized(context)?;
    witness_trace_holder.ensure_cosets_materialized(context)?;
    setup_trace_holder.ensure_cosets_materialized(context)?;
    materialize_cosets_range.end(stream)?;
    tracing_ranges.push(materialize_cosets_range);

    let schedule_range = Range::new("gkr.whir.schedule")?;
    schedule_range.start(stream)?;

    let base_caps_keepalive = [
        memory_base_caps_keepalive,
        witness_base_caps_keepalive,
        setup_base_caps_keepalive,
    ];
    let total_sumcheck_polys = whir_steps_schedule.iter().sum::<usize>();
    let initial_query_count = whir_queries_schedule[0];
    let intermediate_query_counts = whir_queries_schedule[1..].to_vec();
    let whir_pow_rounds = whir_pow_schedule.len();
    let memory_caps_accessors = base_caps_keepalive[0]
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let witness_caps_accessors = base_caps_keepalive[1]
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let setup_caps_accessors = base_caps_keepalive[2]
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let memory_log_lde_factor = memory_trace_holder.log_lde_factor;
    let witness_log_lde_factor = witness_trace_holder.log_lde_factor;
    let setup_log_lde_factor = setup_trace_holder.log_lde_factor;
    let memory_columns_count = memory_trace_holder.columns_count;
    let witness_columns_count = witness_trace_holder.columns_count;
    let setup_columns_count = setup_trace_holder.columns_count;
    let num_intermediate_oracles = whir_steps_lde_factors.len();
    let initial_values_per_leaf = 1usize << whir_steps_schedule[0];
    let tree_cap_log2 = tree_cap_size.trailing_zeros() as usize;
    let memory_base_query_path_len = (memory_trace_holder.log_domain_size
        - memory_trace_holder.log_rows_per_leaf
        - (memory_trace_holder.log_tree_cap_size - memory_trace_holder.log_lde_factor))
        as usize;
    let witness_base_query_path_len = (witness_trace_holder.log_domain_size
        - witness_trace_holder.log_rows_per_leaf
        - (witness_trace_holder.log_tree_cap_size - witness_trace_holder.log_lde_factor))
        as usize;
    let setup_base_query_path_len = (setup_trace_holder.log_domain_size
        - setup_trace_holder.log_rows_per_leaf
        - (setup_trace_holder.log_tree_cap_size - setup_trace_holder.log_lde_factor))
        as usize;
    let mut folded_trace_len_log2 = trace_len_log2;
    let intermediate_query_specs = whir_steps_lde_factors
        .iter()
        .enumerate()
        .map(|(oracle_idx, &lde_factor)| {
            folded_trace_len_log2 -= whir_steps_schedule[oracle_idx];
            let values_per_leaf_log2 = whir_steps_schedule[oracle_idx + 1];
            let path_len = folded_trace_len_log2 + lde_factor.trailing_zeros() as usize
                - values_per_leaf_log2
                - tree_cap_log2;
            (
                whir_queries_schedule[oracle_idx + 1],
                1usize << values_per_leaf_log2,
                path_len,
            )
        })
        .collect::<Vec<_>>();
    let scheduled_proof = WhirPolyCommitProof {
        witness_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: vec![
                        Digest::default();
                        cap_digest_count_from_accessors(&witness_caps_accessors)
                    ],
                },
                _marker: PhantomData,
            },
            num_columns: witness_columns_count,
            evals: vec![E4::ZERO; witness_columns_count],
            queries: make_preallocated_base_queries(
                initial_query_count,
                witness_columns_count * initial_values_per_leaf,
                witness_base_query_path_len,
            ),
        },
        memory_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: vec![
                        Digest::default();
                        cap_digest_count_from_accessors(&memory_caps_accessors)
                    ],
                },
                _marker: PhantomData,
            },
            num_columns: memory_columns_count,
            evals: vec![E4::ZERO; memory_columns_count],
            queries: make_preallocated_base_queries(
                initial_query_count,
                memory_columns_count * initial_values_per_leaf,
                memory_base_query_path_len,
            ),
        },
        setup_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: vec![
                        Digest::default();
                        cap_digest_count_from_accessors(&setup_caps_accessors)
                    ],
                },
                _marker: PhantomData,
            },
            num_columns: setup_columns_count,
            evals: vec![E4::ZERO; setup_columns_count],
            queries: make_preallocated_base_queries(
                initial_query_count,
                setup_columns_count * initial_values_per_leaf,
                setup_base_query_path_len,
            ),
        },
        sumcheck_polys: vec![[E4::ZERO; 3]; total_sumcheck_polys],
        intermediate_whir_oracles: intermediate_query_specs
            .iter()
            .map(
                |&(count, values_per_leaf, path_len)| WhirIntermediateCommitmentAndQueries {
                    commitment: WhirCommitment {
                        cap: MerkleTreeCapVarLength {
                            cap: vec![Digest::default(); tree_cap_size],
                        },
                        _marker: PhantomData,
                    },
                    queries: make_preallocated_extension_queries(count, values_per_leaf, path_len),
                },
            )
            .collect(),
        ood_samples: vec![E4::ZERO; num_intermediate_oracles],
        pow_nonces: vec![0u64; whir_pow_rounds],
        final_monomials: vec![],
    };

    let shared_state = std::sync::Arc::new(std::sync::Mutex::new(ScheduledWhirProofState {
        proof: Some(scheduled_proof),
        #[cfg(test)]
        pre_pow_seeds: vec![Seed::default(); whir_pow_schedule.len()],
    }));
    let mut start_callbacks = Callbacks::new();
    let mut seed_host = unsafe { context.alloc_host_uninit::<Seed>() };
    let seed_accessor = seed_host.get_mut_accessor();
    start_callbacks.schedule(
        move || unsafe {
            seed_accessor.set(seed_source());
        },
        stream,
    )?;
    let mut base_layer_point_host =
        unsafe { context.alloc_host_uninit_slice(base_layer_point_len) };
    let base_layer_point_accessor = base_layer_point_host.get_mut_accessor();
    start_callbacks.schedule(
        move || unsafe {
            fill_base_layer_point(base_layer_point_accessor.get_mut());
        },
        stream,
    )?;
    start_callbacks.schedule(
        {
            let shared_state = std::sync::Arc::clone(&shared_state);
            move || {
                let mut proof_state = shared_state.lock().unwrap();
                let proof = proof_state.proof.as_mut().unwrap();
                fill_full_cap_from_accessors(
                    &mut proof.witness_commitment.commitment.cap.cap,
                    &witness_caps_accessors,
                    witness_log_lde_factor,
                );
                fill_full_cap_from_accessors(
                    &mut proof.memory_commitment.commitment.cap.cap,
                    &memory_caps_accessors,
                    memory_log_lde_factor,
                );
                fill_full_cap_from_accessors(
                    &mut proof.setup_commitment.commitment.cap.cap,
                    &setup_caps_accessors,
                    setup_log_lde_factor,
                );
                fill_wit_polys_claims(&mut proof.witness_commitment.evals);
                fill_mem_polys_claims(&mut proof.memory_commitment.evals);
                fill_setup_polys_claims(&mut proof.setup_commitment.evals);
            }
        },
        stream,
    )?;

    let initialize_state_range = Range::new("gkr.whir.initialize_state")?;
    initialize_state_range.start(stream)?;
    let mut state = GpuWhirState::new(trace_len, context)?;
    initialize_state_range.end(stream)?;
    tracing_ranges.push(initialize_state_range);

    let initialize_batched_forms_range = Range::new("gkr.whir.initialize_batched_forms")?;
    initialize_batched_forms_range.start(stream)?;
    let batch_challenges = schedule_initialize_batched_forms(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        memory_trace_holder.columns_count,
        witness_trace_holder.columns_count,
        setup_trace_holder.columns_count,
        E4::ZERO,
        &mut state,
        &mut start_callbacks,
        context,
    )?;
    initialize_batched_forms_range.end(stream)?;
    tracing_ranges.push(initialize_batched_forms_range);

    let base_eq_values_range = Range::new("gkr.whir.base_eq_values")?;
    base_eq_values_range.start(stream)?;
    memory_copy_async(
        &mut state.point_pows[..base_layer_point_len],
        &base_layer_point_host,
        stream,
    )?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        base_layer_point_len,
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;
    base_eq_values_range.end(stream)?;
    tracing_ranges.push(base_eq_values_range);

    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let mut whir_steps_schedule = whir_steps_schedule.into_iter().peekable();
    let mut whir_queries_schedule = whir_queries_schedule.into_iter();
    let mut whir_steps_lde_factors = whir_steps_lde_factors.into_iter();
    let mut whir_pow_schedule = whir_pow_schedule.into_iter().enumerate();
    let num_whir_steps = num_intermediate_oracles;
    let mut rs_oracle: Option<GpuWhirExtensionOracle> = None;

    let mut fold_eval_readbacks = Vec::new();
    let mut folding_challenges = Vec::new();
    let mut recursive_caps_keepalive = Vec::new();
    let mut ood_points = Vec::new();
    let mut ood_partial_readbacks = Vec::new();
    let mut ood_values = Vec::new();
    let mut query_index_callbacks = Vec::new();
    let mut query_indexes = Vec::new();
    let mut delinearization_challenges = Vec::new();
    let mut pow_nonces = Vec::new();
    let mut base_queries = Vec::new();
    let mut recursive_queries = Vec::new();
    let mut final_callbacks = Callbacks::new();
    let mut scheduled_sumcheck_poly_idx = 0usize;

    let mut schedule_fold_round =
        |num_folding_steps: usize, state: &mut GpuWhirState| -> CudaResult<()> {
            for _ in 0..num_folding_steps {
                let readback = schedule_special_three_point_eval_device(state, context)?;
                let readback_accessor = readback.get_accessor();
                let shared_state = std::sync::Arc::clone(&shared_state);
                let sumcheck_poly_idx = scheduled_sumcheck_poly_idx;
                scheduled_sumcheck_poly_idx += 1;
                let (challenge_upload, challenge_device) =
                    schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
                        let values = readback_accessor.get();
                        let mut f_half = values[2];
                        f_half.mul_assign_by_base(&quart);
                        let coeffs = special_lagrange_interpolate(
                            values[0],
                            values[1],
                            f_half,
                            E4::from_base(two_inv),
                        );
                        let mut proof_state = shared_state.lock().unwrap();
                        let proof = proof_state
                            .proof
                            .as_mut()
                            .expect("proof must be initialized");
                        proof.sumcheck_polys[sumcheck_poly_idx] = coeffs;
                        commit_field_els::<BF, E4>(seed_accessor.get_mut(), &coeffs);
                        dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
                    })?;
                let current_len = state.current_len;
                let next_len = current_len / 2;
                whir_fold_monomial(
                    &state.sumchecked_poly_monomial_form[..current_len],
                    &challenge_device[0],
                    &mut state.monomial_buffer[..next_len],
                    stream,
                )?;
                core::mem::swap(
                    &mut state.sumchecked_poly_monomial_form,
                    &mut state.monomial_buffer,
                );
                whir_fold_split_half_in_place(
                    &mut state.sumchecked_poly_evaluation_form[..current_len],
                    &challenge_device[0],
                    stream,
                )?;
                whir_fold_split_half_in_place(
                    &mut state.eq_poly[..current_len],
                    &challenge_device[0],
                    stream,
                )?;
                state.current_len = next_len;
                fold_eval_readbacks.push(readback);
                folding_challenges.push(challenge_upload);
            }
            Ok(())
        };

    {
        let round_range = Range::new("gkr.whir.base_round.0")?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let (pow_round_idx, pow_bits) = whir_pow_schedule.next().unwrap();
        let folds_range = Range::new("gkr.whir.base_round.0.folds")?;
        folds_range.start(stream)?;
        schedule_fold_round(num_folding_steps, &mut state)?;
        folds_range.end(stream)?;
        tracing_ranges.push(folds_range);

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let commit_next_oracle_range = Range::new("gkr.whir.base_round.0.commit_next_oracle")?;
        commit_next_oracle_range.start(stream)?;
        let oracle = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
            &state.sumchecked_poly_monomial_form[..state.current_len],
            lde_factor,
            1 << next_folding_steps,
            tree_cap_size,
            context,
        )?;
        let oracle_cap_accessors = oracle.tree_cap_accessors();
        final_callbacks.schedule(
            {
                let shared_state = std::sync::Arc::clone(&shared_state);
                move || unsafe {
                    let mut proof_state = shared_state.lock().unwrap();
                    let commitment = &mut proof_state
                        .proof
                        .as_mut()
                        .unwrap()
                        .intermediate_whir_oracles[0]
                        .commitment;
                    fill_full_cap_from_accessors(&mut commitment.cap.cap, &oracle_cap_accessors, 0);
                    add_whir_commitment_to_transcript(seed_accessor.get_mut(), commitment);
                }
            },
            stream,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        rs_oracle = Some(oracle);

        let ood_sample_range = Range::new("gkr.whir.base_round.0.ood_sample")?;
        ood_sample_range.start(stream)?;
        let (ood_point_upload, ood_point_device) =
            schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
                dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
            })?;
        let ood_partials = schedule_monomial_eval_device(&mut state, &ood_point_device, context)?;
        let mut ood_value_host = unsafe { context.alloc_host_uninit_slice(1) };
        let ood_value_accessor = ood_value_host.get_mut_accessor();
        final_callbacks.schedule(
            {
                let shared_state = std::sync::Arc::clone(&shared_state);
                let partial_accessors = ood_partials
                    .iter()
                    .map(HostAllocation::get_accessor)
                    .collect::<Vec<_>>();
                move || unsafe {
                    let mut value = E4::ZERO;
                    for partial in partial_accessors.iter() {
                        value.add_assign(&partial.get()[0]);
                    }
                    ood_value_accessor.get_mut()[0] = value;
                    commit_field_els::<BF, E4>(seed_accessor.get_mut(), &[value]);
                    shared_state
                        .lock()
                        .unwrap()
                        .proof
                        .as_mut()
                        .unwrap()
                        .ood_samples[0] = value;
                }
            },
            stream,
        )?;
        ood_partial_readbacks.push(ood_partials);
        ood_points.push(ood_point_upload);
        ood_values.push(ood_value_host);
        ood_sample_range.end(stream)?;
        tracing_ranges.push(ood_sample_range);

        let pow_and_query_indexes_range =
            Range::new("gkr.whir.base_round.0.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
        let query_domain_log2 =
            trace_len_log2 + original_lde_factor.trailing_zeros() as usize - num_folding_steps;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let query_indexes_accessor = query_indexes_host.get_mut_accessor();
        let nonce_accessor = nonce_host.get_mut_accessor();
        let mut query_index_callbacks_for_round = Callbacks::new();
        if let Some(external_nonce) = external_pow_nonces
            .as_ref()
            .map(|nonces| nonces[pow_round_idx])
        {
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        #[cfg(test)]
                        {
                            shared_state.lock().unwrap().pre_pow_seeds[pow_round_idx] =
                                *seed_accessor.get();
                        }
                        let (_, mut bit_source) = draw_query_bits_with_external_nonce(
                            seed_accessor.get_mut(),
                            num_queries * query_domain_log2,
                            pow_bits,
                            external_nonce,
                        );
                        *nonce_accessor.get_mut() = external_nonce;
                        for dst in query_indexes_accessor.get_mut().iter_mut() {
                            *dst = assemble_query_index(query_domain_log2, &mut bit_source) as u32;
                        }
                        shared_state
                            .lock()
                            .unwrap()
                            .proof
                            .as_mut()
                            .unwrap()
                            .pow_nonces[pow_round_idx] = external_nonce;
                    }
                },
                stream,
            )?;
        } else {
            #[cfg(test)]
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        shared_state.lock().unwrap().pre_pow_seeds[pow_round_idx] =
                            *seed_accessor.get();
                    }
                },
                stream,
            )?;
            search_pow_challenge(
                &mut seed_host,
                &mut nonce_host,
                pow_bits,
                None,
                &mut final_callbacks,
                context,
            )?;
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        let mut bit_source = draw_query_bits_after_verified_pow(
                            seed_accessor.get_mut(),
                            num_queries * query_domain_log2,
                        );
                        for dst in query_indexes_accessor.get_mut().iter_mut() {
                            *dst = assemble_query_index(query_domain_log2, &mut bit_source) as u32;
                        }
                        shared_state
                            .lock()
                            .unwrap()
                            .proof
                            .as_mut()
                            .unwrap()
                            .pow_nonces[pow_round_idx] = *nonce_accessor.get();
                    }
                },
                stream,
            )?;
        }
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let delinearization_eq_range = Range::new("gkr.whir.base_round.0.delinearization_eq")?;
        delinearization_eq_range.start(stream)?;
        let (delinearization_upload, delinearization_device) =
            schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
                dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
            })?;
        let ood_point_accessor = ood_points.last().unwrap().host.get_accessor();
        let eq_upload = schedule_accumulate_eq_sample_in_place_device(
            &mut state,
            move |dst| unsafe {
                let mut value = ood_point_accessor.get()[0];
                for dst_el in dst.iter_mut() {
                    *dst_el = value;
                    value.square();
                }
            },
            &delinearization_device,
            context,
        )?;
        ood_points.push(eq_upload);
        delinearization_eq_range.end(stream)?;
        tracing_ranges.push(delinearization_eq_range);

        let queries_range = Range::new("gkr.whir.base_round.0.queries")?;
        queries_range.start(stream)?;
        let mut round_base_queries = [Vec::new(), Vec::new(), Vec::new()];
        for query_idx in 0..num_queries {
            let mut memory_query_index_host = unsafe { context.alloc_host_uninit_slice(1) };
            let mut witness_query_index_host = unsafe { context.alloc_host_uninit_slice(1) };
            let mut setup_query_index_host = unsafe { context.alloc_host_uninit_slice(1) };
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            for single_accessor in [
                memory_query_index_host.get_mut_accessor(),
                witness_query_index_host.get_mut_accessor(),
                setup_query_index_host.get_mut_accessor(),
            ] {
                let query_indexes_accessor = query_indexes_accessor;
                copy_callbacks.schedule(
                    move || unsafe {
                        single_accessor.get_mut()[0] = query_indexes_accessor.get()[query_idx];
                    },
                    stream,
                )?;
            }

            let memory_query = schedule_unknown_coset_base_field_query(
                memory_trace_holder,
                memory_query_index_host,
                context,
            )?;
            let witness_query = schedule_unknown_coset_base_field_query(
                witness_trace_holder,
                witness_query_index_host,
                context,
            )?;
            let setup_query = schedule_unknown_coset_base_field_query(
                setup_trace_holder,
                setup_query_index_host,
                context,
            )?;

            let memory_query_index_accessor = memory_query.query_index.get_accessor();
            let memory_leaf_accessors = memory_query
                .value_leafs
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let memory_path_accessors = memory_query
                .path_merkle_paths
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let witness_query_index_accessor = witness_query.query_index.get_accessor();
            let witness_leaf_accessors = witness_query
                .value_leafs
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let witness_path_accessors = witness_query
                .path_merkle_paths
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let setup_query_index_accessor = setup_query.query_index.get_accessor();
            let setup_leaf_accessors = setup_query
                .value_leafs
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let setup_path_accessors = setup_query
                .path_merkle_paths
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();

            let query_indexes_accessor = query_indexes_host.get_accessor();
            let eq_upload = schedule_accumulate_eq_sample_in_place_device(
                &mut state,
                move |dst| unsafe {
                    let point = E4::from_base(
                        query_domain_generator.pow(query_indexes_accessor.get()[query_idx]),
                    );
                    let mut value = point;
                    for dst_el in dst.iter_mut() {
                        *dst_el = value;
                        value.square();
                    }
                },
                &delinearization_device,
                context,
            )?;
            ood_points.push(eq_upload);

            final_callbacks.extend(copy_callbacks);
            final_callbacks.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    let memory_values_per_leaf = memory_query.values_per_leaf;
                    let memory_columns_count = memory_query.columns_count;
                    let memory_coset_tree_size = memory_query.coset_tree_size;
                    let memory_log_lde_factor = memory_query.log_lde_factor;
                    let witness_values_per_leaf = witness_query.values_per_leaf;
                    let witness_columns_count = witness_query.columns_count;
                    let witness_coset_tree_size = witness_query.coset_tree_size;
                    let witness_log_lde_factor = witness_query.log_lde_factor;
                    let setup_values_per_leaf = setup_query.values_per_leaf;
                    let setup_columns_count = setup_query.columns_count;
                    let setup_coset_tree_size = setup_query.coset_tree_size;
                    let setup_log_lde_factor = setup_query.log_lde_factor;
                    move || {
                        let mut proof_state = shared_state.lock().unwrap();
                        let proof = proof_state.proof.as_mut().unwrap();
                        let memory_index = unsafe { memory_query_index_accessor.get()[0] as usize };
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.memory_commitment.queries[query_idx],
                            memory_index,
                            memory_coset_tree_size,
                            memory_log_lde_factor,
                            memory_values_per_leaf,
                            memory_columns_count,
                            &memory_leaf_accessors,
                            &memory_path_accessors,
                        );
                        let witness_index =
                            unsafe { witness_query_index_accessor.get()[0] as usize };
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.witness_commitment.queries[query_idx],
                            witness_index,
                            witness_coset_tree_size,
                            witness_log_lde_factor,
                            witness_values_per_leaf,
                            witness_columns_count,
                            &witness_leaf_accessors,
                            &witness_path_accessors,
                        );
                        let setup_index = unsafe { setup_query_index_accessor.get()[0] as usize };
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.setup_commitment.queries[query_idx],
                            setup_index,
                            setup_coset_tree_size,
                            setup_log_lde_factor,
                            setup_values_per_leaf,
                            setup_columns_count,
                            &setup_leaf_accessors,
                            &setup_path_accessors,
                        );
                    }
                },
                stream,
            )?;

            round_base_queries[0].push(memory_query);
            round_base_queries[1].push(witness_query);
            round_base_queries[2].push(setup_query);
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        base_queries.push(round_base_queries);
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        delinearization_challenges.push(delinearization_upload);
        pow_nonces.push(nonce_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    let num_internal_whir_steps = num_whir_steps.saturating_sub(1);
    for internal_round_idx in 0..num_internal_whir_steps {
        let round_name = format!("gkr.whir.internal_round.{}", internal_round_idx);
        let round_range = Range::new(&*round_name)?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let (pow_round_idx, pow_bits) = whir_pow_schedule.next().unwrap();
        let folds_name = format!("{round_name}.folds");
        let folds_range = Range::new(&*folds_name)?;
        folds_range.start(stream)?;
        schedule_fold_round(num_folding_steps, &mut state)?;
        folds_range.end(stream)?;
        tracing_ranges.push(folds_range);

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let commit_name = format!("{round_name}.commit_next_oracle");
        let commit_next_oracle_range = Range::new(&*commit_name)?;
        commit_next_oracle_range.start(stream)?;
        let next_oracle = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
            &state.sumchecked_poly_monomial_form[..state.current_len],
            lde_factor,
            1 << next_folding_steps,
            tree_cap_size,
            context,
        )?;
        let next_oracle_cap_accessors = next_oracle.tree_cap_accessors();
        final_callbacks.schedule(
            {
                let shared_state = std::sync::Arc::clone(&shared_state);
                move || {
                    let mut proof_state = shared_state.lock().unwrap();
                    let commitment = &mut proof_state
                        .proof
                        .as_mut()
                        .unwrap()
                        .intermediate_whir_oracles[internal_round_idx + 1]
                        .commitment;
                    fill_full_cap_from_accessors(
                        &mut commitment.cap.cap,
                        &next_oracle_cap_accessors,
                        0,
                    );
                }
            },
            stream,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        let mut oracle_to_query = rs_oracle.replace(next_oracle).unwrap();

        let ood_sample_name = format!("{round_name}.ood_sample");
        let ood_sample_range = Range::new(&*ood_sample_name)?;
        ood_sample_range.start(stream)?;
        let (ood_point_upload, ood_point_device) =
            schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| {
                dst[0] = E4::from_base(BF::from_u32_unchecked(42));
            })?;
        let ood_partials = schedule_monomial_eval_device(&mut state, &ood_point_device, context)?;
        let mut ood_value_host = unsafe { context.alloc_host_uninit_slice(1) };
        let ood_value_accessor = ood_value_host.get_mut_accessor();
        final_callbacks.schedule(
            {
                let shared_state = std::sync::Arc::clone(&shared_state);
                let partial_accessors = ood_partials
                    .iter()
                    .map(HostAllocation::get_accessor)
                    .collect::<Vec<_>>();
                move || unsafe {
                    let mut value = E4::ZERO;
                    for partial in partial_accessors.iter() {
                        value.add_assign(&partial.get()[0]);
                    }
                    ood_value_accessor.get_mut()[0] = value;
                    shared_state
                        .lock()
                        .unwrap()
                        .proof
                        .as_mut()
                        .unwrap()
                        .ood_samples[internal_round_idx + 1] = value;
                }
            },
            stream,
        )?;
        ood_partial_readbacks.push(ood_partials);
        ood_points.push(ood_point_upload);
        ood_values.push(ood_value_host);
        ood_sample_range.end(stream)?;
        tracing_ranges.push(ood_sample_range);

        let pow_and_query_indexes_name = format!("{round_name}.pow_and_query_indexes");
        let pow_and_query_indexes_range = Range::new(&*pow_and_query_indexes_name)?;
        pow_and_query_indexes_range.start(stream)?;
        let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let query_indexes_accessor = query_indexes_host.get_mut_accessor();
        let nonce_accessor = nonce_host.get_mut_accessor();
        let mut query_index_callbacks_for_round = Callbacks::new();
        if let Some(external_nonce) = external_pow_nonces
            .as_ref()
            .map(|nonces| nonces[pow_round_idx])
        {
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        #[cfg(test)]
                        {
                            shared_state.lock().unwrap().pre_pow_seeds[pow_round_idx] =
                                *seed_accessor.get();
                        }
                        let (_, mut bit_source) = draw_query_bits_with_external_nonce(
                            seed_accessor.get_mut(),
                            num_queries * query_domain_log2,
                            pow_bits,
                            external_nonce,
                        );
                        *nonce_accessor.get_mut() = external_nonce;
                        for dst in query_indexes_accessor.get_mut().iter_mut() {
                            *dst = assemble_query_index(query_domain_log2, &mut bit_source) as u32;
                        }
                        shared_state
                            .lock()
                            .unwrap()
                            .proof
                            .as_mut()
                            .unwrap()
                            .pow_nonces[pow_round_idx] = external_nonce;
                    }
                },
                stream,
            )?;
        } else {
            #[cfg(test)]
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        shared_state.lock().unwrap().pre_pow_seeds[pow_round_idx] =
                            *seed_accessor.get();
                    }
                },
                stream,
            )?;
            search_pow_challenge(
                &mut seed_host,
                &mut nonce_host,
                pow_bits,
                None,
                &mut final_callbacks,
                context,
            )?;
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        let mut bit_source = draw_query_bits_after_verified_pow(
                            seed_accessor.get_mut(),
                            num_queries * query_domain_log2,
                        );
                        for dst in query_indexes_accessor.get_mut().iter_mut() {
                            *dst = assemble_query_index(query_domain_log2, &mut bit_source) as u32;
                        }
                        shared_state
                            .lock()
                            .unwrap()
                            .proof
                            .as_mut()
                            .unwrap()
                            .pow_nonces[pow_round_idx] = *nonce_accessor.get();
                    }
                },
                stream,
            )?;
        }
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let delinearization_eq_name = format!("{round_name}.delinearization_eq");
        let delinearization_eq_range = Range::new(&*delinearization_eq_name)?;
        delinearization_eq_range.start(stream)?;
        let (delinearization_upload, delinearization_device) =
            schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
                dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
            })?;
        let ood_point_accessor = ood_points.last().unwrap().host.get_accessor();
        let eq_upload = schedule_accumulate_eq_sample_in_place_device(
            &mut state,
            move |dst| unsafe {
                let mut value = ood_point_accessor.get()[0];
                for dst_el in dst.iter_mut() {
                    *dst_el = value;
                    value.square();
                }
            },
            &delinearization_device,
            context,
        )?;
        ood_points.push(eq_upload);
        delinearization_eq_range.end(stream)?;
        tracing_ranges.push(delinearization_eq_range);

        let queries_name = format!("{round_name}.queries");
        let queries_range = Range::new(&*queries_name)?;
        queries_range.start(stream)?;
        let mut round_recursive_queries = Vec::new();
        for query_idx in 0..num_queries {
            let mut single_query_index = unsafe { context.alloc_host_uninit_slice(1) };
            let single_query_index_accessor = single_query_index.get_mut_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            copy_callbacks.schedule(
                move || unsafe {
                    single_query_index_accessor.get_mut()[0] =
                        query_indexes_accessor.get()[query_idx];
                },
                stream,
            )?;
            let query = oracle_to_query
                .schedule_query_for_folded_index_from_host(single_query_index, context)?;
            let query_leafs_accessor = query.leafs_accessor();
            let query_paths_accessor = query.merkle_paths_accessor();
            let query_values_per_leaf = query.values_per_leaf();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let eq_upload = schedule_accumulate_eq_sample_in_place_device(
                &mut state,
                move |dst| unsafe {
                    let point = E4::from_base(
                        query_domain_generator.pow(query_indexes_accessor.get()[query_idx]),
                    );
                    let mut value = point;
                    for dst_el in dst.iter_mut() {
                        *dst_el = value;
                        value.square();
                    }
                },
                &delinearization_device,
                context,
            )?;
            ood_points.push(eq_upload);

            final_callbacks.extend(copy_callbacks);
            final_callbacks.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    let query_indexes_accessor = query_indexes_host.get_accessor();
                    move || {
                        let index = unsafe { query_indexes_accessor.get()[query_idx] as usize };
                        fill_extension_query_from_accessors(
                            &mut shared_state
                                .lock()
                                .unwrap()
                                .proof
                                .as_mut()
                                .unwrap()
                                .intermediate_whir_oracles[internal_round_idx]
                                .queries[query_idx],
                            index,
                            query_values_per_leaf,
                            query_leafs_accessor,
                            query_paths_accessor,
                        );
                    }
                },
                stream,
            )?;
            round_recursive_queries.push(query);
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        recursive_caps_keepalive.push(oracle_to_query.into_host_tree_caps());
        recursive_queries.push(round_recursive_queries);
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        delinearization_challenges.push(delinearization_upload);
        pow_nonces.push(nonce_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    {
        let round_range = Range::new("gkr.whir.final_round")?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let (pow_round_idx, pow_bits) = whir_pow_schedule.next().unwrap();
        let folds_range = Range::new("gkr.whir.final_round.folds")?;
        folds_range.start(stream)?;
        schedule_fold_round(num_folding_steps, &mut state)?;
        folds_range.end(stream)?;
        tracing_ranges.push(folds_range);

        let mut oracle_to_query = rs_oracle.take().unwrap();
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let query_domain_size = 1u64 << query_domain_log2;
        let pow_and_query_indexes_range = Range::new("gkr.whir.final_round.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
        let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let query_indexes_accessor = query_indexes_host.get_mut_accessor();
        let nonce_accessor = nonce_host.get_mut_accessor();
        let mut query_index_callbacks_for_round = Callbacks::new();
        if let Some(external_nonce) = external_pow_nonces
            .as_ref()
            .map(|nonces| nonces[pow_round_idx])
        {
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        #[cfg(test)]
                        {
                            shared_state.lock().unwrap().pre_pow_seeds[pow_round_idx] =
                                *seed_accessor.get();
                        }
                        let (_, mut bit_source) = draw_query_bits_with_external_nonce(
                            seed_accessor.get_mut(),
                            num_queries * query_domain_log2,
                            pow_bits,
                            external_nonce,
                        );
                        *nonce_accessor.get_mut() = external_nonce;
                        for dst in query_indexes_accessor.get_mut().iter_mut() {
                            *dst = assemble_query_index(query_domain_log2, &mut bit_source) as u32;
                        }
                        shared_state
                            .lock()
                            .unwrap()
                            .proof
                            .as_mut()
                            .unwrap()
                            .pow_nonces[pow_round_idx] = external_nonce;
                    }
                },
                stream,
            )?;
        } else {
            #[cfg(test)]
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        shared_state.lock().unwrap().pre_pow_seeds[pow_round_idx] =
                            *seed_accessor.get();
                    }
                },
                stream,
            )?;
            search_pow_challenge(
                &mut seed_host,
                &mut nonce_host,
                pow_bits,
                None,
                &mut final_callbacks,
                context,
            )?;
            query_index_callbacks_for_round.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    move || unsafe {
                        let mut bit_source = draw_query_bits_after_verified_pow(
                            seed_accessor.get_mut(),
                            num_queries * query_domain_log2,
                        );
                        for dst in query_indexes_accessor.get_mut().iter_mut() {
                            *dst = assemble_query_index(query_domain_log2, &mut bit_source) as u32;
                        }
                        shared_state
                            .lock()
                            .unwrap()
                            .proof
                            .as_mut()
                            .unwrap()
                            .pow_nonces[pow_round_idx] = *nonce_accessor.get();
                    }
                },
                stream,
            )?;
        }
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);
        let queries_range = Range::new("gkr.whir.final_round.queries")?;
        queries_range.start(stream)?;
        let mut round_recursive_queries = Vec::new();
        let final_oracle_index = num_whir_steps.saturating_sub(1);
        for query_idx in 0..num_queries {
            let mut single_query_index = unsafe { context.alloc_host_uninit_slice(1) };
            let single_query_index_accessor = single_query_index.get_mut_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            copy_callbacks.schedule(
                move || unsafe {
                    single_query_index_accessor.get_mut()[0] =
                        query_indexes_accessor.get()[query_idx];
                },
                stream,
            )?;
            let query = oracle_to_query
                .schedule_query_for_folded_index_from_host(single_query_index, context)?;
            let query_leafs_accessor = query.leafs_accessor();
            let query_paths_accessor = query.merkle_paths_accessor();
            let query_values_per_leaf = query.values_per_leaf();
            final_callbacks.extend(copy_callbacks);
            final_callbacks.schedule(
                {
                    let shared_state = std::sync::Arc::clone(&shared_state);
                    let query_indexes_accessor = query_indexes_host.get_accessor();
                    move || {
                        let index = unsafe { query_indexes_accessor.get()[query_idx] as usize };
                        fill_extension_query_from_accessors(
                            &mut shared_state
                                .lock()
                                .unwrap()
                                .proof
                                .as_mut()
                                .unwrap()
                                .intermediate_whir_oracles[final_oracle_index]
                                .queries[query_idx],
                            index,
                            query_values_per_leaf,
                            query_leafs_accessor,
                            query_paths_accessor,
                        );
                    }
                },
                stream,
            )?;
            round_recursive_queries.push(query);
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        recursive_caps_keepalive.push(oracle_to_query.into_host_tree_caps());
        recursive_queries.push(round_recursive_queries);
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        pow_nonces.push(nonce_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuWhirFoldScheduledExecution {
        tracing_ranges,
        start_callbacks,
        seed_host,
        base_layer_point_host,
        base_caps_keepalive,
        fold_eval_readbacks,
        folding_challenges,
        recursive_caps_keepalive,
        ood_points,
        ood_partial_readbacks,
        ood_values,
        query_index_callbacks,
        query_indexes,
        delinearization_challenges,
        pow_nonces,
        base_queries,
        recursive_queries,
        final_callbacks,
        shared_state,
    })
}

pub(crate) fn gpu_whir_fold_supported_path_with_external_pow(
    memory_trace_holder: &mut TraceHolder<BF>,
    mem_polys_claims: Vec<E4>,
    witness_trace_holder: &mut TraceHolder<BF>,
    wit_polys_claims: Vec<E4>,
    setup_trace_holder: &mut TraceHolder<BF>,
    setup_polys_claims: Vec<E4>,
    original_evaluation_point: Vec<E4>,
    original_lde_factor: usize,
    batching_challenge: E4,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    mut transcript_seed: Seed,
    tree_cap_size: usize,
    trace_len_log2: usize,
    external_pow_nonces: Option<Vec<u64>>,
    _worker: &Worker,
    context: &ProverContext,
) -> CudaResult<WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>> {
    let memory_base_caps_keepalive = memory_trace_holder.take_tree_caps_host();
    let witness_base_caps_keepalive = witness_trace_holder.take_tree_caps_host();
    let setup_base_caps_keepalive = setup_trace_holder.take_tree_caps_host();
    let mem_polys_claims_for_source = mem_polys_claims.clone();
    let wit_polys_claims_for_source = wit_polys_claims.clone();
    let setup_polys_claims_for_source = setup_polys_claims.clone();
    let original_evaluation_point_len = original_evaluation_point.len();

    schedule_gpu_whir_fold_with_sources(
        memory_trace_holder,
        memory_base_caps_keepalive,
        move |dst| dst.copy_from_slice(&mem_polys_claims_for_source),
        witness_trace_holder,
        witness_base_caps_keepalive,
        move |dst| dst.copy_from_slice(&wit_polys_claims_for_source),
        setup_trace_holder,
        setup_base_caps_keepalive,
        move |dst| dst.copy_from_slice(&setup_polys_claims_for_source),
        original_evaluation_point_len,
        move |dst| dst.copy_from_slice(&original_evaluation_point),
        original_lde_factor,
        move || batching_challenge,
        whir_steps_schedule,
        whir_queries_schedule,
        whir_steps_lde_factors,
        whir_pow_schedule,
        move || transcript_seed.clone(),
        tree_cap_size,
        trace_len_log2,
        external_pow_nonces,
        context,
    )?
    .wait(context)
}

pub(crate) fn gpu_whir_fold_supported_path(
    memory_trace_holder: &mut TraceHolder<BF>,
    mem_polys_claims: Vec<E4>,
    witness_trace_holder: &mut TraceHolder<BF>,
    wit_polys_claims: Vec<E4>,
    setup_trace_holder: &mut TraceHolder<BF>,
    setup_polys_claims: Vec<E4>,
    original_evaluation_point: Vec<E4>,
    original_lde_factor: usize,
    batching_challenge: E4,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    transcript_seed: Seed,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
    context: &ProverContext,
) -> CudaResult<WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>> {
    gpu_whir_fold_supported_path_with_external_pow(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        original_lde_factor,
        batching_challenge,
        whir_steps_schedule,
        whir_queries_schedule,
        whir_steps_lde_factors,
        whir_pow_schedule,
        transcript_seed,
        tree_cap_size,
        trace_len_log2,
        None,
        worker,
        context,
    )
}

#[cfg(test)]
pub(crate) fn debug_build_initial_state_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<([Vec<E4>; 3], E4, Vec<E4>, Vec<E4>, Vec<E4>)> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let (batch_challenges, claim) = build_initial_state(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        &mut state,
        context,
    )?;

    Ok((
        batch_challenges,
        claim,
        copy_back(&state.sumchecked_poly_monomial_form[..trace_len], context),
        copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context),
        copy_back(&state.eq_poly[..trace_len], context),
    ))
}

#[cfg(test)]
pub(crate) fn debug_build_initial_batched_main_domain_poly_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn copy_back_bf(values: &DeviceSlice<BF>, context: &ProverContext) -> Vec<BF> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let mut challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    challenge_powers[1..].fill(E4::ZERO);
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims.len());
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims.len());
    debug_assert_eq!(setup_weights.len(), setup_polys_claims.len());

    let _weight_buffers = build_initial_batched_main_domain_poly_device(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        context,
    )?;
    Ok(copy_back(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        context,
    ))
}

#[cfg(test)]
pub(crate) fn debug_build_initial_state_snapshots_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<(Vec<E4>, Vec<E4>)> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let batch_challenges = initialize_batched_forms(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims.len(),
        wit_polys_claims.len(),
        setup_polys_claims.len(),
        batching_challenge,
        &mut state,
        context,
    )?;
    let pre_eq = copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context);

    copy_small_to_device(
        &mut state.point_pows[..original_evaluation_point.len()],
        original_evaluation_point,
        context,
    )?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        original_evaluation_point.len(),
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;
    context.get_exec_stream().synchronize()?;

    let mut batched_claim = E4::ZERO;
    for (weights, claims) in
        batch_challenges
            .iter()
            .zip([mem_polys_claims, wit_polys_claims, setup_polys_claims])
    {
        for (weight, claim) in weights.iter().zip(claims.iter()) {
            let mut term = *claim;
            term.mul_assign(weight);
            batched_claim.add_assign(&term);
        }
    }
    debug_assert!(!batched_claim.is_zero() || batched_claim == E4::ZERO);

    let post_eq = copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context);
    Ok((pre_eq, post_eq))
}

#[cfg(test)]
pub(crate) struct DebugInitialWhirRoundCheckpoint {
    pub(crate) sumcheck_polys: Vec<[E4; 3]>,
    pub(crate) folding_challenges: Vec<E4>,
    pub(crate) folded_monomial_form: Vec<E4>,
    pub(crate) recursive_cap: MerkleTreeCapVarLength,
    pub(crate) ood_point: E4,
    pub(crate) ood_value: E4,
    pub(crate) transcript_seed: Seed,
}

#[cfg(test)]
pub(crate) struct DebugWhirInitialFoldState {
    state: GpuWhirState,
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_initial_round_checkpoint_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    original_lde_factor: usize,
    batching_challenge: E4,
    num_initial_folding_rounds: usize,
    first_recursive_lde_factor: usize,
    next_folding_steps: usize,
    tree_cap_size: usize,
    transcript_seed: Seed,
    context: &ProverContext,
) -> CudaResult<DebugInitialWhirRoundCheckpoint> {
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    build_initial_state(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        &mut state,
        context,
    )?;

    let mut transcript_seed = transcript_seed;
    let mut sumcheck_polys = Vec::with_capacity(num_initial_folding_rounds);
    let mut folding_challenges = Vec::with_capacity(num_initial_folding_rounds);
    for _ in 0..num_initial_folding_rounds {
        let (f0, f1, f_half) = special_three_point_eval_device(&mut state, context)?;
        let coeffs = special_lagrange_interpolate(f0, f1, f_half, E4::from_base(two_inv));
        sumcheck_polys.push(coeffs);
        commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
        let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        folding_challenges.push(folding_challenge);
        fold_monomial_form_in_place_device(&mut state, folding_challenge, context)?;
        fold_evaluation_form_in_place_device(&mut state, folding_challenge, context)?;
        fold_eq_poly_in_place_device(&mut state, folding_challenge, context)?;
        state.current_len /= 2;
    }

    let mut folded_monomial_form_host = alloc_static_pinned_box_uninit(state.current_len)?;
    memory_copy_async(
        &mut folded_monomial_form_host,
        &state.sumchecked_poly_monomial_form[..state.current_len],
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    let folded_monomial_form = folded_monomial_form_host.to_vec();

    let oracle = GpuWhirExtensionOracle::from_device_monomial_coeffs(
        &state.sumchecked_poly_monomial_form[..state.current_len],
        first_recursive_lde_factor,
        1 << next_folding_steps,
        tree_cap_size,
        context,
    )?;
    let recursive_cap = oracle.get_tree_cap();
    add_whir_commitment_to_transcript(
        &mut transcript_seed,
        &WhirCommitment::<BF, DefaultTreeConstructor> {
            cap: recursive_cap.clone(),
            _marker: PhantomData,
        },
    );

    let _rs_domain_log2 = trace_len.trailing_zeros() as usize
        + original_lde_factor.trailing_zeros() as usize
        - num_initial_folding_rounds;
    let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
    let ood_value = evaluate_monomial_form_device(&mut state, ood_point, context)?;
    commit_field_els::<BF, E4>(&mut transcript_seed, &[ood_value]);

    Ok(DebugInitialWhirRoundCheckpoint {
        sumcheck_polys,
        folding_challenges,
        folded_monomial_form,
        recursive_cap,
        ood_point,
        ood_value,
        transcript_seed,
    })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_build_initial_fold_state_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<DebugWhirInitialFoldState> {
    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    build_initial_state(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        &mut state,
        context,
    )?;
    Ok(DebugWhirInitialFoldState { state })
}

#[cfg(test)]
pub(crate) fn debug_apply_initial_fold_challenge_for_test(
    debug_state: &mut DebugWhirInitialFoldState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    fold_monomial_form_in_place_device(&mut debug_state.state, challenge, context)?;
    fold_evaluation_form_in_place_device(&mut debug_state.state, challenge, context)?;
    fold_eq_poly_in_place_device(&mut debug_state.state, challenge, context)?;
    debug_state.state.current_len /= 2;

    let mut host = alloc_static_pinned_box_uninit(debug_state.state.current_len)?;
    memory_copy_async(
        &mut host,
        &debug_state.state.sumchecked_poly_monomial_form[..debug_state.state.current_len],
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    Ok(host.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::alloc::Global;

    use era_cudart::memory::memory_copy_async;
    use fft::{bitreverse_enumeration_inplace, Twiddles};
    use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
    use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
    use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
    use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
    use serial_test::serial;

    use crate::allocator::tracker::AllocationPlacement;
    use crate::prover::test_utils::make_test_context;
    use crate::prover::trace_holder::TreesCacheMode;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::from_u32_unchecked(seed + 1),
            BF::from_u32_unchecked(seed + 2),
            BF::from_u32_unchecked(seed + 3),
            BF::from_u32_unchecked(seed + 4),
        ])
    }

    fn alloc_and_copy(values: &[E4], context: &ProverContext) -> DeviceAllocation<E4> {
        let mut device = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
        device
    }

    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn copy_back_bf(values: &DeviceSlice<BF>, context: &ProverContext) -> Vec<BF> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn fold_monomial_form_for_test(input: &mut Vec<E4>, challenge: E4) {
        let mut buffer = Vec::with_capacity(input.len() / 2);
        for [c0, c1] in input.as_chunks::<2>().0.iter() {
            let mut result = *c1;
            result.mul_assign(&challenge);
            result.add_assign(c0);
            buffer.push(result);
        }
        *input = buffer;
    }

    fn fold_evaluation_form_for_test(input: &mut Vec<E4>, challenge: E4) {
        let half_len = input.len() / 2;
        let (first_half, second_half) = input.split_at_mut(half_len);
        for (a, b) in first_half.iter_mut().zip(second_half.iter()) {
            let mut t = *b;
            t.sub_assign(a);
            t.mul_assign(&challenge);
            a.add_assign(&t);
        }
        input.truncate(half_len);
    }

    fn special_three_point_eval_for_test(a: &[E4], b: &[E4]) -> (E4, E4, E4) {
        let half = a.len() / 2;
        let quart = BF::from_u32_unchecked(4).inverse().unwrap();
        let (a_low, a_high) = a.split_at(half);
        let (b_low, b_high) = b.split_at(half);
        let mut f0 = E4::ZERO;
        let mut f1 = E4::ZERO;
        let mut f_half = E4::ZERO;
        for ((a0, a1), (b0, b1)) in a_low
            .iter()
            .zip(a_high.iter())
            .zip(b_low.iter().zip(b_high.iter()))
        {
            let mut t0 = *a0;
            t0.mul_assign(b0);
            f0.add_assign(&t0);

            let mut t1 = *a1;
            t1.mul_assign(b1);
            f1.add_assign(&t1);

            let mut t_half = *a0;
            t_half.add_assign(a1);
            let mut eq_half = *b0;
            eq_half.add_assign(b1);
            t_half.mul_assign(&eq_half);
            f_half.add_assign(&t_half);
        }
        f_half.mul_assign_by_base(&quart);
        (f0, f1, f_half)
    }

    fn evaluate_monomial_form_for_test(coeffs: &[E4], point: E4) -> E4 {
        let mut result = E4::ZERO;
        let mut current = E4::ONE;
        for coeff in coeffs.iter() {
            let mut term = *coeff;
            term.mul_assign(&current);
            result.add_assign(&term);
            current.mul_assign(&point);
        }
        result
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_special_three_point_eval_matches_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let evals = (0..8)
            .map(|i| sample_ext(10 * i as u32))
            .collect::<Vec<_>>();
        let eq = (0..8)
            .map(|i| sample_ext(100 + 10 * i as u32))
            .collect::<Vec<_>>();
        state.current_len = evals.len();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let actual = special_three_point_eval_device(&mut state, &context).unwrap();
        let expected = special_three_point_eval_for_test(&evals, &eq);

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_special_three_point_eval_large_matches_cpu() {
        let n = 1 << 16;
        let context = make_test_context(1024, 64);
        let mut state = GpuWhirState::new(n, &context).unwrap();
        let evals = (0..n)
            .map(|i| sample_ext(((i * 17) % 1000) as u32))
            .collect::<Vec<_>>();
        let eq = (0..n)
            .map(|i| sample_ext(2000 + ((i * 29) % 1000) as u32))
            .collect::<Vec<_>>();
        state.current_len = n;
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let actual = special_three_point_eval_device(&mut state, &context).unwrap();
        let expected = special_three_point_eval_for_test(&evals, &eq);

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn scheduled_whir_special_three_point_eval_matches_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let evals = (0..8)
            .map(|i| sample_ext(10 * i as u32))
            .collect::<Vec<_>>();
        let eq = (0..8)
            .map(|i| sample_ext(100 + 10 * i as u32))
            .collect::<Vec<_>>();
        state.current_len = evals.len();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let scheduled = schedule_special_three_point_eval_device(&mut state, &context).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let mut actual = unsafe { scheduled.get_accessor().get() }.to_vec();
        actual[2].mul_assign_by_base(&BF::from_u32_unchecked(4).inverse().unwrap());

        let expected = special_three_point_eval_for_test(&evals, &eq);
        assert_eq!(actual.as_slice(), &[expected.0, expected.1, expected.2]);
    }

    fn make_trace_holder(columns: &[Vec<BF>], context: &ProverContext) -> TraceHolder<BF> {
        assert!(!columns.is_empty());
        let rows = columns[0].len();
        let mut trace_holder = TraceHolder::new(
            rows.trailing_zeros(),
            0,
            0,
            0,
            columns.len(),
            TreesCacheMode::CacheNone,
            context,
        )
        .unwrap();
        let flat = columns
            .iter()
            .flat_map(|column| column.iter().copied())
            .collect::<Vec<_>>();
        memory_copy_async(
            trace_holder.get_uninit_hypercube_evals_mut(),
            &flat,
            context.get_exec_stream(),
        )
        .unwrap();
        trace_holder
            .materialize_cosets_from_owned_hypercube(context)
            .unwrap();
        trace_holder
    }

    fn make_lde_trace_holder(
        columns: &[Vec<BF>],
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        context: &ProverContext,
    ) -> TraceHolder<BF> {
        assert!(!columns.is_empty());
        let rows = columns[0].len();
        let mut trace_holder = TraceHolder::new(
            rows.trailing_zeros(),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns.len(),
            TreesCacheMode::CacheFull,
            context,
        )
        .unwrap();
        let flat = columns
            .iter()
            .flat_map(|column| column.iter().copied())
            .collect::<Vec<_>>();
        memory_copy_async(
            trace_holder.get_uninit_hypercube_evals_mut(),
            &flat,
            context.get_exec_stream(),
        )
        .unwrap();
        trace_holder
            .materialize_cosets_from_owned_hypercube(context)
            .unwrap();
        trace_holder.commit_all(context).unwrap();
        trace_holder
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_fold_helpers_match_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let challenge = sample_ext(777);

        let monomial = (0..8)
            .map(|i| sample_ext(20 * i as u32))
            .collect::<Vec<_>>();
        let evals = (0..8)
            .map(|i| sample_ext(200 + 20 * i as u32))
            .collect::<Vec<_>>();
        let eq = (0..8)
            .map(|i| sample_ext(400 + 20 * i as u32))
            .collect::<Vec<_>>();

        state.current_len = 8;
        state.sumchecked_poly_monomial_form = alloc_and_copy(&monomial, &context);
        state.monomial_buffer = context.alloc(4, AllocationPlacement::BestFit).unwrap();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let mut expected_monomial = monomial.clone();
        let mut expected_evals = evals.clone();
        let mut expected_eq = eq.clone();

        fold_monomial_form_for_test(&mut expected_monomial, challenge);
        fold_evaluation_form_for_test(&mut expected_evals, challenge);
        fold_evaluation_form_for_test(&mut expected_eq, challenge);

        fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_evaluation_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_eq_poly_in_place_device(&mut state, challenge, &context).unwrap();
        state.current_len = 4;

        assert_eq!(
            copy_back(
                &state.sumchecked_poly_monomial_form[..state.current_len],
                &context
            ),
            expected_monomial
        );
        assert_eq!(
            copy_back(
                &state.sumchecked_poly_evaluation_form[..state.current_len],
                &context
            ),
            expected_evals
        );
        assert_eq!(
            copy_back(&state.eq_poly[..state.current_len], &context),
            expected_eq
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_multi_step_fold_helpers_match_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(16, &context).unwrap();

        let monomial = (0..16)
            .map(|i| sample_ext(20 * i as u32))
            .collect::<Vec<_>>();
        let evals = (0..16)
            .map(|i| sample_ext(200 + 20 * i as u32))
            .collect::<Vec<_>>();
        let eq = (0..16)
            .map(|i| sample_ext(400 + 20 * i as u32))
            .collect::<Vec<_>>();
        let challenges = [
            sample_ext(777),
            sample_ext(888),
            sample_ext(999),
            sample_ext(1111),
        ];

        state.current_len = monomial.len();
        state.sumchecked_poly_monomial_form = alloc_and_copy(&monomial, &context);
        state.monomial_buffer = context.alloc(8, AllocationPlacement::BestFit).unwrap();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let mut expected_monomial = monomial;
        let mut expected_evals = evals;
        let mut expected_eq = eq;

        for (step_idx, challenge) in challenges.into_iter().enumerate() {
            fold_monomial_form_for_test(&mut expected_monomial, challenge);
            fold_evaluation_form_for_test(&mut expected_evals, challenge);
            fold_evaluation_form_for_test(&mut expected_eq, challenge);

            fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
            fold_evaluation_form_in_place_device(&mut state, challenge, &context).unwrap();
            fold_eq_poly_in_place_device(&mut state, challenge, &context).unwrap();
            state.current_len /= 2;

            assert_eq!(
                copy_back(
                    &state.sumchecked_poly_monomial_form[..state.current_len],
                    &context
                ),
                expected_monomial,
                "monomial fold diverged at step {step_idx}",
            );
            assert_eq!(
                copy_back(
                    &state.sumchecked_poly_evaluation_form[..state.current_len],
                    &context
                ),
                expected_evals,
                "evaluation fold diverged at step {step_idx}",
            );
            assert_eq!(
                copy_back(&state.eq_poly[..state.current_len], &context),
                expected_eq,
                "eq fold diverged at step {step_idx}",
            );
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_large_multi_step_monomial_fold_matches_cpu() {
        const LOG_LEN: usize = 18;
        const LEN: usize = 1 << LOG_LEN;
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(LEN, &context).unwrap();

        let monomial = (0..LEN)
            .map(|i| sample_ext(10_000 + i as u32))
            .collect::<Vec<_>>();
        let challenges = [
            sample_ext(777),
            sample_ext(888),
            sample_ext(999),
            sample_ext(1111),
            sample_ext(1222),
            sample_ext(1333),
        ];

        state.current_len = monomial.len();
        state.sumchecked_poly_monomial_form = alloc_and_copy(&monomial, &context);
        state.monomial_buffer = context
            .alloc(LEN / 2, AllocationPlacement::BestFit)
            .unwrap();

        let mut expected_monomial = monomial;
        for (step_idx, challenge) in challenges.into_iter().enumerate() {
            fold_monomial_form_for_test(&mut expected_monomial, challenge);
            fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
            state.current_len /= 2;

            assert_eq!(
                copy_back(
                    &state.sumchecked_poly_monomial_form[..state.current_len],
                    &context
                ),
                expected_monomial,
                "large monomial fold diverged at step {step_idx}",
            );
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_large_multi_step_fold_helpers_match_cpu() {
        const LOG_LEN: usize = 18;
        const LEN: usize = 1 << LOG_LEN;
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(LEN, &context).unwrap();

        let monomial = (0..LEN)
            .map(|i| sample_ext(20_000 + i as u32))
            .collect::<Vec<_>>();
        let evals = (0..LEN)
            .map(|i| sample_ext(40_000 + i as u32))
            .collect::<Vec<_>>();
        let eq = (0..LEN)
            .map(|i| sample_ext(60_000 + i as u32))
            .collect::<Vec<_>>();
        let challenges = [
            sample_ext(1777),
            sample_ext(1888),
            sample_ext(1999),
            sample_ext(2111),
            sample_ext(2222),
            sample_ext(2333),
        ];

        state.current_len = LEN;
        state.sumchecked_poly_monomial_form = alloc_and_copy(&monomial, &context);
        state.monomial_buffer = context
            .alloc(LEN / 2, AllocationPlacement::BestFit)
            .unwrap();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let mut expected_monomial = monomial;
        let mut expected_evals = evals;
        let mut expected_eq = eq;

        for (step_idx, challenge) in challenges.into_iter().enumerate() {
            fold_monomial_form_for_test(&mut expected_monomial, challenge);
            fold_evaluation_form_for_test(&mut expected_evals, challenge);
            fold_evaluation_form_for_test(&mut expected_eq, challenge);

            fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
            fold_evaluation_form_in_place_device(&mut state, challenge, &context).unwrap();
            fold_eq_poly_in_place_device(&mut state, challenge, &context).unwrap();
            state.current_len /= 2;

            assert_eq!(
                copy_back(
                    &state.sumchecked_poly_monomial_form[..state.current_len],
                    &context
                ),
                expected_monomial,
                "large combined fold monomial state diverged at step {step_idx}",
            );
            assert_eq!(
                copy_back(
                    &state.sumchecked_poly_evaluation_form[..state.current_len],
                    &context
                ),
                expected_evals,
                "large combined fold evaluation state diverged at step {step_idx}",
            );
            assert_eq!(
                copy_back(&state.eq_poly[..state.current_len], &context),
                expected_eq,
                "large combined fold eq state diverged at step {step_idx}",
            );
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_evaluate_monomial_matches_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let coeffs = (0..8)
            .map(|i| sample_ext(50 * i as u32))
            .collect::<Vec<_>>();
        let point = sample_ext(999);
        state.current_len = coeffs.len();
        state.sumchecked_poly_monomial_form = alloc_and_copy(&coeffs, &context);

        let actual = evaluate_monomial_form_device(&mut state, point, &context).unwrap();
        let expected = evaluate_monomial_form_for_test(&coeffs, point);

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn scheduled_whir_evaluate_monomial_matches_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let coeffs = (0..8)
            .map(|i| sample_ext(50 * i as u32))
            .collect::<Vec<_>>();
        let point = sample_ext(999);
        state.current_len = coeffs.len();
        state.sumchecked_poly_monomial_form = alloc_and_copy(&coeffs, &context);
        let point_device = alloc_and_copy(&[point], &context);

        let partials = schedule_monomial_eval_device(&mut state, &point_device, &context).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let mut actual = E4::ZERO;
        for partial in partials.iter() {
            actual.add_assign(&unsafe { partial.get_accessor().get() }[0]);
        }

        let expected = evaluate_monomial_form_for_test(&coeffs, point);
        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_initial_state_matches_cpu() {
        let context = make_test_context(256, 32);
        let worker = Worker::new();
        let memory_columns = vec![
            (0..8)
                .map(|i| BF::from_u32_unchecked(10 + i as u32))
                .collect(),
            (0..8)
                .map(|i| BF::from_u32_unchecked(30 + i as u32))
                .collect(),
        ];
        let witness_columns = vec![(0..8)
            .map(|i| BF::from_u32_unchecked(50 + i as u32))
            .collect()];
        let setup_columns = vec![(0..8)
            .map(|i| BF::from_u32_unchecked(70 + i as u32))
            .collect()];

        let memory_trace_holder = make_trace_holder(&memory_columns, &context);
        let witness_trace_holder = make_trace_holder(&witness_columns, &context);
        let setup_trace_holder = make_trace_holder(&setup_columns, &context);
        let domain_size = memory_columns[0].len();
        let memory_main_domain = copy_back_bf(memory_trace_holder.get_evaluations(), &context)
            .chunks_exact(domain_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();
        let witness_main_domain = copy_back_bf(witness_trace_holder.get_evaluations(), &context)
            .chunks_exact(domain_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();
        let setup_main_domain = copy_back_bf(setup_trace_holder.get_evaluations(), &context)
            .chunks_exact(domain_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();

        let mem_polys_claims = vec![sample_ext(10), sample_ext(20)];
        let wit_polys_claims = vec![sample_ext(30)];
        let setup_polys_claims = vec![sample_ext(40)];
        let original_evaluation_point = vec![sample_ext(100), sample_ext(200), sample_ext(300)];
        let batching_challenge = sample_ext(500);

        let mut state = GpuWhirState::new(8, &context).unwrap();
        let (batch_challenges, claim) = build_initial_state(
            &memory_trace_holder,
            &mem_polys_claims,
            &witness_trace_holder,
            &wit_polys_claims,
            &setup_trace_holder,
            &setup_polys_claims,
            &original_evaluation_point,
            batching_challenge,
            &mut state,
            &context,
        )
        .unwrap();

        let total_base_oracles = 4usize;
        let mut challenge_powers = materialize_powers_serial_starting_with_one::<
            E4,
            std::alloc::Global,
        >(batching_challenge, total_base_oracles);
        challenge_powers[1..].fill(E4::ZERO);
        let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims.len());
        let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims.len());

        assert_eq!(batch_challenges[0], memory_weights);
        assert_eq!(batch_challenges[1], witness_weights);
        assert_eq!(batch_challenges[2], setup_weights);

        let mut expected_evals = vec![E4::ZERO; 8];
        for (weights, columns) in [
            (memory_weights, memory_main_domain.as_slice()),
            (witness_weights, witness_main_domain.as_slice()),
            (setup_weights, setup_main_domain.as_slice()),
        ] {
            for (column, weight) in columns.iter().zip(weights.iter()) {
                for (dst, src) in expected_evals.iter_mut().zip(column.iter()) {
                    let mut term = *weight;
                    term.mul_assign_by_base(src);
                    dst.add_assign(&term);
                }
            }
        }

        let twiddles = Twiddles::<BF, Global>::new(expected_evals.len(), &worker);
        let mut expected_monomials = expected_evals.clone();
        let expected_log_n = expected_monomials.len().trailing_zeros();
        fft::naive::cache_friendly_ntt_natural_to_bitreversed(
            &mut expected_monomials,
            expected_log_n,
            &twiddles.inverse_twiddles[..],
        );
        let size_inv = BF::from_u32_unchecked(expected_monomials.len() as u32)
            .inverse()
            .unwrap();
        for value in expected_monomials.iter_mut() {
            value.mul_assign_by_base(&size_inv);
        }
        bitreverse_enumeration_inplace(&mut expected_monomials);

        let mut expected_eval_form = expected_monomials.clone();
        let expected_eval_log_n = expected_eval_form.len().trailing_zeros();
        multivariate_coeffs_into_hypercube_evals(&mut expected_eval_form, expected_eval_log_n);
        bitreverse_enumeration_inplace(&mut expected_eval_form);

        let expected_eq = make_eq_poly_in_full::<E4>(&original_evaluation_point, &worker)
            .pop()
            .unwrap()
            .into_vec();

        let mut expected_claim = E4::ZERO;
        for (weights, claims) in [
            (memory_weights, mem_polys_claims.as_slice()),
            (witness_weights, wit_polys_claims.as_slice()),
            (setup_weights, setup_polys_claims.as_slice()),
        ] {
            for (weight, claim_value) in weights.iter().zip(claims.iter()) {
                let mut term = *claim_value;
                term.mul_assign(weight);
                expected_claim.add_assign(&term);
            }
        }

        assert_eq!(claim, expected_claim);
        assert_eq!(
            copy_back(&state.sumchecked_poly_monomial_form[..8], &context),
            expected_monomials
        );
        assert_eq!(
            copy_back(&state.sumchecked_poly_evaluation_form[..8], &context),
            expected_eval_form
        );
        assert_eq!(copy_back(&state.eq_poly[..8], &context), expected_eq);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn base_query_paths_match_cpu_tree() {
        let context = make_test_context(256, 32);
        let worker = Worker::new();
        let columns: Vec<Vec<BF>> = vec![
            (0..8)
                .map(|i| BF::from_u32_unchecked(10 + i as u32))
                .collect(),
            (0..8)
                .map(|i| BF::from_u32_unchecked(30 + i as u32))
                .collect(),
        ];
        let log_lde_factor = 2u32;
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = 3u32;
        let rows = columns[0].len();
        let mut trace_holder = make_lde_trace_holder(
            &columns,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        );

        let lde_factor = 1usize << log_lde_factor;
        let cosets_host = (0..lde_factor)
            .map(|coset_index| {
                copy_back_bf(trace_holder.get_coset_evaluations(coset_index), &context)
            })
            .collect::<Vec<_>>();
        let source_storage = cosets_host
            .iter()
            .map(|host| {
                (0..columns.len())
                    .map(|column| {
                        let start = column * rows;
                        &host[start..start + rows]
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let source_refs = source_storage
            .iter()
            .map(|columns| columns.as_slice())
            .collect::<Vec<_>>();
        let cpu_tree = <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            BF,
        >>::construct_from_cosets::<BF, Global>(
            &source_refs,
            1usize << log_rows_per_leaf,
            1usize << log_tree_cap_size,
            true,
            true,
            false,
            &worker,
        );

        let total_queries = (rows << log_lde_factor) >> log_rows_per_leaf;
        for query_index in 0..total_queries {
            let (_, _, gpu_query) =
                query_base_trace_holder_for_folded_index(&mut trace_holder, query_index, &context)
                    .unwrap();
            let (_, cpu_path) =
                <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<BF>>::get_proof::<Global>(
                    &cpu_tree,
                    query_index,
                );
            assert_eq!(gpu_query.path, cpu_path, "query_index={}", query_index);
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_build_eq_values_preserves_large_eval_buffer() {
        let context = make_test_context(2048, 32);
        let trace_len = 1usize << 24;
        let sample_len = 1024usize;
        let mid = trace_len / 2;
        let stream = context.get_exec_stream();

        let mut evals = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        let fill = E4::from_array_of_base([BF::new(7), BF::new(13), BF::new(29), BF::new(43)]);
        get_powers_by_val(fill, 0, false, &mut evals, stream).unwrap();
        stream.synchronize().unwrap();

        let mut expected_head = vec![E4::ZERO; sample_len];
        let mut expected_mid = vec![E4::ZERO; sample_len];
        let mut expected_tail = vec![E4::ZERO; sample_len];
        memory_copy_async(&mut expected_head, &evals[..sample_len], stream).unwrap();
        memory_copy_async(&mut expected_mid, &evals[mid..mid + sample_len], stream).unwrap();
        memory_copy_async(
            &mut expected_tail,
            &evals[trace_len - sample_len..trace_len],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();

        let mut point = context.alloc(24, AllocationPlacement::BestFit).unwrap();
        let coordinates = (0..24)
            .map(|idx| {
                E4::from_array_of_base([
                    BF::new((idx + 3) as u32),
                    BF::new((idx + 17) as u32),
                    BF::new((idx + 31) as u32),
                    BF::new((idx + 53) as u32),
                ])
            })
            .collect::<Vec<_>>();
        copy_small_to_device(&mut point, &coordinates, &context).unwrap();

        let mut eq = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        launch_build_eq_values(
            point.as_ptr(),
            0,
            coordinates.len(),
            eq.as_mut_ptr(),
            trace_len,
            &context,
        )
        .unwrap();
        stream.synchronize().unwrap();

        let mut actual_head = vec![E4::ZERO; sample_len];
        let mut actual_mid = vec![E4::ZERO; sample_len];
        let mut actual_tail = vec![E4::ZERO; sample_len];
        memory_copy_async(&mut actual_head, &evals[..sample_len], stream).unwrap();
        memory_copy_async(&mut actual_mid, &evals[mid..mid + sample_len], stream).unwrap();
        memory_copy_async(
            &mut actual_tail,
            &evals[trace_len - sample_len..trace_len],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();

        assert_eq!(actual_head, expected_head);
        assert_eq!(actual_mid, expected_mid);
        assert_eq!(actual_tail, expected_tail);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_large_e4_bit_reverse_and_copy_matches_cpu() {
        let context = make_test_context(2048, 32);
        let trace_len = 1usize << 24;
        let sample_len = 1024usize;
        let mid = trace_len / 2;
        let stream = context.get_exec_stream();

        let fill = E4::from_array_of_base([BF::new(5), BF::new(11), BF::new(17), BF::new(23)]);
        let mut values = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        let mut scratch = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        get_powers_by_val(fill, 0, false, &mut values, stream).unwrap();
        let src = DeviceMatrix::new(&values, trace_len);
        let mut dst = DeviceMatrixMut::new(&mut scratch, trace_len);
        bit_reverse(&src, &mut dst, stream).unwrap();
        memory_copy_async(&mut values, &scratch, stream).unwrap();
        stream.synchronize().unwrap();

        let mut actual_head = vec![E4::ZERO; sample_len];
        let mut actual_mid = vec![E4::ZERO; sample_len];
        let mut actual_tail = vec![E4::ZERO; sample_len];
        memory_copy_async(&mut actual_head, &values[..sample_len], stream).unwrap();
        memory_copy_async(&mut actual_mid, &values[mid..mid + sample_len], stream).unwrap();
        memory_copy_async(
            &mut actual_tail,
            &values[trace_len - sample_len..trace_len],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();

        let expected_for_index = |index: usize| {
            fill.pow(
                (index.reverse_bits() >> (usize::BITS - trace_len.trailing_zeros()))
                    .try_into()
                    .unwrap(),
            )
        };
        let expected_head = (0..sample_len).map(expected_for_index).collect::<Vec<_>>();
        let expected_mid = (mid..mid + sample_len)
            .map(expected_for_index)
            .collect::<Vec<_>>();
        let expected_tail = ((trace_len - sample_len)..trace_len)
            .map(expected_for_index)
            .collect::<Vec<_>>();

        assert_eq!(actual_head, expected_head);
        assert_eq!(actual_mid, expected_mid);
        assert_eq!(actual_tail, expected_tail);
    }
}
