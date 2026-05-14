use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use crate::ops::cub::device_reduce::Reduce;
use crate::primitives::field::E4;
use crate::prover::proof::layout::ProofLayout;

use super::super::{GpuBaseFieldPoly, GpuGKRStorage};
use super::kernels::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::field::BF;
use crate::upstream::{
    DimensionReducingInputOutput, Field, FieldExtension, GKRAddress, OutputType,
};

/// Stream-ordered keepalive for the main-layer extras eval scratch
/// buffers. The held allocations and Arc-clones outlive every
/// `exec_stream` op scheduled by `schedule_main_layer_extras_eval`; the
/// pool defers underlying free until exec_stream has progressed past the
/// last write that uses these buffers.
pub(crate) struct MainLayerExtrasKeepalive<B, E> {
    _eq_group_tables: DeviceAllocation<E>,
    _eq_values: DeviceAllocation<E>,
    _block_partials: DeviceAllocation<E>,
    _reduction_temp: DeviceAllocation<u8>,
    /// Per-orphan resolved views over the consolidated
    /// `base_class_backings`. Holding the views keeps the underlying
    /// `Arc<DeviceAllocation<B>>` backings alive until kernels reading
    /// from them have been scheduled and the pool drop is safe.
    _orphan_views: Vec<GpuBaseFieldPoly<B>>,
}

/// Schedules the on-device evaluation of `orphan_addresses` at the
/// folding point `[r_0..r_{folding_steps - 1}]` of length
/// `folding_steps`. For each orphan, computes
/// `inner_product(orphan_poly, eq_values)` and writes one `E` value into:
/// (a) `extras_dst_ptr[i]`, the tail of the caller's `device_new_claims`
///     buffer (so the next layer's IN claim buffer carries the orphan
///     claim), and
/// (b) `proof_layout.backward[layer_slot].extra_evaluations`, the slab
///     range (so the verifier can read the explicit at-point evals).
///
/// Mirrors the CPU's
/// `extra_evaluations_from_caching_relations` mechanism (see
/// [`prover/src/gkr/prover/sumcheck_loop/mod.rs:293-395`]). Returns a
/// keepalive that the caller drops at the end of the scheduler — the
/// keepalive owns the temporaries (`eq_values`, `block_partials`,
/// `reduction_temp`) and the orphan view Arc-clones.
///
/// Operates entirely on `exec_stream`. No host blocking. Compatible
/// with the GPU scheduling contract (`gpu_prover/docs/gpu_scheduling_contract.md`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_main_layer_extras_eval<E>(
    layer_idx: usize,
    orphan_addresses: &[GKRAddress],
    storage: &GpuGKRStorage<BF, E>,
    folding_point_ptr: *const E,
    folding_steps: usize,
    trace_len: usize,
    extras_dst_ptr: *mut E,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    layer_slot: usize,
    context: &ProverContext,
) -> CudaResult<MainLayerExtrasKeepalive<BF, E>>
where
    E: crate::prover::gkr::GpuKernels + Field + FieldExtension<BF> + Reduce + 'static,
{
    let orphan_count = orphan_addresses.len();
    assert!(
        orphan_count > 0,
        "schedule_main_layer_extras_eval should only be called with at least one orphan"
    );
    assert_eq!(
        trace_len,
        1usize << folding_steps,
        "trace_len must equal 2^folding_steps for full-folding-point eq build",
    );
    assert!(trace_len <= u32::MAX as usize);
    let stream = context.get_exec_stream();

    // 1. Build the full-folding-point `eq_values` of length `trace_len`
    //    from the just-produced folding point in `device_claim_point_out`.
    //    The dim-reducing eq builder is reused: it derives `eq_values`
    //    over the entire hypercube of size `2^challenge_count` from a
    //    single contiguous challenge slab — exactly what we need here.
    let mut eq_group_tables: DeviceAllocation<E> = context.alloc(
        eq_group_tables_len(folding_steps).max(1),
        AllocationPlacement::Top,
    )?;
    let mut eq_values: DeviceAllocation<E> = context.alloc(trace_len, AllocationPlacement::Top)?;
    launch_build_eq_values_from_point(
        folding_point_ptr,
        0,
        folding_steps,
        eq_group_tables.as_mut_ptr(),
        eq_values.as_mut_ptr(),
        trace_len,
        context,
    )?;

    // 2. Resolve each orphan to its `(backing, offset, len)` view via
    //    the storage layout. Non-mutating — no fresh allocations
    //    triggered. The Arc clones held in `orphan_views` are the
    //    keepalive that ties this scheduler's lifetime to the backings.
    let orphan_views: Vec<GpuBaseFieldPoly<BF>> = orphan_addresses
        .iter()
        .map(|addr| {
            let view = storage.resolve_base_view_or_panic(layer_idx, *addr);
            assert_eq!(
                view.len(),
                trace_len,
                "orphan poly length must match trace_len (address {addr:?})"
            );
            view
        })
        .collect();

    // 3. Per-orphan partial-sum reduction → `block_partials[orphan_count, blocks_count]`
    //    matrix, then `batch_reduce` over rows to produce `[orphan_count]`
    //    scalar inner products written straight into `extras_dst_ptr`.
    let blocks_count = context.get_device_properties().sm_count;
    assert!(blocks_count > 0, "device must expose at least one SM");
    assert!(blocks_count <= u32::MAX as usize);
    let mut block_partials: DeviceAllocation<E> =
        context.alloc(orphan_count * blocks_count, AllocationPlacement::Top)?;
    let reduction_temp_bytes = get_batch_reduce_temp_storage_bytes::<E>(
        ReduceOperation::Sum,
        orphan_count as i32,
        blocks_count as i32,
    )?;
    let mut reduction_temp = context
        .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
            reduction_temp_bytes,
            AllocationPlacement::Top,
        )?;

    for (orphan_i, view) in orphan_views.iter().enumerate() {
        // SAFETY: block_partials buffer is sized [orphan_count *
        // blocks_count]; the kernel writes exactly `blocks_count`
        // contiguous slots starting at this pointer (since we pass
        // `column_start = 0`, `chunk_cols = 1`).
        let row_partials_ptr = unsafe { block_partials.as_mut_ptr().add(orphan_i * blocks_count) };
        launch_trace_holder_block_partials::<E>(
            view.as_ptr(),
            eq_values.as_ptr(),
            row_partials_ptr,
            trace_len,
            0,
            1,
            blocks_count,
            context,
        )?;
    }

    let block_partials_matrix = DeviceMatrix::new(&block_partials, blocks_count);
    // SAFETY: `extras_dst_ptr` is a tail slot in `device_new_claims`,
    // sized to fit `orphan_count` `E` values by the caller.
    let extras_dst_slice = unsafe { DeviceSlice::from_raw_parts_mut(extras_dst_ptr, orphan_count) };
    let reduction_temp_slice = unsafe {
        DeviceSlice::from_raw_parts_mut(reduction_temp.as_mut_ptr(), reduction_temp.len())
    };
    batch_reduce(
        ReduceOperation::Sum,
        reduction_temp_slice,
        &block_partials_matrix,
        extras_dst_slice,
        stream,
    )?;

    // 4. Production slab path: copy the orphan claim values from the
    //    `device_new_claims` tail into the slab's per-layer-slot
    //    `extra_evaluations` range so the verifier can parse them
    //    alongside `final_step_evaluations`. Test paths (no slab)
    //    skip this — the values still live in the claims buffer for
    //    the next layer's consumption.
    if let Some(slab) = proof_slab {
        // SAFETY: E = E4 in every instantiation; the slab range was
        // sized at `extra_evaluations_addresses.len()` E4 by the
        // proof-layout builder.
        let (slab_dst_ptr, slab_dst_len) = unsafe {
            proof_layout.backward_extra_evaluations_device_mut(slab.as_ptr() as *mut u8, layer_slot)
        };
        debug_assert_eq!(
            slab_dst_len, orphan_count,
            "slab extra_evaluations range must match orphan_count for layer {layer_slot}",
        );
        let slab_dst_slice =
            unsafe { DeviceSlice::from_raw_parts_mut(slab_dst_ptr as *mut E, orphan_count) };
        let extras_src_slice =
            unsafe { DeviceSlice::from_raw_parts(extras_dst_ptr as *const E, orphan_count) };
        memory_copy_async(slab_dst_slice, extras_src_slice, stream)?;
    }

    Ok(MainLayerExtrasKeepalive {
        _eq_group_tables: eq_group_tables,
        _eq_values: eq_values,
        _block_partials: block_partials,
        _reduction_temp: reduction_temp,
        _orphan_views: orphan_views,
    })
}

/// Structural variant of [`schedule_dimension_reduction_forward`]'s
/// `dimension_reduction_description` output: replicates the address-only
/// portion of the per-round lowering at
/// `gpu_prover/src/prover/gkr/forward.rs:1965-2074` without scheduling any GPU work.
///
/// Address-assignment rules (matched exactly):
/// - Each round walks `layer_inputs.iter()` (BTreeMap → ordered by `OutputType`).
/// - Both `PermutationProduct` and `Lookup*` arg types emit two output addresses
///   per slot (`InnerLayer { layer: output_layer, offset: output_idx }` then
///   `output_idx += 1`), so the offset assignment is purely positional.
/// - Round 0's `layer_inputs` is `compiled_circuit.global_output_map`; subsequent
///   rounds chain from the previous round's `output`.
///
/// Used by [`crate::prover::proof::layout::build_proof_layout_inputs`]
/// to size the proof slab before forward runs.
pub(crate) fn derive_dimension_reducing_inputs(
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
) -> BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> {
    let mut result: BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> =
        BTreeMap::new();
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return result;
    }
    let mut current_layer_idx = initial_layer_idx;
    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = initial_output_map.clone();

    for _round in 0..total_rounds {
        let output_layer = current_layer_idx + 1;
        let mut output_idx = 0usize;
        let mut layer_description: BTreeMap<OutputType, DimensionReducingInputOutput> =
            BTreeMap::new();

        for (arg_type, inputs) in layer_inputs.iter() {
            assert_eq!(
                inputs.len(),
                2,
                "dim reduction expects 2 inputs per slot for {:?}",
                arg_type,
            );
            let out_a = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx,
            };
            output_idx += 1;
            let out_b = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx,
            };
            output_idx += 1;
            layer_description.insert(
                *arg_type,
                DimensionReducingInputOutput {
                    inputs: inputs.clone(),
                    output: vec![out_a, out_b],
                },
            );
        }

        layer_inputs = layer_description
            .iter()
            .map(|(k, v)| (*k, v.output.clone()))
            .collect();

        result.insert(current_layer_idx, layer_description);
        current_layer_idx += 1;
    }
    result
}
