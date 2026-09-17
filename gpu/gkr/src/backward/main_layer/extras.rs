use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use crate::proof_layout::ProofLayout;
use crate::{GpuBaseFieldPoly, GpuGKRStorage};
use gpu_core::primitives::field::E4;

use super::super::kernels::*;
use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::BF;
use gpu_prover_context::ProverContext;

/// Stream-ordered keepalive for the main-layer extras eval scratch
/// buffers. The held allocations and Arc-clones outlive every
/// `exec_stream` op scheduled by `schedule_main_layer_extras_eval`. Handles
/// may be dropped after the last use is enqueued; later pool reuse is ordered
/// behind it on that stream.
pub(crate) struct MainLayerExtrasKeepalive {
    _eq: ExtraEq,
    _block_partials: DeviceAllocation<E4>,
    /// Per-extra resolved views over the consolidated
    /// `base_class_backings`. Holding the views keeps the underlying
    /// `Arc<DeviceAllocation<B>>` backings alive until kernels reading
    /// from them have been scheduled and the pool drop is safe.
    _extra_views: Vec<GpuBaseFieldPoly<BF>>,
}

enum ExtraEq {
    Dense {
        _groups: DeviceAllocation<E4>,
        values: DeviceAllocation<E4>,
    },
    Deferred {
        low: DeviceAllocation<E4>,
        sizes: GkrEqSizes,
        blocks: usize,
    },
}

/// A packed thread processes four adjacent rows. Preserve the low and middle
/// coordinates across its grid stride so their Eq factors can leave the loop.
fn deferred_extra_geometry(folding_steps: usize, sm_count: usize) -> Option<(GkrEqSizes, usize)> {
    assert!(sm_count > 0);
    if folding_steps > (GKR_EQ_HIGH_SLOTS + 1) * GKR_EQ_GROUP_SIZE {
        return None;
    }
    let sizes = make_eq_sizes(folding_steps);
    if sizes.low < 2 {
        return None;
    }
    let period = 1usize << (sizes.low + sizes.high[1]);
    let quantum = period.div_ceil(GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK as usize * 4);
    Some((sizes, sm_count.div_ceil(quantum) * quantum))
}

fn prepare_extra_eq(
    folding_point: *const E4,
    folding_steps: usize,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<ExtraEq> {
    if let Some((sizes, blocks)) =
        deferred_extra_geometry(folding_steps, context.get_device_properties().sm_count)
    {
        let mut low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?;
        // All current-layer Eq readers precede this call on exec_stream. The
        // next layer (or base-layer claims) rebuilds the high slabs before use.
        // This is the outgoing full point, not the destructively folded Eq
        // scratch used by the current layer's rounds.
        launch_build_eq_high_and_low_groups_from_point(
            folding_point,
            0,
            folding_steps,
            get_eq_high_constant_device_ptr(),
            low.as_mut_ptr(),
            context,
        )?;
        return Ok(ExtraEq::Deferred { low, sizes, blocks });
    }
    let mut groups = context.alloc(
        eq_group_tables_len(folding_steps).max(1),
        AllocationPlacement::Top,
    )?;
    let mut values = context.alloc(trace_len, AllocationPlacement::Top)?;
    launch_build_eq_values_from_point(
        folding_point,
        0,
        folding_steps,
        groups.as_mut_ptr(),
        values.as_mut_ptr(),
        trace_len,
        context,
    )?;
    Ok(ExtraEq::Dense {
        _groups: groups,
        values,
    })
}

/// Schedules the on-device evaluation of `extra_addresses` at the
/// folding point `[r_0..r_{folding_steps - 1}]` of length
/// `folding_steps`. For each missing cached-relation dependency, computes
/// `inner_product(extra_poly, eq_values)` and writes one `E` value into:
/// (a) `extras_dst_ptr[i]`, the tail of the caller's `device_new_claims`
///     buffer (so the next layer's IN claim buffer carries the extra
///     claim), and
/// (b) `proof_layout.backward[layer_slot].extra_evaluations`, the slab
///     range (so the verifier can read the explicit at-point evals).
///
/// Mirrors the CPU's
/// `extra_evaluations_from_caching_relations` mechanism (see
/// [`prover/src/gkr/prover/sumcheck_loop/mod.rs:293-395`]). Returns a
/// keepalive that the caller drops at the end of the scheduler — the
/// keepalive owns the temporaries (`eq_values`, `block_partials`) and the
/// extra-polynomial view Arc-clones.
///
/// Operates entirely on `exec_stream`. No host blocking. Compatible
/// with the GPU scheduling contract (`gpu/docs/gpu_scheduling_contract.md`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_main_layer_extras_eval(
    layer_idx: usize,
    extra_addresses: &[GKRAddress],
    storage: &GpuGKRStorage<BF, E4>,
    folding_point_ptr: *const E4,
    folding_steps: usize,
    trace_len: usize,
    extras_dst_ptr: *mut E4,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    layer_slot: usize,
    context: &ProverContext,
) -> CudaResult<MainLayerExtrasKeepalive> {
    let extra_count = extra_addresses.len();
    assert!(
        extra_count > 0,
        "schedule_main_layer_extras_eval should only be called with at least one extra"
    );
    assert_eq!(
        trace_len,
        1usize << folding_steps,
        "trace_len must equal 2^folding_steps for full-folding-point eq build",
    );
    assert!(trace_len <= u32::MAX as usize);
    let stream = context.get_exec_stream();

    // 1. Build Eq over the full outgoing folding point.
    let eq = prepare_extra_eq(folding_point_ptr, folding_steps, trace_len, context)?;

    // 2. Resolve each extra to its `(backing, offset, len)` view via
    //    the storage layout. Compiler cache-relation dependencies are
    //    base-field polynomials; `resolve_base_view_or_panic` deliberately
    //    fails fast if a future relation variant violates that invariant.
    //    Resolution is non-mutating and triggers no fresh allocations. The
    //    Arc clones held in `extra_views` tie this scheduler's lifetime to
    //    the backings.
    let extra_views: Vec<GpuBaseFieldPoly<BF>> = extra_addresses
        .iter()
        .map(|addr| {
            let view = storage.resolve_base_view_or_panic(layer_idx, *addr);
            assert_eq!(
                view.len(),
                trace_len,
                "extra poly length must match trace_len (address {addr:?})"
            );
            view
        })
        .collect();

    // 3. Per-extra partial-sum reduction → `block_partials[extra_count, blocks_count]`
    //    matrix, then `batch_reduce` over rows to produce `[extra_count]`
    //    scalar inner products written straight into `extras_dst_ptr`.
    let blocks_count = match &eq {
        ExtraEq::Deferred { blocks, .. } => *blocks,
        ExtraEq::Dense { .. } => context.get_device_properties().sm_count,
    };
    assert!(blocks_count > 0, "device must expose at least one SM");
    assert!(blocks_count <= u32::MAX as usize);
    let mut block_partials: DeviceAllocation<E4> =
        context.alloc(extra_count * blocks_count, AllocationPlacement::Top)?;

    for (extra_i, view) in extra_views.iter().enumerate() {
        // SAFETY: each extra owns one blocks_count-element row in this allocation.
        let row_partials_ptr = unsafe { block_partials.as_mut_ptr().add(extra_i * blocks_count) };
        match &eq {
            ExtraEq::Dense { values, .. } => launch_trace_holder_block_partials(
                view.as_ptr(),
                values.as_ptr(),
                row_partials_ptr,
                trace_len,
                0,
                1,
                blocks_count,
                context,
            )?,
            ExtraEq::Deferred { low, sizes, .. } => launch_trace_holder_block_partials_eq_deferred(
                view.as_ptr(),
                low.as_ptr(),
                *sizes,
                row_partials_ptr,
                trace_len,
                blocks_count,
                context,
            )?,
        }
    }

    // `extras_dst_ptr` is a tail slot in `device_new_claims`, sized to fit
    // `extra_count` `E` values by the caller.
    launch_trace_holder_column_sums(
        block_partials.as_ptr(),
        extras_dst_ptr,
        extra_count,
        blocks_count,
        context,
    )?;

    // 4. Copy the extra claim values from the `device_new_claims` tail into
    //    the slab's per-layer-slot `extra_evaluations` range so the verifier
    //    can parse them alongside `final_step_evaluations`.
    {
        // SAFETY: E = E4 in every instantiation; the slab range was
        // sized at `extra_evaluations_addresses.len()` E4 by the
        // proof-layout builder.
        let (slab_dst_ptr, slab_dst_len) = unsafe {
            proof_layout
                .backward_extra_evaluations_device_mut(proof_slab.as_ptr() as *mut u8, layer_slot)
        };
        assert_eq!(
            slab_dst_len, extra_count,
            "slab extra_evaluations range must match extra_count for layer {layer_slot}",
        );
        let slab_dst_slice =
            unsafe { DeviceSlice::from_raw_parts_mut(slab_dst_ptr as *mut E4, extra_count) };
        let extras_src_slice =
            unsafe { DeviceSlice::from_raw_parts(extras_dst_ptr as *const E4, extra_count) };
        memory_copy_async(slab_dst_slice, extras_src_slice, stream)?;
    }

    Ok(MainLayerExtrasKeepalive {
        _eq: eq,
        _block_partials: block_partials,
        _extra_views: extra_views,
    })
}

/// Structural variant of `prepare_dimension_reduction_forward`'s
/// `dimension_reduction_description` output: replicates the address-only
/// portion of the per-round lowering in
/// `gpu/gkr/src/forward/dimension_reducing.rs`'s
/// `lower_dimension_reducing_forward_round` without scheduling any GPU work.
///
/// Address-assignment rules (matched exactly):
/// - Each round walks `layer_inputs.iter()` (BTreeMap → ordered by `OutputType`).
/// - Both `PermutationProduct` and `Lookup*` arg types emit two output addresses
///   per slot (`InnerLayer { layer: output_layer, offset: output_idx }` then
///   `output_idx += 1`), so the offset assignment is purely positional.
/// - Round 0's `layer_inputs` is `compiled_circuit.global_output_map`; subsequent
///   rounds chain from the previous round's `output`.
///
/// Used to size the proof slab before forward runs.
pub(crate) fn derive_dimension_reducing_inputs(
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: u32,
    final_trace_log_2: u32,
) -> BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> {
    let mut result: BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> =
        BTreeMap::new();
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return result;
    }
    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = initial_output_map.clone();

    for (layer_offset, _) in (0..total_rounds).enumerate() {
        let current_layer_idx = initial_layer_idx + layer_offset;
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
    }
    result
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn cpu_deferred_extra_geometry_preserves_factor_indices() {
        for bits in 0usize..=31 {
            for sm_count in [1usize, 47, 188, 189, 256] {
                let geometry = deferred_extra_geometry(bits, sm_count);
                // The factor slabs are at most eight bits; the last slab must
                // contain the complete four-row pack handled by a thread.
                let eligible = matches!(bits, 2..=8 | 10..=16 | 18..=24);
                assert_eq!(geometry.is_some(), eligible, "bits={bits}");
                if let Some((sizes, blocks)) = geometry {
                    assert_eq!(
                        sizes.low as usize + sizes.high[0] as usize + sizes.high[1] as usize,
                        bits
                    );
                    let period = 1usize << (sizes.low + sizes.high[1]);
                    let rows_per_block = GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK as usize * 4;
                    assert!(blocks >= sm_count);
                    assert_eq!(blocks * rows_per_block % period, 0);
                    assert!(
                        (sm_count..blocks).all(|n| !(n * rows_per_block).is_multiple_of(period))
                    );
                    for row in [0usize, 4, 124, (1usize << bits) - 4] {
                        let next = row + blocks * rows_per_block;
                        assert_eq!(row % period, next % period);
                        assert!((row & ((1 << sizes.low) - 1)) + 3 < 1 << sizes.low);
                    }
                }
            }
        }
    }
}
