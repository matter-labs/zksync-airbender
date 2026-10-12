use std::collections::{BTreeMap, VecDeque};

use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_prover_context::ProverContext;

use crate::backward::ClaimBufferLayout;
use crate::forward::{GpuGKRForwardOutput, GpuGKRTranscriptHandoff};
use crate::upstream::{DimensionReducingInputOutput, OutputType, PR};
use crate::GpuGKRStorage;

pub struct GpuGKRDimensionReducingBackwardStatePr {
    pub(crate) forward_tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<PR, PR>,
    pub(crate) pending_layers:
        VecDeque<(usize, BTreeMap<OutputType, DimensionReducingInputOutput>)>,
    pub(crate) next_trace_len_after_reduction: usize,
}

impl GpuGKRDimensionReducingBackwardStatePr {
    pub(crate) fn from_forward_parts(
        parts: (
            Vec<Range>,
            GpuGKRStorage<PR, PR>,
            usize,
            BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
        ),
    ) -> Self {
        let (
            forward_tracing_ranges,
            storage,
            initial_layer_for_sumcheck,
            dimension_reducing_inputs,
        ) = parts;
        let first = dimension_reducing_inputs[&initial_layer_for_sumcheck]
            .values()
            .next()
            .and_then(|io| io.output.first())
            .copied()
            .expect("Proth120 backward state requires reduced outputs");
        let next_trace_len_after_reduction = storage.get_ext_poly(first).len();
        let pending_layers = dimension_reducing_inputs.into_iter().rev().collect();
        Self {
            forward_tracing_ranges,
            storage,
            pending_layers,
            next_trace_len_after_reduction,
        }
    }
}

pub struct ForwardToBackwardHandoffPr {
    pub(crate) transcript_handoff: GpuGKRTranscriptHandoff<PR>,
    pub(crate) backward_state: GpuGKRDimensionReducingBackwardStatePr,
    pub(crate) d_seed: DeviceAllocation<u8>,
    pub(crate) d_evaluation_point_and_batching: DeviceAllocation<PR>,
    pub(crate) top_layer_claim_layout: ClaimBufferLayout,
    pub(crate) initial_d_claims: DeviceAllocation<PR>,
    pub(crate) post_forward_handoff_range: Range,
}

pub fn prepare_backward_handoff_pr(
    forward_output: GpuGKRForwardOutput<PR, PR>,
    mut seed: DeviceAllocation<u8>,
    final_trace_size_log_2: u32,
    context: &ProverContext,
) -> CudaResult<ForwardToBackwardHandoffPr> {
    assert_eq!(
        final_trace_size_log_2, 4,
        "Proth120 handoff final trace log must be 4"
    );
    assert_eq!(
        seed.len(),
        32,
        "Proth120 handoff seed must contain 32 bytes"
    );
    let transcript_handoff = forward_output.transcript_handoff();
    let output_map =
        &forward_output.dimension_reducing_inputs[&forward_output.initial_layer_for_sumcheck];
    let addresses: Vec<_> = output_map
        .values()
        .flat_map(|io| io.output.iter().copied())
        .collect();
    let mut ordered = addresses.clone();
    ordered.sort();
    assert_eq!(
        ordered, addresses,
        "Proth120 top-layer claim slots differ from output iteration order"
    );
    let top_layer_claim_layout = ClaimBufferLayout::from_addresses(ordered);
    let poly_len = 1usize << final_trace_size_log_2;
    assert_eq!(
        transcript_handoff.device_flat_evaluations().len(),
        top_layer_claim_layout.claim_count() * poly_len,
        "Proth120 handoff output length mismatch"
    );
    let range = Range::new("gkr.proth120.forward.handoff")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    gpu_hash::keccak256::transcript_commit_fields(
        &mut seed,
        transcript_handoff.device_flat_evaluations(),
        stream,
    )?;
    let mut d_evaluation_point_and_batching = context.alloc(
        (final_trace_size_log_2 + 1) as usize,
        AllocationPlacement::BestFit,
    )?;
    gpu_hash::keccak256::transcript_draw_fields(
        &mut seed,
        &mut d_evaluation_point_and_batching,
        stream,
    )?;
    let mut groups = context.alloc(
        crate::backward::eq_group_tables_len(final_trace_size_log_2 as usize).max(1),
        AllocationPlacement::BestFit,
    )?;
    let mut values = context.alloc(poly_len, AllocationPlacement::BestFit)?;
    super::kernels::launch_eq_values(
        d_evaluation_point_and_batching.as_ptr(),
        final_trace_size_log_2,
        groups.as_mut_ptr(),
        values.as_mut_ptr(),
        context,
    )?;
    let mut initial_d_claims = context.alloc(
        top_layer_claim_layout.claim_count(),
        AllocationPlacement::BestFit,
    )?;
    super::kernels::launch_initial_inner_products(
        transcript_handoff.device_flat_evaluations().as_ptr(),
        top_layer_claim_layout.claim_count(),
        values.as_ptr(),
        poly_len as u32,
        initial_d_claims.as_mut_ptr(),
        context,
    )?;
    range.end(stream)?;
    let backward_state =
        GpuGKRDimensionReducingBackwardStatePr::from_forward_parts(forward_output.into_parts());
    Ok(ForwardToBackwardHandoffPr {
        transcript_handoff,
        backward_state,
        d_seed: seed,
        d_evaluation_point_and_batching,
        top_layer_claim_layout,
        initial_d_claims,
        post_forward_handoff_range: range,
    })
}
