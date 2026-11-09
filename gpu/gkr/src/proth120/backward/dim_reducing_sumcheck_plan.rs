use std::collections::{BTreeMap, BTreeSet};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_tracing::Range;
use gpu_hash::keccak256::{transcript_commit_fields, transcript_draw_fields};
use gpu_prover_context::ProverContext;

use super::capacity::DrTailCapacityDecisionPr;
use super::dr_tail::{
    dimension_reducing_slots_pr, encode_dr_tail_slots_pr, launch_dr_tail_megakernel_pr,
    DrTailMegakernelDescPr, DrTailPlanCursorPr, DrTailProofPlanPr, PR_DR_TAIL_MAX_SOURCES,
};
use super::gkr_ops;
use super::scheduled_execution::{gather_pr, LayerInputPr, ScheduledLayerExecutionPr};
use super::window::launch_window_tail_pr;
use super::window_dr::{
    schedule_dr_batch_challenge_table_pr, unwrap_dr_window_pr, DrLayerTranscriptPr,
    DrWindowLayerHookPr, DrWindowRawInputKeepalivePr,
};
use super::GpuGKRDimensionReducingBackwardStatePr;
use crate::backward::{ClaimBufferLayout, GpuGKRDimensionReducingLayerSlots};
use crate::proth120::proof_layout::ProofSlabPr;
use crate::upstream::{GKRAddress, PR};
use crate::GpuGKRStorage;

pub(crate) struct DimensionReducingLayerPlanPr {
    pub(crate) layer_idx: usize,
    folding_steps: usize,
    layer_slots: GpuGKRDimensionReducingLayerSlots,
    folding_addresses: Vec<GKRAddress>,
    capacity: DrTailCapacityDecisionPr,
}

fn canonical_address(storage: &GpuGKRStorage<PR, PR>, address: GKRAddress) -> GKRAddress {
    storage
        .layout
        .as_ref()
        .and_then(|layout| layout.aliases.get(&address))
        .copied()
        .unwrap_or(address)
}

impl GpuGKRDimensionReducingBackwardStatePr {
    pub(crate) fn prepare_next_layer_pr(
        &mut self,
        cursor: &mut DrTailPlanCursorPr<'_>,
    ) -> Option<DimensionReducingLayerPlanPr> {
        let (layer_idx, layer) = self.pending_layers.pop_front()?;
        let trace_len = self.next_trace_len_after_reduction;
        assert!(
            trace_len.is_power_of_two() && trace_len >= 4,
            "Proth120 dimension-reducing trace length {trace_len} is unsupported"
        );
        let folding_steps = trace_len.trailing_zeros() as usize;
        let layer_slots = dimension_reducing_slots_pr(&layer);
        assert_ne!(
            layer_slots.enabled_mask(),
            0,
            "Proth120 dimension-reducing layer {layer_idx} enables no slot"
        );
        let folding_addresses: Vec<GKRAddress> = layer_slots
            .input_addresses()
            .map(|address| canonical_address(&self.storage, address))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let capacity = cursor.bind(layer_idx, folding_steps, &folding_addresses);
        self.next_trace_len_after_reduction *= 2;
        Some(DimensionReducingLayerPlanPr {
            layer_idx,
            folding_steps,
            layer_slots,
            folding_addresses,
            capacity,
        })
    }
}

impl DimensionReducingLayerPlanPr {
    pub(crate) fn schedule_execute_pr(
        &self,
        input: LayerInputPr,
        plan: &DrTailProofPlanPr,
        storage: &mut GpuGKRStorage<PR, PR>,
        proof: &mut ProofSlabPr,
        context: &ProverContext,
    ) -> CudaResult<ScheduledLayerExecutionPr> {
        let stream = context.get_exec_stream();
        let layer = self.layer_idx;
        let n = self.folding_steps;
        let entry_round = self.capacity.entry_round;
        let LayerInputPr {
            mut seed,
            point_and_batching: point_in,
            claims: claims_in,
            claim_layout,
        } = input;
        let range = Range::new(format!(
            "gkr.proth120.backward.dimension_reducing.layer.{layer}"
        ))?;
        range.start(stream)?;
        assert_eq!(
            point_in.len(),
            n + 1,
            "Proth120 dimension-reducing claim point length mismatch"
        );
        assert_eq!(
            claims_in.len(),
            claim_layout.claim_count(),
            "Proth120 dimension-reducing claim layout mismatch"
        );
        let desc_pairs: Vec<u32> = self
            .layer_slots
            .iter_enabled()
            .flat_map(|(_, slot)| {
                slot.outputs
                    .iter()
                    .zip(slot.batch_exp.iter())
                    .flat_map(|(output, exp)| [u32::from(*exp), claim_layout.claim_idx(output)])
            })
            .collect();
        let mut claim = context.alloc(1, AllocationPlacement::Top)?;
        let mut eq_prefactor = context.alloc(1, AllocationPlacement::Top)?;
        let coeffs = {
            let coeffs = proof.round_coefficients_device_mut(layer);
            assert_eq!(
                coeffs.len(),
                4 * n,
                "Proth120 dimension-reducing coefficient range mismatch"
            );
            coeffs.as_mut_ptr()
        };
        let batch_table = schedule_dr_batch_challenge_table_pr(point_in[n..].as_ptr(), context)?;
        gkr_ops::build_combined_claim(
            &claims_in,
            &point_in[n..n + 1],
            &desc_pairs,
            &mut claim,
            &mut eq_prefactor,
            stream,
        )?;
        drop(claims_in);
        let mut point_out = context.alloc(n + 2, AllocationPlacement::Top)?;
        memory_copy_async(&mut point_out[..n], &point_in[..n], stream)?;
        let program = plan.window_program(layer);
        let transcript = DrLayerTranscriptPr {
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coeffs,
            point_out: point_out.as_mut_ptr(),
        };
        let (hook, direct_inputs) = if entry_round == 0 {
            let inputs = unwrap_dr_window_pr(DrWindowRawInputKeepalivePr::from_projection(
                storage,
                program.input_projection(),
            ))?;
            (None, Some(inputs))
        } else {
            let hook = unwrap_dr_window_pr(DrWindowLayerHookPr::bind(
                program,
                storage,
                entry_round,
                batch_table.as_ptr(),
                point_out.as_ptr(),
                context,
            ))?;
            assert_eq!(hook.folding_steps(), n);
            hook.launch_r0(context)?;
            launch_window_tail_pr(&hook.r0_tail_state(&transcript), context)?;
            storage.purge_up_to_layer(layer);
            for pass in hook.continuations() {
                pass.launch(context)?;
                launch_window_tail_pr(&pass.tail_state(&transcript), context)?;
            }
            (Some(hook), None)
        };
        let sources = match (&hook, &direct_inputs) {
            (Some(hook), _) => {
                unwrap_dr_window_pr(hook.megakernel_source_pointers(program, storage))?
            }
            (None, Some(inputs)) => unwrap_dr_window_pr(
                inputs.canonical_source_pointers(storage, program.input_projection()),
            )?,
            (None, None) => unreachable!(),
        };
        let source_count = self.folding_addresses.len();
        assert_eq!(
            sources.len(),
            source_count,
            "Proth120 DR tail source count mismatch"
        );
        assert!(source_count <= PR_DR_TAIL_MAX_SOURCES);
        let mut source_ptrs = [std::ptr::null(); PR_DR_TAIL_MAX_SOURCES];
        source_ptrs[..source_count].copy_from_slice(&sources);
        let slots = encode_dr_tail_slots_pr(
            &self.layer_slots,
            &self.folding_addresses,
            storage.layout.as_ref().map(|layout| &layout.aliases),
        );
        let mut final_sources = context.alloc(4 * source_count, AllocationPlacement::Top)?;
        launch_dr_tail_megakernel_pr(
            DrTailMegakernelDescPr {
                enabled_mask: self.layer_slots.enabled_mask(),
                folding_steps: n as u32,
                entry_round: entry_round as u32,
                source_count: source_count as u32,
                source_ptrs,
                final_sources: final_sources.as_mut_ptr(),
                tau: point_in.as_ptr(),
                seed: transcript.seed,
                claim: transcript.claim,
                eq_prefactor: transcript.eq_prefactor,
                coeffs_out: coeffs,
                challenges_out: transcript.point_out,
                batch_challenges: batch_table.as_ptr(),
                slots,
            },
            &self.capacity,
            context,
        )?;
        if entry_round == 0 {
            storage.purge_up_to_layer(layer);
        }
        drop(hook);
        drop(direct_inputs);
        let mut transcript_sources: BTreeMap<GKRAddress, *const PR> = BTreeMap::new();
        for address in self.layer_slots.input_addresses() {
            let index = self
                .folding_addresses
                .binary_search(&canonical_address(storage, address))
                .expect("Proth120 DR final source is missing from the canonical sources");
            transcript_sources
                .entry(address)
                .or_insert(final_sources[4 * index..].as_ptr());
        }
        let addresses: Vec<GKRAddress> = transcript_sources.keys().copied().collect();
        let count = addresses.len();
        let mut last = context.alloc(4 * count, AllocationPlacement::Top)?;
        gather_pr(transcript_sources.values().copied(), &mut last, stream)?;
        drop(final_sources);
        {
            let finals = proof.final_step_evaluations_device_mut(layer);
            assert_eq!(
                finals.len(),
                2 * count,
                "Proth120 dimension-reducing final evaluation range mismatch"
            );
            gkr_ops::dim_reducing_lsb_lines(&last, &point_out[n - 1..n], finals, stream)?;
        }
        transcript_commit_fields(
            &mut seed,
            &*proof.final_step_evaluations_device_mut(layer),
            stream,
        )?;
        transcript_draw_fields(&mut seed, &mut point_out[n..n + 2], stream)?;
        let mut new_claims = context.alloc(count, AllocationPlacement::Top)?;
        gkr_ops::new_claims_two_var(&last, &point_out[n - 1..n + 1], &mut new_claims, stream)?;
        let mut point_next = context.alloc(n + 2, AllocationPlacement::Top)?;
        memory_copy_async(&mut point_next[..1], &point_out[n..n + 1], stream)?;
        memory_copy_async(&mut point_next[1..n + 1], &point_out[..n], stream)?;
        memory_copy_async(&mut point_next[n + 1..], &point_out[n + 1..], stream)?;
        range.end(stream)?;
        drop(last);
        drop(claim);
        drop(eq_prefactor);
        drop(batch_table);
        drop(point_in);
        drop(point_out);
        Ok(ScheduledLayerExecutionPr {
            layer_idx: layer,
            _tracing_ranges: vec![range],
            next: Some(LayerInputPr {
                seed,
                point_and_batching: point_next,
                claims: new_claims,
                claim_layout: ClaimBufferLayout::from_addresses(addresses),
            }),
        })
    }
}
