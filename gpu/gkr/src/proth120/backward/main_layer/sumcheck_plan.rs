use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_gkr_compiler::CanonicalSourceIdentity;
use gpu_hash::keccak256::{transcript_commit_fields, transcript_draw_fields};
use gpu_prover_context::ProverContext;

use super::{release_scratch_views, MainLayerBackwardStatePr};
use crate::backward::window::bank::{drained_eq_sizes, virtual_setup_poly_address};
use crate::backward::{
    make_eq_sizes, max_partials_len, record_active_eq_slot_fold, ClaimBufferLayout,
    GKR_EQ_GROUP_TABLE_LEN,
};
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::proth120::backward::banks::{
    schedule_coefficient_bank_fill_pr, CoefficientBankPr, CoefficientTablesPr,
};
use crate::proth120::backward::eq::{
    launch_eq_high_low_pr, resolve_active_eq_slot_pr, BackwardScratchPr,
};
use crate::proth120::backward::extras::{schedule_layer_extras_pr, LayerExtrasEqPr};
use crate::proth120::backward::gkr_ops;
use crate::proth120::backward::main_continuation::{
    MainContinuationScratchPr, MainContinuationSequencePr, MainLayerRoundStatePr,
};
use crate::proth120::backward::main_tail::{
    bind_main_tail_pr, launch_main_tail_pr, MainTailRuntimePr,
};
use crate::proth120::backward::scheduled_execution::{
    gather_pr, note_device, note_resource, LayerInputPr, ResourceEventPr, ScheduledLayerExecutionPr,
};
use crate::proth120::backward::window::binding::WindowRuntimeScratchPr;
use crate::proth120::backward::window::{
    bind_r0_pr, launch_r0_pr, launch_window_tail_pr, r0_partials_len_pr, R0WindowLaunchPr,
    WindowTailStatePr,
};
use crate::proth120::packed_challenges::PackedChallenges;
use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofSlabPr;
use crate::transform::logical_protocol_address;
use crate::upstream::{GKRAddress, PR};
use crate::GpuGKRStorage;

pub(crate) struct MainLayerPlanPr {
    pub(crate) layer_idx: usize,
    folding_steps: usize,
    programs: Arc<GkrProgramsPr>,
    claim_terms: Vec<(usize, GKRAddress)>,
    folding_evaluation_sources: Vec<GKRAddress>,
    canonical_final_addresses: Vec<(usize, GKRAddress)>,
    eq_low: DeviceAllocation<PR>,
    partials: DeviceAllocation<PR>,
    bank: CoefficientBankPr,
    r0: R0WindowLaunchPr,
    sequence: MainContinuationSequencePr,
}

impl MainLayerBackwardStatePr {
    pub(crate) fn prepare_next_layer_pr(
        &mut self,
        tables: &CoefficientTablesPr,
        scratch: &mut BackwardScratchPr,
        context: &ProverContext,
    ) -> CudaResult<Option<MainLayerPlanPr>> {
        let Some(layer_idx) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        assert!(
            self.trace_len.is_power_of_two() && self.trace_len.trailing_zeros() >= 4,
            "Proth120 main layer trace length is unsupported"
        );
        self.storage.purge_up_to_layer(layer_idx);
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        let programs = Arc::clone(&self.programs);
        let layer_plan = &programs.backward_layers[layer_idx];
        let eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?;
        let mut partials = context.alloc(
            max_partials_len(self.trace_len / 2).max(r0_partials_len_pr(self.trace_len, 1)),
            AllocationPlacement::Top,
        )?;
        note_device(
            context,
            "backward.main",
            Some(layer_idx),
            ResourceEventPr::Allocated,
            "bwd.main.eq_low",
            &eq_low,
        );
        note_device(
            context,
            "backward.main",
            Some(layer_idx),
            ResourceEventPr::Allocated,
            "bwd.main.r0_partials",
            &partials,
        );
        let bank = CoefficientBankPr::new(tables, layer_idx, context)?;
        let r0 = bind_r0_pr(
            &programs.r0[layer_idx],
            None,
            &self.storage,
            folding_steps,
            WindowRuntimeScratchPr {
                eq_high: scratch.eq_high_0(),
                eq_low: eq_low.as_ptr(),
                partials: partials.as_mut_ptr(),
                partials_capacity: partials.len(),
            },
            bank.r0(),
        )
        .unwrap_or_else(|error| panic!("Proth120 R0 binding for layer {layer_idx}: {error:?}"));
        let mapping = &programs.runtime_circuit.scratch_space_mapping_rev;
        let logicalize = |address| logical_protocol_address(address, mapping);
        let folding_evaluation_sources = layer_plan
            .inputs
            .iter()
            .copied()
            .filter(|address| *address != GKRAddress::placeholder())
            .map(logicalize)
            .collect();
        let canonical_final_addresses = programs.main_continuation_window[layer_idx]
            .canonical_source_identities()
            .into_iter()
            .enumerate()
            .map(|(column, identity)| {
                let address = match identity {
                    CanonicalSourceIdentity::Read(place) => read_place_to_gkr_address(&place),
                    CanonicalSourceIdentity::VirtualSetup { kind } => {
                        virtual_setup_poly_address(kind)
                    }
                };
                (column, logicalize(address))
            })
            .collect();
        let claim_terms = layer_plan
            .claims
            .iter()
            .map(|&(offset, address)| (offset, logicalize(address)))
            .collect();
        let sequence = MainContinuationSequencePr::new(
            &programs.main_continuation_window[layer_idx],
            layer_idx,
            folding_steps,
        );
        Ok(Some(MainLayerPlanPr {
            layer_idx,
            folding_steps,
            programs,
            claim_terms,
            folding_evaluation_sources,
            canonical_final_addresses,
            eq_low,
            partials,
            bank,
            r0,
            sequence,
        }))
    }
}

impl MainLayerPlanPr {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn schedule_execute_pr(
        &mut self,
        input: LayerInputPr,
        tables: &CoefficientTablesPr,
        challenges: &PackedChallenges,
        storage: &mut GpuGKRStorage<PR, PR>,
        proof: &mut ProofSlabPr,
        scratch: &mut BackwardScratchPr,
        release_scratch: bool,
        context: &ProverContext,
    ) -> CudaResult<ScheduledLayerExecutionPr> {
        let stream = context.get_exec_stream();
        let layer = self.layer_idx;
        let n = self.folding_steps;
        let LayerInputPr {
            mut seed,
            point_and_batching: point_in,
            claims: claims_in,
            claim_layout,
        } = input;
        let range = Range::new(format!("gkr.proth120.backward.main.layer.{layer}"))?;
        range.start(stream)?;
        assert_eq!(
            point_in.len(),
            n + 1,
            "Proth120 main layer claim point length mismatch"
        );
        assert_eq!(
            claims_in.len(),
            claim_layout.claim_count(),
            "Proth120 main layer claim layout mismatch"
        );
        assert_eq!(
            challenges.challenges().len(),
            9,
            "Proth120 main layer needs the nine packed challenges"
        );
        let desc_pairs: Vec<u32> = self
            .claim_terms
            .iter()
            .flat_map(|(offset, address)| [*offset as u32, claim_layout.claim_idx(address)])
            .collect();
        let mut claim = context.alloc(1, AllocationPlacement::Top)?;
        let mut eq_prefactor = context.alloc(1, AllocationPlacement::Top)?;
        let coeffs = {
            let coeffs = proof.round_coefficients_device_mut(layer);
            assert_eq!(
                coeffs.len(),
                4 * n,
                "Proth120 main layer coefficient range mismatch"
            );
            coeffs.as_mut_ptr()
        };
        let eq_high_0 = scratch.eq_high_0();
        let eq_high_1 = scratch.eq_high_1();
        let eq_low = self.eq_low.as_mut_ptr();
        launch_eq_high_low_pr(
            point_in.as_ptr(),
            3,
            (n - 3) as u32,
            eq_high_0,
            eq_high_1,
            eq_low,
            context,
        )?;
        let mut eq_sizes = make_eq_sizes(n - 3);
        gkr_ops::build_combined_claim(
            &claims_in,
            &point_in[n..n + 1],
            &desc_pairs,
            &mut claim,
            &mut eq_prefactor,
            stream,
        )?;
        drop(claims_in);
        let mut point_out = context.alloc(n + 1, AllocationPlacement::Top)?;
        schedule_coefficient_bank_fill_pr(
            tables,
            &mut self.bank,
            challenges.challenges().as_ptr(),
            point_in[n..].as_ptr(),
            context,
        )?;
        launch_r0_pr(&self.r0, context)?;
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_active_eq_slot_pr(&eq_sizes, eq_low, eq_high_0, eq_high_1);
        launch_window_tail_pr(
            &WindowTailStatePr {
                partials: self.partials.as_ptr(),
                row_tiles: self.r0.reduction_tiles,
                reduced_tensor: self.r0.reduced_tensor,
                prev_claim_coords: point_in.as_ptr(),
                seed: seed.as_mut_ptr(),
                claim: claim.as_mut_ptr(),
                eq_prefactor: eq_prefactor.as_mut_ptr(),
                coeffs_out: coeffs,
                challenges_out: point_out.as_mut_ptr(),
                active_eq_slot_base,
                active_eq_size_before_fold,
            },
            context,
        )?;
        record_active_eq_slot_fold(&mut eq_sizes);
        assert_eq!(
            eq_sizes,
            drained_eq_sizes(make_eq_sizes(n - 3), 1),
            "Proth120 R0 tail eq state mismatch"
        );
        let programs = Arc::clone(&self.programs);
        let continuation = self.bank.continuation();
        let round = MainLayerRoundStatePr {
            claim_point_in: point_in.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coeffs,
            challenges_out: point_out.as_mut_ptr(),
        };
        self.sequence.schedule_windows(
            &programs.main_continuation_window[layer],
            storage,
            MainContinuationScratchPr {
                coefficients: continuation.coefficients,
                coefficient_count: continuation.coefficient_count,
                immediates: continuation.immediates,
                immediate_count: continuation.immediate_count,
                fold_weights: scratch.fold_weights.as_mut_ptr(),
                eq_high: eq_high_0,
                eq_low,
                partials: self.partials.as_mut_ptr(),
                partials_capacity: self.partials.len(),
            },
            round,
            context,
        )?;
        let tail_start = usize::from(self.sequence.tail_start_round());
        let boundary = self
            .sequence
            .final_eq_boundary()
            .expect("Proth120 main continuation did not publish its eq boundary");
        assert_eq!(
            usize::from(boundary.consumer_round),
            tail_start,
            "Proth120 main continuation boundary differs from the tail start"
        );
        assert_eq!(
            boundary.eq_sizes,
            drained_eq_sizes(make_eq_sizes(n - tail_start), 1),
            "Proth120 main tail eq state mismatch"
        );
        let published = self
            .sequence
            .take_published_level()
            .expect("Proth120 main continuation did not publish its final level");
        let main_tail = self.bank.main_tail();
        let bound = bind_main_tail_pr(
            layer,
            &programs.main_tail[layer],
            published,
            tail_start,
            n,
            boundary,
            MainTailRuntimePr {
                eq_low,
                eq_high: eq_high_0.cast_const(),
                prev_claim_coordinates: point_in.as_ptr(),
                seed: seed.as_mut_ptr(),
                claim: claim.as_mut_ptr(),
                eq_prefactor: eq_prefactor.as_mut_ptr(),
                coefficients_out: coeffs,
                challenges_out: point_out.as_mut_ptr(),
                coefficients: main_tail.coefficients,
                coefficient_count: main_tail.coefficient_count,
                immediates: main_tail.immediates,
                immediate_count: main_tail.immediate_count,
            },
            context,
        )?;
        let tail = launch_main_tail_pr(bound, context)?;
        let sources: BTreeMap<GKRAddress, *const PR> = tail
            .final_level()
            .final_evaluation_pointers(self.canonical_final_addresses.iter().copied());
        assert_eq!(
            sources.keys().copied().collect::<BTreeSet<_>>(),
            self.folding_evaluation_sources
                .iter()
                .copied()
                .collect::<BTreeSet<_>>(),
            "Proth120 main tail final sources differ from the layer inputs"
        );
        let addresses: Vec<GKRAddress> = sources.keys().copied().collect();
        let count = addresses.len();
        let mut last = context.alloc(2 * count, AllocationPlacement::Top)?;
        gather_pr(sources.values().copied(), &mut last, stream)?;
        drop(tail);
        {
            let finals = proof.final_step_evaluations_device_mut(layer);
            assert_eq!(
                finals.len(),
                count,
                "Proth120 main layer final evaluation range mismatch"
            );
            gkr_ops::new_claims_linear(&last, &point_out[n - 1..n], finals, stream)?;
        }
        let extra_addresses = proof
            .layout
            .backward_layers
            .iter()
            .find(|layout| layout.layer_idx == layer)
            .expect("Proth120 main layer layout is missing")
            .extra_evaluations_addresses
            .clone();
        let mut new_claims =
            context.alloc(count + extra_addresses.len(), AllocationPlacement::Top)?;
        memory_copy_async(
            &mut new_claims[..count],
            &*proof.final_step_evaluations_device_mut(layer),
            stream,
        )?;
        let extras = if extra_addresses.is_empty() {
            None
        } else {
            let (_, claims_tail) = new_claims.split_at_mut(count);
            Some(schedule_layer_extras_pr(
                &extra_addresses,
                storage,
                point_out.as_ptr(),
                n,
                &LayerExtrasEqPr {
                    eq_high_0,
                    eq_high_1,
                    eq_low,
                },
                claims_tail,
                proof.extra_evaluations_device_mut(layer),
                context,
            )?)
        };
        if release_scratch {
            if let Some((id, counts)) = release_scratch_views(storage) {
                for event in [
                    ResourceEventPr::LastReaderEnqueued,
                    ResourceEventPr::Released,
                ] {
                    note_resource(
                        context,
                        "backward.main",
                        Some(layer),
                        event,
                        "m5.scratch",
                        id,
                        Some(counts),
                    );
                }
            }
        }
        transcript_commit_fields(&mut seed, &new_claims, stream)?;
        transcript_draw_fields(&mut seed, &mut point_out[n..n + 1], stream)?;
        let mut next_addresses = addresses;
        next_addresses.extend(extra_addresses);
        range.end(stream)?;
        drop(extras);
        drop(last);
        drop(claim);
        drop(eq_prefactor);
        drop(point_in);
        Ok(ScheduledLayerExecutionPr {
            layer_idx: layer,
            _tracing_ranges: vec![range],
            next: Some(LayerInputPr {
                seed,
                point_and_batching: point_out,
                claims: new_claims,
                claim_layout: ClaimBufferLayout::from_addresses(next_addresses),
            }),
        })
    }
}
