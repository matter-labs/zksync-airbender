use era_cudart::result::CudaResult;

use crate::upstream::GKRAddress;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContext;

use super::super::kernels::*;
use super::super::main_continuation::MainContinuationWindowSequence;
use super::super::window::binding::{window_partials_len, WindowRuntimeScratch};
impl GpuGKRMainLayerBackwardState {
    fn prepare_layer(
        &mut self,
        layer_idx: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerSumcheckLayerPlan> {
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        let layer_plan = &self.programs.backward_layers[layer_idx];
        let main_execution_plan =
            super::execution_plan::derive_main_layer_execution_plan(folding_steps);
        assert!(self.programs.main_continuation_window_programs_ready());
        assert!(self.programs.main_tail_programs_ready());

        // The shared buffer holds the larger of the continuation partials and
        // the window tensor plus its split-tail reduction target.
        let partials_len = super::super::kernels::max_partials_len(self.trace_len / 2)
            .max(window_partials_len(self.trace_len));
        let mut round_scratch = GpuGKRMainLayerRoundScratch {
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            partials: context.alloc(partials_len, AllocationPlacement::Top)?,
        };
        assert!(
            round_scratch.partials.len() >= window_partials_len(self.trace_len),
            "the shared partials buffer cannot hold the window producer's tensor"
        );

        let program = self.programs.window_layer(layer_idx);
        let bank = super::super::window::bank::prepare_window_coefficient_bank(
            program,
            &self.inits_and_teardowns_top_bits,
            context,
        )?;
        let window = super::super::window::binding::bind_window_launch(
            program,
            &self.storage,
            folding_steps,
            WindowRuntimeScratch {
                eq_low: round_scratch.eq_low_group.as_ptr(),
                partials: round_scratch.partials.as_mut_ptr(),
                partials_capacity: round_scratch.partials.len(),
            },
        )
        .unwrap_or_else(|error| panic!("windowed R0 binding for layer {layer_idx}: {error:?}"));
        let windowed_r0 = WindowedR0Launch { bank, window };
        let main_continuation_bank =
            super::super::window::bank::prepare_main_continuation_coefficient_bank(
                self.programs.continuation_layer(layer_idx),
                &self.inits_and_teardowns_top_bits,
                context,
            )?;

        let logicalize = |address| {
            self.storage
                .layout
                .as_ref()
                .map(|layout| {
                    crate::transform::logical_protocol_address(
                        address,
                        &layout.scratch_space_mapping_rev,
                    )
                })
                .unwrap_or(address)
        };
        let folding_evaluation_sources = layer_plan
            .inputs
            .iter()
            .copied()
            .filter(|address| *address != GKRAddress::placeholder())
            .map(logicalize)
            .collect();
        let canonical_final_addresses = self
            .programs
            .main_continuation_window_layer(layer_idx)
            .canonical_source_identities()
            .into_iter()
            .enumerate()
            .map(|(column, identity)| {
                let address = match identity {
                    gpu_gkr_compiler::CanonicalSourceIdentity::Read(place) => {
                        crate::forward::vm::lower::read_place_to_gkr_address(&place)
                    }
                    gpu_gkr_compiler::CanonicalSourceIdentity::VirtualSetup { kind } => {
                        super::super::window::bank::virtual_setup_poly_address(kind)
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

        Ok(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            folding_steps,
            claim_terms,
            folding_evaluation_sources,
            canonical_final_addresses,
            round_scratch,
            windowed_r0,
            main_continuation_bank,
            main_execution_plan,
            main_continuation: MainContinuationWindowSequence::new(
                main_execution_plan,
                layer_idx,
                self.programs.clone(),
            ),
            main_tail_program: self.programs.resolve_main_tail_programs().layers[layer_idx].clone(),
            main_tail_launched: None,
            eq_sizes: GkrEqSizes::zeroed(),
        })
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan>> {
        let Some(layer_idx) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        assert!(self.trace_len.trailing_zeros() >= 4);

        Ok(Some(self.prepare_layer(layer_idx, context)?))
    }
}
