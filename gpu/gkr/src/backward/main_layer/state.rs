use era_cudart::result::CudaResult;

use crate::upstream::GKRAddress;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContext;

use super::super::kernels::*;
use super::super::window::binding::window_partials_len;

impl GpuGKRMainLayerBackwardState {
    fn prepare_layer(
        &mut self,
        layer_idx: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerSumcheckLayerPlan> {
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        let layer_plan = &self.programs.backward_layers[layer_idx];

        // Both arms publish into the same buffer, so it holds whichever layout is
        // larger: the per-round warp partials, or the window producer's row-tile-
        // major tensor plus the split tail arm's reduction target.
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

        let bwd_vm_round0 = super::super::vm::production_bind::build_bwd_vm_round0(
            &self.storage,
            self.programs.r0_layer(layer_idx),
            1usize << (folding_steps - 1),
            round_scratch.eq_low_group.as_ptr(),
            make_eq_sizes(folding_steps - 1),
            round_scratch.partials.as_mut_ptr(),
            &self.inits_and_teardowns_top_bits,
            context,
        )?;
        let bwd_vm_ext = super::super::vm::production_bind::build_bwd_vm_ext_rounds(
            &self.storage,
            self.programs.continuation_layer(layer_idx),
            folding_steps,
            round_scratch.eq_low_group.as_ptr(),
            round_scratch.partials.as_mut_ptr(),
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
            round_scratch,
            bwd_vm_round0,
            bwd_vm_ext,
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
