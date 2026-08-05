use std::collections::BTreeMap;

use era_cudart::result::CudaResult;

use super::transform::normalize_compiled_circuit_for_gpu;
use super::GpuGKRStorage;
use super::GpuSumcheckRound0LaunchDescriptors;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::BF;
use gpu_cub::cub::device_reduce::Reduce;
use gpu_prover_context::ProverContext;

mod builders;
pub(crate) mod compact;
mod dim_reducing_sumcheck_plan;
pub(crate) mod flat;
// `pub` (not `pub(crate)`): apex proof/whir + e2e tests reach the eq slice and
// backward-workflow types via `gpu_gkr::backward::kernels::…`. Pinned public API.
pub mod kernels;
mod lookup_builders;
// Relocated here from `backward/tests`: apex `expected_specs` builds
// CPU-expected inputs+metadata via these. `#[doc(hidden)] pub` per the
// test-reference policy.
#[doc(hidden)]
pub use lookup_builders::{
    build_lookup_from_vector_input_with_setup_inputs_and_metadata,
    build_lookup_pair_from_base_inputs_inputs_and_metadata,
    build_lookup_pair_from_vector_inputs_inputs_and_metadata,
    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata,
    build_lookup_with_dens_and_setup_expressions_inputs_and_metadata,
};
mod main_layer;
mod scheduled_execution;
pub(crate) mod vm;

// Surface every kernels item via `backward::*` to preserve the previous
// crate-wide path for consumers that read these as `backward::X`. Direct
// imports of `crate::backward::kernels::X` work too.
pub(crate) use kernels::*;
// `pub` re-exports: apex proof/whir + e2e tests import these as
// `gpu_gkr::backward::…`. Pinned public API of the gpu_gkr split.
pub use kernels::{
    eq_group_count, eq_group_tables_len, gkr_dim_reducing_launch_config,
    launch_build_eq_values_from_point, make_deferred_backward_workflow_state, make_eq_sizes,
    ClaimBufferLayout, DeviceClaimPointAndBatching, GkrEqSizes, GpuGKRBackwardExecution,
    GpuGKRBackwardScheduledExecution, GpuGKRDimensionReducingBackwardState,
    GpuGKRMainLayerBackwardState, GpuGKRMainLayerConstraintLinearTerm,
    GpuGKRMainLayerConstraintQuadraticTerm, GpuGKRMainLayerKernelKind, GpuGKRMainLayerKernelPlan,
    GpuGKRMainLayerSumcheckLayerPlan, ScheduledBackwardWorkflowState,
    ScheduledBackwardWorkflowStateHandle, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};

// `pub` (not `pub(crate)`): apex proof builds dimension-reducing inputs / main-
// layer address sets from these helpers.
pub use main_layer::extras::derive_dimension_reducing_inputs;

#[cfg(test)]
use crate::upstream::GKRInputs;
use crate::upstream::{
    high_bits_offset_for_inits_and_teardowns, DimensionReducingInputOutput, Field, FieldExtension,
    GKRAddress, GKRCircuitArtifact, GKRExternalChallenges, OutputType,
};
// `mod builders` is private, so sibling modules reach its builders via this
// re-export as `backward::*`. rustc's `unused_imports` lint mis-flags a
// path-consumed `pub use *`, and the consumed set varies by cfg, so allow it.
#[allow(unused_imports)]
pub(crate) use builders::*;
// apex `expected_specs` compares CPU-expected inputs+metadata built by
// these production helpers. `#[doc(hidden)] pub` per the test-reference
// policy.
#[doc(hidden)]
pub use builders::{
    build_initial_grand_product_without_caches_inputs_and_metadata,
    build_inits_and_teardowns_initial_pair_inputs_and_metadata,
    build_materialize_grand_product_term_expression_inputs_and_metadata,
};
use main_layer::blueprints::build_dimension_reducing_kernel_blueprints_static;
#[cfg(test)]
pub(crate) use main_layer::blueprints::build_main_layer_kernel_blueprints_static;
// `pub` (not `pub(crate)`): apex proof layout builder reads these address sets.
pub use main_layer::blueprints::{
    collect_main_layer_cached_dependencies_per_layer, collect_main_layer_input_addresses_per_layer,
    compute_main_layer_extra_evaluation_addresses_per_layer,
};

impl<B, E> GpuGKRDimensionReducingBackwardState<B, E> {
    pub(super) fn new(
        forward_tracing_ranges: Vec<Range>,
        storage: GpuGKRStorage<B, E>,
        initial_layer_for_sumcheck: usize,
        dimension_reducing_inputs: BTreeMap<
            usize,
            BTreeMap<OutputType, DimensionReducingInputOutput>,
        >,
    ) -> Self {
        let first_output_addr = dimension_reducing_inputs[&initial_layer_for_sumcheck]
            .values()
            .next()
            .and_then(|io| io.output.first())
            .copied()
            .expect("dimension-reducing backward state requires at least one reduced output");
        let next_trace_len_after_reduction = storage.get_ext_poly(first_output_addr).len();
        let pending_layers = dimension_reducing_inputs.into_iter().rev().collect();

        Self {
            forward_tracing_ranges,
            storage,
            pending_layers,
            next_trace_len_after_reduction,
        }
    }
    pub fn storage(&self) -> &GpuGKRStorage<B, E> {
        &self.storage
    }
    #[doc(hidden)]
    pub fn storage_mut(&mut self) -> &mut GpuGKRStorage<B, E> {
        &mut self.storage
    }

    pub fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field + FieldExtension<BF>> GpuGKRDimensionReducingBackwardState<BF, E> {
    /// Hand off to main-layer state with caller-provided lookup challenges.
    /// Production callers use [`into_main_layer_backward_state_static`], which
    /// binds the lookup challenges later through `_static` kernel prepare; this
    /// form exists for tests that verify dynamic challenge binding.
    pub fn into_main_layer_backward_state(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        is_delegation: bool,
    ) -> GpuGKRMainLayerBackwardState<E> {
        // Test-only dynamic-challenge path: fixtures always carry real i&t
        // data, so the canonical top bits are the actual ones.
        let inits_and_teardowns_top_bits = canonical_inits_and_teardowns_top_bits(
            compiled_circuit.memory_layout.teardown_sets.len(),
        );
        self.into_main_layer_backward_state_inner(
            compiled_circuit,
            external_challenges,
            inits_and_teardowns_top_bits,
            lookup_multiplicative_challenge,
            lookup_additive_challenge,
            is_delegation,
            None,
        )
    }

    pub(crate) fn into_main_layer_backward_state_static(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        inits_and_teardowns_top_bits: Vec<u32>,
        is_delegation: bool,
        programs: Option<std::sync::Arc<crate::GkrPrograms>>,
    ) -> GpuGKRMainLayerBackwardState<E> {
        self.into_main_layer_backward_state_inner(
            compiled_circuit,
            external_challenges,
            inits_and_teardowns_top_bits,
            E::ZERO,
            E::ZERO,
            is_delegation,
            programs,
        )
    }

    fn into_main_layer_backward_state_inner(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        // ACTUAL per-circuit i&t top bits: canonical for real i&t data, all
        // zeros for trivial (dummy) unified chunks (CPU-reference parity).
        inits_and_teardowns_top_bits: Vec<u32>,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        is_delegation: bool,
        programs: Option<std::sync::Arc<crate::GkrPrograms>>,
    ) -> GpuGKRMainLayerBackwardState<E> {
        let compiled_circuit = normalize_compiled_circuit_for_gpu(compiled_circuit);
        assert!(
            self.pending_layers.is_empty(),
            "main-layer handoff requires dimension-reducing layers to be exhausted"
        );
        GpuGKRMainLayerBackwardState {
            forward_tracing_ranges: self.forward_tracing_ranges,
            storage: self.storage,
            pending_layers: compiled_circuit
                .layers
                .into_iter()
                .enumerate()
                .rev()
                .collect(),
            trace_len: compiled_circuit.trace_len,
            external_challenges,
            inits_and_teardowns_top_bits: {
                assert_eq!(
                    inits_and_teardowns_top_bits.len(),
                    compiled_circuit.memory_layout.teardown_sets.len(),
                    "i&t top bits must have one entry per teardown set",
                );
                inits_and_teardowns_top_bits
            },
            inits_and_teardowns_address_high_bits_shift: if compiled_circuit
                .memory_layout
                .teardown_sets
                .is_empty()
            {
                0
            } else {
                high_bits_offset_for_inits_and_teardowns::<2>(compiled_circuit.trace_len)
            },
            lookup_multiplicative_challenge,
            lookup_additive_challenge,
            is_delegation,
            programs,
        }
    }
}

impl<B: 'static, E: Field + Reduce> GpuGKRDimensionReducingBackwardState<B, E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: &[DimensionReducingKernelBlueprint<E>],
        batch_challenge_base: Option<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>> {
        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);
        assert!(
            blueprints.len() <= GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
            "fused dimension-reducing backward supports at most {} kernels per layer, got {}",
            GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
            blueprints.len()
        );
        let batch_challenge_count = blueprints
            .iter()
            .map(|blueprint| blueprint.batch_challenge_count)
            .sum::<usize>();
        assert!(
            batch_challenge_count <= GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
            "fused dimension-reducing backward supports at most {} batch challenges per layer, got {}",
            GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
            batch_challenge_count
        );

        let aliases = self.storage.layout.as_ref().map(|layout| &layout.aliases);
        let dim_reducing_ext_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_extension.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .map(|address| {
                aliases
                    .and_then(|aliases| aliases.get(&address))
                    .copied()
                    .unwrap_or(address)
            })
            .collect();
        let kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<E>> = blueprints
            .iter()
            .map(|blueprint| GpuGKRDimensionReducingKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs.clone(),
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges.clone(),
            })
            .collect();

        let round0_batch_template_compact =
            self::compact::encoder::build_round0_batch_compact(blueprints, &self.storage);
        let max_acc_size = trace_len_after_reduction / 2;
        let partials_len = kernels::max_partials_len(max_acc_size);
        let partials = context.alloc(partials_len, AllocationPlacement::Top)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            partials,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            batch_challenge_base,
            kernel_plans,
            folding_addresses: dim_reducing_ext_inputs.into_iter().collect(),
            round0_batch_template_compact,
            round_scratch,
            eq_sizes: GkrEqSizes::zeroed(),
            _phantom: std::marker::PhantomData,
        })
    }

    pub fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let blueprints = build_dimension_reducing_kernel_blueprints_static::<E>(&layer);
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx,
            &blueprints,
            None,
            context,
        )?))
    }
}

impl<E> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub fn kernel_plans(&self) -> &[GpuGKRMainLayerKernelPlan<E>] {
        &self.kernel_plans
    }

    pub fn round0_descriptors(&self) -> &[GpuSumcheckRound0LaunchDescriptors<BF, E>] {
        &self.round0_descriptors
    }
}
#[cfg(test)]
mod tests;
