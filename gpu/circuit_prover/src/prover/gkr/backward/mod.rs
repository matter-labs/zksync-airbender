use std::collections::BTreeMap;

use era_cudart::result::CudaResult;

use super::transform::normalize_compiled_circuit_for_gpu;
use super::GpuGKRStorage;
#[cfg(test)]
use super::GpuSumcheckRound0LaunchDescriptors;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, Reduce, ReduceOperation};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::ProverContext;

mod builders;
pub(crate) mod compact;
mod dim_reducing_sumcheck_plan;
pub(crate) mod flat;
pub(crate) mod kernels;
mod lookup_builders;
mod main_layer;
mod scheduled_execution;

// Surface every kernels item via `backward::*` to preserve the previous
// crate-wide path for consumers that read these as `backward::X`. Direct
// imports of `crate::prover::gkr::backward::kernels::X` work too.
pub(crate) use kernels::*;

use main_layer::state::{FlatContinuationLaunchSizes, FlatContinuationSizeCheck};

pub(crate) use main_layer::extras::derive_dimension_reducing_inputs;

#[cfg(test)]
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::{
    high_bits_offset_for_inits_and_teardowns, DimensionReducingInputOutput, Field, FieldExtension,
    GKRAddress, GKRCircuitArtifact, GKRExternalChallenges, OutputType,
};
#[cfg(test)]
use crate::upstream::{
    BaseFieldCopyGKRRelation, BatchedGKRKernel, ExtensionCopyGKRRelation, GKRInputs,
    LookupBaseExtMinusBaseExtGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
    LookupBasePairGKRRelation, LookupExtensionMinusMultiplicityByExtensionGKRRelation,
    LookupExtensionPairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
pub(crate) use builders::*;
#[cfg(test)]
use builders::{
    collect_no_cache_linear_form_inputs, validate_no_cache_linear_form_metadata,
    NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
};
use main_layer::blueprints::build_dimension_reducing_kernel_blueprints_static;
#[cfg(test)]
pub(crate) use main_layer::blueprints::build_main_layer_kernel_blueprints_static;
pub(crate) use main_layer::blueprints::{
    collect_main_layer_input_addresses_per_layer,
    collect_main_layer_kernel_output_addresses_per_layer,
    compute_main_layer_orphan_output_addresses_per_layer,
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

    #[cfg(test)]
    pub(crate) fn storage(&self) -> &GpuGKRStorage<B, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field + FieldExtension<BF>> GpuGKRDimensionReducingBackwardState<BF, E> {
    /// Hand off to main-layer state with caller-provided lookup challenges.
    /// Production callers use [`into_main_layer_backward_state_static`], which
    /// binds the lookup challenges later through `_static` kernel prepare; this
    /// form exists for tests that verify dynamic challenge binding.
    #[cfg(test)]
    pub(crate) fn into_main_layer_backward_state(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        is_delegation: bool,
    ) -> GpuGKRMainLayerBackwardState<E> {
        self.into_main_layer_backward_state_inner(
            compiled_circuit,
            external_challenges,
            lookup_multiplicative_challenge,
            lookup_additive_challenge,
            is_delegation,
        )
    }

    pub(crate) fn into_main_layer_backward_state_static(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        is_delegation: bool,
    ) -> GpuGKRMainLayerBackwardState<E> {
        self.into_main_layer_backward_state_inner(
            compiled_circuit,
            external_challenges,
            E::ZERO,
            E::ZERO,
            is_delegation,
        )
    }

    fn into_main_layer_backward_state_inner(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        is_delegation: bool,
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
            inits_and_teardowns_top_bits: canonical_inits_and_teardowns_top_bits(
                compiled_circuit.memory_layout.teardown_sets.len(),
            ),
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
            num_base_layer_memory_polys: compiled_circuit.memory_layout.total_width,
            num_base_layer_witness_polys: compiled_circuit.witness_layout.total_width,
            is_delegation,
        }
    }
}

impl<B: 'static, E: Field + Reduce> GpuGKRDimensionReducingBackwardState<B, E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: Vec<DimensionReducingKernelBlueprint<E>>,
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

        // Pre-allocate one consolidated ext-folding backing for this layer so
        // every per-blueprint `prepare_for_sumcheck_round_*` call slices a
        // view into it instead of allocating per-poly. The compact kernel-arg
        // encoding indexes into this single Arc via a u16 source descriptor +
        // per-launch bases table.
        let dim_reducing_ext_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_extension.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .collect();
        self.storage.register_dim_reducing_inputs_for_layer(
            layer_idx,
            &dim_reducing_ext_inputs,
            context,
        )?;

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(self.storage.prepare_for_sumcheck_round_1(
                &blueprint.inputs,
                layer_idx,
                context,
            )?);
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(if folding_steps >= 3 {
                Some(self.storage.prepare_for_sumcheck_round_2(
                    &blueprint.inputs,
                    layer_idx,
                    context,
                )?)
            } else {
                None
            });
        }

        let mut round3_prepared_all: Vec<Vec<GpuGKRDimensionReducingRound3Prepared<E>>> =
            Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    layer_idx,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }
        }

        let kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<B, E>> = blueprints
            .iter()
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
            .map(
                |(((blueprint, round1_prepared), round2_prepared), round3_and_beyond_prepared)| {
                    GpuGKRDimensionReducingKernelPlan {
                        kind: blueprint.kind,
                        inputs: blueprint.inputs.clone(),
                        batch_challenge_offset: blueprint.batch_challenge_offset,
                        batch_challenge_count: blueprint.batch_challenge_count,
                        batch_challenges: blueprint.batch_challenges.clone(),
                        round1_prepared,
                        round2_prepared,
                        round3_and_beyond_prepared,
                    }
                },
            )
            .collect();

        let round0_batch_template_compact =
            self::compact::encoder::build_round0_batch_compact(&blueprints, &self.storage);
        let round1_batch_template_compact =
            self::compact::encoder::build_round1_batch_compact(&blueprints, &self.storage);
        let continuation_batch_template_compact =
            self::compact::encoder::build_continuation_batch_compact(&blueprints, &self.storage);

        let max_acc_size = trace_len_after_reduction / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;
        let partials_len = kernels::max_partials_len(max_acc_size);
        let partials = context.alloc(partials_len, AllocationPlacement::Top)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            claim_point: context.alloc(folding_steps + 1, AllocationPlacement::Top)?,
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduction_temp_storage_bytes,
                    AllocationPlacement::Top,
                )?,
            partials,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            batch_challenge_base,
            kernel_plans,
            round0_batch_template_compact,
            round1_batch_template_compact,
            continuation_batch_template_compact,
            round_scratch,
            batch_challenge_base_override_ptr: None,
            eq_sizes: GkrEqSizes::zeroed(),
        })
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let blueprints = build_dimension_reducing_kernel_blueprints_static::<E>(&layer);
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}

impl<E> GpuGKRMainLayerSumcheckLayerPlan<E> {
    #[cfg(test)]
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRMainLayerKernelPlan<E>] {
        &self.kernel_plans
    }

    #[cfg(test)]
    pub(crate) fn round0_descriptors(&self) -> &[GpuSumcheckRound0LaunchDescriptors<BF, E>] {
        &self.round0_descriptors
    }

    fn update_flat_cont_sizes_from_source(
        sizes: &mut Option<FlatContinuationLaunchSizes>,
        consistent: &mut bool,
        src: &super::GpuExtensionFieldPolyContinuingSourcePlan<E>,
    ) {
        if src.this_layer_size == 0 || src.next_layer_size == 0 {
            return;
        }
        let candidate =
            FlatContinuationLaunchSizes::from_sizes(src.this_layer_size, src.next_layer_size);
        match sizes {
            None => *sizes = Some(candidate),
            Some(prev) => {
                if *prev != candidate {
                    *consistent = false;
                }
            }
        }
    }

    fn flat_round1_size_check(&self) -> FlatContinuationSizeCheck {
        let Some(plan) = self.flat_continuation_plan.as_ref() else {
            return FlatContinuationSizeCheck::empty();
        };
        let mut sizes = None;
        let mut has_sources = false;
        let mut consistent = true;
        for assignment in plan.source_assignments.iter() {
            if !assignment.is_ext {
                continue;
            }
            let src = &self.kernel_plans[assignment.gate_idx]
                .round1_prepared
                .extension_field_inputs[assignment.input_idx];
            if src.this_layer_size == 0 || src.next_layer_size == 0 {
                continue;
            }
            has_sources = true;
            Self::update_flat_cont_sizes_from_source(&mut sizes, &mut consistent, src);
            if !consistent {
                break;
            }
        }
        FlatContinuationSizeCheck {
            sizes,
            has_sources,
            consistent: consistent && (!has_sources || sizes.is_some()),
        }
    }

    fn flat_round2_size_check(&self) -> FlatContinuationSizeCheck {
        let Some(plan) = self.flat_continuation_plan.as_ref() else {
            return FlatContinuationSizeCheck::empty();
        };
        let mut sizes = None;
        let mut has_sources = false;
        let mut consistent = true;
        for assignment in plan.source_assignments.iter() {
            if !assignment.is_ext {
                continue;
            }
            let src = &self.kernel_plans[assignment.gate_idx]
                .round2_prepared
                .extension_field_inputs[assignment.input_idx];
            if src.this_layer_size == 0 || src.next_layer_size == 0 {
                continue;
            }
            has_sources = true;
            Self::update_flat_cont_sizes_from_source(&mut sizes, &mut consistent, src);
            if !consistent {
                break;
            }
        }
        FlatContinuationSizeCheck {
            sizes,
            has_sources,
            consistent: consistent && (!has_sources || sizes.is_some()),
        }
    }

    fn flat_round3_size_check(&self, step: usize) -> FlatContinuationSizeCheck {
        let Some(plan) = self.flat_continuation_plan.as_ref() else {
            return FlatContinuationSizeCheck::empty();
        };
        let mut sizes = None;
        let mut has_sources = false;
        let mut consistent = true;
        for assignment in plan.source_assignments.iter() {
            let round3 = self.kernel_plans[assignment.gate_idx]
                .round3_and_beyond_prepared
                .iter()
                .find(|r| r.step == step);
            let Some(round3) = round3 else {
                continue;
            };
            let src = if assignment.is_ext {
                &round3.prepared.extension_field_inputs[assignment.input_idx]
            } else {
                &round3.prepared.base_field_inputs[assignment.input_idx]
            };
            if src.this_layer_size == 0 || src.next_layer_size == 0 {
                continue;
            }
            has_sources = true;
            Self::update_flat_cont_sizes_from_source(&mut sizes, &mut consistent, src);
            if !consistent {
                break;
            }
        }
        FlatContinuationSizeCheck {
            sizes,
            has_sources,
            consistent: consistent && (!has_sources || sizes.is_some()),
        }
    }
}

const fn main_layer_kind_batch_challenge_count(kind: GpuGKRMainLayerKernelKind) -> usize {
    match kind {
        GpuGKRMainLayerKernelKind::LookupPair
        | GpuGKRMainLayerKernelKind::LookupBasePair
        | GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase
        | GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt
        | GpuGKRMainLayerKernelKind::LookupUnbalanced
        | GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup
        | GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs
        | GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions
        | GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs
        | GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup
        | GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs
        | GpuGKRMainLayerKernelKind::LookupExtPair
        | GpuGKRMainLayerKernelKind::LookupUnbalancedExtension => 2,
        _ => 1,
    }
}

pub(super) fn packed_main_layer_batch_challenge_len<E>(
    kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
) -> usize {
    kernel_plans
        .iter()
        .map(|kernel| {
            let count = main_layer_kind_batch_challenge_count(kernel.kind);
            assert_eq!(
                kernel.batch_challenge_count, count,
                "kernel {:?} has unexpected batch-challenge count",
                kernel.kind
            );
            count
        })
        .sum()
}

#[cfg(test)]
pub(crate) use tests::{
    build_lookup_from_vector_input_with_setup_inputs_and_metadata,
    build_lookup_pair_from_base_inputs_inputs_and_metadata,
    build_lookup_pair_from_vector_inputs_inputs_and_metadata,
    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata,
    build_lookup_with_dens_and_setup_expressions_inputs_and_metadata,
};

#[cfg(test)]
mod tests;
