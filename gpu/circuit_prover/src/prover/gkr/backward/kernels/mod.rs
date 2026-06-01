mod dim_reducing;
mod encoding;
mod fused_tail;
mod launchers;
mod main_layer;
mod shared;

pub(crate) use dim_reducing::*;
pub(crate) use encoding::*;
pub(crate) use fused_tail::*;
pub(crate) use launchers::*;
pub(crate) use main_layer::*;
pub(crate) use shared::*;

use super::compact::{
    ab_gkr_main_round0_flat_compact_e4_kernel, ab_gkr_main_round0_flat_constant_compact_e4_kernel,
    ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel,
    ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel,
    ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel,
    ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel, ab_gkr_round2_challenges_prelude,
    GpuGKRMainRound0FlatCompactSignature, GpuGKRMainRound0FlatConstantCompactSignature,
    GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature,
    GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature,
    GpuGKRMainRound3FlatConstantUnifiedCompactSignature, GpuGKRRound2ChallengesPreludeSignature,
};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

/// Backward-phase GPU kernels, spanning the dim-reducing kernels (owned by this
/// `backward::kernels` module) and the compact main-layer rounds (owned by the
/// sibling `backward::compact`, imported above). Defined and implemented here;
/// the combined `crate::prover::gkr::GpuKernels` supertrait aggregates this with
/// the setup/forward sub-traits.
#[allow(dead_code)] // several constants are referenced only from #[cfg(test)] launchers
pub(crate) trait BackwardKernels: Copy + Sized {
    // --- backward (dim-reducing) ------------------------------------------
    const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self>;
    const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self>;
    const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self>;
    const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self>;
    const BUILD_EQ_GROUP_TABLES_FROM_PAIRS:
        GpuDimensionReducingBuildEqGroupTablesFromPairsSignature<Self>;
    const BUILD_EQ_GROUP_TABLES_FROM_POINT:
        GpuDimensionReducingBuildEqGroupTablesFromPointSignature<Self>;
    const BUILD_EQ_HIGH_LOW_FROM_POINT: GpuDimensionReducingBuildEqHighLowFromPointSignature<Self>;
    const BUILD_EQ_VALUES_FROM_GROUP_TABLES:
        GpuDimensionReducingBuildEqValuesFromGroupTablesSignature<Self>;
    const FOLD_EQ_VALUES: GpuDimensionReducingFoldEqValuesSignature<Self>;
    const FOLD_EQ_HIGH_GROUP_IN_PLACE: GpuDimensionReducingFoldEqHighGroupSignature<Self>;
    const TRACE_HOLDER_BLOCK_PARTIALS: GpuDimensionReducingTraceHolderBlockPartialsSignature<Self>;
    const ROUND0_BATCHED_COMPACT: GpuDimensionReducingRound0BatchedCompactSignature<Self>;
    const ROUND1_BATCHED_COMPACT: GpuDimensionReducingRound1BatchedCompactSignature<Self>;
    const CONTINUATION_BATCHED_COMPACT: GpuDimensionReducingContinuationBatchedCompactSignature<
        Self,
    >;
    const EQ_INLINE_MATERIALIZE_FOR_TEST: GpuGKREqInlineMaterializeForTestSignature<Self>;
    #[allow(clippy::too_many_arguments)]
    fn launch_backward_sumcheck_round_update(
        reduction_output: &DeviceSlice<Self>,
        prev_claim_coord: &DeviceSlice<Self>,
        seed: &mut DeviceSlice<u32>,
        claim: &mut DeviceSlice<Self>,
        eq_prefactor: &mut DeviceSlice<Self>,
        coeffs_out: &mut DeviceSlice<Self>,
        challenge_out: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()>;

    // --- backward (compact main-layer rounds) ------------------------------
    const MAIN_ROUND0_FLAT_COMPACT: GpuGKRMainRound0FlatCompactSignature<Self>;
    const MAIN_ROUND0_FLAT_CONSTANT_COMPACT: GpuGKRMainRound0FlatConstantCompactSignature<Self>;
    const MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature<Self>;
    const MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature<Self>;
    const ROUND2_CHALLENGES_PRELUDE: GpuGKRRound2ChallengesPreludeSignature<Self>;
    const MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self>;
    const MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self>;
}

impl BackwardKernels for crate::primitives::field::E4 {
    // --- backward (dim-reducing) ------------------------------------------
    const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self> =
        ab_gkr_dim_reducing_pairwise_round0_e4_kernel;
    const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self> =
        ab_gkr_dim_reducing_lookup_round0_e4_kernel;
    const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self> =
        ab_gkr_dim_reducing_pairwise_continuation_e4_kernel;
    const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self> =
        ab_gkr_dim_reducing_lookup_continuation_e4_kernel;
    const BUILD_EQ_GROUP_TABLES_FROM_PAIRS:
        GpuDimensionReducingBuildEqGroupTablesFromPairsSignature<Self> =
        ab_gkr_dim_reducing_build_eq_group_tables_from_pairs_e4_kernel;
    const BUILD_EQ_GROUP_TABLES_FROM_POINT:
        GpuDimensionReducingBuildEqGroupTablesFromPointSignature<Self> =
        ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel;
    const BUILD_EQ_HIGH_LOW_FROM_POINT: GpuDimensionReducingBuildEqHighLowFromPointSignature<Self> =
        ab_gkr_dim_reducing_build_eq_high_low_from_point_e4_kernel;
    const BUILD_EQ_VALUES_FROM_GROUP_TABLES:
        GpuDimensionReducingBuildEqValuesFromGroupTablesSignature<Self> =
        ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel;
    const FOLD_EQ_VALUES: GpuDimensionReducingFoldEqValuesSignature<Self> =
        ab_gkr_dim_reducing_fold_eq_values_e4_kernel;
    const FOLD_EQ_HIGH_GROUP_IN_PLACE: GpuDimensionReducingFoldEqHighGroupSignature<Self> =
        ab_gkr_dim_reducing_fold_eq_high_group_in_place_e4_kernel;
    const TRACE_HOLDER_BLOCK_PARTIALS: GpuDimensionReducingTraceHolderBlockPartialsSignature<Self> =
        ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel;
    const ROUND0_BATCHED_COMPACT: GpuDimensionReducingRound0BatchedCompactSignature<Self> =
        ab_gkr_dim_reducing_round0_batched_compact_e4_kernel;
    const ROUND1_BATCHED_COMPACT: GpuDimensionReducingRound1BatchedCompactSignature<Self> =
        ab_gkr_dim_reducing_round1_batched_compact_e4_kernel;
    const CONTINUATION_BATCHED_COMPACT: GpuDimensionReducingContinuationBatchedCompactSignature<
        Self,
    > = ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel;
    const EQ_INLINE_MATERIALIZE_FOR_TEST: GpuGKREqInlineMaterializeForTestSignature<Self> =
        ab_gkr_eq_inline_materialize_for_test_e4_kernel;

    fn launch_backward_sumcheck_round_update(
        reduction_output: &DeviceSlice<Self>,
        prev_claim_coord: &DeviceSlice<Self>,
        seed: &mut DeviceSlice<u32>,
        claim: &mut DeviceSlice<Self>,
        eq_prefactor: &mut DeviceSlice<Self>,
        coeffs_out: &mut DeviceSlice<Self>,
        challenge_out: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        launch_backward_sumcheck_round_update_e4(
            reduction_output,
            prev_claim_coord,
            seed,
            claim,
            eq_prefactor,
            coeffs_out,
            challenge_out,
            stream,
        )
    }

    // --- backward (compact main-layer rounds) ------------------------------
    const MAIN_ROUND0_FLAT_COMPACT: GpuGKRMainRound0FlatCompactSignature<Self> =
        ab_gkr_main_round0_flat_compact_e4_kernel;
    const MAIN_ROUND0_FLAT_CONSTANT_COMPACT: GpuGKRMainRound0FlatConstantCompactSignature<Self> =
        ab_gkr_main_round0_flat_constant_compact_e4_kernel;
    const MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature<Self> =
        ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel;
    const MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature<Self> =
        ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel;
    const ROUND2_CHALLENGES_PRELUDE: GpuGKRRound2ChallengesPreludeSignature<Self> =
        ab_gkr_round2_challenges_prelude;
    const MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self> =
        ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel;
    const MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self> =
        ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel;
}

#[cfg(test)]
pub(crate) use tests::{
    apply_eq_and_reduce_accumulator, h2d_claim_point_and_batching_from_host, h2d_claims_from_host,
    h2d_lookup_and_constraint_from_shared_state, h2d_seed_from_host,
    populate_backward_workflow_state, take_backward_execution_from_shared_state,
    GpuGKRBackwardExecution,
};

#[cfg(test)]
mod tests;
