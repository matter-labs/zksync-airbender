//! Unified GPU-kernel dispatch surface.
//!
//! Collapses the previous twelve single-impl `Gpu*KernelSet` traits into a
//! single trait that bundles every extension-field kernel function pointer
//! (and the single round-update helper) under one `<E>` bound. Today `E4` is
//! the only implementor; adding `E6` is a single new `impl` block.

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::primitives::context::ProverContext;
use crate::primitives::field::E4;
use crate::prover::gkr::backward::compact::{
    ab_gkr_main_round0_flat_compact_e4_kernel,
    ab_gkr_main_round0_flat_constant_compact_e4_kernel,
    ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel,
    ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel,
    ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel,
    ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel,
    ab_gkr_round2_challenges_prelude, GpuGKRMainRound0FlatCompactSignature,
    GpuGKRMainRound0FlatConstantCompactSignature,
    GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature,
    GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature,
    GpuGKRMainRound3FlatConstantUnifiedCompactSignature, GpuGKRRound2ChallengesPreludeSignature,
};
use crate::prover::gkr::backward::kernels::{
    ab_gkr_dim_reducing_build_eq_group_tables_from_pairs_e4_kernel,
    ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel,
    ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel,
    ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel,
    ab_gkr_dim_reducing_fold_eq_values_e4_kernel,
    ab_gkr_dim_reducing_lookup_continuation_e4_kernel,
    ab_gkr_dim_reducing_lookup_round0_e4_kernel,
    ab_gkr_dim_reducing_pairwise_continuation_e4_kernel,
    ab_gkr_dim_reducing_pairwise_round0_e4_kernel,
    ab_gkr_dim_reducing_round0_batched_compact_e4_kernel,
    ab_gkr_dim_reducing_round1_batched_compact_e4_kernel,
    ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel,
    launch_backward_sumcheck_round_update_e4,
    GpuDimensionReducingBuildEqGroupTablesFromPairsSignature,
    GpuDimensionReducingBuildEqGroupTablesFromPointSignature,
    GpuDimensionReducingBuildEqValuesFromGroupTablesSignature,
    GpuDimensionReducingContinuationBatchedCompactSignature,
    GpuDimensionReducingFoldEqValuesSignature, GpuDimensionReducingLookupContinuationSignature,
    GpuDimensionReducingLookupRound0Signature,
    GpuDimensionReducingPairwiseContinuationSignature,
    GpuDimensionReducingPairwiseRound0Signature,
    GpuDimensionReducingRound0BatchedCompactSignature,
    GpuDimensionReducingRound1BatchedCompactSignature,
    GpuDimensionReducingTraceHolderBlockPartialsSignature,
};
use crate::prover::gkr::forward::kernels::{
    ab_gkr_dim_reducing_forward_tower_lookup_e4_kernel,
    ab_gkr_dim_reducing_forward_tower_pairwise_e4_kernel, ab_gkr_flat_forward_layer_e4_kernel,
    ab_gkr_forward_cache_e4_kernel, ab_gkr_virtual_base_accum_e4_kernel,
    schedule_lookup_gamma_consts_prelude_e4, GpuGKRDimensionReducingForwardTowerLookupSignature,
    GpuGKRDimensionReducingForwardTowerPairwiseSignature, GpuGKRFlatForwardLayerSignature,
    GpuGKRForwardCacheSignature, GpuGKRVirtualBaseAccumSignature,
};
use crate::prover::gkr::setup::kernels::{
    ab_gkr_forward_setup_generic_lookup_e4_kernel, GpuGKRForwardSetupGenericLookupSignature,
};

/// Unified surface for every extension-field kernel the prover dispatches on
/// `<E>`. Replaces the previous per-kernel-set traits so that adding a new
/// extension field (e.g. `E6`) means writing one new `impl GpuKernels for E6`
/// rather than touching every kernel module.
#[allow(dead_code)] // several constants are referenced only from #[cfg(test)] launchers
pub(crate) trait GpuKernels: Copy + Sized {
    // --- setup -------------------------------------------------------------
    const FORWARD_SETUP_GENERIC_LOOKUP: GpuGKRForwardSetupGenericLookupSignature<Self>;

    // --- forward -----------------------------------------------------------
    const FORWARD_CACHE: GpuGKRForwardCacheSignature<Self>;
    const VIRTUAL_BASE_ACCUM: GpuGKRVirtualBaseAccumSignature<Self>;
    const DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE:
        GpuGKRDimensionReducingForwardTowerPairwiseSignature<Self>;
    const DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP:
        GpuGKRDimensionReducingForwardTowerLookupSignature<Self>;
    const FLAT_FORWARD_LAYER: GpuGKRFlatForwardLayerSignature<Self>;
    fn schedule_lookup_gamma_consts_prelude(
        gamma: *const Self,
        context: &ProverContext,
    ) -> CudaResult<()>;

    // --- backward (dim-reducing) ------------------------------------------
    const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self>;
    const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self>;
    const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self>;
    const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self>;
    const BUILD_EQ_GROUP_TABLES_FROM_PAIRS:
        GpuDimensionReducingBuildEqGroupTablesFromPairsSignature<Self>;
    const BUILD_EQ_GROUP_TABLES_FROM_POINT:
        GpuDimensionReducingBuildEqGroupTablesFromPointSignature<Self>;
    const BUILD_EQ_VALUES_FROM_GROUP_TABLES:
        GpuDimensionReducingBuildEqValuesFromGroupTablesSignature<Self>;
    const FOLD_EQ_VALUES: GpuDimensionReducingFoldEqValuesSignature<Self>;
    const TRACE_HOLDER_BLOCK_PARTIALS: GpuDimensionReducingTraceHolderBlockPartialsSignature<Self>;
    const ROUND0_BATCHED_COMPACT: GpuDimensionReducingRound0BatchedCompactSignature<Self>;
    const ROUND1_BATCHED_COMPACT: GpuDimensionReducingRound1BatchedCompactSignature<Self>;
    const CONTINUATION_BATCHED_COMPACT:
        GpuDimensionReducingContinuationBatchedCompactSignature<Self>;
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

impl GpuKernels for E4 {
    // --- setup -------------------------------------------------------------
    const FORWARD_SETUP_GENERIC_LOOKUP: GpuGKRForwardSetupGenericLookupSignature<Self> =
        ab_gkr_forward_setup_generic_lookup_e4_kernel;

    // --- forward -----------------------------------------------------------
    const FORWARD_CACHE: GpuGKRForwardCacheSignature<Self> = ab_gkr_forward_cache_e4_kernel;
    const VIRTUAL_BASE_ACCUM: GpuGKRVirtualBaseAccumSignature<Self> =
        ab_gkr_virtual_base_accum_e4_kernel;
    const DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE:
        GpuGKRDimensionReducingForwardTowerPairwiseSignature<Self> =
        ab_gkr_dim_reducing_forward_tower_pairwise_e4_kernel;
    const DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP:
        GpuGKRDimensionReducingForwardTowerLookupSignature<Self> =
        ab_gkr_dim_reducing_forward_tower_lookup_e4_kernel;
    const FLAT_FORWARD_LAYER: GpuGKRFlatForwardLayerSignature<Self> =
        ab_gkr_flat_forward_layer_e4_kernel;

    fn schedule_lookup_gamma_consts_prelude(
        gamma: *const Self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        schedule_lookup_gamma_consts_prelude_e4(gamma, context)
    }

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
    const BUILD_EQ_VALUES_FROM_GROUP_TABLES:
        GpuDimensionReducingBuildEqValuesFromGroupTablesSignature<Self> =
        ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel;
    const FOLD_EQ_VALUES: GpuDimensionReducingFoldEqValuesSignature<Self> =
        ab_gkr_dim_reducing_fold_eq_values_e4_kernel;
    const TRACE_HOLDER_BLOCK_PARTIALS: GpuDimensionReducingTraceHolderBlockPartialsSignature<Self> =
        ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel;
    const ROUND0_BATCHED_COMPACT: GpuDimensionReducingRound0BatchedCompactSignature<Self> =
        ab_gkr_dim_reducing_round0_batched_compact_e4_kernel;
    const ROUND1_BATCHED_COMPACT: GpuDimensionReducingRound1BatchedCompactSignature<Self> =
        ab_gkr_dim_reducing_round1_batched_compact_e4_kernel;
    const CONTINUATION_BATCHED_COMPACT:
        GpuDimensionReducingContinuationBatchedCompactSignature<Self> =
        ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel;

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
