use std::collections::VecDeque;

use super::super::super::{
    GpuGKRStorage, GpuSumcheckRound0LaunchDescriptors, GpuSumcheckRound1PreparedStorage,
    GpuSumcheckRound2PreparedStorage, GpuSumcheckRound3AndBeyondPreparedStorage,
};
use super::shared::{
    ClaimBufferLayout, DeviceClaimPointAndBatching, ScheduledChallengeBuffer,
    ScheduledChallengeStorage, ScheduledDimensionReducingFinalReadback,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::{
    Field, FieldExtension, GKRExternalChallenges, GKRInputs, GKRLayerDescription, Seed,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum GpuGKRMainLayerKernelKind {
    BaseCopy = 0,
    ExtCopy = 1,
    Product = 2,
    MaskIdentity = 3,
    LookupPair = 4,
    LookupBasePair = 5,
    LookupBaseMinusMultiplicityByBase = 6,
    LookupExtMinusMultiplicityByExt = 7,
    LookupUnbalanced = 8,
    LookupWithCachedDensAndSetup = 9,
    EnforceConstraintsMaxQuadratic = 10,
    LinearBaseOutput = 11,
    InitsAndTeardownsInitialPair = 12,
    InitialGrandProductWithoutCaches = 13,
    MaterializeGrandProductTermExpression = 14,
    LookupPairFromBaseInputs = 15,
    LookupWithDensAndSetupExpressions = 16,
    LookupPairFromVectorInputs = 17,
    LookupFromVectorInputWithSetup = 18,
    LookupUnbalancedPairWithVectorInputs = 19,
    LookupExtPair = 20,
    LookupUnbalancedExtension = 21,
    MaxQuadraticBaseOutput = 22,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct GpuGKRMainLayerConstraintQuadraticTerm<E> {
    pub(crate) lhs: u32,
    pub(crate) rhs: u32,
    pub(crate) challenge: E,
    pub(crate) immediate_recipe: ImmediateFactorRecipeStructural,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct GpuGKRMainLayerConstraintLinearTerm<E> {
    pub(crate) input: u32,
    pub(crate) challenge: E,
    pub(crate) immediate_recipe: ImmediateFactorRecipeStructural,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GpuGKRMainLayerConstraintHostMetadata<E> {
    pub(crate) quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(crate) linear_terms: Vec<GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(crate) constant_offset: E,
    pub(crate) constant_offset_recipe: ImmediateFactorRecipeStructural,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GpuGKRMainLayerConstraintChallengeTerm {
    pub(crate) coeff: BF,
    pub(crate) source: GpuGKRMainLayerDeferredChallengeSource,
    pub(crate) power: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GpuGKRMainLayerDeferredChallengeSource {
    LookupMultiplicative,
    LookupAdditive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GpuGKRMainLayerConstraintQuadraticTemplate {
    pub(crate) lhs: u32,
    pub(crate) rhs: u32,
    pub(crate) challenge_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GpuGKRMainLayerConstraintLinearTemplate {
    pub(crate) input: u32,
    pub(crate) challenge_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GpuGKRMainLayerConstraintTemplate {
    pub(crate) quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTemplate>,
    pub(crate) linear_terms: Vec<GpuGKRMainLayerConstraintLinearTemplate>,
    pub(crate) constant_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GpuGKRMainLayerAuxiliaryChallengeSource<E> {
    Immediate(E),
    LookupAdditive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GpuGKRMainLayerConstraintMetadataSource<E> {
    Immediate(GpuGKRMainLayerConstraintHostMetadata<E>),
    Deferred(GpuGKRMainLayerConstraintTemplate),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GpuGKRMainLayerKernelBlueprint<E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
    pub(crate) auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    pub(crate) constraint_metadata_source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuGKRMainLayerRound3Prepared<E> {
    pub(crate) step: usize,
    pub(crate) prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

#[allow(dead_code)]
pub(crate) struct GpuGKRMainLayerRoundScratch<E> {
    pub(crate) claim_point: DeviceAllocation<E>,
    pub(crate) eq_pair_values: DeviceAllocation<E>,
    pub(crate) eq_group_tables: DeviceAllocation<E>,
    pub(crate) eq_values: DeviceAllocation<E>,
    pub(crate) accumulator: DeviceAllocation<E>,
    pub(crate) reduction_output: DeviceAllocation<E>,
    pub(crate) reduction_temp_storage: DeviceAllocation<u8>,
}

pub(crate) struct GpuGKRMainLayerKernelPlan<E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
    #[allow(dead_code)]
    pub(crate) auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    pub(crate) constraint_metadata_source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
    #[allow(dead_code)]
    pub(crate) constraint_metadata_summary: Option<(usize, usize, E)>,
    pub(crate) round1_prepared: GpuSumcheckRound1PreparedStorage<BF, E>,
    pub(crate) round2_prepared: GpuSumcheckRound2PreparedStorage<BF, E>,
    pub(crate) round3_and_beyond_prepared: Vec<GpuGKRMainLayerRound3Prepared<E>>,
}

pub(crate) struct GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) layer_idx: usize,
    #[allow(dead_code)]
    pub(crate) trace_len: usize,
    pub(crate) folding_steps: usize,
    #[allow(dead_code)]
    pub(crate) batch_challenge_base: Option<E>,
    #[allow(dead_code)]
    pub(crate) lookup_multiplicative_challenge: E,
    #[allow(dead_code)]
    pub(crate) lookup_additive_challenge: E,
    #[allow(dead_code)]
    pub(crate) external_challenges_flat: Vec<E>,
    pub(crate) kernel_plans: Vec<GpuGKRMainLayerKernelPlan<E>>,
    #[allow(dead_code)]
    pub(crate) round0_descriptors: Vec<GpuSumcheckRound0LaunchDescriptors<BF, E>>,
    /// Compact flat round-0 descriptor. Consumed by
    /// `launch_main_round0_constant`.
    pub(crate) flat_round0_template_compact: Option<super::super::compact::FlatRound0BuildPlan<E>>,
    /// Inline eval-recipes descriptor passed by value to each round-0 launch.
    pub(crate) flat_recipe_desc:
        Option<Box<crate::prover::gkr::eval_recipes::GpuFlatRecipeEvalDesc>>,
    pub(crate) flat_recipe_count: usize,
    /// Device buffer for eval_recipes output (delegation L0 round 0 only; others write to __constant__).
    pub(crate) flat_coeff_device_buf: Option<DeviceAllocation<E>>,
    /// Whether round 0 uses __constant__ for coefficients (false only for delegation L0).
    pub(crate) flat_use_constant: bool,
    /// Flat continuation plan for rounds 1+ (shared term arrays + per-step source tables).
    pub(crate) flat_continuation_plan: Option<super::super::flat::FlatContinuationBuildPlan<E>>,
    /// Inline eval-recipes descriptor passed by value to each continuation launch.
    pub(crate) flat_cont_recipe_desc:
        Option<Box<crate::prover::gkr::eval_recipes::GpuFlatRecipeEvalDesc>>,
    pub(crate) flat_cont_recipe_count: usize,
    /// Continuation compact descriptors (per step). Consumed by
    /// `launch_main_round3_unified`.
    pub(crate) flat_continuation_unified_descs_compact: Vec<(
        usize,
        Box<super::super::compact::GpuFlatContinuationUnifiedDesc>,
    )>,
    /// Round 1 compact descriptor. Consumed by
    /// `launch_main_round1_unified`.
    pub(crate) flat_round1_unified_desc_compact:
        Option<Box<super::super::compact::GpuFlatRound1UnifiedDesc>>,
    /// Round 2 compact descriptor.
    pub(crate) flat_round2_unified_desc_compact:
        Option<Box<super::super::compact::GpuFlatRound2UnifiedDesc>>,
    pub(crate) round_scratch: GpuGKRMainLayerRoundScratch<E>,
    /// Keepalive slot for scheduling callbacks unrelated to inline recipe descriptors.
    pub(crate) recipe_upload_callbacks: Callbacks<'static>,
    /// When set, `batch_challenge_base_ptr()` returns this raw pointer instead
    /// of `round_scratch.claim_point.as_ptr().add(folding_steps)`. The
    /// workflow_state path uses this to point at the orchestrator-owned
    /// `device_claim_point_in[folding_steps]` so the per-layer
    /// `round_scratch.claim_point` D2D is no longer needed.
    #[allow(dead_code)]
    pub(crate) batch_challenge_base_override_ptr: Option<*const E>,
}

// SAFETY: `batch_challenge_base_override_ptr` only stores a raw pointer into a
// device allocation that the caller keeps alive for the full duration of any
// scheduled stream op consuming this layer plan. The pointer is never
// dereferenced from Rust — it is only forwarded to kernel arguments.
unsafe impl<E> Send for GpuGKRMainLayerSumcheckLayerPlan<E> where E: Send {}
unsafe impl<E> Sync for GpuGKRMainLayerSumcheckLayerPlan<E> where E: Sync {}

pub(crate) struct GpuGKRMainLayerBackwardState<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(crate) forward_tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<BF, E>,
    pub(crate) pending_layers: VecDeque<(usize, GKRLayerDescription)>,
    pub(crate) trace_len: usize,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E>,
    pub(crate) inits_and_teardowns_top_bits: Vec<u32>,
    pub(crate) inits_and_teardowns_address_high_bits_shift: u32,
    pub(crate) lookup_multiplicative_challenge: E,
    pub(crate) lookup_additive_challenge: E,
    pub(crate) num_base_layer_memory_polys: usize,
    pub(crate) num_base_layer_witness_polys: usize,
    pub(crate) is_delegation: bool,
}

pub(crate) struct ScheduledMainLayerExecutionState<E: FieldExtension<BF> + Field> {
    pub(crate) seed: Seed,
    pub(crate) folding_challenges: Vec<E>,
}

pub(crate) struct GpuGKRMainLayerScheduledLayerExecution<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(crate) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(crate) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(crate) batch_challenge_storage: ScheduledChallengeStorage<E>,
    #[allow(dead_code)]
    pub(crate) batch_challenge_buffer: ScheduledChallengeBuffer<E>,
    #[allow(dead_code)]
    pub(crate) final_readback: ScheduledDimensionReducingFinalReadback,
    #[allow(dead_code)]
    pub(crate) flat_coeff_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(crate) recipe_upload_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    // keepalive: shared state is referenced by stream-scheduled callbacks via shared_state_handle.
    pub(crate) shared_state: Box<ScheduledMainLayerExecutionState<E>>,
    /// Device-resident Fiat-Shamir seed (see dim-reducing twin). Taken by the
    /// orchestrator to thread into the next backward layer.
    pub(crate) device_seed: Option<DeviceAllocation<u32>>,
    /// Device-resident `[claim_point || batching_challenge]` for the NEXT
    /// backward layer (see dim-reducing twin). Taken by the orchestrator.
    pub(crate) device_claim_point_for_next_layer: Option<DeviceClaimPointAndBatching<E>>,
    /// Device-resident `current_claims` buffer for the NEXT backward layer.
    pub(crate) device_claims_for_next_layer: Option<DeviceAllocation<E>>,
    /// Explicit address order of `device_claims_for_next_layer`.
    pub(crate) claim_layout_for_next_layer: Option<ClaimBufferLayout>,
}
