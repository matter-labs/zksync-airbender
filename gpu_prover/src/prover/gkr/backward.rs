use std::cell::UnsafeCell;
use std::collections::{BTreeMap, VecDeque};
use std::ptr::null;
use std::sync::{Arc, Mutex};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRRelation,
    NoFieldMaxQuadraticConstraintsGKRRelation, OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::SumcheckIntermediateProofValues;
use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    ExtensionCopyGKRRelation, GKRInputs, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use prover::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use prover::transcript::Seed;

use super::{
    alloc_host_and_schedule_copy, GpuBaseFieldPolySource,
    GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuGKRStorage, GpuSumcheckRound0HostLaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1PreparedStorage,
    GpuSumcheckRound1ScheduledLaunchDescriptors, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, Reduce, ReduceOperation,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E2, E4, E6};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

#[derive(Debug, Clone, PartialEq, Eq)]
struct DimensionReducingKernelBlueprint<E> {
    inputs: GKRInputs,
    batch_challenge_offset: usize,
    batch_challenge_count: usize,
    batch_challenges: Vec<E>,
}

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
    LookupUnbalanced = 7,
    LookupWithCachedDensAndSetup = 8,
    EnforceConstraintsMaxQuadratic = 9,
}

impl GpuGKRMainLayerKernelKind {
    const fn as_u32(self) -> u32 {
        self as u32
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct GpuGKRMainLayerConstraintQuadraticTerm<E> {
    pub(crate) lhs: u32,
    pub(crate) rhs: u32,
    pub(crate) challenge: E,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct GpuGKRMainLayerConstraintLinearTerm<E> {
    pub(crate) input: u32,
    pub(crate) challenge: E,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GpuGKRMainLayerConstraintHostMetadata<E> {
    quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    linear_terms: Vec<GpuGKRMainLayerConstraintLinearTerm<E>>,
    constant_offset: E,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GpuGKRMainLayerConstraintChallengeTerm {
    coeff: BF,
    power: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GpuGKRMainLayerConstraintQuadraticTemplate {
    lhs: u32,
    rhs: u32,
    challenge_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GpuGKRMainLayerConstraintLinearTemplate {
    input: u32,
    challenge_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GpuGKRMainLayerConstraintTemplate {
    quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTemplate>,
    linear_terms: Vec<GpuGKRMainLayerConstraintLinearTemplate>,
    constant_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GpuGKRMainLayerAuxiliaryChallengeSource<E> {
    Immediate(E),
    LookupAdditive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum GpuGKRMainLayerConstraintMetadataSource<E> {
    Immediate(GpuGKRMainLayerConstraintHostMetadata<E>),
    Deferred(GpuGKRMainLayerConstraintTemplate),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GpuGKRMainLayerKernelBlueprint<E> {
    kind: GpuGKRMainLayerKernelKind,
    inputs: GKRInputs,
    batch_challenge_offset: usize,
    batch_challenge_count: usize,
    batch_challenges: Vec<E>,
    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    constraint_metadata_source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
}

#[derive(Clone, Debug)]
struct GpuGKRDimensionReducingRound3Prepared<E> {
    step: usize,
    prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

struct GpuGKRDimensionReducingRoundScratch<E> {
    claim_point: DeviceAllocation<E>,
    eq_values: DeviceAllocation<E>,
    contributions: DeviceAllocation<E>,
    weighted_rows: DeviceAllocation<E>,
    reduction_output: DeviceAllocation<E>,
    reduction_temp_storage: DeviceAllocation<u8>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuGKRDimensionReducingKernelPlan<B, E> {
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
    round1_prepared: GpuSumcheckRound1PreparedStorage<B, E>,
    round2_prepared: Option<GpuSumcheckRound2PreparedStorage<B, E>>,
    round3_and_beyond_prepared: Vec<GpuGKRDimensionReducingRound3Prepared<E>>,
}

pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) layer_idx: usize,
    pub(crate) trace_len_after_reduction: usize,
    pub(crate) folding_steps: usize,
    kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<B, E>>,
    round0_descriptors: Vec<GpuSumcheckRound0ScheduledLaunchDescriptors<B, E>>,
    round_scratch: GpuGKRDimensionReducingRoundScratch<E>,
}

pub(crate) struct GpuGKRDimensionReducingBackwardState<B, E> {
    #[allow(dead_code)] // Keeps queued forward ranges alive until the stream consumes them.
    forward_tracing_ranges: Vec<Range>,
    storage: GpuGKRStorage<B, E>,
    pending_layers: VecDeque<(usize, BTreeMap<OutputType, DimensionReducingInputOutput>)>,
    next_trace_len_after_reduction: usize,
}

pub(crate) struct GpuGKRDimensionReducingLayerExecution<E: FieldExtension<BF> + Field> {
    pub(crate) proof: SumcheckIntermediateProofValues<BF, E>,
    pub(crate) new_claims: BTreeMap<GKRAddress, E>,
    pub(crate) new_claim_point: Vec<E>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

enum ScheduledDimensionReducingRoundState<B, E> {
    Round1 {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>>,
    },
    Round2 {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>>,
    },
    Round3AndBeyond {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>,
    },
}

enum HostScheduledDimensionReducingRoundState {
    Round1 { callbacks: Callbacks<'static> },
    Round2 { callbacks: Callbacks<'static> },
    Round3AndBeyond { callbacks: Callbacks<'static> },
}

struct ScheduledDimensionReducingReductionState<E> {
    callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    _phantom: std::marker::PhantomData<E>,
}

struct SharedChallengeDevice<E> {
    device: UnsafeCell<DeviceAllocation<E>>,
}

// SAFETY: uploads and kernel launches are enqueued from the host in stream order.
// SharedChallengeDevice only exposes raw pointers or temporary slice views for those enqueues.
unsafe impl<E: Send> Send for SharedChallengeDevice<E> {}
// SAFETY: the wrapped device allocation lives for the duration of all queued work and is only
// accessed through explicit pointer/slice helpers.
unsafe impl<E: Sync> Sync for SharedChallengeDevice<E> {}

impl<E> SharedChallengeDevice<E> {
    fn new(device: DeviceAllocation<E>) -> Self {
        Self {
            device: UnsafeCell::new(device),
        }
    }

    fn as_ptr(&self, offset: usize) -> *const E {
        // SAFETY: every offset is validated when the buffer view is created.
        unsafe { (&*self.device.get()).as_ptr().add(offset) }
    }

    unsafe fn slice_mut(&self, offset: usize, len: usize) -> &mut DeviceSlice<E> {
        // SAFETY: callers guarantee the requested range is within bounds and that using this
        // temporary mutable view only serves to enqueue stream-ordered H2D copies.
        &mut (&mut *self.device.get())[offset..offset + len]
    }

    #[cfg(test)]
    unsafe fn slice(&self, offset: usize, len: usize) -> &DeviceSlice<E> {
        // SAFETY: callers guarantee the requested range is within bounds.
        &(&*self.device.get())[offset..offset + len]
    }
}

struct ScheduledChallengeBuffer<E> {
    callbacks: Arc<Callbacks<'static>>,
    device: Arc<SharedChallengeDevice<E>>,
    offset: usize,
    len: usize,
}

impl<E> ScheduledChallengeBuffer<E> {
    fn as_ptr(&self) -> *const E {
        self.device.as_ptr(self.offset)
    }

    #[cfg(test)]
    fn device_slice(&self) -> &DeviceSlice<E> {
        // SAFETY: buffer views only expose ranges created from valid packed offsets.
        unsafe { self.device.slice(self.offset, self.len) }
    }
}

struct HostScheduledChallengeBuffer<E> {
    callbacks: Arc<Callbacks<'static>>,
    device: Arc<SharedChallengeDevice<E>>,
    #[allow(dead_code)]
    _phantom: std::marker::PhantomData<E>,
}

struct ScheduledUpload<T> {
    callbacks: Callbacks<'static>,
    device: DeviceAllocation<T>,
}

struct HostScheduledUpload<T> {
    callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    _phantom: std::marker::PhantomData<T>,
}

struct ScheduledMainLayerConstraintMetadataUpload<E> {
    callbacks: Callbacks<'static>,
    quadratic_terms: ScheduledUpload<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    linear_terms: ScheduledUpload<GpuGKRMainLayerConstraintLinearTerm<E>>,
    constant_offset: ScheduledUpload<E>,
}

struct HostScheduledMainLayerConstraintMetadataUpload<E> {
    callbacks: Callbacks<'static>,
    quadratic_terms: HostScheduledUpload<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    linear_terms: HostScheduledUpload<GpuGKRMainLayerConstraintLinearTerm<E>>,
    constant_offset: HostScheduledUpload<E>,
}

struct ScheduledDimensionReducingFinalReadback<E> {
    callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    _phantom: std::marker::PhantomData<E>,
}

struct ScheduledDimensionReducingLayerExecutionState<E: FieldExtension<BF> + Field> {
    seed: Seed,
    claim: E,
    eq_prefactor: E,
    folding_challenges: Vec<E>,
    internal_round_coefficients: Vec<[E; 4]>,
    result: Option<GpuGKRDimensionReducingLayerExecution<E>>,
}

struct ScheduledMainLayerExecutionState<E: FieldExtension<BF> + Field> {
    seed: Seed,
    claim: E,
    eq_prefactor: E,
    folding_challenges: Vec<E>,
    internal_round_coefficients: Vec<[E; 4]>,
    result: Option<GpuGKRMainLayerExecution<E>>,
}

pub(crate) struct GpuGKRDimensionReducingScheduledLayerExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    // Keeps layer-start callbacks alive until the stream consumes them.
    start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    // Keeps per-kernel batch challenge uploads alive until the stream consumes them.
    batch_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    // Keeps queued per-round folding challenge uploads alive until the stream consumes them.
    round_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    // Keeps queued descriptor uploads and their callbacks alive until the stream consumes them.
    round_states: Vec<ScheduledDimensionReducingRoundState<B, E>>,
    #[allow(dead_code)]
    // Keeps round reduction uploads/readbacks and callbacks alive until the stream consumes them.
    reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    // Keeps final-step readbacks and callback alive until the stream consumes them.
    final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    // Keeps round-0 descriptor callbacks alive until the stream consumes them.
    round0_callbacks: Vec<Callbacks<'static>>,
    shared_state: Arc<Mutex<ScheduledDimensionReducingLayerExecutionState<E>>>,
}

#[derive(Clone, Debug)]
struct GpuGKRMainLayerRound3Prepared<E> {
    step: usize,
    prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

struct GpuGKRMainLayerRoundScratch<E> {
    claim_point: DeviceAllocation<E>,
    eq_values: DeviceAllocation<E>,
    contributions: DeviceAllocation<E>,
    weighted_rows: DeviceAllocation<E>,
    reduction_output: DeviceAllocation<E>,
    reduction_temp_storage: DeviceAllocation<u8>,
}

pub(crate) struct GpuGKRMainLayerKernelPlan<E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    constraint_metadata_source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
    round1_prepared: GpuSumcheckRound1PreparedStorage<BF, E>,
    round2_prepared: GpuSumcheckRound2PreparedStorage<BF, E>,
    round3_and_beyond_prepared: Vec<GpuGKRMainLayerRound3Prepared<E>>,
}

pub(crate) struct GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) layer_idx: usize,
    pub(crate) trace_len: usize,
    pub(crate) folding_steps: usize,
    kernel_plans: Vec<GpuGKRMainLayerKernelPlan<E>>,
    round0_descriptors: Vec<GpuSumcheckRound0ScheduledLaunchDescriptors<BF, E>>,
    round_scratch: GpuGKRMainLayerRoundScratch<E>,
}

impl<E: Copy + Field> GpuGKRMainLayerKernelPlan<E> {
    pub(crate) fn auxiliary_challenge_summary(&self) -> Option<E> {
        match self.auxiliary_challenge_source {
            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => Some(value),
            GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => None,
        }
    }

    pub(crate) fn constraint_metadata_summary(&self) -> Option<(usize, usize, E)> {
        match self.constraint_metadata_source.as_ref() {
            Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => Some((
                metadata.quadratic_terms.len(),
                metadata.linear_terms.len(),
                metadata.constant_offset,
            )),
            Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(metadata)) => Some((
                metadata.quadratic_terms.len(),
                metadata.linear_terms.len(),
                E::ZERO,
            )),
            None => None,
        }
    }
}

pub(crate) struct GpuGKRMainLayerBackwardState<E> {
    #[allow(dead_code)]
    forward_tracing_ranges: Vec<Range>,
    storage: GpuGKRStorage<BF, E>,
    pending_layers: VecDeque<(usize, GKRLayerDescription)>,
    trace_len: usize,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
}

pub(crate) struct GpuGKRMainLayerExecution<E: FieldExtension<BF> + Field> {
    pub(crate) proof: SumcheckIntermediateProofValues<BF, E>,
    pub(crate) new_claims: BTreeMap<GKRAddress, E>,
    pub(crate) new_claim_point: Vec<E>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

#[allow(dead_code)]
// Keeps per-round async descriptor uploads alive until the stream completes the round.
enum ScheduledMainLayerRoundState<E> {
    Round1 {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<BF, E>>,
    },
    Round2 {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<BF, E>>,
    },
    Round3AndBeyond {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>,
    },
}

enum HostScheduledMainLayerRoundState {
    Round1 { callbacks: Callbacks<'static> },
    Round2 { callbacks: Callbacks<'static> },
    Round3AndBeyond { callbacks: Callbacks<'static> },
}

pub(crate) struct GpuGKRMainLayerScheduledLayerExecution<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    batch_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    auxiliary_uploads: Vec<ScheduledUpload<E>>,
    #[allow(dead_code)]
    constraint_uploads: Vec<Option<ScheduledMainLayerConstraintMetadataUpload<E>>>,
    #[allow(dead_code)]
    round_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    round_states: Vec<ScheduledMainLayerRoundState<E>>,
    #[allow(dead_code)]
    reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    // Keeps round-0 descriptor callbacks alive until the stream consumes them.
    round0_callbacks: Vec<Callbacks<'static>>,
    shared_state: Arc<Mutex<ScheduledMainLayerExecutionState<E>>>,
}

pub(crate) struct ScheduledBackwardWorkflowState<E: FieldExtension<BF> + Field> {
    claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    current_claims: BTreeMap<GKRAddress, E>,
    current_claim_point: Vec<E>,
    current_batching_challenge: E,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
    seed: Seed,
    proofs: BTreeMap<usize, SumcheckIntermediateProofValues<BF, E>>,
}

pub(crate) struct GpuGKRBackwardExecution<E: FieldExtension<BF> + Field> {
    pub(crate) proofs: BTreeMap<usize, SumcheckIntermediateProofValues<BF, E>>,
    pub(crate) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(crate) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

pub(crate) struct GpuGKRBackwardScheduledExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    dimension_reducing_layers: Vec<GpuGKRDimensionReducingScheduledLayerExecution<B, E>>,
    #[allow(dead_code)]
    main_layers: Vec<GpuGKRMainLayerScheduledLayerExecution<E>>,
    shared_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
}

pub(crate) struct GpuGKRDimensionReducingHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    batch_challenge_buffers: Vec<HostScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    round_challenge_buffers: Vec<HostScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    round_states: Vec<HostScheduledDimensionReducingRoundState>,
    #[allow(dead_code)]
    _phantom: std::marker::PhantomData<B>,
    #[allow(dead_code)]
    reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    // Keeps round-0 descriptor HostFn closures alive until the stream executes them.
    round0_callbacks: Vec<Callbacks<'static>>,
    #[allow(dead_code)]
    shared_state: Arc<Mutex<ScheduledDimensionReducingLayerExecutionState<E>>>,
}

pub(crate) struct GpuGKRMainLayerHostKeepalive<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    batch_challenge_buffers: Vec<HostScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    auxiliary_uploads: Vec<HostScheduledUpload<E>>,
    #[allow(dead_code)]
    constraint_uploads: Vec<Option<HostScheduledMainLayerConstraintMetadataUpload<E>>>,
    #[allow(dead_code)]
    round_challenge_buffers: Vec<HostScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    round_states: Vec<HostScheduledMainLayerRoundState>,
    #[allow(dead_code)]
    reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    // Keeps round-0 descriptor HostFn closures alive until the stream executes them.
    round0_callbacks: Vec<Callbacks<'static>>,
    #[allow(dead_code)]
    shared_state: Arc<Mutex<ScheduledMainLayerExecutionState<E>>>,
}

pub(crate) struct GpuGKRBackwardHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    dimension_reducing_layers: Vec<GpuGKRDimensionReducingHostKeepalive<B, E>>,
    #[allow(dead_code)]
    main_layers: Vec<GpuGKRMainLayerHostKeepalive<E>>,
    #[allow(dead_code)]
    shared_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
}

impl<E> ScheduledBackwardWorkflowState<E>
where
    E: FieldExtension<BF> + Field,
{
    pub(crate) fn deferred() -> Self {
        Self {
            claims_for_layers: BTreeMap::new(),
            points_for_claims_at_layer: BTreeMap::new(),
            current_claims: BTreeMap::new(),
            current_claim_point: Vec::new(),
            current_batching_challenge: E::ZERO,
            lookup_additive_challenge: E::ZERO,
            constraint_batch_challenge: E::ZERO,
            seed: Seed::default(),
            proofs: BTreeMap::new(),
        }
    }
}

pub(crate) fn make_deferred_backward_workflow_state<E>(
) -> Arc<Mutex<ScheduledBackwardWorkflowState<E>>>
where
    E: FieldExtension<BF> + Field,
{
    Arc::new(Mutex::new(ScheduledBackwardWorkflowState::deferred()))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn populate_backward_workflow_state<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    initial_output_layer_idx: usize,
    top_layer_claims: BTreeMap<GKRAddress, E>,
    evaluation_point: Vec<E>,
    seed: Seed,
    batching_challenge: E,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
) where
    E: FieldExtension<BF> + Field,
{
    let mut state = shared_state.lock().unwrap();
    state.claims_for_layers =
        BTreeMap::from([(initial_output_layer_idx, top_layer_claims.clone())]);
    state.points_for_claims_at_layer =
        BTreeMap::from([(initial_output_layer_idx, evaluation_point.clone())]);
    state.current_claims = top_layer_claims;
    state.current_claim_point = evaluation_point;
    state.current_batching_challenge = batching_challenge;
    state.lookup_additive_challenge = lookup_additive_challenge;
    state.constraint_batch_challenge = constraint_batch_challenge;
    state.seed = seed;
}

pub(crate) fn clone_backward_claim_point_for_layer<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    layer_idx: usize,
) -> Vec<E>
where
    E: FieldExtension<BF> + Field + Clone,
{
    shared_state
        .lock()
        .unwrap()
        .points_for_claims_at_layer
        .get(&layer_idx)
        .cloned()
        .expect("missing backward claim point for layer")
}

pub(crate) fn fill_backward_claim_point_for_layer<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    layer_idx: usize,
    dst: &mut [E],
) where
    E: FieldExtension<BF> + Field + Copy,
{
    let state = shared_state.lock().unwrap();
    let src = state
        .points_for_claims_at_layer
        .get(&layer_idx)
        .expect("missing backward claim point for layer");
    assert_eq!(
        dst.len(),
        src.len(),
        "backward claim point destination length mismatch"
    );
    dst.copy_from_slice(src);
}

pub(crate) fn clone_backward_claims_for_layer<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    layer_idx: usize,
) -> BTreeMap<GKRAddress, E>
where
    E: FieldExtension<BF> + Field + Clone,
{
    shared_state
        .lock()
        .unwrap()
        .claims_for_layers
        .get(&layer_idx)
        .cloned()
        .expect("missing backward claims for layer")
}

pub(crate) fn current_backward_batching_challenge<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
) -> E
where
    E: FieldExtension<BF> + Field + Copy,
{
    shared_state.lock().unwrap().current_batching_challenge
}

pub(crate) fn current_backward_seed<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
) -> Seed
where
    E: FieldExtension<BF> + Field,
{
    shared_state.lock().unwrap().seed
}

pub(crate) fn apply_base_layer_extra_evaluations_to_workflow_state<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    extra_evaluations_from_caching_relations: &BTreeMap<GKRAddress, E>,
    extra_evaluations_transcript_batches: &[Vec<E>],
) where
    E: FieldExtension<BF> + Field + Copy,
    [(); E::DEGREE]: Sized,
{
    if extra_evaluations_from_caching_relations.is_empty() {
        return;
    }

    let mut state = shared_state.lock().unwrap();
    for transcript_input in extra_evaluations_transcript_batches.iter() {
        commit_field_els::<BF, E>(&mut state.seed, transcript_input);
    }

    {
        let layer_0_claims = state
            .claims_for_layers
            .get_mut(&0)
            .expect("missing layer-0 claims before base-layer transcript update");
        layer_0_claims.extend(
            extra_evaluations_from_caching_relations
                .iter()
                .map(|(address, value)| (*address, *value)),
        );
    }
    state.current_claims.extend(
        extra_evaluations_from_caching_relations
            .iter()
            .map(|(address, value)| (*address, *value)),
    );
    state
        .proofs
        .get_mut(&0)
        .expect("missing layer-0 proof before base-layer transcript update")
        .extra_evaluations_from_caching_relations =
        extra_evaluations_from_caching_relations.clone();
}

pub(crate) fn take_backward_execution_from_shared_state<E>(
    shared_state: &Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
) -> GpuGKRBackwardExecution<E>
where
    E: FieldExtension<BF> + Field,
{
    let mut state = shared_state.lock().unwrap();
    GpuGKRBackwardExecution {
        proofs: std::mem::take(&mut state.proofs),
        claims_for_layers: std::mem::take(&mut state.claims_for_layers),
        points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
        next_batching_challenge: state.current_batching_challenge,
        updated_seed: state.seed,
    }
}

fn challenge_buffer_into_host_keepalive<E>(
    buffer: ScheduledChallengeBuffer<E>,
) -> HostScheduledChallengeBuffer<E> {
    let ScheduledChallengeBuffer {
        callbacks,
        device,
        offset: _,
        len: _,
    } = buffer;
    HostScheduledChallengeBuffer {
        callbacks,
        device,
        _phantom: std::marker::PhantomData,
    }
}

fn upload_into_host_keepalive<T>(upload: ScheduledUpload<T>) -> HostScheduledUpload<T> {
    let ScheduledUpload {
        callbacks,
        device: _,
    } = upload;
    HostScheduledUpload {
        callbacks,
        _phantom: std::marker::PhantomData,
    }
}

fn constraint_upload_into_host_keepalive<E>(
    upload: ScheduledMainLayerConstraintMetadataUpload<E>,
) -> HostScheduledMainLayerConstraintMetadataUpload<E> {
    let ScheduledMainLayerConstraintMetadataUpload {
        callbacks,
        quadratic_terms,
        linear_terms,
        constant_offset,
    } = upload;
    HostScheduledMainLayerConstraintMetadataUpload {
        callbacks,
        quadratic_terms: upload_into_host_keepalive(quadratic_terms),
        linear_terms: upload_into_host_keepalive(linear_terms),
        constant_offset: upload_into_host_keepalive(constant_offset),
    }
}

fn dimension_reducing_round_state_into_host_keepalive<B, E>(
    state: ScheduledDimensionReducingRoundState<B, E>,
) -> HostScheduledDimensionReducingRoundState {
    match state {
        ScheduledDimensionReducingRoundState::Round1 {
            callbacks,
            scheduled: _,
        } => HostScheduledDimensionReducingRoundState::Round1 { callbacks },
        ScheduledDimensionReducingRoundState::Round2 {
            callbacks,
            scheduled: _,
        } => HostScheduledDimensionReducingRoundState::Round2 { callbacks },
        ScheduledDimensionReducingRoundState::Round3AndBeyond {
            callbacks,
            scheduled: _,
        } => HostScheduledDimensionReducingRoundState::Round3AndBeyond { callbacks },
    }
}

fn main_layer_round_state_into_host_keepalive<E>(
    state: ScheduledMainLayerRoundState<E>,
) -> HostScheduledMainLayerRoundState {
    match state {
        ScheduledMainLayerRoundState::Round1 {
            callbacks,
            scheduled: _,
        } => HostScheduledMainLayerRoundState::Round1 { callbacks },
        ScheduledMainLayerRoundState::Round2 {
            callbacks,
            scheduled: _,
        } => HostScheduledMainLayerRoundState::Round2 { callbacks },
        ScheduledMainLayerRoundState::Round3AndBeyond {
            callbacks,
            scheduled: _,
        } => HostScheduledMainLayerRoundState::Round3AndBeyond { callbacks },
    }
}

fn schedule_immediate_field_upload<E: Field + Send + Sync + 'static>(
    context: &ProverContext,
    padded_len: usize,
    values: &[E],
) -> CudaResult<ScheduledChallengeBuffer<E>> {
    assert!(values.len() <= padded_len);
    let values = values.to_vec();
    let mut callbacks = Callbacks::new();
    let (host, device) = schedule_callback_populated_field_upload(
        context,
        padded_len,
        &mut callbacks,
        move |slice| {
            slice[..values.len()].copy_from_slice(&values);
        },
    )?;
    // host is H2D staging only — drop it, no CPU readback needed
    drop(host);
    Ok(ScheduledChallengeBuffer {
        callbacks: Arc::new(callbacks),
        device: Arc::new(SharedChallengeDevice::new(device)),
        offset: 0,
        len: padded_len,
    })
}

fn schedule_packed_immediate_field_uploads<E: Field + Send + Sync + 'static>(
    context: &ProverContext,
    padded_len: usize,
    values: &[Vec<E>],
) -> CudaResult<Vec<ScheduledChallengeBuffer<E>>> {
    if values.is_empty() {
        return Ok(Vec::new());
    }
    for entry in values.iter() {
        assert!(entry.len() <= padded_len);
    }

    let count = values.len();
    let total_len = padded_len * count;
    let values = values.to_vec();
    let mut callbacks = Callbacks::new();
    let (host, device) = schedule_callback_populated_field_upload(
        context,
        total_len,
        &mut callbacks,
        move |slice| {
            for (idx, src) in values.iter().enumerate() {
                let start = idx * padded_len;
                slice[start..start + src.len()].copy_from_slice(src);
            }
        },
    )?;
    drop(host);

    let callbacks = Arc::new(callbacks);
    let device = Arc::new(SharedChallengeDevice::new(device));
    Ok((0..count)
        .map(|idx| ScheduledChallengeBuffer {
            callbacks: Arc::clone(&callbacks),
            device: Arc::clone(&device),
            offset: idx * padded_len,
            len: padded_len,
        })
        .collect())
}

fn schedule_packed_round_challenge_upload<E: Field + 'static>(
    context: &ProverContext,
    device: Arc<SharedChallengeDevice<E>>,
    offset: usize,
    len: usize,
    fill: impl Fn(&mut [E]) + Send + Sync + 'static,
) -> CudaResult<ScheduledChallengeBuffer<E>> {
    let mut callbacks = Callbacks::new();
    let mut host = unsafe { context.alloc_host_uninit_slice(len) };
    let host_accessor = host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            let dst = host_accessor.get_mut();
            dst.fill(E::ZERO);
            fill(dst);
        },
        context.get_exec_stream(),
    )?;
    // SAFETY: the packed device buffer outlives the queued copy and the slice range belongs to
    // this buffer view. Uploads are enqueued on a single CUDA stream in program order.
    unsafe {
        memory_copy_async(
            device.slice_mut(offset, len),
            &host,
            context.get_exec_stream(),
        )?;
    }
    drop(host);

    Ok(ScheduledChallengeBuffer {
        callbacks: Arc::new(callbacks),
        device,
        offset,
        len,
    })
}

fn schedule_callback_populated_field_upload<'a, E: Field + 'a>(
    context: &ProverContext,
    padded_len: usize,
    callbacks: &mut Callbacks<'a>,
    fill: impl Fn(&mut [E]) + Send + Sync + 'a,
) -> CudaResult<(HostAllocation<[E]>, DeviceAllocation<E>)> {
    let mut host = unsafe { context.alloc_host_uninit_slice(padded_len) };
    let host_accessor = host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            let dst = host_accessor.get_mut();
            dst.fill(E::ZERO);
            fill(dst);
        },
        context.get_exec_stream(),
    )?;
    let mut device = context.alloc(padded_len, AllocationPlacement::Top)?;
    memory_copy_async(&mut device, &host, context.get_exec_stream())?;
    Ok((host, device))
}

fn schedule_callback_populated_upload<'a, T: Copy + 'a>(
    context: &ProverContext,
    len: usize,
    callbacks: &mut Callbacks<'a>,
    fill: impl Fn(&mut [T]) + Send + Sync + 'a,
) -> CudaResult<ScheduledUpload<T>> {
    let mut host = unsafe { context.alloc_host_uninit_slice(len) };
    let host_accessor = host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            fill(host_accessor.get_mut());
        },
        context.get_exec_stream(),
    )?;
    let mut device = context.alloc(len, AllocationPlacement::Top)?;
    memory_copy_async(&mut device, &host, context.get_exec_stream())?;
    drop(host);
    Ok(ScheduledUpload {
        callbacks: Callbacks::new(),
        device,
    })
}

fn schedule_deferred_main_layer_constraint_metadata_upload<
    E: Field + FieldExtension<BF> + 'static,
>(
    template: &GpuGKRMainLayerConstraintTemplate,
    main_layer_challenges: UnsafeAccessor<[E]>,
    context: &ProverContext,
) -> CudaResult<ScheduledMainLayerConstraintMetadataUpload<E>> {
    let mut callbacks = Callbacks::new();
    let quadratic_terms = schedule_callback_populated_upload(
        context,
        template.quadratic_terms.len(),
        &mut callbacks,
        {
            let template = template.quadratic_terms.clone();
            move |dst: &mut [GpuGKRMainLayerConstraintQuadraticTerm<E>]| unsafe {
                let challenge = main_layer_challenges.get()[1];
                for (dst, src) in dst.iter_mut().zip(template.iter()) {
                    *dst = GpuGKRMainLayerConstraintQuadraticTerm {
                        lhs: src.lhs,
                        rhs: src.rhs,
                        challenge: evaluate_constraint_prefactor(&src.challenge_terms, challenge),
                    };
                }
            }
        },
    )?;
    let linear_terms = schedule_callback_populated_upload(
        context,
        template.linear_terms.len(),
        &mut callbacks,
        {
            let template = template.linear_terms.clone();
            move |dst: &mut [GpuGKRMainLayerConstraintLinearTerm<E>]| unsafe {
                let challenge = main_layer_challenges.get()[1];
                for (dst, src) in dst.iter_mut().zip(template.iter()) {
                    *dst = GpuGKRMainLayerConstraintLinearTerm {
                        input: src.input,
                        challenge: evaluate_constraint_prefactor(&src.challenge_terms, challenge),
                    };
                }
            }
        },
    )?;
    let constant_offset = schedule_callback_populated_upload(context, 1, &mut callbacks, {
        let template = template.constant_terms.clone();
        move |dst: &mut [E]| unsafe {
            dst[0] = evaluate_constraint_prefactor(&template, main_layer_challenges.get()[1]);
        }
    })?;
    Ok(ScheduledMainLayerConstraintMetadataUpload {
        callbacks,
        quadratic_terms,
        linear_terms,
        constant_offset,
    })
}

fn schedule_main_layer_auxiliary_upload<E: Field + 'static>(
    source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    main_layer_challenges: UnsafeAccessor<[E]>,
    context: &ProverContext,
) -> CudaResult<ScheduledUpload<E>> {
    let mut callbacks = Callbacks::new();
    let mut upload =
        schedule_callback_populated_upload(context, 1, &mut callbacks, move |dst: &mut [E]| {
            dst[0] = match source {
                GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => value,
                GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => unsafe {
                    main_layer_challenges.get()[0]
                },
            };
        })?;
    upload.callbacks = callbacks;
    Ok(upload)
}

fn schedule_main_layer_constraint_metadata_upload<E: Field + FieldExtension<BF> + 'static>(
    source: Option<&GpuGKRMainLayerConstraintMetadataSource<E>>,
    main_layer_challenges: UnsafeAccessor<[E]>,
    context: &ProverContext,
) -> CudaResult<Option<ScheduledMainLayerConstraintMetadataUpload<E>>> {
    match source {
        None => Ok(None),
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(template)) => Ok(Some(
            schedule_deferred_main_layer_constraint_metadata_upload(
                template,
                main_layer_challenges,
                context,
            )?,
        )),
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => {
            let mut callbacks = Callbacks::new();
            let quadratic_terms = schedule_callback_populated_upload(
                context,
                metadata.quadratic_terms.len(),
                &mut callbacks,
                {
                    let terms = metadata.quadratic_terms.clone();
                    move |dst: &mut [GpuGKRMainLayerConstraintQuadraticTerm<E>]| {
                        dst.copy_from_slice(&terms);
                    }
                },
            )?;
            let linear_terms = schedule_callback_populated_upload(
                context,
                metadata.linear_terms.len(),
                &mut callbacks,
                {
                    let terms = metadata.linear_terms.clone();
                    move |dst: &mut [GpuGKRMainLayerConstraintLinearTerm<E>]| {
                        dst.copy_from_slice(&terms);
                    }
                },
            )?;
            let constant_offset =
                schedule_callback_populated_upload(context, 1, &mut callbacks, {
                    let constant = metadata.constant_offset;
                    move |dst: &mut [E]| {
                        dst[0] = constant;
                    }
                })?;
            Ok(Some(ScheduledMainLayerConstraintMetadataUpload {
                callbacks,
                quadratic_terms,
                linear_terms,
                constant_offset,
            }))
        }
    }
}

fn field_pow<E: Field>(base: E, exponent: usize) -> E {
    let mut result = E::ONE;
    for _ in 0..exponent {
        result.mul_assign(&base);
    }
    result
}

fn fill_batch_challenge_slice<E: Field>(
    dst: &mut [E],
    batch_challenge_base: E,
    offset: usize,
    count: usize,
) {
    assert!(count <= dst.len());
    dst.fill(E::ZERO);
    let mut current = field_pow(batch_challenge_base, offset);
    for value in dst.iter_mut().take(count) {
        *value = current;
        current.mul_assign(&batch_challenge_base);
    }
}

fn main_layer_round_challenge_len(step: usize) -> usize {
    match step {
        1 => 1,
        2 => 2,
        _ => 1,
    }
}

fn schedule_workflow_batch_challenge_upload<E>(
    context: &ProverContext,
    workflow_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    padded_len: usize,
    offset: usize,
    count: usize,
) -> CudaResult<ScheduledChallengeBuffer<E>>
where
    E: FieldExtension<BF> + Field + 'static,
{
    let mut callbacks = Callbacks::new();
    let (host, device) = schedule_callback_populated_field_upload(
        context,
        padded_len,
        &mut callbacks,
        move |dst| {
            let batch_challenge_base = workflow_state.lock().unwrap().current_batching_challenge;
            fill_batch_challenge_slice(dst, batch_challenge_base, offset, count);
        },
    )?;
    drop(host);

    Ok(ScheduledChallengeBuffer {
        callbacks: Arc::new(callbacks),
        device: Arc::new(SharedChallengeDevice::new(device)),
        offset: 0,
        len: padded_len,
    })
}

fn schedule_packed_workflow_batch_challenge_uploads<E>(
    context: &ProverContext,
    workflow_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
    padded_len: usize,
    specs: &[(usize, usize)],
) -> CudaResult<Vec<ScheduledChallengeBuffer<E>>>
where
    E: FieldExtension<BF> + Field + 'static,
{
    if specs.is_empty() {
        return Ok(Vec::new());
    }

    let count = specs.len();
    let total_len = padded_len * count;
    let specs = specs.to_vec();
    let mut callbacks = Callbacks::new();
    let (host, device) =
        schedule_callback_populated_field_upload(context, total_len, &mut callbacks, move |dst| {
            let batch_challenge_base = workflow_state.lock().unwrap().current_batching_challenge;
            for (idx, (offset, count)) in specs.iter().copied().enumerate() {
                let start = idx * padded_len;
                fill_batch_challenge_slice(
                    &mut dst[start..start + padded_len],
                    batch_challenge_base,
                    offset,
                    count,
                );
            }
        })?;
    drop(host);

    let callbacks = Arc::new(callbacks);
    let device = Arc::new(SharedChallengeDevice::new(device));
    Ok((0..count)
        .map(|idx| ScheduledChallengeBuffer {
            callbacks: Arc::clone(&callbacks),
            device: Arc::clone(&device),
            offset: idx * padded_len,
            len: padded_len,
        })
        .collect())
}

fn empty_round0_host_launch_descriptors<B, E>(
    context: &ProverContext,
) -> GpuSumcheckRound0HostLaunchDescriptors<B, E> {
    GpuSumcheckRound0HostLaunchDescriptors {
        base_field_inputs: unsafe { context.alloc_host_uninit_slice(0) },
        extension_field_inputs: unsafe { context.alloc_host_uninit_slice(0) },
        base_field_outputs: unsafe { context.alloc_host_uninit_slice(0) },
        extension_field_outputs: unsafe { context.alloc_host_uninit_slice(0) },
    }
}

const GKR_DIM_REDUCING_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingPairwiseRound0<T>,
    inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenges: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingLookupRound0<T>,
    inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenges: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingPairwiseContinuation<T>,
    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    folding_challenge: *const T,
    batch_challenges: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingLookupContinuation<T>,
    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    folding_challenge: *const T,
    batch_challenges: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingBuildEq<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingWeightContributions<T>,
    contributions: *const T,
    kernel_count: u32,
    eq_values: *const T,
    weighted_rows: *mut T,
    acc_size: u32,
);

pub(crate) trait GpuDimensionReducingKernelSet: Reduce + Copy + Sized {
    const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self>;
    const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self>;
    const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self>;
    const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self>;
    const BUILD_EQ: GpuDimensionReducingBuildEqSignature<Self>;
    const WEIGHT_CONTRIBUTIONS: GpuDimensionReducingWeightContributionsSignature<Self>;
}

macro_rules! gkr_dim_reducing_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_pairwise_round0_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    outputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    batch_challenges: *const $type,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_lookup_round0_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    outputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    batch_challenges: *const $type,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_pairwise_continuation_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    folding_challenge: *const $type,
                    batch_challenges: *const $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_lookup_continuation_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    folding_challenge: *const $type,
                    batch_challenges: *const $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_build_eq_ $type:lower _kernel>](
                    claim_point: *const $type,
                    challenge_offset: u32,
                    challenge_count: u32,
                    eq_values: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_weight_contributions_ $type:lower _kernel>](
                    contributions: *const $type,
                    kernel_count: u32,
                    eq_values: *const $type,
                    weighted_rows: *mut $type,
                    acc_size: u32,
                )
            );

            impl GpuDimensionReducingKernelSet for $type {
                const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self> =
                    [<ab_gkr_dim_reducing_pairwise_round0_ $type:lower _kernel>];
                const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self> =
                    [<ab_gkr_dim_reducing_lookup_round0_ $type:lower _kernel>];
                const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self> =
                    [<ab_gkr_dim_reducing_pairwise_continuation_ $type:lower _kernel>];
                const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self> =
                    [<ab_gkr_dim_reducing_lookup_continuation_ $type:lower _kernel>];
                const BUILD_EQ: GpuDimensionReducingBuildEqSignature<Self> =
                    [<ab_gkr_dim_reducing_build_eq_ $type:lower _kernel>];
                const WEIGHT_CONTRIBUTIONS: GpuDimensionReducingWeightContributionsSignature<Self> =
                    [<ab_gkr_dim_reducing_weight_contributions_ $type:lower _kernel>];
            }
        }
    };
}

gkr_dim_reducing_kernels!(E2);
gkr_dim_reducing_kernels!(E4);
gkr_dim_reducing_kernels!(E6);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound0<T>,
    kind: u32,
    base_inputs: *const GpuBaseFieldPolySource<BF>,
    extension_inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    base_outputs: *const GpuBaseFieldPolySource<BF>,
    extension_outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenges: *const T,
    auxiliary_challenge: *const T,
    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<T>,
    constraint_quadratic_terms_count: u32,
    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<T>,
    constraint_linear_terms_count: u32,
    constraint_constant_offset: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound1<T>,
    kind: u32,
    base_inputs: *const GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, T>,
    extension_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    batch_challenges: *const T,
    folding_challenge: *const T,
    auxiliary_challenge: *const T,
    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<T>,
    constraint_quadratic_terms_count: u32,
    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<T>,
    constraint_linear_terms_count: u32,
    constraint_constant_offset: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound2<T>,
    kind: u32,
    base_inputs: *const GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<BF, T>,
    extension_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    batch_challenges: *const T,
    folding_challenges: *const T,
    auxiliary_challenge: *const T,
    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<T>,
    constraint_quadratic_terms_count: u32,
    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<T>,
    constraint_linear_terms_count: u32,
    constraint_constant_offset: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3<T>,
    kind: u32,
    base_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    extension_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    batch_challenges: *const T,
    folding_challenge: *const T,
    auxiliary_challenge: *const T,
    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<T>,
    constraint_quadratic_terms_count: u32,
    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<T>,
    constraint_linear_terms_count: u32,
    constraint_constant_offset: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

trait GpuMainLayerKernelSet: GpuDimensionReducingKernelSet {
    const MAIN_ROUND0: GpuGKRMainRound0Signature<Self>;
    const MAIN_ROUND1: GpuGKRMainRound1Signature<Self>;
    const MAIN_ROUND2: GpuGKRMainRound2Signature<Self>;
    const MAIN_ROUND3: GpuGKRMainRound3Signature<Self>;
}

macro_rules! gkr_main_layer_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_main_round0_ $type:lower _kernel>](
                    kind: u32,
                    base_inputs: *const GpuBaseFieldPolySource<BF>,
                    extension_inputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    base_outputs: *const GpuBaseFieldPolySource<BF>,
                    extension_outputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    batch_challenges: *const $type,
                    auxiliary_challenge: *const $type,
                    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<$type>,
                    constraint_quadratic_terms_count: u32,
                    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<$type>,
                    constraint_linear_terms_count: u32,
                    constraint_constant_offset: *const $type,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_main_round1_ $type:lower _kernel>](
                    kind: u32,
                    base_inputs: *const GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, $type>,
                    extension_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    batch_challenges: *const $type,
                    folding_challenge: *const $type,
                    auxiliary_challenge: *const $type,
                    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<$type>,
                    constraint_quadratic_terms_count: u32,
                    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<$type>,
                    constraint_linear_terms_count: u32,
                    constraint_constant_offset: *const $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_main_round2_ $type:lower _kernel>](
                    kind: u32,
                    base_inputs: *const GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<BF, $type>,
                    extension_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    batch_challenges: *const $type,
                    folding_challenges: *const $type,
                    auxiliary_challenge: *const $type,
                    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<$type>,
                    constraint_quadratic_terms_count: u32,
                    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<$type>,
                    constraint_linear_terms_count: u32,
                    constraint_constant_offset: *const $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_main_round3_ $type:lower _kernel>](
                    kind: u32,
                    base_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    extension_inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    batch_challenges: *const $type,
                    folding_challenge: *const $type,
                    auxiliary_challenge: *const $type,
                    constraint_quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<$type>,
                    constraint_quadratic_terms_count: u32,
                    constraint_linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<$type>,
                    constraint_linear_terms_count: u32,
                    constraint_constant_offset: *const $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );

            impl GpuMainLayerKernelSet for $type {
                const MAIN_ROUND0: GpuGKRMainRound0Signature<Self> =
                    [<ab_gkr_main_round0_ $type:lower _kernel>];
                const MAIN_ROUND1: GpuGKRMainRound1Signature<Self> =
                    [<ab_gkr_main_round1_ $type:lower _kernel>];
                const MAIN_ROUND2: GpuGKRMainRound2Signature<Self> =
                    [<ab_gkr_main_round2_ $type:lower _kernel>];
                const MAIN_ROUND3: GpuGKRMainRound3Signature<Self> =
                    [<ab_gkr_main_round3_ $type:lower _kernel>];
            }
        }
    };
}

gkr_main_layer_kernels!(E2);
gkr_main_layer_kernels!(E4);
gkr_main_layer_kernels!(E6);

fn gkr_dim_reducing_launch_config(count: u32, context: &ProverContext) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_DIM_REDUCING_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

fn launch_pairwise_round0<E: GpuDimensionReducingKernelSet>(
    descriptors: &GpuSumcheckRound0ScheduledLaunchDescriptors<impl Sized, E>,
    batch_challenges: *const E,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let inputs = descriptors.device.extension_field_inputs.as_ptr();
    let outputs = descriptors.device.extension_field_outputs.as_ptr();
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingPairwiseRound0Arguments::new(
        inputs,
        outputs,
        batch_challenges,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingPairwiseRound0Function(E::PAIRWISE_ROUND0).launch(&config, &args)
}

fn launch_lookup_round0<E: GpuDimensionReducingKernelSet>(
    descriptors: &GpuSumcheckRound0ScheduledLaunchDescriptors<impl Sized, E>,
    batch_challenges: *const E,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let inputs = descriptors.device.extension_field_inputs.as_ptr();
    let outputs = descriptors.device.extension_field_outputs.as_ptr();
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingLookupRound0Arguments::new(
        inputs,
        outputs,
        batch_challenges,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingLookupRound0Function(E::LOOKUP_ROUND0).launch(&config, &args)
}

fn launch_pairwise_continuation<E: GpuDimensionReducingKernelSet>(
    descriptors: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E>,
    folding_challenge: *const E,
    batch_challenges: *const E,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingPairwiseContinuationArguments::new(
        descriptors,
        folding_challenge,
        batch_challenges,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingPairwiseContinuationFunction(E::PAIRWISE_CONTINUATION)
        .launch(&config, &args)
}

fn launch_lookup_continuation<E: GpuDimensionReducingKernelSet>(
    descriptors: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E>,
    folding_challenge: *const E,
    batch_challenges: *const E,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingLookupContinuationArguments::new(
        descriptors,
        folding_challenge,
        batch_challenges,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingLookupContinuationFunction(E::LOOKUP_CONTINUATION).launch(&config, &args)
}

fn launch_weight_contributions<E: GpuDimensionReducingKernelSet>(
    contributions: *const E,
    kernel_count: usize,
    eq_values: *const E,
    weighted_rows: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingWeightContributionsArguments::new(
        contributions,
        kernel_count as u32,
        eq_values,
        weighted_rows,
        acc_size as u32,
    );

    GpuDimensionReducingWeightContributionsFunction(E::WEIGHT_CONTRIBUTIONS).launch(&config, &args)
}

pub(crate) fn launch_build_eq_values<E: GpuDimensionReducingKernelSet>(
    claim_point: *const E,
    challenge_offset: usize,
    challenge_count: usize,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingBuildEqArguments::new(
        claim_point,
        challenge_offset as u32,
        challenge_count as u32,
        eq_values,
        acc_size as u32,
    );

    GpuDimensionReducingBuildEqFunction(E::BUILD_EQ).launch(&config, &args)
}

fn constraint_metadata_args<E>(
    metadata: Option<&ScheduledMainLayerConstraintMetadataUpload<E>>,
) -> (
    *const GpuGKRMainLayerConstraintQuadraticTerm<E>,
    usize,
    *const GpuGKRMainLayerConstraintLinearTerm<E>,
    usize,
    *const E,
)
where
    E: Field,
{
    if let Some(metadata) = metadata {
        (
            metadata.quadratic_terms.device.as_ptr(),
            metadata.quadratic_terms.device.len(),
            metadata.linear_terms.device.as_ptr(),
            metadata.linear_terms.device.len(),
            metadata.constant_offset.device.as_ptr(),
        )
    } else {
        (null(), 0, null(), 0, null())
    }
}

fn launch_main_round0<E: GpuMainLayerKernelSet + Field>(
    kind: GpuGKRMainLayerKernelKind,
    descriptors: &GpuSumcheckRound0ScheduledLaunchDescriptors<BF, E>,
    batch_challenges: *const E,
    auxiliary_challenge: *const E,
    constraint_metadata: Option<&ScheduledMainLayerConstraintMetadataUpload<E>>,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let (
        constraint_quadratic_terms,
        constraint_quadratic_terms_count,
        constraint_linear_terms,
        constraint_linear_terms_count,
        constraint_constant_offset,
    ) = constraint_metadata_args(constraint_metadata);
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound0Arguments::new(
        kind.as_u32(),
        descriptors.device.base_field_inputs.as_ptr(),
        descriptors.device.extension_field_inputs.as_ptr(),
        descriptors.device.base_field_outputs.as_ptr(),
        descriptors.device.extension_field_outputs.as_ptr(),
        batch_challenges,
        auxiliary_challenge,
        constraint_quadratic_terms,
        constraint_quadratic_terms_count as u32,
        constraint_linear_terms,
        constraint_linear_terms_count as u32,
        constraint_constant_offset,
        contributions,
        acc_size as u32,
    );

    GpuGKRMainRound0Function(E::MAIN_ROUND0).launch(&config, &args)
}

fn launch_main_round1<E: GpuMainLayerKernelSet + Field>(
    kind: GpuGKRMainLayerKernelKind,
    descriptors: &GpuSumcheckRound1ScheduledLaunchDescriptors<BF, E>,
    batch_challenges: *const E,
    folding_challenge: *const E,
    auxiliary_challenge: *const E,
    constraint_metadata: Option<&ScheduledMainLayerConstraintMetadataUpload<E>>,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let (
        constraint_quadratic_terms,
        constraint_quadratic_terms_count,
        constraint_linear_terms,
        constraint_linear_terms_count,
        constraint_constant_offset,
    ) = constraint_metadata_args(constraint_metadata);
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound1Arguments::new(
        kind.as_u32(),
        descriptors.device.base_field_inputs.as_ptr(),
        descriptors.device.extension_field_inputs.as_ptr(),
        batch_challenges,
        folding_challenge,
        auxiliary_challenge,
        constraint_quadratic_terms,
        constraint_quadratic_terms_count as u32,
        constraint_linear_terms,
        constraint_linear_terms_count as u32,
        constraint_constant_offset,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuGKRMainRound1Function(E::MAIN_ROUND1).launch(&config, &args)
}

fn launch_main_round2<E: GpuMainLayerKernelSet + Field>(
    kind: GpuGKRMainLayerKernelKind,
    descriptors: &GpuSumcheckRound2ScheduledLaunchDescriptors<BF, E>,
    batch_challenges: *const E,
    folding_challenges: *const E,
    auxiliary_challenge: *const E,
    constraint_metadata: Option<&ScheduledMainLayerConstraintMetadataUpload<E>>,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let (
        constraint_quadratic_terms,
        constraint_quadratic_terms_count,
        constraint_linear_terms,
        constraint_linear_terms_count,
        constraint_constant_offset,
    ) = constraint_metadata_args(constraint_metadata);
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound2Arguments::new(
        kind.as_u32(),
        descriptors.device.base_field_inputs.as_ptr(),
        descriptors.device.extension_field_inputs.as_ptr(),
        batch_challenges,
        folding_challenges,
        auxiliary_challenge,
        constraint_quadratic_terms,
        constraint_quadratic_terms_count as u32,
        constraint_linear_terms,
        constraint_linear_terms_count as u32,
        constraint_constant_offset,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuGKRMainRound2Function(E::MAIN_ROUND2).launch(&config, &args)
}

fn launch_main_round3<E: GpuMainLayerKernelSet + Field>(
    kind: GpuGKRMainLayerKernelKind,
    descriptors: &GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>,
    batch_challenges: *const E,
    folding_challenge: *const E,
    auxiliary_challenge: *const E,
    constraint_metadata: Option<&ScheduledMainLayerConstraintMetadataUpload<E>>,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let (
        constraint_quadratic_terms,
        constraint_quadratic_terms_count,
        constraint_linear_terms,
        constraint_linear_terms_count,
        constraint_constant_offset,
    ) = constraint_metadata_args(constraint_metadata);
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound3Arguments::new(
        kind.as_u32(),
        descriptors.device.base_field_inputs.as_ptr(),
        descriptors.device.extension_field_inputs.as_ptr(),
        batch_challenges,
        folding_challenge,
        auxiliary_challenge,
        constraint_quadratic_terms,
        constraint_quadratic_terms_count as u32,
        constraint_linear_terms,
        constraint_linear_terms_count as u32,
        constraint_constant_offset,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuGKRMainRound3Function(E::MAIN_ROUND3).launch(&config, &args)
}

fn build_dimension_reducing_kernel_blueprints<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    batch_challenge_base: E,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut next_batch_challenge_offset = 0usize;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    let batch_challenge_offset = next_batch_challenge_offset;
                    next_batch_challenge_offset += 1;
                    blueprints.push(DimensionReducingKernelBlueprint {
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: vec![get_challenge()],
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced_io
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two inputs");
                let outputs: [GKRAddress; 2] = reduced_io
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two outputs");
                let batch_challenge_offset = next_batch_challenge_offset;
                next_batch_challenge_offset += 2;
                blueprints.push(DimensionReducingKernelBlueprint {
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                });
            }
        }
    }

    blueprints
}

fn build_dimension_reducing_kernel_blueprints_static<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    let batch_challenge_offset = next_batch_challenge_offset;
                    next_batch_challenge_offset += 1;
                    blueprints.push(DimensionReducingKernelBlueprint {
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: Vec::new(),
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced_io
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two inputs");
                let outputs: [GKRAddress; 2] = reduced_io
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two outputs");
                let batch_challenge_offset = next_batch_challenge_offset;
                next_batch_challenge_offset += 2;
                blueprints.push(DimensionReducingKernelBlueprint {
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: Vec::new(),
                });
            }
        }
    }

    blueprints
}

fn build_constraint_metadata_template(
    input: &NoFieldMaxQuadraticConstraintsGKRRelation,
    num_memory_polys: usize,
    num_witness_polys: usize,
) -> GpuGKRMainLayerConstraintTemplate {
    let remap_offset = |a: GKRAddress| match a {
        GKRAddress::BaseLayerMemory(offset) => {
            assert!(offset < num_memory_polys);
            offset
        }
        GKRAddress::BaseLayerWitness(offset) => {
            assert!(offset < num_witness_polys);
            offset + num_memory_polys
        }
        GKRAddress::Setup(..) => unreachable!(),
        _ => unreachable!(),
    };

    let quadratic_terms = input
        .quadratic_terms
        .iter()
        .map(
            |((lhs, rhs), terms)| GpuGKRMainLayerConstraintQuadraticTemplate {
                lhs: remap_offset(*lhs) as u32,
                rhs: remap_offset(*rhs) as u32,
                challenge_terms: terms
                    .iter()
                    .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                        coeff: BF::from_u32_with_reduction(*coeff),
                        power: *power as u32,
                    })
                    .collect(),
            },
        )
        .collect();
    let linear_terms = input
        .linear_terms
        .iter()
        .map(|(input, terms)| GpuGKRMainLayerConstraintLinearTemplate {
            input: remap_offset(*input) as u32,
            challenge_terms: terms
                .iter()
                .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                    coeff: BF::from_u32_with_reduction(*coeff),
                    power: *power as u32,
                })
                .collect(),
        })
        .collect();
    let constant_terms = input
        .constants
        .iter()
        .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
            coeff: BF::from_u32_with_reduction(*coeff),
            power: *power as u32,
        })
        .collect();

    GpuGKRMainLayerConstraintTemplate {
        quadratic_terms,
        linear_terms,
        constant_terms,
    }
}

fn evaluate_constraint_prefactor<E: Field + FieldExtension<BF>>(
    challenge_terms: &[GpuGKRMainLayerConstraintChallengeTerm],
    challenge: E,
) -> E {
    let mut total = E::ZERO;
    for term in challenge_terms.iter() {
        let mut contribution = challenge.pow(term.power);
        contribution.mul_assign_by_base(&term.coeff);
        total.add_assign(&contribution);
    }
    total
}

fn build_main_layer_kernel_blueprints<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    batch_challenge_base: E,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
) -> Vec<GpuGKRMainLayerKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut next_batch_challenge_offset = 0usize;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let push_challenges = |count: usize,
                               next_batch_challenge_offset: &mut usize,
                               get_challenge: &mut dyn FnMut() -> E| {
            let batch_challenge_offset = *next_batch_challenge_offset;
            *next_batch_challenge_offset += count;
            let batch_challenges = (0..count).map(|_| get_challenge()).collect::<Vec<_>>();
            (batch_challenge_offset, batch_challenges)
        };
        match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => {
                let (batch_challenge_offset, batch_challenges) =
                    push_challenges(1, &mut next_batch_challenge_offset, &mut get_challenge);
                if storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input)
                {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges,
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges,
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                            lookup_additive_challenge,
                        ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedExtensionGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                            lookup_additive_challenge,
                        ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let relation = BatchConstraintEvalGKRRelation::<BF, E>::new(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                    constraint_batch_challenge,
                );
                let constraint_metadata = GpuGKRMainLayerConstraintHostMetadata {
                    quadratic_terms: relation
                        .kernel
                        .quadratic_parts
                        .iter()
                        .map(
                            |((lhs, rhs), challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                                lhs: *lhs as u32,
                                rhs: *rhs as u32,
                                challenge: *challenge,
                            },
                        )
                        .collect(),
                    linear_terms: relation
                        .kernel
                        .linear_parts
                        .iter()
                        .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
                            input: *input as u32,
                            challenge: *challenge,
                        })
                        .collect(),
                    constant_offset: relation.kernel.constant_offset,
                };
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                        inputs: <BatchConstraintEvalGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset: next_batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: {
                            next_batch_challenge_offset += 1;
                            vec![get_challenge()]
                        },
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: Some(
                            GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                        ),
                    },
                );
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

fn build_main_layer_kernel_blueprints_static<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
) -> Vec<GpuGKRMainLayerKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let push_empty = |count: usize, next_batch_challenge_offset: &mut usize| {
            let batch_challenge_offset = *next_batch_challenge_offset;
            *next_batch_challenge_offset += count;
            (batch_challenge_offset, count)
        };
        match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => {
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                if storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input)
                {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedExtensionGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let relation = BatchConstraintEvalGKRRelation::<BF, E>::new(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                    E::ZERO,
                );
                let constraint_metadata = build_constraint_metadata_template(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                        inputs: <BatchConstraintEvalGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: Some(
                            GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                        ),
                    },
                );
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

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

    pub(crate) fn storage(&self) -> &GpuGKRStorage<B, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field> GpuGKRDimensionReducingBackwardState<BF, E> {
    pub(crate) fn into_main_layer_backward_state(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        lookup_additive_challenge: E,
        constraint_batch_challenge: E,
    ) -> GpuGKRMainLayerBackwardState<E> {
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
            lookup_additive_challenge,
            constraint_batch_challenge,
            num_base_layer_memory_polys: compiled_circuit.memory_layout.total_width,
            num_base_layer_witness_polys: compiled_circuit.witness_layout.total_width,
        }
    }
}

impl<B: 'static, E: Field + Reduce> GpuGKRDimensionReducingBackwardState<B, E> {
    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);

        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        let mut round0_descriptors = Vec::with_capacity(blueprints.len());

        for blueprint in blueprints {
            let round0 = self
                .storage
                .schedule_upload_for_sumcheck_round_0(&blueprint.inputs, context)?;
            let round1_prepared = self
                .storage
                .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?;
            let round2_prepared = if folding_steps >= 3 {
                Some(
                    self.storage
                        .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
                )
            } else {
                None
            };
            let mut round3_and_beyond_prepared = Vec::new();
            for step in 3..folding_steps {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    step,
                    context,
                )?;
                round3_and_beyond_prepared
                    .push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }

            round0_descriptors.push(round0);
            kernel_plans.push(GpuGKRDimensionReducingKernelPlan {
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let kernel_count = kernel_plans.len();
        let max_acc_size = trace_len_after_reduction / 2;
        let weighted_rows_len = max_acc_size * 2;
        let contributions_len = kernel_count * weighted_rows_len;
        let reduction_temp_storage_bytes =
            get_batch_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, 2, max_acc_size as i32)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            claim_point: context.alloc(folding_steps, AllocationPlacement::Top)?,
            eq_values: context.alloc(max_acc_size, AllocationPlacement::Top)?,
            contributions: context.alloc(contributions_len, AllocationPlacement::Top)?,
            weighted_rows: context.alloc(weighted_rows_len, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(Some(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            kernel_plans,
            round0_descriptors,
            round_scratch,
        }))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);

        let blueprints = build_dimension_reducing_kernel_blueprints_static::<E>(&layer);
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        let mut round0_descriptors = Vec::with_capacity(blueprints.len());

        for blueprint in blueprints {
            let round0 = self
                .storage
                .schedule_upload_for_sumcheck_round_0(&blueprint.inputs, context)?;
            let round1_prepared = self
                .storage
                .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?;
            let round2_prepared = if folding_steps >= 3 {
                Some(
                    self.storage
                        .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
                )
            } else {
                None
            };
            let mut round3_and_beyond_prepared = Vec::new();
            for step in 3..folding_steps {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    step,
                    context,
                )?;
                round3_and_beyond_prepared
                    .push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }

            round0_descriptors.push(round0);
            kernel_plans.push(GpuGKRDimensionReducingKernelPlan {
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let kernel_count = kernel_plans.len();
        let max_acc_size = trace_len_after_reduction / 2;
        let weighted_rows_len = max_acc_size * 2;
        let contributions_len = kernel_count * weighted_rows_len;
        let reduction_temp_storage_bytes =
            get_batch_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, 2, max_acc_size as i32)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            claim_point: context.alloc(folding_steps, AllocationPlacement::Top)?,
            eq_values: context.alloc(max_acc_size, AllocationPlacement::Top)?,
            contributions: context.alloc(contributions_len, AllocationPlacement::Top)?,
            weighted_rows: context.alloc(weighted_rows_len, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(Some(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            kernel_plans,
            round0_descriptors,
            round_scratch,
        }))
    }
}

impl<E: Field> GpuGKRMainLayerBackwardState<E> {
    pub(crate) fn storage(&self) -> &GpuGKRStorage<BF, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field + FieldExtension<BF> + Reduce> GpuGKRMainLayerBackwardState<E> {
    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            layer_idx,
            &self.storage,
            batch_challenge_base,
            self.lookup_additive_challenge,
            self.constraint_batch_challenge,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(
                self.storage
                    .schedule_upload_for_sumcheck_round_0(&blueprint.inputs, context)?,
            );
        }

        let mut round1_prepared = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared.push(
                self.storage
                    .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?,
            );
        }

        let mut round2_prepared = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared.push(
                self.storage
                    .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
            );
        }

        let mut round3_and_beyond_prepared = std::iter::repeat_with(Vec::new)
            .take(blueprints.len())
            .collect::<Vec<_>>();
        for step in 3..folding_steps {
            for (round3_for_kernel, blueprint) in
                round3_and_beyond_prepared.iter_mut().zip(blueprints.iter())
            {
                round3_for_kernel.push(GpuGKRMainLayerRound3Prepared {
                    step,
                    prepared: self.storage.prepare_for_sumcheck_round_3_and_beyond(
                        &blueprint.inputs,
                        step,
                        context,
                    )?,
                });
            }
        }

        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (((blueprint, round1_prepared), round2_prepared), round3_and_beyond_prepared) in
            blueprints
                .into_iter()
                .zip(round1_prepared.into_iter())
                .zip(round2_prepared.into_iter())
                .zip(round3_and_beyond_prepared.into_iter())
        {
            kernel_plans.push(GpuGKRMainLayerKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                auxiliary_challenge_source: blueprint.auxiliary_challenge_source,
                constraint_metadata_source: blueprint.constraint_metadata_source,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let kernel_count = kernel_plans.len();
        let max_acc_size = self.trace_len / 2;
        let weighted_rows_len = max_acc_size * 2;
        let contributions_len = kernel_count * weighted_rows_len;
        let reduction_temp_storage_bytes =
            get_batch_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, 2, max_acc_size as i32)?;
        let round_scratch = GpuGKRMainLayerRoundScratch {
            claim_point: context.alloc(folding_steps, AllocationPlacement::Top)?,
            eq_values: context.alloc(max_acc_size, AllocationPlacement::Top)?,
            contributions: context.alloc(contributions_len, AllocationPlacement::Top)?,
            weighted_rows: context.alloc(weighted_rows_len, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        Ok(Some(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            trace_len: self.trace_len,
            folding_steps,
            kernel_plans,
            round0_descriptors,
            round_scratch,
        }))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            layer_idx,
            &self.storage,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(
                self.storage
                    .schedule_upload_for_sumcheck_round_0(&blueprint.inputs, context)?,
            );
        }

        let mut round1_prepared = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared.push(
                self.storage
                    .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?,
            );
        }

        let mut round2_prepared = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared.push(
                self.storage
                    .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
            );
        }

        let mut round3_and_beyond_prepared = std::iter::repeat_with(Vec::new)
            .take(blueprints.len())
            .collect::<Vec<_>>();
        for step in 3..folding_steps {
            for (round3_for_kernel, blueprint) in
                round3_and_beyond_prepared.iter_mut().zip(blueprints.iter())
            {
                round3_for_kernel.push(GpuGKRMainLayerRound3Prepared {
                    step,
                    prepared: self.storage.prepare_for_sumcheck_round_3_and_beyond(
                        &blueprint.inputs,
                        step,
                        context,
                    )?,
                });
            }
        }

        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (((blueprint, round1_prepared), round2_prepared), round3_and_beyond_prepared) in
            blueprints
                .into_iter()
                .zip(round1_prepared.into_iter())
                .zip(round2_prepared.into_iter())
                .zip(round3_and_beyond_prepared.into_iter())
        {
            kernel_plans.push(GpuGKRMainLayerKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                auxiliary_challenge_source: blueprint.auxiliary_challenge_source,
                constraint_metadata_source: blueprint.constraint_metadata_source,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let kernel_count = kernel_plans.len();
        let max_acc_size = self.trace_len / 2;
        let weighted_rows_len = max_acc_size * 2;
        let contributions_len = kernel_count * weighted_rows_len;
        let reduction_temp_storage_bytes =
            get_batch_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, 2, max_acc_size as i32)?;
        let round_scratch = GpuGKRMainLayerRoundScratch {
            claim_point: context.alloc(folding_steps, AllocationPlacement::Top)?,
            eq_values: context.alloc(max_acc_size, AllocationPlacement::Top)?,
            contributions: context.alloc(contributions_len, AllocationPlacement::Top)?,
            weighted_rows: context.alloc(weighted_rows_len, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        Ok(Some(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            trace_len: self.trace_len,
            folding_steps,
            kernel_plans,
            round0_descriptors,
            round_scratch,
        }))
    }
}

impl<B, E> GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRDimensionReducingKernelPlan<B, E>] {
        &self.kernel_plans
    }

    pub(crate) fn round0_descriptors(
        &self,
    ) -> &[GpuSumcheckRound0ScheduledLaunchDescriptors<B, E>] {
        &self.round0_descriptors
    }
}

impl<E> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRMainLayerKernelPlan<E>] {
        &self.kernel_plans
    }

    pub(crate) fn round0_descriptors(
        &self,
    ) -> &[GpuSumcheckRound0ScheduledLaunchDescriptors<BF, E>] {
        &self.round0_descriptors
    }
}

impl<E: Field + 'static> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) fn schedule_round_1(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<BF, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round1_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_2(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<BF, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round2_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_3_and_beyond(
        &self,
        step: usize,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing prepared round 3+ storage for step {step}"))
                    .prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }
}

impl<B: 'static, E: Field + 'static> GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) fn schedule_round_1(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round1_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_2(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>>> {
        assert!(
            self.folding_steps >= 3,
            "round 2 scheduling requires at least three folding steps"
        );
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round2_prepared
                    .as_ref()
                    .expect("round 2 storage must be prepared")
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_3_and_beyond(
        &self,
        step: usize,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>> {
        assert!(step >= 3, "round 3+ scheduling starts at step 3");
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing prepared round 3+ storage for step {step}"))
                    .prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }
}

impl<B: 'static, E: 'static> GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuDimensionReducingKernelSet,
    [(); E::DEGREE]: Sized,
{
    fn evaluate_with_precomputed_eq_ext(values: &[E], eq: &[E]) -> E {
        assert_eq!(values.len(), eq.len());
        let mut result = E::ZERO;
        for (value, eq_value) in values.iter().zip(eq.iter()) {
            let mut term = *eq_value;
            term.mul_assign(value);
            result.add_assign(&term);
        }

        result
    }

    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            for (output, challenge) in kernel
                .inputs
                .outputs_in_extension
                .iter()
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn compute_combined_claim_with_batch_base(
        &self,
        output_claims: &BTreeMap<GKRAddress, E>,
        batch_challenge_base: E,
    ) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for output in kernel.inputs.outputs_in_extension.iter() {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(&challenge);
                result.add_assign(&term);
                challenge.mul_assign(&batch_challenge_base);
            }
        }

        result
    }

    fn launch_round0_kernels(
        &mut self,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, ((kernel, descriptors), batch_challenges)) in self
            .kernel_plans
            .iter()
            .zip(self.round0_descriptors.iter())
            .zip(batch_challenge_buffers.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            match kernel.batch_challenge_count {
                1 => launch_pairwise_round0(
                    descriptors,
                    batch_challenges.as_ptr(),
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_round0(
                    descriptors,
                    batch_challenges.as_ptr(),
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn launch_round1_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>],
        folding_challenge: &ScheduledChallengeBuffer<E>,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, ((kernel, descriptors), batch_challenges)) in self
            .kernel_plans
            .iter()
            .zip(scheduled.iter())
            .zip(batch_challenge_buffers.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            let input_descriptors = descriptors.device.extension_field_inputs.as_ptr();
            match kernel.batch_challenge_count {
                1 => launch_pairwise_continuation(
                    input_descriptors,
                    folding_challenge.as_ptr(),
                    batch_challenges.as_ptr(),
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_continuation(
                    input_descriptors,
                    folding_challenge.as_ptr(),
                    batch_challenges.as_ptr(),
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn launch_round2_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>],
        folding_challenge: &ScheduledChallengeBuffer<E>,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, ((kernel, descriptors), batch_challenges)) in self
            .kernel_plans
            .iter()
            .zip(scheduled.iter())
            .zip(batch_challenge_buffers.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            let input_descriptors = descriptors.device.extension_field_inputs.as_ptr();
            match kernel.batch_challenge_count {
                1 => launch_pairwise_continuation(
                    input_descriptors,
                    folding_challenge.as_ptr(),
                    batch_challenges.as_ptr(),
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_continuation(
                    input_descriptors,
                    folding_challenge.as_ptr(),
                    batch_challenges.as_ptr(),
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn launch_round3_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>],
        folding_challenge: &ScheduledChallengeBuffer<E>,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, ((kernel, descriptors), batch_challenges)) in self
            .kernel_plans
            .iter()
            .zip(scheduled.iter())
            .zip(batch_challenge_buffers.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            let input_descriptors = descriptors.device.extension_field_inputs.as_ptr();
            match kernel.batch_challenge_count {
                1 => launch_pairwise_continuation(
                    input_descriptors,
                    folding_challenge.as_ptr(),
                    batch_challenges.as_ptr(),
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_continuation(
                    input_descriptors,
                    folding_challenge.as_ptr(),
                    batch_challenges.as_ptr(),
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let challenge_offset = step + 1;
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        launch_build_eq_values(
            self.round_scratch.claim_point.as_ptr(),
            challenge_offset,
            challenge_count,
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )?;

        launch_weight_contributions(
            self.round_scratch.contributions.as_ptr(),
            self.kernel_plans.len(),
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.weighted_rows.as_mut_ptr(),
            acc_size,
            context,
        )?;

        let weighted_rows = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.weighted_rows.as_mut_ptr(),
                acc_size * 2,
            )
        };
        let weighted_matrix = DeviceMatrix::new(weighted_rows, acc_size);
        let reduction_output = unsafe {
            DeviceSlice::from_raw_parts_mut(self.round_scratch.reduction_output.as_mut_ptr(), 2)
        };
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        batch_reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &weighted_matrix,
            reduction_output,
            context.get_exec_stream(),
        )?;

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn evaluate_with_two_variable_eq_ext(values: &[E; 4], r_before_last: E, r_last: E) -> E {
        let mut result = E::ZERO;

        let mut w00 = E::ONE;
        w00.sub_assign(&r_before_last);
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w00.mul_assign(&tmp);
        let mut term = values[0];
        term.mul_assign(&w00);
        result.add_assign(&term);

        let mut w01 = E::ONE;
        w01.sub_assign(&r_before_last);
        w01.mul_assign(&r_last);
        let mut term = values[1];
        term.mul_assign(&w01);
        result.add_assign(&term);

        let mut w10 = r_before_last;
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w10.mul_assign(&tmp);
        let mut term = values[2];
        term.mul_assign(&w10);
        result.add_assign(&term);

        let mut w11 = r_before_last;
        w11.mul_assign(&r_last);
        let mut term = values[3];
        term.mul_assign(&w11);
        result.add_assign(&term);

        result
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let sources = match last_step {
                1 => &kernel.round1_prepared.extension_field_inputs,
                2 => {
                    &kernel
                        .round2_prepared
                        .as_ref()
                        .expect("round 2 storage must be prepared")
                        .extension_field_inputs
                }
                step => {
                    &kernel
                        .round3_and_beyond_prepared
                        .iter()
                        .find(|prepared| prepared.step == step)
                        .unwrap_or_else(|| {
                            panic!("missing prepared round 3+ storage for step {step}")
                        })
                        .prepared
                        .extension_field_inputs
                }
            };
            for (address, source) in kernel.inputs.inputs_in_extension.iter().zip(sources.iter()) {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 4, context)?,
            );
        }
        Ok(result)
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        _batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "dimension-reducing claim point must match folding steps"
        );

        let last_step = self.folding_steps - 1;
        let batch_challenge_values = self
            .kernel_plans
            .iter()
            .map(|kernel| kernel.batch_challenges.clone())
            .collect::<Vec<_>>();
        let batch_challenge_buffers =
            schedule_packed_immediate_field_uploads(context, 2, &batch_challenge_values)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_device = if last_step == 0 {
            None
        } else {
            Some(Arc::new(SharedChallengeDevice::new(
                context.alloc(last_step, AllocationPlacement::Top)?,
            )))
        };
        let mut start_callbacks = Callbacks::new();
        let claim_point_values = previous_claim_point.to_vec();
        let claim_point_host =
            alloc_host_and_schedule_copy(context, &mut start_callbacks, claim_point_values);
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;
        drop(claim_point_host);

        let shared_state = Arc::new(Mutex::new(ScheduledDimensionReducingLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));
        let mut round_states = Vec::with_capacity(last_step.saturating_sub(1) + 1);
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(&batch_challenge_buffers, acc_size, context)?;
            } else {
                match step {
                    1 => {
                        let mut callbacks = Callbacks::new();
                        let scheduled = self.schedule_round_1(&mut callbacks, context)?;
                        self.launch_round1_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round1 {
                            callbacks,
                            scheduled,
                        });
                    }
                    2 => {
                        let mut callbacks = Callbacks::new();
                        let scheduled = self.schedule_round_2(&mut callbacks, context)?;
                        self.launch_round2_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round2 {
                            callbacks,
                            scheduled,
                        });
                    }
                    _ => {
                        let mut callbacks = Callbacks::new();
                        let scheduled =
                            self.schedule_round_3_and_beyond(step, &mut callbacks, context)?;
                        self.launch_round3_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round3AndBeyond {
                            callbacks,
                            scheduled,
                        });
                    }
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges_offset = if step < last_step { Some(step) } else { None };
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord = previous_claim_point[step];
            let callback = move |dst: &mut [E]| {
                debug_assert_eq!(dst.len(), 1);
                unsafe {
                    let reduction = reduction_accessor.get();
                    let c0 = reduction[0];
                    let c2 = reduction[1];
                    let mut state = shared_state_for_callback.lock().unwrap();
                    let mut normalized_claim = state.claim;
                    normalized_claim.mul_assign(
                        &state
                            .eq_prefactor
                            .inverse()
                            .expect("eq prefactor must be non-zero"),
                    );
                    let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                        previous_claim_coord,
                        normalized_claim,
                        c0,
                        c2,
                    );
                    commit_field_els(&mut state.seed, &coeffs);
                    state.internal_round_coefficients.push(coeffs);

                    let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                    state.claim =
                        evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                    state.eq_prefactor =
                        evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                    state.folding_challenges.push(folding_challenge);
                    dst[0] = folding_challenge;
                }
            };
            let callbacks = if let (Some(device), Some(offset)) = (
                round_challenge_device.as_ref().cloned(),
                next_round_challenges_offset,
            ) {
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context, device, offset, 1, callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 1];
                        callback(&mut tmp);
                    },
                    context.get_exec_stream(),
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        let final_round_state = match last_step {
            1 => {
                let mut callbacks = Callbacks::new();
                let scheduled = self.schedule_round_1(&mut callbacks, context)?;
                self.launch_round1_kernels(
                    &scheduled,
                    &round_challenge_buffers[last_step - 1],
                    &batch_challenge_buffers,
                    1,
                    true,
                    context,
                )?;
                ScheduledDimensionReducingRoundState::Round1 {
                    callbacks,
                    scheduled,
                }
            }
            2 => {
                let mut callbacks = Callbacks::new();
                let scheduled = self.schedule_round_2(&mut callbacks, context)?;
                self.launch_round2_kernels(
                    &scheduled,
                    &round_challenge_buffers[last_step - 1],
                    &batch_challenge_buffers,
                    1,
                    true,
                    context,
                )?;
                ScheduledDimensionReducingRoundState::Round2 {
                    callbacks,
                    scheduled,
                }
            }
            step => {
                let mut callbacks = Callbacks::new();
                let scheduled = self.schedule_round_3_and_beyond(step, &mut callbacks, context)?;
                self.launch_round3_kernels(
                    &scheduled,
                    &round_challenge_buffers[last_step - 1],
                    &batch_challenge_buffers,
                    1,
                    true,
                    context,
                )?;
                ScheduledDimensionReducingRoundState::Round3AndBeyond {
                    callbacks,
                    scheduled,
                }
            }
        };
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges: Vec::new(),
            start_callbacks,
            batch_challenge_buffers,
            round_challenge_buffers,
            round_states: {
                let mut states = round_states;
                states.push(final_round_state);
                states
            },
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            round0_callbacks: self
                .round0_descriptors
                .iter_mut()
                .map(|d| std::mem::replace(&mut d.callbacks, Callbacks::new()))
                .collect(),
            shared_state,
        })
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer_from_workflow_state(
        &mut self,
        workflow_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        let mut start_callbacks = Callbacks::new();
        let shared_state = Arc::new(Mutex::new(ScheduledDimensionReducingLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));

        let mut claim_point_host = unsafe { context.alloc_host_uninit_slice(self.folding_steps) };
        let claim_point_accessor = claim_point_host.get_mut_accessor();
        let workflow_state_for_start = Arc::clone(&workflow_state);
        let shared_state_for_start = Arc::clone(&shared_state);
        let layer_claim_callback = self
            .kernel_plans
            .iter()
            .map(|kernel| {
                (
                    kernel.batch_challenge_offset,
                    kernel.inputs.outputs_in_extension.clone(),
                )
            })
            .collect::<Vec<_>>();
        start_callbacks.schedule(
            move || unsafe {
                let workflow_state = workflow_state_for_start.lock().unwrap();
                let dst = claim_point_accessor.get_mut();
                dst.copy_from_slice(&workflow_state.current_claim_point);
                let mut layer_state = shared_state_for_start.lock().unwrap();
                layer_state.seed = workflow_state.seed;
                layer_state.claim = {
                    let mut result = E::ZERO;
                    for (offset, outputs) in layer_claim_callback.iter() {
                        let mut challenge =
                            field_pow(workflow_state.current_batching_challenge, *offset);
                        for output in outputs.iter() {
                            let mut term = workflow_state
                                .current_claims
                                .get(output)
                                .copied()
                                .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                            term.mul_assign(&challenge);
                            result.add_assign(&term);
                            challenge.mul_assign(&workflow_state.current_batching_challenge);
                        }
                    }
                    result
                };
                layer_state.eq_prefactor = E::ONE;
                layer_state.folding_challenges.clear();
                layer_state.internal_round_coefficients.clear();
            },
            stream,
        )?;
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            stream,
        )?;

        let batch_specs = self
            .kernel_plans
            .iter()
            .map(|kernel| (kernel.batch_challenge_offset, kernel.batch_challenge_count))
            .collect::<Vec<_>>();
        let batch_challenge_buffers = schedule_packed_workflow_batch_challenge_uploads(
            context,
            Arc::clone(&workflow_state),
            2,
            &batch_specs,
        )?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_device = if last_step == 0 {
            None
        } else {
            Some(Arc::new(SharedChallengeDevice::new(
                context.alloc(last_step, AllocationPlacement::Top)?,
            )))
        };
        let mut round_states = Vec::with_capacity(last_step.saturating_sub(1) + 1);
        let mut reduction_states = Vec::with_capacity(last_step);
        let mut round3_plus_range = None;

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            let mut round_range = match step {
                0 => Some(Range::new(format!("{layer_name}.round0"))?),
                1 => Some(Range::new(format!("{layer_name}.round1"))?),
                2 => Some(Range::new(format!("{layer_name}.round2"))?),
                _ => None,
            };
            if let Some(range) = round_range.as_ref() {
                range.start(stream)?;
            }
            if step == 3 {
                let range = Range::new(format!("{layer_name}.round3_plus"))?;
                range.start(stream)?;
                round3_plus_range = Some(range);
            }

            if step == 0 {
                self.launch_round0_kernels(&batch_challenge_buffers, acc_size, context)?;
            } else {
                match step {
                    1 => {
                        let mut callbacks = Callbacks::new();
                        let mut scheduled = self.schedule_round_1(&mut callbacks, context)?;
                        self.launch_round1_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round1 {
                            callbacks,
                            scheduled,
                        });
                    }
                    2 => {
                        let mut callbacks = Callbacks::new();
                        let mut scheduled = self.schedule_round_2(&mut callbacks, context)?;
                        self.launch_round2_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round2 {
                            callbacks,
                            scheduled,
                        });
                    }
                    _ => {
                        let mut callbacks = Callbacks::new();
                        let mut scheduled =
                            self.schedule_round_3_and_beyond(step, &mut callbacks, context)?;
                        self.launch_round3_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round3AndBeyond {
                            callbacks,
                            scheduled,
                        });
                    }
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges_offset = if step < last_step { Some(step) } else { None };
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord_idx = step;
            let claim_point_for_callback = Arc::clone(&workflow_state);
            let callback = move |dst: &mut [E]| unsafe {
                debug_assert_eq!(dst.len(), 1);
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let previous_claim_coord =
                    claim_point_for_callback.lock().unwrap().current_claim_point
                        [previous_claim_coord_idx];
                let mut state = shared_state_for_callback.lock().unwrap();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                dst[0] = folding_challenge;
            };
            let callbacks = if let (Some(device), Some(offset)) = (
                round_challenge_device.as_ref().cloned(),
                next_round_challenges_offset,
            ) {
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context, device, offset, 1, callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 1];
                        callback(&mut tmp);
                    },
                    stream,
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });

            if let Some(range) = round_range.take() {
                range.end(stream)?;
                tracing_ranges.push(range);
            }
        }

        let mut final_round_range = match last_step {
            1 => Some(Range::new(format!("{layer_name}.round1"))?),
            2 => Some(Range::new(format!("{layer_name}.round2"))?),
            _ => None,
        };
        if let Some(range) = final_round_range.as_ref() {
            range.start(stream)?;
        }
        if last_step >= 3 && round3_plus_range.is_none() {
            let range = Range::new(format!("{layer_name}.round3_plus"))?;
            range.start(stream)?;
            round3_plus_range = Some(range);
        }

        let final_round_state = match last_step {
            1 => {
                let mut callbacks = Callbacks::new();
                let mut scheduled = self.schedule_round_1(&mut callbacks, context)?;
                self.launch_round1_kernels(
                    &scheduled,
                    &round_challenge_buffers[last_step - 1],
                    &batch_challenge_buffers,
                    1,
                    true,
                    context,
                )?;
                ScheduledDimensionReducingRoundState::Round1 {
                    callbacks,
                    scheduled,
                }
            }
            2 => {
                let mut callbacks = Callbacks::new();
                let mut scheduled = self.schedule_round_2(&mut callbacks, context)?;
                self.launch_round2_kernels(
                    &scheduled,
                    &round_challenge_buffers[last_step - 1],
                    &batch_challenge_buffers,
                    1,
                    true,
                    context,
                )?;
                ScheduledDimensionReducingRoundState::Round2 {
                    callbacks,
                    scheduled,
                }
            }
            step => {
                let mut callbacks = Callbacks::new();
                let mut scheduled =
                    self.schedule_round_3_and_beyond(step, &mut callbacks, context)?;
                self.launch_round3_kernels(
                    &scheduled,
                    &round_challenge_buffers[last_step - 1],
                    &batch_challenge_buffers,
                    1,
                    true,
                    context,
                )?;
                ScheduledDimensionReducingRoundState::Round3AndBeyond {
                    callbacks,
                    scheduled,
                }
            }
        };
        if let Some(range) = final_round_range.take() {
            range.end(stream)?;
            tracing_ranges.push(range);
        }
        if let Some(range) = round3_plus_range.take() {
            range.end(stream)?;
            tracing_ranges.push(range);
        }

        let finalize_range = Range::new(format!("{layer_name}.finalize"))?;
        finalize_range.start(stream)?;
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let workflow_state_for_callback = Arc::clone(&workflow_state);
        let folding_steps = self.folding_steps;
        let layer_idx = self.layer_idx;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                {
                    let mut workflow_state = workflow_state_for_callback.lock().unwrap();
                    workflow_state.current_claims = new_claims.clone();
                    workflow_state.current_claim_point = new_claim_point.clone();
                    workflow_state.current_batching_challenge = next_batching_challenge;
                    workflow_state.seed = state.seed;
                    workflow_state.proofs.insert(layer_idx, proof.clone());
                    workflow_state
                        .claims_for_layers
                        .insert(layer_idx, new_claims.clone());
                    workflow_state
                        .points_for_claims_at_layer
                        .insert(layer_idx, new_claim_point.clone());
                }

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            stream,
        )?;
        finalize_range.end(stream)?;
        tracing_ranges.push(finalize_range);
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(claim_point_host);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            start_callbacks,
            batch_challenge_buffers,
            round_challenge_buffers,
            round_states: {
                let mut states = round_states;
                states.push(final_round_state);
                states
            },
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            round0_callbacks: self
                .round0_descriptors
                .iter_mut()
                .map(|d| std::mem::replace(&mut d.callbacks, Callbacks::new()))
                .collect(),
            shared_state,
        })
    }
}

impl<B, E: FieldExtension<BF> + Field> GpuGKRDimensionReducingScheduledLayerExecution<B, E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRDimensionReducingHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            batch_challenge_buffers,
            round_challenge_buffers,
            round_states,
            reduction_states,
            final_readback,
            round0_callbacks,
            shared_state,
        } = self;
        GpuGKRDimensionReducingHostKeepalive {
            tracing_ranges,
            start_callbacks,
            batch_challenge_buffers: batch_challenge_buffers
                .into_iter()
                .map(challenge_buffer_into_host_keepalive)
                .collect(),
            round_challenge_buffers: round_challenge_buffers
                .into_iter()
                .map(challenge_buffer_into_host_keepalive)
                .collect(),
            round_states: round_states
                .into_iter()
                .map(dimension_reducing_round_state_into_host_keepalive)
                .collect(),
            reduction_states,
            final_readback,
            round0_callbacks,
            shared_state,
            _phantom: std::marker::PhantomData,
        }
    }

    pub(crate) fn into_execution(self) -> GpuGKRDimensionReducingLayerExecution<E> {
        self.shared_state
            .lock()
            .unwrap()
            .result
            .take()
            .expect("dimension-reducing layer execution is not ready yet")
    }
}

impl<E: 'static> GpuGKRMainLayerSumcheckLayerPlan<E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuMainLayerKernelSet,
    [(); E::DEGREE]: Sized,
{
    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            for (output, challenge) in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn compute_combined_claim_with_batch_base(
        &self,
        output_claims: &BTreeMap<GKRAddress, E>,
        batch_challenge_base: E,
    ) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for output in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(&challenge);
                result.add_assign(&term);
                challenge.mul_assign(&batch_challenge_base);
            }
        }

        result
    }

    fn launch_round0_kernels(
        &mut self,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        auxiliary_uploads: &[ScheduledUpload<E>],
        constraint_uploads: &[Option<ScheduledMainLayerConstraintMetadataUpload<E>>],
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (((kernel, descriptors), batch_challenges), auxiliary_upload)) in self
            .kernel_plans
            .iter()
            .zip(self.round0_descriptors.iter())
            .zip(batch_challenge_buffers.iter())
            .zip(auxiliary_uploads.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            launch_main_round0(
                kernel.kind,
                descriptors,
                batch_challenges.as_ptr(),
                auxiliary_upload.device.as_ptr(),
                constraint_uploads[idx].as_ref(),
                contributions,
                acc_size,
                context,
            )?;
        }

        Ok(())
    }

    fn launch_round1_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound1ScheduledLaunchDescriptors<BF, E>],
        folding_challenge: &ScheduledChallengeBuffer<E>,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        auxiliary_uploads: &[ScheduledUpload<E>],
        constraint_uploads: &[Option<ScheduledMainLayerConstraintMetadataUpload<E>>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (((kernel, descriptors), batch_challenges), auxiliary_upload)) in self
            .kernel_plans
            .iter()
            .zip(scheduled.iter())
            .zip(batch_challenge_buffers.iter())
            .zip(auxiliary_uploads.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            launch_main_round1(
                kernel.kind,
                descriptors,
                batch_challenges.as_ptr(),
                folding_challenge.as_ptr(),
                auxiliary_upload.device.as_ptr(),
                constraint_uploads[idx].as_ref(),
                explicit_form,
                contributions,
                acc_size,
                context,
            )?;
        }

        Ok(())
    }

    fn launch_round2_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound2ScheduledLaunchDescriptors<BF, E>],
        folding_challenges: &ScheduledChallengeBuffer<E>,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        auxiliary_uploads: &[ScheduledUpload<E>],
        constraint_uploads: &[Option<ScheduledMainLayerConstraintMetadataUpload<E>>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (((kernel, descriptors), batch_challenges), auxiliary_upload)) in self
            .kernel_plans
            .iter()
            .zip(scheduled.iter())
            .zip(batch_challenge_buffers.iter())
            .zip(auxiliary_uploads.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            launch_main_round2(
                kernel.kind,
                descriptors,
                batch_challenges.as_ptr(),
                folding_challenges.as_ptr(),
                auxiliary_upload.device.as_ptr(),
                constraint_uploads[idx].as_ref(),
                explicit_form,
                contributions,
                acc_size,
                context,
            )?;
        }

        Ok(())
    }

    fn launch_round3_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>],
        folding_challenge: &ScheduledChallengeBuffer<E>,
        batch_challenge_buffers: &[ScheduledChallengeBuffer<E>],
        auxiliary_uploads: &[ScheduledUpload<E>],
        constraint_uploads: &[Option<ScheduledMainLayerConstraintMetadataUpload<E>>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (((kernel, descriptors), batch_challenges), auxiliary_upload)) in self
            .kernel_plans
            .iter()
            .zip(scheduled.iter())
            .zip(batch_challenge_buffers.iter())
            .zip(auxiliary_uploads.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            launch_main_round3(
                kernel.kind,
                descriptors,
                batch_challenges.as_ptr(),
                folding_challenge.as_ptr(),
                auxiliary_upload.device.as_ptr(),
                constraint_uploads[idx].as_ref(),
                explicit_form,
                contributions,
                acc_size,
                context,
            )?;
        }

        Ok(())
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let challenge_offset = step + 1;
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        launch_build_eq_values(
            self.round_scratch.claim_point.as_ptr(),
            challenge_offset,
            challenge_count,
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )?;
        launch_weight_contributions(
            self.round_scratch.contributions.as_ptr(),
            self.kernel_plans.len(),
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.weighted_rows.as_mut_ptr(),
            acc_size,
            context,
        )?;

        let weighted_rows = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.weighted_rows.as_mut_ptr(),
                acc_size * 2,
            )
        };
        let weighted_matrix = DeviceMatrix::new(weighted_rows, acc_size);
        let reduction_output = unsafe {
            DeviceSlice::from_raw_parts_mut(self.round_scratch.reduction_output.as_mut_ptr(), 2)
        };
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        batch_reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &weighted_matrix,
            reduction_output,
            context.get_exec_stream(),
        )?;

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        assert!(last_step >= 3, "main-layer final step must be in round 3+");
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let prepared = &kernel
                .round3_and_beyond_prepared
                .iter()
                .find(|prepared| prepared.step == last_step)
                .unwrap_or_else(|| panic!("missing round 3+ prepared storage for step {last_step}"))
                .prepared;
            for (address, source) in kernel
                .inputs
                .inputs_in_base
                .iter()
                .zip(prepared.base_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
            for (address, source) in kernel
                .inputs
                .inputs_in_extension
                .iter()
                .zip(prepared.extension_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 2, context)?,
            );
        }
        Ok(result)
    }

    fn interpolate_linear(f0: E, f1: E, r: &E) -> E {
        let mut result = f1;
        result.sub_assign(&f0);
        result.mul_assign(r);
        result.add_assign(&f0);
        result
    }

    pub(crate) fn schedule_execute_main_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "main-layer claim point must match folding steps"
        );

        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        let batch_challenge_values = self
            .kernel_plans
            .iter()
            .map(|kernel| kernel.batch_challenges.clone())
            .collect::<Vec<_>>();
        let batch_challenge_buffers =
            schedule_packed_immediate_field_uploads(context, 2, &batch_challenge_values)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_len = (1..=last_step)
            .map(main_layer_round_challenge_len)
            .sum::<usize>();
        let round_challenge_device = Arc::new(SharedChallengeDevice::new(
            context.alloc(round_challenge_len, AllocationPlacement::Top)?,
        ));
        let mut next_round_challenge_offset = 0usize;
        let mut start_callbacks = Callbacks::new();
        let claim_point_values = previous_claim_point.to_vec();
        let claim_point_host =
            alloc_host_and_schedule_copy(context, &mut start_callbacks, claim_point_values);
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;
        drop(claim_point_host);
        let mut main_layer_challenges_host = unsafe { context.alloc_host_uninit_slice(2) };
        let challenges_fill_accessor = main_layer_challenges_host.get_mut_accessor();
        start_callbacks.schedule(
            move || unsafe {
                let dst = challenges_fill_accessor.get_mut();
                dst[0] = E::ZERO;
                dst[1] = E::ZERO;
            },
            context.get_exec_stream(),
        )?;
        let main_layer_challenges = main_layer_challenges_host.get_accessor();

        let shared_state = Arc::new(Mutex::new(ScheduledMainLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));
        let mut auxiliary_uploads = Vec::with_capacity(self.kernel_plans.len());
        let mut constraint_uploads = Vec::with_capacity(self.kernel_plans.len());
        for kernel in self.kernel_plans.iter() {
            auxiliary_uploads.push(schedule_main_layer_auxiliary_upload(
                kernel.auxiliary_challenge_source,
                main_layer_challenges,
                context,
            )?);
            constraint_uploads.push(schedule_main_layer_constraint_metadata_upload(
                kernel.constraint_metadata_source.as_ref(),
                main_layer_challenges,
                context,
            )?);
        }
        drop(main_layer_challenges_host);
        let mut round_states = Vec::with_capacity(last_step);
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(
                    &batch_challenge_buffers,
                    &auxiliary_uploads,
                    &constraint_uploads,
                    acc_size,
                    context,
                )?;
            } else {
                match step {
                    1 => {
                        let mut callbacks = Callbacks::new();
                        let scheduled = self.schedule_round_1(&mut callbacks, context)?;
                        self.launch_round1_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledMainLayerRoundState::Round1 {
                            callbacks,
                            scheduled,
                        });
                    }
                    2 => {
                        let mut callbacks = Callbacks::new();
                        let scheduled = self.schedule_round_2(&mut callbacks, context)?;
                        self.launch_round2_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledMainLayerRoundState::Round2 {
                            callbacks,
                            scheduled,
                        });
                    }
                    _ => {
                        let mut callbacks = Callbacks::new();
                        let scheduled =
                            self.schedule_round_3_and_beyond(step, &mut callbacks, context)?;
                        self.launch_round3_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledMainLayerRoundState::Round3AndBeyond {
                            callbacks,
                            scheduled,
                        });
                    }
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_len =
                (step < last_step).then(|| main_layer_round_challenge_len(step + 1));
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord = previous_claim_point[step];
            let callback = move |dst: &mut [E]| unsafe {
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let mut state = shared_state_for_callback.lock().unwrap();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                match step + 1 {
                    1 => dst[0] = state.folding_challenges[0],
                    2 => {
                        dst[0] = state.folding_challenges[0];
                        dst[1] = state.folding_challenges[1];
                    }
                    _ => dst[0] = *state.folding_challenges.last().unwrap(),
                }
            };
            let callbacks = if let Some(len) = next_round_len {
                let offset = next_round_challenge_offset;
                next_round_challenge_offset += len;
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    Arc::clone(&round_challenge_device),
                    offset,
                    len,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 2];
                        callback(&mut tmp[..main_layer_round_challenge_len(step + 1)]);
                    },
                    context.get_exec_stream(),
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        let final_round_state = {
            let mut callbacks = Callbacks::new();
            let scheduled = self.schedule_round_3_and_beyond(last_step, &mut callbacks, context)?;
            self.launch_round3_kernels(
                &scheduled,
                &round_challenge_buffers[last_step - 1],
                &batch_challenge_buffers,
                &auxiliary_uploads,
                &constraint_uploads,
                1,
                true,
                context,
            )?;
            ScheduledMainLayerRoundState::Round3AndBeyond {
                callbacks,
                scheduled,
            }
        };
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 2] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 2);
                let [last_r, next_batching_challenge]: [E; 2] = challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(last_r);
                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, [f0, f1])| (*addr, Self::interpolate_linear(*f0, *f1, &last_r)))
                    .collect();
                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRMainLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        let mut all_round_states = round_states;
        all_round_states.push(final_round_state);

        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges: Vec::new(),
            start_callbacks,
            batch_challenge_buffers,
            auxiliary_uploads,
            constraint_uploads,
            round_challenge_buffers,
            round_states: all_round_states,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            round0_callbacks: self
                .round0_descriptors
                .iter_mut()
                .map(|d| std::mem::replace(&mut d.callbacks, Callbacks::new()))
                .collect(),
            shared_state,
        })
    }

    pub(crate) fn schedule_execute_main_layer_from_workflow_state(
        &mut self,
        workflow_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.main.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        let mut start_callbacks = Callbacks::new();
        let shared_state = Arc::new(Mutex::new(ScheduledMainLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));

        let mut claim_point_host = unsafe { context.alloc_host_uninit_slice(self.folding_steps) };
        let claim_point_accessor = claim_point_host.get_mut_accessor();
        let mut main_layer_challenges_host = unsafe { context.alloc_host_uninit_slice(2) };
        let main_layer_challenges_accessor = main_layer_challenges_host.get_mut_accessor();
        let main_layer_challenges = main_layer_challenges_host.get_accessor();
        let workflow_state_for_start = Arc::clone(&workflow_state);
        let shared_state_for_start = Arc::clone(&shared_state);
        let layer_claim_callback = self
            .kernel_plans
            .iter()
            .filter(|kernel| {
                kernel.kind != GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
            })
            .map(|kernel| {
                (
                    kernel.batch_challenge_offset,
                    kernel
                        .inputs
                        .outputs_in_base
                        .iter()
                        .chain(kernel.inputs.outputs_in_extension.iter())
                        .copied()
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        start_callbacks.schedule(
            move || unsafe {
                let workflow_state = workflow_state_for_start.lock().unwrap();
                let dst = claim_point_accessor.get_mut();
                dst.copy_from_slice(&workflow_state.current_claim_point);
                let challenges = main_layer_challenges_accessor.get_mut();
                challenges[0] = workflow_state.lookup_additive_challenge;
                challenges[1] = workflow_state.constraint_batch_challenge;
                let mut layer_state = shared_state_for_start.lock().unwrap();
                layer_state.seed = workflow_state.seed;
                layer_state.claim = {
                    let mut result = E::ZERO;
                    for (offset, outputs) in layer_claim_callback.iter() {
                        let mut challenge =
                            field_pow(workflow_state.current_batching_challenge, *offset);
                        for output in outputs.iter() {
                            let mut term = workflow_state
                                .current_claims
                                .get(output)
                                .copied()
                                .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                            term.mul_assign(&challenge);
                            result.add_assign(&term);
                            challenge.mul_assign(&workflow_state.current_batching_challenge);
                        }
                    }
                    result
                };
                layer_state.eq_prefactor = E::ONE;
                layer_state.folding_challenges.clear();
                layer_state.internal_round_coefficients.clear();
            },
            stream,
        )?;
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            stream,
        )?;

        let batch_specs = self
            .kernel_plans
            .iter()
            .map(|kernel| (kernel.batch_challenge_offset, kernel.batch_challenge_count))
            .collect::<Vec<_>>();
        let batch_challenge_buffers = schedule_packed_workflow_batch_challenge_uploads(
            context,
            Arc::clone(&workflow_state),
            2,
            &batch_specs,
        )?;
        let mut auxiliary_uploads = Vec::with_capacity(self.kernel_plans.len());
        let mut constraint_uploads = Vec::with_capacity(self.kernel_plans.len());
        for kernel in self.kernel_plans.iter() {
            auxiliary_uploads.push(schedule_main_layer_auxiliary_upload(
                kernel.auxiliary_challenge_source,
                main_layer_challenges,
                context,
            )?);
            constraint_uploads.push(schedule_main_layer_constraint_metadata_upload(
                kernel.constraint_metadata_source.as_ref(),
                main_layer_challenges,
                context,
            )?);
        }
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_len = (1..=last_step)
            .map(main_layer_round_challenge_len)
            .sum::<usize>();
        let round_challenge_device = Arc::new(SharedChallengeDevice::new(
            context.alloc(round_challenge_len, AllocationPlacement::Top)?,
        ));
        let mut next_round_challenge_offset = 0usize;
        let mut round_states = Vec::with_capacity(last_step);
        let mut reduction_states = Vec::with_capacity(last_step);
        let mut round3_plus_range = None;

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            let mut round_range = match step {
                0 => Some(Range::new(format!("{layer_name}.round0"))?),
                1 => Some(Range::new(format!("{layer_name}.round1"))?),
                2 => Some(Range::new(format!("{layer_name}.round2"))?),
                _ => None,
            };
            if let Some(range) = round_range.as_ref() {
                range.start(stream)?;
            }
            if step == 3 {
                let range = Range::new(format!("{layer_name}.round3_plus"))?;
                range.start(stream)?;
                round3_plus_range = Some(range);
            }

            if step == 0 {
                self.launch_round0_kernels(
                    &batch_challenge_buffers,
                    &auxiliary_uploads,
                    &constraint_uploads,
                    acc_size,
                    context,
                )?;
            } else {
                match step {
                    1 => {
                        let mut callbacks = Callbacks::new();
                        let mut scheduled = self.schedule_round_1(&mut callbacks, context)?;
                        self.launch_round1_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledMainLayerRoundState::Round1 {
                            callbacks,
                            scheduled,
                        });
                    }
                    2 => {
                        let mut callbacks = Callbacks::new();
                        let mut scheduled = self.schedule_round_2(&mut callbacks, context)?;
                        self.launch_round2_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledMainLayerRoundState::Round2 {
                            callbacks,
                            scheduled,
                        });
                    }
                    _ => {
                        let mut callbacks = Callbacks::new();
                        let mut scheduled =
                            self.schedule_round_3_and_beyond(step, &mut callbacks, context)?;
                        self.launch_round3_kernels(
                            &scheduled,
                            &round_challenge_buffers[step - 1],
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )?;
                        round_states.push(ScheduledMainLayerRoundState::Round3AndBeyond {
                            callbacks,
                            scheduled,
                        });
                    }
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_len =
                (step < last_step).then(|| main_layer_round_challenge_len(step + 1));
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord_idx = step;
            let claim_point_for_callback = Arc::clone(&workflow_state);
            let callback = move |dst: &mut [E]| unsafe {
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let previous_claim_coord =
                    claim_point_for_callback.lock().unwrap().current_claim_point
                        [previous_claim_coord_idx];
                let mut state = shared_state_for_callback.lock().unwrap();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                match step + 1 {
                    1 => dst[0] = state.folding_challenges[0],
                    2 => {
                        dst[0] = state.folding_challenges[0];
                        dst[1] = state.folding_challenges[1];
                    }
                    _ => dst[0] = *state.folding_challenges.last().unwrap(),
                }
            };
            let callbacks = if let Some(len) = next_round_len {
                let offset = next_round_challenge_offset;
                next_round_challenge_offset += len;
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    Arc::clone(&round_challenge_device),
                    offset,
                    len,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 2];
                        callback(&mut tmp[..main_layer_round_challenge_len(step + 1)]);
                    },
                    stream,
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });

            if let Some(range) = round_range.take() {
                range.end(stream)?;
                tracing_ranges.push(range);
            }
        }

        if round3_plus_range.is_none() {
            let range = Range::new(format!("{layer_name}.round3_plus"))?;
            range.start(stream)?;
            round3_plus_range = Some(range);
        }
        let final_round_state = {
            let mut callbacks = Callbacks::new();
            let mut scheduled =
                self.schedule_round_3_and_beyond(last_step, &mut callbacks, context)?;
            self.launch_round3_kernels(
                &scheduled,
                &round_challenge_buffers[last_step - 1],
                &batch_challenge_buffers,
                &auxiliary_uploads,
                &constraint_uploads,
                1,
                true,
                context,
            )?;
            ScheduledMainLayerRoundState::Round3AndBeyond {
                callbacks,
                scheduled,
            }
        };
        if let Some(range) = round3_plus_range.take() {
            range.end(stream)?;
            tracing_ranges.push(range);
        }

        let finalize_range = Range::new(format!("{layer_name}.finalize"))?;
        finalize_range.start(stream)?;
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let workflow_state_for_callback = Arc::clone(&workflow_state);
        let folding_steps = self.folding_steps;
        let layer_idx = self.layer_idx;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 2] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 2);
                let [last_r, next_batching_challenge]: [E; 2] = challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(last_r);
                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, [f0, f1])| (*addr, Self::interpolate_linear(*f0, *f1, &last_r)))
                    .collect::<BTreeMap<_, _>>();
                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                {
                    let mut workflow_state = workflow_state_for_callback.lock().unwrap();
                    workflow_state.current_claims = new_claims.clone();
                    workflow_state.current_claim_point = new_claim_point.clone();
                    workflow_state.current_batching_challenge = next_batching_challenge;
                    workflow_state.seed = state.seed;
                    workflow_state.proofs.insert(layer_idx, proof.clone());
                    workflow_state
                        .claims_for_layers
                        .insert(layer_idx, new_claims.clone());
                    workflow_state
                        .points_for_claims_at_layer
                        .insert(layer_idx, new_claim_point.clone());
                }

                state.result = Some(GpuGKRMainLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            stream,
        )?;
        finalize_range.end(stream)?;
        tracing_ranges.push(finalize_range);
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        let mut all_round_states = round_states;
        all_round_states.push(final_round_state);

        drop(claim_point_host);
        drop(main_layer_challenges_host);
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            start_callbacks,
            batch_challenge_buffers,
            auxiliary_uploads,
            constraint_uploads,
            round_challenge_buffers,
            round_states: all_round_states,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            round0_callbacks: self
                .round0_descriptors
                .iter_mut()
                .map(|d| std::mem::replace(&mut d.callbacks, Callbacks::new()))
                .collect(),
            shared_state,
        })
    }
}

impl<E: FieldExtension<BF> + Field> GpuGKRMainLayerScheduledLayerExecution<E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRMainLayerHostKeepalive<E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            batch_challenge_buffers,
            auxiliary_uploads,
            constraint_uploads,
            round_challenge_buffers,
            round_states,
            reduction_states,
            final_readback,
            round0_callbacks,
            shared_state,
        } = self;
        GpuGKRMainLayerHostKeepalive {
            tracing_ranges,
            start_callbacks,
            batch_challenge_buffers: batch_challenge_buffers
                .into_iter()
                .map(challenge_buffer_into_host_keepalive)
                .collect(),
            auxiliary_uploads: auxiliary_uploads
                .into_iter()
                .map(upload_into_host_keepalive)
                .collect(),
            constraint_uploads: constraint_uploads
                .into_iter()
                .map(|upload| upload.map(constraint_upload_into_host_keepalive))
                .collect(),
            round_challenge_buffers: round_challenge_buffers
                .into_iter()
                .map(challenge_buffer_into_host_keepalive)
                .collect(),
            round_states: round_states
                .into_iter()
                .map(main_layer_round_state_into_host_keepalive)
                .collect(),
            reduction_states,
            final_readback,
            round0_callbacks,
            shared_state,
        }
    }

    pub(crate) fn into_execution(self) -> GpuGKRMainLayerExecution<E> {
        self.shared_state
            .lock()
            .unwrap()
            .result
            .take()
            .expect("main-layer execution is not ready yet")
    }
}

impl<B, E> GpuGKRBackwardScheduledExecution<B, E>
where
    E: FieldExtension<BF> + Field,
{
    pub(crate) fn into_host_keepalive(self) -> GpuGKRBackwardHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
        } = self;
        GpuGKRBackwardHostKeepalive {
            tracing_ranges,
            dimension_reducing_layers: dimension_reducing_layers
                .into_iter()
                .map(GpuGKRDimensionReducingScheduledLayerExecution::into_host_keepalive)
                .collect(),
            main_layers: main_layers
                .into_iter()
                .map(GpuGKRMainLayerScheduledLayerExecution::into_host_keepalive)
                .collect(),
            shared_state,
        }
    }

    pub(crate) fn shared_state_handle(&self) -> Arc<Mutex<ScheduledBackwardWorkflowState<E>>> {
        Arc::clone(&self.shared_state)
    }

    pub(crate) fn wait(self, context: &ProverContext) -> CudaResult<GpuGKRBackwardExecution<E>> {
        context.get_exec_stream().synchronize()?;
        let mut state = self.shared_state.lock().unwrap();
        Ok(GpuGKRBackwardExecution {
            proofs: std::mem::take(&mut state.proofs),
            claims_for_layers: std::mem::take(&mut state.claims_for_layers),
            points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
            next_batching_challenge: state.current_batching_challenge,
            updated_seed: state.seed,
        })
    }
}

impl<E> GpuGKRDimensionReducingBackwardState<BF, E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuMainLayerKernelSet + 'static,
    [(); E::DEGREE]: Sized,
{
    pub(crate) fn schedule_execute_backward_workflow_from_shared_state(
        mut self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        shared_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let workflow_range = Range::new("gkr.backward.schedule")?;
        workflow_range.start(stream)?;
        let mut dimension_reducing_layers = Vec::new();
        let dimension_reducing_layers_range = Range::new("gkr.backward.dimension_reducing_layers")?;
        dimension_reducing_layers_range.start(stream)?;
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(context)? {
            let layer_idx = prepared_layer.layer_idx;
            dimension_reducing_layers.push(
                prepared_layer.schedule_execute_dimension_reducing_layer_from_workflow_state(
                    Arc::clone(&shared_state),
                    context,
                )?,
            );
            // Stream-ordered storage can be dropped once the layer's uploads and kernels have
            // been fully enqueued on exec_stream.
            self.purge_up_to_layer(layer_idx);
        }
        dimension_reducing_layers_range.end(stream)?;
        tracing_ranges.push(dimension_reducing_layers_range);

        let mut main_backward_state =
            self.into_main_layer_backward_state(compiled_circuit, E::ZERO, E::ZERO);
        let mut main_layers = Vec::new();
        let main_layers_range = Range::new("gkr.backward.main_layers")?;
        main_layers_range.start(stream)?;
        while let Some(mut prepared_layer) =
            main_backward_state.prepare_next_layer_static(context)?
        {
            let layer_idx = prepared_layer.layer_idx;
            main_layers.push(
                prepared_layer.schedule_execute_main_layer_from_workflow_state(
                    Arc::clone(&shared_state),
                    context,
                )?,
            );
            main_backward_state.purge_up_to_layer(layer_idx);
        }
        main_layers_range.end(stream)?;
        tracing_ranges.push(main_layers_range);

        let GpuGKRMainLayerBackwardState { storage: _, .. } = main_backward_state;
        // Remaining main-layer storage drops here after all exec-stream work has been scheduled.
        workflow_range.end(stream)?;
        tracing_ranges.push(workflow_range);

        Ok(GpuGKRBackwardScheduledExecution {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn schedule_execute_backward_workflow(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        initial_output_layer_idx: usize,
        top_layer_claims: BTreeMap<GKRAddress, E>,
        evaluation_point: Vec<E>,
        seed: Seed,
        batching_challenge: E,
        lookup_additive_challenge: E,
        constraint_batch_challenge: E,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let shared_state = Arc::new(Mutex::new(ScheduledBackwardWorkflowState {
            claims_for_layers: BTreeMap::from([(
                initial_output_layer_idx,
                top_layer_claims.clone(),
            )]),
            points_for_claims_at_layer: BTreeMap::from([(
                initial_output_layer_idx,
                evaluation_point.clone(),
            )]),
            current_claims: top_layer_claims,
            current_claim_point: evaluation_point,
            current_batching_challenge: batching_challenge,
            lookup_additive_challenge,
            constraint_batch_challenge,
            seed,
            proofs: BTreeMap::new(),
        }));
        self.schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit,
            shared_state,
            context,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{
        build_dimension_reducing_kernel_blueprints, build_main_layer_kernel_blueprints,
        launch_build_eq_values, launch_lookup_continuation, launch_lookup_round0,
        launch_main_round0, launch_pairwise_continuation, launch_pairwise_round0,
        launch_weight_contributions, make_deferred_backward_workflow_state,
        populate_backward_workflow_state, schedule_workflow_batch_challenge_upload,
        GKRCircuitArtifact, GpuGKRDimensionReducingBackwardState,
        GpuGKRMainLayerConstraintLinearTerm, GpuGKRMainLayerConstraintQuadraticTerm,
        GpuGKRMainLayerKernelKind,
    };
    use crate::allocator::tracker::AllocationPlacement;
    use crate::ops::cub::device_reduce::{
        batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
    };
    use crate::primitives::callbacks::Callbacks;
    use crate::primitives::context::{DeviceAllocation, ProverContext};
    use crate::primitives::device_structures::DeviceMatrix;
    use crate::primitives::field::{BF, E4};
    use crate::prover::gkr::{
        GpuBaseFieldPolySource, GpuExtensionFieldPolyContinuingLaunchDescriptor,
        GpuExtensionFieldPolyInitialSource, GpuSumcheckRound0DeviceLaunchDescriptors,
        GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0ScheduledLaunchDescriptors,
    };
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::{
        GKRLayerDescription, GateArtifacts, NoFieldGKRRelation,
        NoFieldMaxQuadraticConstraintsGKRRelation, OutputType,
    };
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
    use field::{Field, FieldExtension};
    use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
    use prover::gkr::sumcheck::evaluation_kernels::{
        BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    };
    use prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic;
    use prover::transcript::Seed;
    use serial_test::serial;
    use std::collections::BTreeMap;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    fn successive_powers<E: Field>(base: E, count: usize) -> Vec<E> {
        let mut current = E::ONE;
        (0..count)
            .map(|_| {
                let result = current;
                current.mul_assign(&base);
                result
            })
            .collect()
    }

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        allocation
    }

    fn copy_device_values<T: Copy>(context: &ProverContext, values: &DeviceSlice<T>) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { allocation.get_accessor().get().to_vec() }
    }

    #[test]
    #[serial]
    fn shared_state_dimension_reduction_purges_storage_after_each_layer() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let expected_dimension_reducing_layers =
            fixture.initial_output_layer_idx - fixture.compiled_circuit.layers.len();
        assert!(
            expected_dimension_reducing_layers >= 2,
            "fixture must include multiple dimension-reducing layers"
        );

        let mut backward_state = fixture.gpu_backward_state;
        let shared_state = make_deferred_backward_workflow_state();
        populate_backward_workflow_state(
            &shared_state,
            fixture.initial_output_layer_idx,
            fixture.top_layer_claims,
            fixture.evaluation_point,
            fixture.seed,
            fixture.batching_challenge,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        let mut dimension_reducing_layers = Vec::new();
        let mut purged_layers = 0usize;
        while let Some(mut prepared_layer) =
            backward_state.prepare_next_layer_static(context).unwrap()
        {
            let layer_idx = prepared_layer.layer_idx;
            let scheduled = prepared_layer
                .schedule_execute_dimension_reducing_layer_from_workflow_state(
                    std::sync::Arc::clone(&shared_state),
                    context,
                )
                .unwrap();
            dimension_reducing_layers.push(scheduled);
            backward_state.purge_up_to_layer(layer_idx);
            purged_layers += 1;

            assert_eq!(
                backward_state.storage().layers.len(),
                layer_idx + 1,
                "storage should be truncated through scheduled dimension-reducing layer {layer_idx}"
            );
            assert!(
                backward_state.storage().layers.get(layer_idx + 1).is_none(),
                "layers above {layer_idx} should be purged after scheduling"
            );
        }

        assert_eq!(purged_layers, expected_dimension_reducing_layers);

        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            E4::ZERO,
            E4::ZERO,
        );
        let mut first_main_layer = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan after dimension reduction");
        let first_main_layer_idx = first_main_layer.layer_idx;
        let _first_main_layer_execution = first_main_layer
            .schedule_execute_main_layer_from_workflow_state(
                std::sync::Arc::clone(&shared_state),
                context,
            )
            .unwrap();

        context.get_exec_stream().synchronize().unwrap();

        let execution = super::take_backward_execution_from_shared_state(&shared_state);
        assert!(
            execution.proofs.contains_key(&first_main_layer_idx),
            "shared-state workflow should still schedule the first main layer after purging"
        );
    }

    #[test]
    #[serial]
    fn first_main_layer_static_uploads_match_expected_values() {
        fn advance_dimension_reduction(
            mut state: GpuGKRDimensionReducingBackwardState<BF, E4>,
            compiled_circuit: &GKRCircuitArtifact<BF>,
            mut current_claims: BTreeMap<GKRAddress, E4>,
            mut current_point: Vec<E4>,
            mut seed: Seed,
            mut batching_challenge: E4,
            lookup_additive_part: E4,
            constraints_batch_challenge: E4,
            context: &ProverContext,
        ) -> (
            crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
            BTreeMap<GKRAddress, E4>,
            Vec<E4>,
            Seed,
            E4,
        ) {
            while let Some(mut plan) = state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            {
                let scheduled = plan
                    .schedule_execute_dimension_reducing_layer(
                        &current_claims,
                        &current_point,
                        seed,
                        batching_challenge,
                        context,
                    )
                    .unwrap();
                context.get_exec_stream().synchronize().unwrap();
                let execution = scheduled.into_execution();
                current_claims = execution.new_claims;
                current_point = execution.new_claim_point;
                seed = execution.updated_seed;
                batching_challenge = execution.next_batching_challenge;
            }

            (
                state.into_main_layer_backward_state(
                    compiled_circuit.clone(),
                    lookup_additive_part,
                    constraints_batch_challenge,
                ),
                current_claims,
                current_point,
                seed,
                batching_challenge,
            )
        }

        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let (mut main_state, current_claims, current_point, seed, batching_challenge) =
            advance_dimension_reduction(
                fixture.gpu_backward_state,
                &fixture.compiled_circuit,
                fixture.top_layer_claims,
                fixture.evaluation_point,
                fixture.seed,
                fixture.batching_challenge,
                fixture.lookup_additive_part,
                fixture.constraints_batch_challenge,
                context,
            );

        let static_plan = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan");
        let expected = crate::prover::tests::expected_main_layer_kernel_specs_for_test(
            &fixture.compiled_circuit.layers[static_plan.layer_idx],
            static_plan.layer_idx,
            main_state.storage(),
            batching_challenge,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
            fixture.compiled_circuit.memory_layout.total_width,
            fixture.compiled_circuit.witness_layout.total_width,
        );
        assert_eq!(static_plan.kernel_plans.len(), expected.len());

        let shared_state = make_deferred_backward_workflow_state();
        populate_backward_workflow_state(
            &shared_state,
            static_plan.layer_idx + 1,
            current_claims,
            current_point,
            seed,
            batching_challenge,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        let mut main_layer_challenges_host = unsafe { context.alloc_host_uninit_slice(2) };
        unsafe {
            let accessor = main_layer_challenges_host.get_mut_accessor();
            let dst = accessor.get_mut();
            dst[0] = fixture.lookup_additive_part;
            dst[1] = fixture.constraints_batch_challenge;
        }
        let main_layer_challenges = main_layer_challenges_host.get_accessor();

        let mut batch_challenge_buffers = Vec::with_capacity(static_plan.kernel_plans.len());
        let mut auxiliary_uploads = Vec::with_capacity(static_plan.kernel_plans.len());
        let mut constraint_uploads = Vec::with_capacity(static_plan.kernel_plans.len());
        for kernel in static_plan.kernel_plans.iter() {
            batch_challenge_buffers.push(
                schedule_workflow_batch_challenge_upload(
                    context,
                    std::sync::Arc::clone(&shared_state),
                    2,
                    kernel.batch_challenge_offset,
                    kernel.batch_challenge_count,
                )
                .unwrap(),
            );
            auxiliary_uploads.push(
                super::schedule_main_layer_auxiliary_upload(
                    kernel.auxiliary_challenge_source,
                    main_layer_challenges,
                    context,
                )
                .unwrap(),
            );
            constraint_uploads.push(
                super::schedule_main_layer_constraint_metadata_upload(
                    kernel.constraint_metadata_source.as_ref(),
                    main_layer_challenges,
                    context,
                )
                .unwrap(),
            );
        }
        context.get_exec_stream().synchronize().unwrap();

        for (idx, expected_kernel) in expected.iter().enumerate() {
            let mut expected_batch = vec![E4::ZERO; 2];
            expected_batch[..expected_kernel.batch_challenges.len()]
                .copy_from_slice(&expected_kernel.batch_challenges);
            assert_eq!(
                copy_device_values(context, batch_challenge_buffers[idx].device_slice()),
                expected_batch,
                "kernel {idx} batch challenges mismatch"
            );
            assert_eq!(
                copy_device_values(context, &auxiliary_uploads[idx].device),
                vec![expected_kernel.auxiliary_challenge],
                "kernel {idx} auxiliary challenge mismatch"
            );

            match (
                &constraint_uploads[idx],
                &expected_kernel.constraint_metadata,
            ) {
                (None, None) => {}
                (Some(actual), Some(expected_metadata)) => {
                    assert_eq!(
                        copy_device_values(context, &actual.quadratic_terms.device),
                        expected_metadata.quadratic_terms,
                        "kernel {idx} quadratic metadata mismatch"
                    );
                    assert_eq!(
                        copy_device_values(context, &actual.linear_terms.device),
                        expected_metadata.linear_terms,
                        "kernel {idx} linear metadata mismatch"
                    );
                    assert_eq!(
                        copy_device_values(context, &actual.constant_offset.device),
                        vec![expected_metadata.constant_offset],
                        "kernel {idx} constant offset mismatch"
                    );
                }
                _ => panic!("kernel {idx} constraint metadata presence mismatch"),
            }
        }
    }

    #[test]
    #[serial]
    fn main_layer0_round_coefficients_match_cpu_reference() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let cpu_fixture = crate::prover::tests::prepare_basic_unrolled_proof_fixture();
        let expected_layer0 = cpu_fixture
            .expected_cpu_proof
            .sumcheck_intermediate_values
            .get(&0)
            .expect("CPU proof must contain layer 0");
        let context = &fixture.context;

        let mut backward_state = fixture.gpu_backward_state;
        let mut current_claims = fixture.top_layer_claims;
        let mut current_point = fixture.evaluation_point;
        let mut seed = fixture.seed;
        let mut batching_challenge = fixture.batching_challenge;

        while let Some(mut plan) = backward_state
            .prepare_next_layer(batching_challenge, context)
            .unwrap()
        {
            let scheduled = plan
                .schedule_execute_dimension_reducing_layer(
                    &current_claims,
                    &current_point,
                    seed,
                    batching_challenge,
                    context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
        }

        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        let mut layer0_plan = loop {
            let Some(mut plan) = main_state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            else {
                panic!("expected to reach main layer 0");
            };
            let layer_idx = plan.layer_idx;
            if layer_idx == 0 {
                break plan;
            }
            let scheduled = plan
                .schedule_execute_main_layer(&current_claims, &current_point, seed, context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
            main_state.purge_up_to_layer(layer_idx);
        };

        let mut claim_point_host = unsafe { context.alloc_host_uninit_slice(current_point.len()) };
        unsafe {
            claim_point_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&current_point);
        }
        memory_copy_async(
            &mut layer0_plan.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )
        .unwrap();

        let mut batch_challenge_buffers = Vec::with_capacity(layer0_plan.kernel_plans.len());
        for kernel in layer0_plan.kernel_plans.iter() {
            batch_challenge_buffers.push(
                super::schedule_immediate_field_upload(context, 2, &kernel.batch_challenges)
                    .unwrap(),
            );
        }

        let mut main_layer_challenges_host = unsafe { context.alloc_host_uninit_slice(2) };
        unsafe {
            let accessor = main_layer_challenges_host.get_mut_accessor();
            let dst = accessor.get_mut();
            dst[0] = E4::ZERO;
            dst[1] = E4::ZERO;
        }
        let main_layer_challenges = main_layer_challenges_host.get_accessor();
        let mut auxiliary_uploads = Vec::with_capacity(layer0_plan.kernel_plans.len());
        let mut constraint_uploads = Vec::with_capacity(layer0_plan.kernel_plans.len());
        for kernel in layer0_plan.kernel_plans.iter() {
            auxiliary_uploads.push(
                super::schedule_main_layer_auxiliary_upload(
                    kernel.auxiliary_challenge_source,
                    main_layer_challenges,
                    context,
                )
                .unwrap(),
            );
            constraint_uploads.push(
                super::schedule_main_layer_constraint_metadata_upload(
                    kernel.constraint_metadata_source.as_ref(),
                    main_layer_challenges,
                    context,
                )
                .unwrap(),
            );
        }

        let mut probe_seed = seed;
        let mut probe_claim = layer0_plan.compute_combined_claim(&current_claims);
        let mut eq_prefactor = E4::ONE;
        let mut folding_challenges = Vec::with_capacity(layer0_plan.folding_steps);

        for step in 0..(layer0_plan.folding_steps - 1) {
            let acc_size = 1usize << (layer0_plan.folding_steps - step - 1);
            match step {
                0 => {
                    layer0_plan
                        .launch_round0_kernels(
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            context,
                        )
                        .unwrap();
                }
                1 => {
                    let mut callbacks = Callbacks::new();
                    let scheduled = layer0_plan
                        .schedule_round_1(&mut callbacks, context)
                        .unwrap();
                    let folding_buffer = super::schedule_immediate_field_upload(
                        context,
                        1,
                        &[folding_challenges[0]],
                    )
                    .unwrap();
                    layer0_plan
                        .launch_round1_kernels(
                            &scheduled,
                            &folding_buffer,
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )
                        .unwrap();
                }
                2 => {
                    let mut callbacks = Callbacks::new();
                    let scheduled = layer0_plan
                        .schedule_round_2(&mut callbacks, context)
                        .unwrap();
                    let folding_buffer = super::schedule_immediate_field_upload(
                        context,
                        2,
                        &[folding_challenges[0], folding_challenges[1]],
                    )
                    .unwrap();
                    layer0_plan
                        .launch_round2_kernels(
                            &scheduled,
                            &folding_buffer,
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )
                        .unwrap();
                }
                _ => {
                    let mut callbacks = Callbacks::new();
                    let scheduled = layer0_plan
                        .schedule_round_3_and_beyond(step, &mut callbacks, context)
                        .unwrap();
                    let folding_buffer = super::schedule_immediate_field_upload(
                        context,
                        1,
                        &[*folding_challenges.last().unwrap()],
                    )
                    .unwrap();
                    layer0_plan
                        .launch_round3_kernels(
                            &scheduled,
                            &folding_buffer,
                            &batch_challenge_buffers,
                            &auxiliary_uploads,
                            &constraint_uploads,
                            acc_size,
                            false,
                            context,
                        )
                        .unwrap();
                }
            }

            let reduction_output = layer0_plan
                .schedule_round_coefficients_reduction(step, acc_size, context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let reduction_values: [E4; 2] =
                unsafe { reduction_output.get_accessor().get().try_into().unwrap() };

            let mut normalized_claim = probe_claim;
            normalized_claim.mul_assign(
                &eq_prefactor
                    .inverse()
                    .expect("eq prefactor must be non-zero"),
            );
            let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E4>(
                current_point[step],
                normalized_claim,
                reduction_values[0],
                reduction_values[1],
            );
            assert_eq!(
                coeffs, expected_layer0.internal_round_coefficients[step],
                "layer 0 round {step} coeffs diverged: reduction={reduction_values:?}, normalized_claim={normalized_claim:?}, eq_prefactor={eq_prefactor:?}"
            );

            commit_field_els::<BF, E4>(&mut probe_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut probe_seed, 1)[0];
            probe_claim = prover::gkr::sumcheck::evaluate_small_univariate_poly::<BF, E4, _>(
                &coeffs,
                &folding_challenge,
            );
            eq_prefactor = prover::gkr::sumcheck::evaluate_eq_poly::<BF, E4>(
                &folding_challenge,
                &current_point[step],
            );
            folding_challenges.push(folding_challenge);
        }
    }

    #[test]
    fn dimension_reducing_kernel_blueprints_match_cpu_order_and_challenges() {
        let layer = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 1,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 1,
                        },
                    ],
                },
            ),
            (
                OutputType::Lookup16Bits,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 3,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 3,
                        },
                    ],
                },
            ),
            (
                OutputType::LookupTimestamps,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 5,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 5,
                        },
                    ],
                },
            ),
            (
                OutputType::GenericLookup,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 7,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 7,
                        },
                    ],
                },
            ),
        ]);

        let batch_challenge_base = sample_ext(10);
        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        let powers = successive_powers(batch_challenge_base, 8);

        assert_eq!(blueprints.len(), 5);
        assert_eq!(
            blueprints[0].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[0]]
        );
        assert_eq!(
            blueprints[0].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[0]]
        );
        assert_eq!(blueprints[0].batch_challenges, vec![powers[0]]);

        assert_eq!(
            blueprints[1].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[1]]
        );
        assert_eq!(
            blueprints[1].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[1]]
        );
        assert_eq!(blueprints[1].batch_challenges, vec![powers[1]]);

        assert_eq!(
            blueprints[2].inputs.inputs_in_extension,
            layer[&OutputType::Lookup16Bits].inputs
        );
        assert_eq!(
            blueprints[2].inputs.outputs_in_extension,
            layer[&OutputType::Lookup16Bits].output
        );
        assert_eq!(blueprints[2].batch_challenges, vec![powers[2], powers[3]]);

        assert_eq!(
            blueprints[3].inputs.inputs_in_extension,
            layer[&OutputType::LookupTimestamps].inputs
        );
        assert_eq!(
            blueprints[3].inputs.outputs_in_extension,
            layer[&OutputType::LookupTimestamps].output
        );
        assert_eq!(blueprints[3].batch_challenges, vec![powers[4], powers[5]]);

        assert_eq!(
            blueprints[4].inputs.inputs_in_extension,
            layer[&OutputType::GenericLookup].inputs
        );
        assert_eq!(
            blueprints[4].inputs.outputs_in_extension,
            layer[&OutputType::GenericLookup].output
        );
        assert_eq!(blueprints[4].batch_challenges, vec![powers[6], powers[7]]);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_pairwise_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let mut c0 = batch_challenge;
            c0.mul_assign(&output_values[output_index]);
            let mut a = input_values[4 + index];
            a.sub_assign(&input_values[index]);
            let mut b = input_values[4 + index + 1];
            b.sub_assign(&input_values[index + 1]);
            let mut c1 = a;
            c1.mul_assign(&b);
            c1.mul_assign(&batch_challenge);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
        let input0 = alloc_and_copy(&context, &input0_values);
        let input1 = alloc_and_copy(&context, &input1_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input0.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: input1.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output_num.as_ptr(),
                next_layer_size: 2,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: output_den.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_lookup_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let pair_index = index + 1;

            let mut a = input0_values[4 + index];
            a.sub_assign(&input0_values[index]);
            let mut b = input1_values[4 + index];
            b.sub_assign(&input1_values[index]);
            let mut c = input0_values[4 + pair_index];
            c.sub_assign(&input0_values[pair_index]);
            let mut d = input1_values[4 + pair_index];
            d.sub_assign(&input1_values[pair_index]);

            let mut num = a;
            num.mul_assign(&d);
            let mut t = c;
            t.mul_assign(&b);
            num.add_assign(&t);

            let mut den = b;
            den.mul_assign(&d);

            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut c1 = batch0;
            c1.mul_assign(&num);
            let mut den_term = batch1;
            den_term.mul_assign(&den);
            c1.add_assign(&den_term);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev0_dev.as_ptr(),
                this_layer_start: cache0.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev1_dev.as_ptr(),
                this_layer_start: cache1.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            },
        ];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_lookup_continuation::<E4>(
            descriptors_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            batch_challenges_dev.as_ptr(),
            false,
            contributions.as_ptr().cast_mut(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };
        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let a0 = fold(&prev0, idx);
            let a1 = fold(&prev0, idx + 4);
            let mut da = a1;
            da.sub_assign(&a0);
            let b0 = fold(&prev1, idx);
            let b1 = fold(&prev1, idx + 4);
            let mut db = b1;
            db.sub_assign(&b0);

            let c0 = fold(&prev0, idx + 1);
            let c1 = fold(&prev0, idx + 5);
            let mut dc = c1;
            dc.sub_assign(&c0);
            let d0 = fold(&prev1, idx + 1);
            let d1 = fold(&prev1, idx + 5);
            let mut dd = d1;
            dd.sub_assign(&d0);

            let mut num = da;
            num.mul_assign(&dd);
            let mut t = dc;
            t.mul_assign(&db);
            num.add_assign(&t);

            let mut den = db;
            den.mul_assign(&dd);

            let mut e0 = batch0;
            e0.mul_assign(&num);
            let mut e1 = batch1;
            e1.mul_assign(&den);
            e0.add_assign(&e1);

            expected.push(E4::ZERO);
            expected.push(e0);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch]);
        let descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: prev_dev.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 8,
            next_layer_size: 4,
            first_access: true,
        }];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_pairwise_continuation::<E4>(
            descriptors_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            batch_challenges_dev.as_ptr(),
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let even0 = fold(&prev, idx);
            let even1 = fold(&prev, idx + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold(&prev, idx + 1);
            let odd1 = fold(&prev, idx + 5);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn weight_contributions_and_reduce_match_cpu() {
        let context = make_test_context(64, 8);
        let contributions = vec![
            sample_ext(10),
            sample_ext(11),
            sample_ext(12),
            sample_ext(13),
            sample_ext(20),
            sample_ext(21),
            sample_ext(22),
            sample_ext(23),
        ];
        let eq = vec![sample_ext(30), sample_ext(31)];
        let contributions_dev = alloc_and_copy(&context, &contributions);
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut weighted_rows = context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_weight_contributions::<E4>(
            contributions_dev.as_ptr(),
            2,
            eq_dev.as_ptr(),
            weighted_rows.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let temp_bytes =
            get_batch_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, 2, 2).unwrap();
        let mut temp = context.alloc(temp_bytes, AllocationPlacement::Top).unwrap();
        let mut reduced = context.alloc(2, AllocationPlacement::Top).unwrap();
        let weighted_rows_slice =
            unsafe { DeviceSlice::from_raw_parts(weighted_rows.as_ptr(), weighted_rows.len()) };
        let weighted_matrix = DeviceMatrix::new(weighted_rows_slice, 2);
        let temp_slice = unsafe { DeviceSlice::from_raw_parts_mut(temp.as_mut_ptr(), temp.len()) };
        let reduced_slice =
            unsafe { DeviceSlice::from_raw_parts_mut(reduced.as_mut_ptr(), reduced.len()) };
        batch_reduce(
            ReduceOperation::Sum,
            temp_slice,
            &weighted_matrix,
            reduced_slice,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(&mut host, &reduced, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = [E4::ZERO; 2];
        for row in 0..2 {
            let mut row0 = contributions[row * 2];
            row0.add_assign(&contributions[4 + row * 2]);
            row0.mul_assign(&eq[row]);
            expected[0].add_assign(&row0);

            let mut row1 = contributions[row * 2 + 1];
            row1.add_assign(&contributions[4 + row * 2 + 1]);
            row1.mul_assign(&eq[row]);
            expected[1].add_assign(&row1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn build_eq_values_matches_cpu() {
        let context = make_test_context(64, 8);
        let claim_point = vec![
            sample_ext(40),
            sample_ext(50),
            sample_ext(60),
            sample_ext(70),
        ];
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let mut eq_values = context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_build_eq_values::<E4>(
            claim_point_dev.as_ptr(),
            1,
            2,
            eq_values.as_mut_ptr(),
            4,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &eq_values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let r0 = claim_point[1];
        let r1 = claim_point[2];
        let mut one_minus_r0 = E4::ONE;
        one_minus_r0.sub_assign(&r0);
        let mut one_minus_r1 = E4::ONE;
        one_minus_r1.sub_assign(&r1);

        let mut expected_00 = one_minus_r0;
        expected_00.mul_assign(&one_minus_r1);
        let mut expected_01 = one_minus_r0;
        expected_01.mul_assign(&r1);
        let mut expected_10 = r0;
        expected_10.mul_assign(&one_minus_r1);
        let mut expected_11 = r0;
        expected_11.mul_assign(&r1);

        let expected = vec![expected_00, expected_01, expected_10, expected_11];

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| BF::new(100 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(1)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(1)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(1, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(1, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: input.as_ptr(),
                    next_layer_size: 2,
                };
            round0.host.base_field_outputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: output.as_ptr(),
                    next_layer_size: 2,
                };
        }
        memory_copy_async(
            &mut round0.device.base_field_inputs,
            &round0.host.base_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.base_field_outputs,
            &round0.host.base_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_main_round0(
            GpuGKRMainLayerKernelKind::BaseCopy,
            &round0,
            batch_challenges_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign_by_base(&output_values[output_index]);
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::BaseCopy,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign(&fold_base(&input_values, gid));
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_ext_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors_dev = context
            .alloc::<crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>>(0, AllocationPlacement::Top)
            .unwrap();
        let ext_descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: input.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 4,
            next_layer_size: 2,
            first_access: true,
        }];
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::ExtCopy,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign(&fold_ext(&input_values, gid));
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_product_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| sample_ext(30 + i)).collect::<Vec<_>>();
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let cache_a: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors_dev = context
            .alloc::<crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>>(0, AllocationPlacement::Top)
            .unwrap();
        let ext_descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_a.as_ptr(),
                this_layer_start: cache_a.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_b.as_ptr(),
                this_layer_start: cache_b.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
        ];
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::Product,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_ext(&input_a_values, gid);
            let a1_full = fold_ext(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_ext(&input_b_values, gid);
            let b1_full = fold_ext(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let mut c0 = batch_challenge;
            let mut eval0 = a0;
            eval0.mul_assign(&b0);
            c0.mul_assign(&eval0);

            let mut c1 = batch_challenge;
            let mut eval1 = da;
            eval1.mul_assign(&db);
            c1.mul_assign(&eval1);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_enforce_constraints_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let constant_offset = sample_ext(400);
        let quadratic_terms = vec![
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 1,
                challenge: sample_ext(500),
            },
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 1,
                rhs: 2,
                challenge: sample_ext(600),
            },
        ];
        let linear_terms = vec![GpuGKRMainLayerConstraintLinearTerm {
            input: 2,
            challenge: sample_ext(700),
        }];
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let constraint_upload = super::ScheduledMainLayerConstraintMetadataUpload {
            callbacks: Callbacks::new(),
            quadratic_terms: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &quadratic_terms),
            },
            linear_terms: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &linear_terms),
            },
            constant_offset: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &[constant_offset]),
            },
        };

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            Some(&constraint_upload),
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);

            let mut eval0 = constant_offset;
            let mut term0 = a0;
            term0.mul_assign(&b0);
            term0.mul_assign(&quadratic_terms[0].challenge);
            eval0.add_assign(&term0);
            let mut term1 = b0;
            term1.mul_assign(&c0_in);
            term1.mul_assign(&quadratic_terms[1].challenge);
            eval0.add_assign(&term1);
            let mut linear = c0_in;
            linear.mul_assign(&linear_terms[0].challenge);
            eval0.add_assign(&linear);

            let mut eval1 = E4::ZERO;
            let mut delta0 = da;
            delta0.mul_assign(&db);
            delta0.mul_assign(&quadratic_terms[0].challenge);
            eval1.add_assign(&delta0);

            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);
            let mut delta1 = db;
            delta1.mul_assign(&dc);
            delta1.mul_assign(&quadratic_terms[1].challenge);
            eval1.add_assign(&delta1);

            let mut c0 = batch_challenge;
            c0.mul_assign(&eval0);
            let mut c1 = batch_challenge;
            c1.mul_assign(&eval1);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_lookup_base_pair_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_d_values = (0..4).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(300);
        let batch1 = sample_ext(400);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let lookup_additive_challenge = sample_ext(500);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(2)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(2, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: input_b.as_ptr(),
                    next_layer_size: 2,
                };
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[1] =
                GpuBaseFieldPolySource {
                    start: input_d.as_ptr(),
                    next_layer_size: 2,
                };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output_num.as_ptr(),
                next_layer_size: 2,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: output_den.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.base_field_inputs,
            &round0.host.base_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_main_round0(
            GpuGKRMainLayerKernelKind::LookupBasePair,
            &round0,
            batch_challenges_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut b1 = input_b_values[2 + output_index];
            b1.sub_assign(&input_b_values[output_index]);
            let mut d1 = input_d_values[2 + output_index];
            d1.sub_assign(&input_d_values[output_index]);
            let mut den = b1;
            den.mul_assign(&d1);

            let mut c1 = batch1;
            c1.mul_assign_by_base(&den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_with_cached_dens_and_setup_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();

        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);
        let cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache_d: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let ext_descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_b.as_ptr(),
                this_layer_start: cache_b.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_d.as_ptr(),
                this_layer_start: cache_d.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };
        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let c0_in = fold_base(&input_c_values, gid);
            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);

            let b0 = fold_ext(&input_b_values, gid);
            let b1_full = fold_ext(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_ext(&input_d_values, gid);
            let d1_full = fold_ext(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);
            let mut num0 = a0;
            num0.mul_assign(&shifted_d0);
            let mut t0 = c0_in;
            t0.mul_assign(&shifted_b0);
            num0.sub_assign(&t0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.sub_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_base_pair_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();

        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_d.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupBasePair,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_base(&input_d_values, gid);
            let d1_full = fold_base(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_b0;
            num0.add_assign(&shifted_d0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let num1 = E4::ZERO;
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_base_minus_multiplicity_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();

        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_d.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);
            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);

            let d0 = fold_base(&input_d_values, gid);
            let d1_full = fold_base(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_d0;
            let mut t0 = c0_in;
            t0.mul_assign(&shifted_b0);
            num0.sub_assign(&t0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut num1 = dc;
            num1.mul_assign(&db);
            num1.negate();
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    fn main_layer_constraint_blueprint_metadata_matches_cpu() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
        };
        let constraint_input = NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms: vec![
                (
                    (
                        GKRAddress::BaseLayerMemory(0),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(2u32, 0usize), (3u32, 2usize)].into_boxed_slice(),
                ),
                (
                    (
                        GKRAddress::BaseLayerWitness(1),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(5u32, 1usize)].into_boxed_slice(),
                ),
            ]
            .into_boxed_slice(),
            linear_terms: vec![(
                GKRAddress::BaseLayerMemory(1),
                vec![(7u32, 0usize)].into_boxed_slice(),
            )]
            .into_boxed_slice(),
            constants: vec![(11u32, 0usize), (13u32, 1usize)].into_boxed_slice(),
        };
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
                    input: constraint_input.clone(),
                },
            }],
            additional_base_layer_openings: Vec::new(),
        };
        let constraint_batch_challenge = sample_ext(20);
        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            0,
            &storage,
            sample_ext(10),
            sample_ext(30),
            constraint_batch_challenge,
            2,
            2,
        );

        assert_eq!(blueprints.len(), 1);
        let blueprint = &blueprints[0];
        let relation = BatchConstraintEvalGKRRelation::<BF, E4>::new(
            &constraint_input,
            2,
            2,
            constraint_batch_challenge,
        );

        assert_eq!(
            blueprint.kind,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
        );
        assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
        assert_eq!(
            blueprint.inputs,
            <BatchConstraintEvalGKRRelation<BF, E4> as BatchedGKRKernel<BF, E4>>::get_inputs(
                &relation,
            )
        );

        let metadata = blueprint
            .constraint_metadata_source
            .as_ref()
            .expect("constraint metadata must be present");
        let metadata = match metadata {
            super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
            super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                panic!("dynamic blueprint must materialize immediate constraint metadata")
            }
        };
        assert_eq!(metadata.constant_offset, relation.kernel.constant_offset);
        assert_eq!(
            metadata.quadratic_terms.len(),
            relation.kernel.quadratic_parts.len()
        );
        assert_eq!(
            metadata.linear_terms.len(),
            relation.kernel.linear_parts.len()
        );
        assert_eq!(
            metadata.quadratic_terms,
            relation
                .kernel
                .quadratic_parts
                .iter()
                .map(
                    |((lhs, rhs), challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                        lhs: *lhs as u32,
                        rhs: *rhs as u32,
                        challenge: *challenge,
                    }
                )
                .collect::<Vec<_>>()
        );
        assert_eq!(
            metadata.linear_terms,
            relation
                .kernel
                .linear_parts
                .iter()
                .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
                    input: *input as u32,
                    challenge: *challenge,
                })
                .collect::<Vec<_>>()
        );
    }
}
