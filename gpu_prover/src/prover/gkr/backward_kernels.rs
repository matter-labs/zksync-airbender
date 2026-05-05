use std::cell::UnsafeCell;
use std::collections::{BTreeMap, VecDeque};
use std::mem::align_of;
use std::ptr::{null, null_mut};
use std::slice;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, OutputType};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::transcript_utils::commit_field_els;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::sumcheck::evaluation_kernels::GKRInputs;
use prover::transcript::Seed;

use super::{
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuGKRStorage, GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0LaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1PreparedStorage,
    GpuSumcheckRound2PreparedStorage, GpuSumcheckRound3AndBeyondHostLaunchDescriptors,
    GpuSumcheckRound3AndBeyondPreparedStorage,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{reduce, Reduce, ReduceOperation};
use crate::ops::immediate_factors::ImmediateFactorRecipeStructural;
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, SchedulerHostAllocation, UnsafeAccessor,
    UnsafeMutAccessor,
};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClaimBufferLayout {
    pub(crate) addresses: Vec<GKRAddress>,
    pub(crate) index_by_address: BTreeMap<GKRAddress, u32>,
}

impl ClaimBufferLayout {
    pub(crate) fn from_addresses(addresses: Vec<GKRAddress>) -> Self {
        assert!(
            !addresses.is_empty(),
            "claim buffer layout must contain at least one address"
        );
        assert!(
            addresses.len() <= u32::MAX as usize,
            "claim buffer layout exceeds u32 indexing"
        );
        let mut index_by_address = BTreeMap::new();
        for (idx, address) in addresses.iter().copied().enumerate() {
            let prev = index_by_address.insert(address, idx as u32);
            assert!(
                prev.is_none(),
                "duplicate claim address in claim buffer layout: {address:?}"
            );
        }
        Self {
            addresses,
            index_by_address,
        }
    }

    pub(crate) fn from_claims<E>(claims: &BTreeMap<GKRAddress, E>) -> Self {
        Self::from_addresses(claims.keys().copied().collect())
    }

    pub(crate) fn len(&self) -> usize {
        self.addresses.len()
    }

    pub(crate) fn claim_idx(&self, address: &GKRAddress) -> u32 {
        self.index_by_address
            .get(address)
            .copied()
            .unwrap_or_else(|| panic!("missing claim address in layout: {address:?}"))
    }

    pub(crate) fn write_values_from_claims<E: Copy>(
        &self,
        claims: &BTreeMap<GKRAddress, E>,
        dst: &mut [E],
    ) {
        assert_eq!(
            dst.len(),
            self.len(),
            "claim buffer destination must match layout length"
        );
        for (idx, address) in self.addresses.iter().enumerate() {
            dst[idx] = claims
                .get(address)
                .copied()
                .unwrap_or_else(|| panic!("missing claim value for {address:?}"));
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct DimensionReducingKernelBlueprint<E> {
    pub(super) kind: GpuGKRDimensionReducingKernelKind,
    pub(super) inputs: GKRInputs,
    pub(super) batch_challenge_offset: usize,
    pub(super) batch_challenge_count: usize,
    pub(super) batch_challenges: Vec<E>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum GpuGKRDimensionReducingKernelKind {
    Pairwise = 0,
    Lookup = 1,
}

impl GpuGKRDimensionReducingKernelKind {
    pub(super) const fn as_u32(self) -> u32 {
        self as u32
    }
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
}

impl GpuGKRMainLayerKernelKind {
    pub(super) const fn as_u32(self) -> u32 {
        self as u32
    }
}

pub(super) const GKR_BACKWARD_MAX_KERNELS_PER_LAYER: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub(super) enum GpuGKRMainLayerBatchRecordMode {
    InlineAll = 0,
    InlineNoMetadata = 1,
    PointerDescriptors = 2,
}

impl GpuGKRMainLayerBatchRecordMode {
    pub(super) const fn as_u32(self) -> u32 {
        self as u32
    }
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
pub(super) struct GpuGKRMainLayerConstraintChallengeTerm {
    pub(super) coeff: BF,
    pub(super) source: GpuGKRMainLayerDeferredChallengeSource,
    pub(super) power: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum GpuGKRMainLayerDeferredChallengeSource {
    LookupMultiplicative,
    LookupAdditive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GpuGKRMainLayerConstraintQuadraticTemplate {
    pub(super) lhs: u32,
    pub(super) rhs: u32,
    pub(super) challenge_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GpuGKRMainLayerConstraintLinearTemplate {
    pub(super) input: u32,
    pub(super) challenge_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GpuGKRMainLayerConstraintTemplate {
    pub(super) quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTemplate>,
    pub(super) linear_terms: Vec<GpuGKRMainLayerConstraintLinearTemplate>,
    pub(super) constant_terms: Vec<GpuGKRMainLayerConstraintChallengeTerm>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum GpuGKRMainLayerAuxiliaryChallengeSource<E> {
    Immediate(E),
    LookupAdditive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum GpuGKRMainLayerConstraintMetadataSource<E> {
    Immediate(GpuGKRMainLayerConstraintHostMetadata<E>),
    Deferred(GpuGKRMainLayerConstraintTemplate),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GpuGKRMainLayerKernelBlueprint<E> {
    pub(super) kind: GpuGKRMainLayerKernelKind,
    pub(super) inputs: GKRInputs,
    pub(super) batch_challenge_offset: usize,
    pub(super) batch_challenge_count: usize,
    pub(super) batch_challenges: Vec<E>,
    pub(super) auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    pub(super) constraint_metadata_source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
}

#[derive(Clone, Debug)]
pub(super) struct GpuGKRMainLayerRound3HostDescriptors<E: Copy> {
    pub(super) step: usize,
    pub(super) descriptors: GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E>,
}

// ---------------------------------------------------------------------------
// Compact dim-reducing descriptor types. Each source record carries two u16s:
// one for the source pointer/index and one for the cache pointer/index. Both
// halves resolve against the same per-launch `bases` / `log2_stride` tables.
// ---------------------------------------------------------------------------

/// Pessimistic upper bound on the per-launch u16 source list. Sized from the
/// Phase 0 measured worst-case (`FLAT_ROUND0_MAX_SOURCES = 1280`,
/// `gkr_address_audit.rs`) — re-anchor in Phase D once dim-reducing-specific
/// measurement says this can be tightened.
pub(crate) const GKR_DIM_REDUCING_INLINE_U16_BUDGET: usize = 1280;

/// Number of per-launch base-pointer slots. Phase 0 measured up to 5
/// distinct address classes per layer (8-slot static taxonomy in
/// `gkr_address_audit.rs`). Bumped to 16 because Phase C round 1/2 main-layer
/// flat-path launches use one slot per *backing* (not per class): up to 4
/// base read backings, 4 base cache backings, 1-3 ext read backings, and
/// 1 ext cache backing — easily 10+ distinct Arcs per launch. 16 leaves
/// comfortable headroom; the 4-bit `ptr_idx` field in every u16 source
/// encoding is sized to match.
pub(crate) const GKR_DIM_REDUCING_BASE_SLOTS: usize = 16;

/// `(offset, count)` over the `inline_payload[GpuGKRSourceRecord]` array.
/// 4 B per range record.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct PayloadRange16 {
    pub(crate) offset: u16,
    pub(crate) count: u16,
}

/// One dim-reducing record (kernel-batch entry). 16 B with two PayloadRange16
/// slots, a u32 kind, and u16 batch-challenge metadata.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct GpuGKRDimensionReducingBatchRecordCompact {
    pub(crate) kind: u32,
    pub(crate) inputs: PayloadRange16,
    pub(crate) outputs: PayloadRange16,
    pub(crate) batch_challenge_offset: u16,
    pub(crate) batch_challenge_count: u16,
}

/// Per-launch pointer + stride tables.
/// `bases[ptr_idx]` is the base of slot `ptr_idx`'s allocation;
/// `log2_stride[ptr_idx]` is the per-poly stride exponent (decode:
/// `element_addr = bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx])`).
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingTables {
    pub(crate) bases: [*const u8; GKR_DIM_REDUCING_BASE_SLOTS],
    pub(crate) log2_stride: [u32; GKR_DIM_REDUCING_BASE_SLOTS],
}

impl Default for GpuGKRDimensionReducingTables {
    fn default() -> Self {
        Self {
            bases: [null(); GKR_DIM_REDUCING_BASE_SLOTS],
            log2_stride: [0; GKR_DIM_REDUCING_BASE_SLOTS],
        }
    }
}

// SAFETY: holds raw device pointers — safe to send across threads.
unsafe impl Send for GpuGKRDimensionReducingTables {}
unsafe impl Sync for GpuGKRDimensionReducingTables {}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct GpuGKRSourceRecord {
    pub(crate) src: u16,
    pub(crate) cache: u16,
}

impl GpuGKRSourceRecord {
    pub(crate) const fn source_only(src: u16) -> Self {
        Self { src, cache: 0 }
    }

    pub(crate) const fn new(src: u16, cache: u16) -> Self {
        Self { src, cache }
    }
}

/// Compact replacement for `GpuGKRDimensionReducingRound0Batch<E>`.
/// ~3.7 KB by-value kernel-arg footprint.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound0BatchCompact<E> {
    pub(crate) record_count: u32,
    pub(crate) _reserved0: u32,
    pub(crate) _reserved1: u32,
    pub(crate) _reserved2: u32,
    pub(crate) eq_values: *const E,
    pub(crate) batch_challenge_base: *const E,
    pub(crate) contributions: *mut E,
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) records:
        [GpuGKRDimensionReducingBatchRecordCompact; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(crate) inline_payload: [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_U16_BUDGET],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound0BatchCompact<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            _reserved1: 0,
            _reserved2: 0,
            eq_values: null(),
            batch_challenge_base: null(),
            contributions: null_mut(),
            tables: GpuGKRDimensionReducingTables::default(),
            records: [GpuGKRDimensionReducingBatchRecordCompact::default();
                GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_INLINE_U16_BUDGET],
        }
    }
}

/// Compact replacement for `GpuGKRDimensionReducingRound{1,2,3}Batch<E>`.
/// Continuation rounds drop the `outputs` payload range (per-record reads
/// only) but otherwise share the round-0 layout. The kernel infers
/// `previous_layer_start` / `this_layer_start` / sizes from the per-launch
/// `step` plus the `bases` / `log2_stride` tables.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingContinuationBatchCompact<E> {
    pub(crate) record_count: u32,
    pub(crate) _reserved0: u32,
    pub(crate) _reserved1: u32,
    pub(crate) _reserved2: u32,
    pub(crate) eq_values: *const E,
    pub(crate) batch_challenge_base: *const E,
    pub(crate) folding_challenge: *const E,
    pub(crate) contributions: *mut E,
    pub(crate) explicit_form: bool,
    pub(crate) _padding: [u8; 7],
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) records:
        [GpuGKRDimensionReducingBatchRecordCompact; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(crate) inline_payload: [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_U16_BUDGET],
}

impl<E: Field> Default for GpuGKRDimensionReducingContinuationBatchCompact<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            _reserved1: 0,
            _reserved2: 0,
            eq_values: null(),
            batch_challenge_base: null(),
            folding_challenge: null(),
            contributions: null_mut(),
            explicit_form: false,
            _padding: [0; 7],
            tables: GpuGKRDimensionReducingTables::default(),
            records: [GpuGKRDimensionReducingBatchRecordCompact::default();
                GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_INLINE_U16_BUDGET],
        }
    }
}

/// `(first_access, ptr_idx, poly_idx)` packed into a u16 source descriptor.
/// `first_access` is bit 15 (cheapest single-bit test on the GPU);
/// `ptr_idx` is bits 14..11 (4 bits, 16 slots); `poly_idx` is bits 10..0
/// (11 bits, up to 2048 polys per slot — Phase 0 measured max 646).
#[inline]
pub(crate) const fn pack_source_u16(first_access: bool, ptr_idx: u8, poly_idx: u16) -> u16 {
    let fa = if first_access { 1u16 << 15 } else { 0 };
    let p = ((ptr_idx as u16) & 0xF) << 11;
    let q = poly_idx & 0x07FF;
    fa | p | q
}

#[inline]
pub(crate) const fn unpack_source_u16(packed: u16) -> (bool, u8, u16) {
    let first_access = packed & (1 << 15) != 0;
    let ptr_idx = ((packed >> 11) & 0xF) as u8;
    let poly_idx = packed & 0x07FF;
    (first_access, ptr_idx, poly_idx)
}

/// Cache half of a dual source record. Bit 15 is normally reserved and kept
/// clear; flat base virtual sources use it as a local discriminator because
/// their source half carries `first_access` plus a virtual source kind rather
/// than a real source pointer.
#[inline]
pub(crate) const fn pack_cache_u16(ptr_idx: u8, poly_idx: u16) -> u16 {
    let p = ((ptr_idx as u16) & 0xF) << 11;
    let q = poly_idx & 0x07FF;
    p | q
}

#[inline]
pub(crate) const fn unpack_cache_u16(packed: u16) -> (u8, u16) {
    let ptr_idx = ((packed >> 11) & 0xF) as u8;
    let poly_idx = packed & 0x07FF;
    (ptr_idx, poly_idx)
}

#[derive(Clone, Debug)]
pub(super) struct GpuGKRDimensionReducingRound3Prepared<E> {
    pub(super) step: usize,
    pub(super) prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

pub(super) struct GpuGKRDimensionReducingRoundScratch<E> {
    pub(super) claim_point: DeviceAllocation<E>,
    pub(super) eq_pair_values: DeviceAllocation<E>,
    pub(super) eq_group_tables: DeviceAllocation<E>,
    pub(super) eq_values: DeviceAllocation<E>,
    pub(super) accumulator: DeviceAllocation<E>,
    pub(super) reduction_output: DeviceAllocation<E>,
    pub(super) reduction_temp_storage: DeviceAllocation<u8>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuGKRDimensionReducingKernelPlan<B, E> {
    pub(crate) kind: GpuGKRDimensionReducingKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
    pub(super) round1_prepared: GpuSumcheckRound1PreparedStorage<B, E>,
    pub(super) round2_prepared: Option<GpuSumcheckRound2PreparedStorage<B, E>>,
    pub(super) round3_and_beyond_prepared: Vec<GpuGKRDimensionReducingRound3Prepared<E>>,
}

pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) layer_idx: usize,
    pub(crate) trace_len_after_reduction: usize,
    pub(crate) folding_steps: usize,
    pub(super) batch_challenge_base: Option<E>,
    pub(super) kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<B, E>>,
    pub(super) round0_batch_template_compact: GpuGKRDimensionReducingRound0BatchCompact<E>,
    pub(super) round1_batch_template_compact: GpuGKRDimensionReducingContinuationBatchCompact<E>,
    /// Single descriptor reused for every continuation step >= 2. The kernel
    /// derives per-step folding-buffer offsets from `step + acc_size`.
    pub(super) continuation_batch_template_compact:
        GpuGKRDimensionReducingContinuationBatchCompact<E>,
    pub(super) round_scratch: GpuGKRDimensionReducingRoundScratch<E>,
    /// When set, `batch_challenge_base_ptr()` returns this raw pointer instead
    /// of `round_scratch.claim_point.as_ptr().add(folding_steps)`. The
    /// workflow_state path uses this to point at the orchestrator-owned
    /// `device_claim_point_in[folding_steps]` so the per-layer
    /// `round_scratch.claim_point` D2D is no longer needed.
    pub(super) batch_challenge_base_override_ptr: Option<*const E>,
}

// SAFETY: `batch_challenge_base_override_ptr` only stores a raw pointer into a
// device allocation that the caller keeps alive for the full duration of any
// scheduled stream op consuming this layer plan. The pointer is never
// dereferenced from Rust — it is only forwarded to kernel arguments.
unsafe impl<B, E> Send for GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    B: Send,
    E: Send,
{
}
unsafe impl<B, E> Sync for GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    B: Sync,
    E: Sync,
{
}

pub(crate) struct GpuGKRDimensionReducingBackwardState<B, E> {
    #[allow(dead_code)] // Keeps queued forward ranges alive until the stream consumes them.
    pub(super) forward_tracing_ranges: Vec<Range>,
    pub(super) storage: GpuGKRStorage<B, E>,
    pub(super) pending_layers:
        VecDeque<(usize, BTreeMap<OutputType, DimensionReducingInputOutput>)>,
    pub(super) next_trace_len_after_reduction: usize,
}

pub(crate) struct GpuGKRDimensionReducingLayerExecution<E: FieldExtension<BF> + Field> {
    pub(crate) new_claims: BTreeMap<GKRAddress, E>,
    pub(crate) new_claim_point: Vec<E>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

pub(super) struct ScheduledDimensionReducingReductionState<E> {
    pub(super) callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) _phantom: std::marker::PhantomData<E>,
}

pub(super) struct SharedChallengeDevice<E> {
    pub(super) device: UnsafeCell<DeviceAllocation<E>>,
}

// SAFETY: uploads and kernel launches are enqueued from the host in stream order.
// SharedChallengeDevice only exposes raw pointers or temporary slice views for those enqueues.
unsafe impl<E: Send> Send for SharedChallengeDevice<E> {}
// SAFETY: the wrapped device allocation lives for the duration of all queued work and is only
// accessed through explicit pointer/slice helpers.
unsafe impl<E: Sync> Sync for SharedChallengeDevice<E> {}

impl<E> SharedChallengeDevice<E> {
    pub(super) fn new(device: DeviceAllocation<E>) -> Self {
        Self {
            device: UnsafeCell::new(device),
        }
    }

    pub(super) fn as_ptr(&self, offset: usize) -> *const E {
        // SAFETY: every offset is validated when the buffer view is created.
        unsafe { (&*self.device.get()).as_ptr().add(offset) }
    }

    pub(super) unsafe fn slice_mut(&self, offset: usize, len: usize) -> &mut DeviceSlice<E> {
        // SAFETY: callers guarantee the requested range is within bounds and that using this
        // temporary mutable view only serves to enqueue stream-ordered H2D copies.
        &mut (&mut *self.device.get())[offset..offset + len]
    }

    #[cfg(test)]
    pub(super) unsafe fn slice(&self, offset: usize, len: usize) -> &DeviceSlice<E> {
        // SAFETY: callers guarantee the requested range is within bounds.
        &(&*self.device.get())[offset..offset + len]
    }
}

pub(super) struct ScheduledChallengeBuffer<E> {
    pub(super) device: UnsafeAccessor<SharedChallengeDevice<E>>,
    pub(super) offset: usize,
    pub(super) len: usize,
}

impl<E> ScheduledChallengeBuffer<E> {
    pub(super) fn as_ptr(&self) -> *const E {
        unsafe { self.device.get() }.as_ptr(self.offset)
    }

    #[cfg(test)]
    pub(super) fn device_slice(&self) -> &DeviceSlice<E> {
        // SAFETY: buffer views only expose ranges created from valid packed offsets.
        unsafe { self.device.get().slice(self.offset, self.len) }
    }
}

pub(super) struct ScheduledChallengeStorage<E> {
    pub(super) callbacks: Callbacks<'static>,
    pub(super) device: Box<SharedChallengeDevice<E>>,
}

impl<E> ScheduledChallengeStorage<E> {
    pub(super) fn new(device: DeviceAllocation<E>) -> Self {
        Self {
            callbacks: Callbacks::new(),
            device: Box::new(SharedChallengeDevice::new(device)),
        }
    }

    pub(super) fn device_accessor(&self) -> UnsafeAccessor<SharedChallengeDevice<E>> {
        UnsafeAccessor::new(self.device.as_ref())
    }
}

pub(super) struct HostScheduledChallengeStorage<E> {
    pub(super) callbacks: Callbacks<'static>,
    pub(super) _phantom: std::marker::PhantomData<E>,
}

pub(super) struct ScheduledUpload<T> {
    pub(super) callbacks: Callbacks<'static>,
    pub(super) device: DeviceAllocation<T>,
    #[allow(dead_code)]
    pub(super) scheduler_host: Option<SchedulerHostAllocation<[T]>>,
}

pub(super) struct HostScheduledUpload<T> {
    pub(super) callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) scheduler_host: Option<SchedulerHostAllocation<[T]>>,
    #[allow(dead_code)]
    pub(super) _phantom: std::marker::PhantomData<T>,
}

pub(super) struct ScheduledDimensionReducingFinalReadback<E> {
    pub(super) callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) _phantom: std::marker::PhantomData<E>,
}

pub(super) struct ScheduledDimensionReducingLayerExecutionState<E: FieldExtension<BF> + Field> {
    pub(super) seed: Seed,
    pub(super) claim: E,
    pub(super) eq_prefactor: E,
    pub(super) folding_challenges: Vec<E>,
    pub(super) result: Option<GpuGKRDimensionReducingLayerExecution<E>>,
}

pub(super) struct ScheduledMainLayerExecutionState<E: FieldExtension<BF> + Field> {
    pub(super) seed: Seed,
    pub(super) claim: E,
    pub(super) eq_prefactor: E,
    pub(super) folding_challenges: Vec<E>,
    pub(super) result: Option<GpuGKRMainLayerExecution<E>>,
}

pub(crate) type ScheduledDimensionReducingLayerExecutionStateHandle<E> =
    UnsafeMutAccessor<ScheduledDimensionReducingLayerExecutionState<E>>;
pub(crate) type ScheduledMainLayerExecutionStateHandle<E> =
    UnsafeMutAccessor<ScheduledMainLayerExecutionState<E>>;
pub(crate) type ScheduledBackwardWorkflowStateHandle<E> =
    UnsafeMutAccessor<ScheduledBackwardWorkflowState<E>>;

pub(crate) struct GpuGKRDimensionReducingScheduledLayerExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    // Keeps layer-start callbacks alive until the stream consumes them.
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) round_challenge_storage: Option<ScheduledChallengeStorage<E>>,
    #[allow(dead_code)]
    pub(super) round_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    pub(super) shared_state: Box<ScheduledDimensionReducingLayerExecutionState<E>>,
    /// Device-resident Fiat-Shamir seed passed in by the caller, consumed by
    /// this layer's per-round + end-of-layer transcript work, and returned
    /// via `.take()` for the next backward layer scheduler to reuse. `None`
    /// after the orchestrator has pulled it out. Replaces the per-layer entry
    /// H2D that used to mirror `workflow_state.seed` into a fresh device slot.
    pub(super) device_seed: Option<DeviceAllocation<u32>>,
    /// Device-resident `[claim_point || batching_challenge]` buffer for the
    /// NEXT backward layer. Populated on-device from this layer's folding
    /// challenges + end-of-layer squeezed challenges. Taken by the orchestrator
    /// via `.take()`. Replaces the per-layer entry H2D that used to copy
    /// `workflow_state.current_claim_point` + `current_batching_challenge`
    /// from host.
    pub(super) device_claim_point_for_next_layer: Option<DeviceAllocation<E>>,
    /// Device-resident `current_claims` buffer for the NEXT backward layer.
    /// This layer's `device_new_claims` becomes the next layer's input to
    /// `build_combined_claim`.
    pub(super) device_claims_for_next_layer: Option<DeviceAllocation<E>>,
    /// Explicit address order of `device_claims_for_next_layer`.
    pub(super) claim_layout_for_next_layer: Option<ClaimBufferLayout>,
    #[allow(dead_code)]
    pub(super) _phantom: std::marker::PhantomData<B>,
}

#[derive(Clone, Debug)]
pub(super) struct GpuGKRMainLayerRound3Prepared<E> {
    pub(super) step: usize,
    pub(super) prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

pub(super) struct GpuGKRMainLayerRoundScratch<E> {
    pub(super) claim_point: DeviceAllocation<E>,
    pub(super) eq_pair_values: DeviceAllocation<E>,
    pub(super) eq_group_tables: DeviceAllocation<E>,
    pub(super) eq_values: DeviceAllocation<E>,
    pub(super) accumulator: DeviceAllocation<E>,
    pub(super) reduction_output: DeviceAllocation<E>,
    pub(super) reduction_temp_storage: DeviceAllocation<u8>,
}

pub(crate) struct GpuGKRMainLayerKernelPlan<E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
    pub(super) auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    pub(super) constraint_metadata_source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
    pub(super) constraint_metadata_summary: Option<(usize, usize, E)>,
    pub(super) round1_prepared: GpuSumcheckRound1PreparedStorage<BF, E>,
    pub(super) round2_prepared: GpuSumcheckRound2PreparedStorage<BF, E>,
    pub(super) round3_and_beyond_prepared: Vec<GpuGKRMainLayerRound3Prepared<E>>,
}

pub(crate) struct GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) layer_idx: usize,
    pub(crate) trace_len: usize,
    pub(crate) folding_steps: usize,
    pub(super) batch_challenge_base: Option<E>,
    pub(super) lookup_multiplicative_challenge: E,
    pub(super) lookup_additive_challenge: E,
    pub(super) external_challenges_flat: Vec<E>,
    pub(super) kernel_plans: Vec<GpuGKRMainLayerKernelPlan<E>>,
    pub(super) round0_descriptors: Vec<GpuSumcheckRound0LaunchDescriptors<BF, E>>,
    /// Phase C compact flat round-0 descriptor. Built at prepare time from
    /// the (transient) legacy `FlatRound0BuildPlan`; only the compact form
    /// survives onto the plan struct. Consumed by
    /// `launch_main_round0_flat_constant_compact`.
    pub(super) flat_round0_template_compact:
        Option<super::backward_flat_compact::FlatRound0BuildPlanCompact<E>>,
    /// Inline eval-recipes descriptor passed by value to each round-0 launch.
    pub(super) flat_recipe_desc: Option<Box<crate::ops::eval_recipes::GpuFlatRecipeEvalDesc>>,
    pub(super) flat_recipe_count: usize,
    /// Device buffer for eval_recipes output (delegation L0 round 0 only; others write to __constant__).
    pub(super) flat_coeff_device_buf: Option<DeviceAllocation<E>>,
    /// Whether round 0 uses __constant__ for coefficients (false only for delegation L0).
    pub(super) flat_use_constant: bool,
    /// Flat continuation plan for rounds 1+ (shared term arrays + per-step source tables).
    pub(super) flat_continuation_plan: Option<super::backward_flat::FlatContinuationBuildPlan<E>>,
    /// Inline eval-recipes descriptor passed by value to each continuation launch.
    pub(super) flat_cont_recipe_desc: Option<Box<crate::ops::eval_recipes::GpuFlatRecipeEvalDesc>>,
    pub(super) flat_cont_recipe_count: usize,
    /// Phase C continuation compact descriptors (per step). Built at prepare
    /// time from the transient legacy unified descriptors and converted; only
    /// the compact form survives onto the plan. Consumed by
    /// `launch_main_round3_flat_constant_unified_compact`.
    pub(super) flat_continuation_unified_descs_compact: Vec<(
        usize,
        Box<super::backward_flat_compact::GpuFlatContinuationUnifiedDescCompact>,
    )>,
    /// Phase C round 1 compact descriptor. Built at prepare time from the
    /// transient legacy `GpuFlatRound1UnifiedDesc`. Consumed by
    /// `launch_main_round1_flat_constant_compact_unified_compact`.
    pub(super) flat_round1_unified_desc_compact:
        Option<Box<super::backward_flat_compact::GpuFlatRound1UnifiedDescCompact>>,
    /// Phase C round 2 compact descriptor. Built at prepare time from the
    /// transient legacy `GpuFlatRound2UnifiedDesc`.
    pub(super) flat_round2_unified_desc_compact:
        Option<Box<super::backward_flat_compact::GpuFlatRound2UnifiedDescCompact>>,
    pub(super) round_scratch: GpuGKRMainLayerRoundScratch<E>,
    /// Legacy keepalive slot for scheduling callbacks unrelated to inline recipe descriptors.
    pub(super) recipe_upload_callbacks: Callbacks<'static>,
    /// When set, `batch_challenge_base_ptr()` returns this raw pointer instead
    /// of `round_scratch.claim_point.as_ptr().add(folding_steps)`. The
    /// workflow_state path uses this to point at the orchestrator-owned
    /// `device_claim_point_in[folding_steps]` so the per-layer
    /// `round_scratch.claim_point` D2D is no longer needed.
    pub(super) batch_challenge_base_override_ptr: Option<*const E>,
}

// SAFETY: `batch_challenge_base_override_ptr` only stores a raw pointer into a
// device allocation that the caller keeps alive for the full duration of any
// scheduled stream op consuming this layer plan. The pointer is never
// dereferenced from Rust — it is only forwarded to kernel arguments.
unsafe impl<E> Send for GpuGKRMainLayerSumcheckLayerPlan<E> where E: Send {}
unsafe impl<E> Sync for GpuGKRMainLayerSumcheckLayerPlan<E> where E: Sync {}

impl<E: Copy + Field> GpuGKRMainLayerKernelPlan<E> {
    pub(crate) fn auxiliary_challenge_summary(&self) -> Option<E> {
        match self.auxiliary_challenge_source {
            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => Some(value),
            GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => None,
        }
    }

    pub(crate) fn constraint_metadata_summary(&self) -> Option<(usize, usize, E)> {
        self.constraint_metadata_summary
    }
}

pub(crate) struct GpuGKRMainLayerBackwardState<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) forward_tracing_ranges: Vec<Range>,
    pub(super) storage: GpuGKRStorage<BF, E>,
    pub(super) pending_layers: VecDeque<(usize, GKRLayerDescription)>,
    pub(super) trace_len: usize,
    pub(super) external_challenges: GKRExternalChallenges<BF, E>,
    pub(super) inits_and_teardowns_top_bits: Vec<u32>,
    pub(super) inits_and_teardowns_address_high_bits_shift: u32,
    pub(super) lookup_multiplicative_challenge: E,
    pub(super) lookup_additive_challenge: E,
    pub(super) num_base_layer_memory_polys: usize,
    pub(super) num_base_layer_witness_polys: usize,
    pub(super) is_delegation: bool,
}

pub(crate) struct GpuGKRMainLayerExecution<E: FieldExtension<BF> + Field> {
    pub(crate) new_claims: BTreeMap<GKRAddress, E>,
    pub(crate) new_claim_point: Vec<E>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

pub(crate) struct GpuGKRMainLayerScheduledLayerExecution<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) batch_challenge_storage: ScheduledChallengeStorage<E>,
    #[allow(dead_code)]
    pub(super) batch_challenge_buffer: ScheduledChallengeBuffer<E>,
    #[allow(dead_code)]
    pub(super) round_challenge_storage: ScheduledChallengeStorage<E>,
    #[allow(dead_code)]
    pub(super) round_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    pub(super) flat_coeff_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) recipe_upload_callbacks: Callbacks<'static>,
    pub(super) shared_state: Box<ScheduledMainLayerExecutionState<E>>,
    /// Device-resident Fiat-Shamir seed (see dim-reducing twin). Taken by the
    /// orchestrator to thread into the next backward layer.
    pub(super) device_seed: Option<DeviceAllocation<u32>>,
    /// Device-resident `[claim_point || batching_challenge]` for the NEXT
    /// backward layer (see dim-reducing twin). Taken by the orchestrator.
    pub(super) device_claim_point_for_next_layer: Option<DeviceAllocation<E>>,
    /// Device-resident `current_claims` buffer for the NEXT backward layer.
    pub(super) device_claims_for_next_layer: Option<DeviceAllocation<E>>,
    /// Explicit address order of `device_claims_for_next_layer`.
    pub(super) claim_layout_for_next_layer: Option<ClaimBufferLayout>,
}

pub(crate) struct ScheduledBackwardWorkflowState<E: FieldExtension<BF> + Field> {
    pub(super) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(super) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(super) current_claims: BTreeMap<GKRAddress, E>,
    pub(super) current_claim_point: Vec<E>,
    pub(super) current_batching_challenge: E,
    pub(super) lookup_multiplicative_challenge: E,
    pub(super) lookup_additive_challenge: E,
    pub(super) seed: Seed,
}

pub(crate) struct GpuGKRBackwardExecution<E: FieldExtension<BF> + Field> {
    pub(crate) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(crate) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

pub(crate) struct GpuGKRBackwardScheduledExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) dimension_reducing_layers: Vec<GpuGKRDimensionReducingScheduledLayerExecution<B, E>>,
    #[allow(dead_code)]
    pub(super) main_layers: Vec<GpuGKRMainLayerScheduledLayerExecution<E>>,
    pub(super) shared_state: Box<ScheduledBackwardWorkflowState<E>>,
    #[allow(dead_code)]
    // Keeps test-path initial-staging callbacks alive until the stream consumes them.
    pub(super) initial_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) external_challenges_device_keepalive: Option<DeviceAllocation<E>>,
    pub(super) final_device_seed: Option<DeviceAllocation<u32>>,
    pub(super) final_device_claim_point_and_batching: Option<DeviceAllocation<E>>,
    pub(super) final_claim_layout: Option<ClaimBufferLayout>,
    // Pinned host buffers populated by `schedule_post_backward_handoff`'s D2H. The
    // host callback that mirrors them into `ScheduledBackwardWorkflowState` reads
    // via raw-pointer accessors, so the buffers must outlive the callback. Holding
    // them on `self` (which lives until `into_host_keepalive`) is straightforward
    // and survives multi-prove pool reuse — without this, a sibling prove can
    // reallocate the freed chunks before this prove's callback fires.
    #[allow(dead_code)]
    pub(super) final_seed_host: Option<crate::primitives::context::HostAllocation<[u32]>>,
    #[allow(dead_code)]
    pub(super) final_claim_point_and_batching_host:
        Option<crate::primitives::context::HostAllocation<[E]>>,
}

pub(crate) struct GpuGKRDimensionReducingHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) round_challenge_storage: Option<HostScheduledChallengeStorage<E>>,
    #[allow(dead_code)]
    pub(super) _phantom: std::marker::PhantomData<B>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    pub(super) shared_state: Box<ScheduledDimensionReducingLayerExecutionState<E>>,
}

pub(crate) struct GpuGKRMainLayerHostKeepalive<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) batch_challenge_storage: HostScheduledChallengeStorage<E>,
    #[allow(dead_code)]
    pub(super) round_challenge_storage: HostScheduledChallengeStorage<E>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    pub(super) flat_coeff_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) recipe_upload_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) shared_state: Box<ScheduledMainLayerExecutionState<E>>,
}

pub(crate) struct GpuGKRBackwardHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) dimension_reducing_layers: Vec<GpuGKRDimensionReducingHostKeepalive<B, E>>,
    #[allow(dead_code)]
    pub(super) main_layers: Vec<GpuGKRMainLayerHostKeepalive<E>>,
    #[allow(dead_code)]
    pub(super) shared_state: Box<ScheduledBackwardWorkflowState<E>>,
    #[allow(dead_code)]
    pub(super) initial_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) external_challenges_device_keepalive: Option<DeviceAllocation<E>>,
    #[allow(dead_code)]
    pub(super) final_device_seed: Option<DeviceAllocation<u32>>,
    #[allow(dead_code)]
    pub(super) final_device_claim_point_and_batching: Option<DeviceAllocation<E>>,
    #[allow(dead_code)]
    pub(super) final_claim_layout: Option<ClaimBufferLayout>,
    #[allow(dead_code)]
    pub(super) final_seed_host: Option<crate::primitives::context::HostAllocation<[u32]>>,
    #[allow(dead_code)]
    pub(super) final_claim_point_and_batching_host:
        Option<crate::primitives::context::HostAllocation<[E]>>,
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
            lookup_multiplicative_challenge: E::ZERO,
            lookup_additive_challenge: E::ZERO,
            seed: Seed::default(),
        }
    }
}

/// Allocate a device `DeviceAllocation<u32>` of length `STATE_SIZE` and H2D a host `Seed`
/// into it. Only test paths still need this bridge (the hot path threads the post-forward
/// device seed straight through). The staging buffer is filled inside a stream-ordered
/// callback (per the GPU scheduling contract — `HostAllocation` contents must not be touched
/// on the scheduling thread), so the caller-owned `Callbacks` must outlive stream execution.
pub(crate) fn h2d_seed_from_host(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    host_seed: &Seed,
) -> CudaResult<DeviceAllocation<u32>> {
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(crate::ops::blake2s::STATE_SIZE, AllocationPlacement::Top)?;
    let mut host_slot =
        unsafe { context.alloc_host_uninit_slice::<u32>(crate::ops::blake2s::STATE_SIZE) };
    let accessor = host_slot.get_mut_accessor();
    let seed_words = host_seed.0;
    callbacks.schedule(
        move || unsafe {
            accessor.get_mut().copy_from_slice(&seed_words);
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut d_seed, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok(d_seed)
}

/// Allocate a device `DeviceAllocation<E>` of length `claim_point.len() + 1`, laid out as
/// `[claim_point || batching_challenge]` (matching the first backward layer's
/// `round_scratch.claim_point`), and H2D the host values into it. Only test paths still need
/// this bridge — the hot path threads the post-forward device squeeze buffer
/// (`d_evaluation_point_and_batching`) straight into the orchestrator. The staging buffer is
/// filled inside a stream-ordered callback; the caller-owned `Callbacks` must outlive stream
/// execution.
pub(crate) fn h2d_claim_point_and_batching_from_host<E: FieldExtension<BF> + Field + 'static>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    claim_point: &[E],
    batching_challenge: E,
) -> CudaResult<DeviceAllocation<E>> {
    let len = claim_point.len() + 1;
    let mut buf: DeviceAllocation<E> = context.alloc(len, AllocationPlacement::Top)?;
    let mut host_slot = unsafe { context.alloc_host_uninit_slice::<E>(len) };
    let accessor = host_slot.get_mut_accessor();
    let claim_point_owned: Vec<E> = claim_point.to_vec();
    callbacks.schedule(
        move || unsafe {
            let dst = accessor.get_mut();
            let (cp_dst, batching_dst) = dst.split_at_mut(claim_point_owned.len());
            cp_dst.copy_from_slice(&claim_point_owned);
            batching_dst[0] = batching_challenge;
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut buf, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok(buf)
}

/// Allocate a device claims buffer and upload values in the explicit order
/// defined by the returned `ClaimBufferLayout`. The staging buffer is filled
/// inside a stream-ordered callback; the caller-owned `Callbacks` must outlive
/// stream execution.
pub(crate) fn h2d_claims_from_host<E: FieldExtension<BF> + Field + 'static>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    claims: &BTreeMap<GKRAddress, E>,
) -> CudaResult<(DeviceAllocation<E>, ClaimBufferLayout)> {
    let layout = ClaimBufferLayout::from_claims(claims);
    let len = layout.len();
    let mut buf: DeviceAllocation<E> = context.alloc(len, AllocationPlacement::Top)?;
    let mut host_slot = unsafe { context.alloc_host_uninit_slice::<E>(len) };
    let accessor = host_slot.get_mut_accessor();
    let layout_for_callback = layout.clone();
    let claims_owned = claims.clone();
    callbacks.schedule(
        move || unsafe {
            layout_for_callback.write_values_from_claims(&claims_owned, accessor.get_mut());
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut buf, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok((buf, layout))
}

pub(crate) fn make_deferred_backward_workflow_state<E>() -> Box<ScheduledBackwardWorkflowState<E>>
where
    E: FieldExtension<BF> + Field,
{
    Box::new(ScheduledBackwardWorkflowState::deferred())
}

/// Stage `[lookup_multiplicative, lookup_additive]` into a 2-element
/// device buffer, reading from `shared_state` inside a stream-ordered callback. Used
/// once per proof by the main-layer pipeline so per-layer `schedule_flat_eval_recipes`
/// can D2D these constants into its 3-scalar eval_recipes challenge buffer instead of
/// reading from host `workflow_state` on every layer. The caller-owned `Callbacks` must
/// outlive stream execution.
pub(crate) fn h2d_lookup_and_constraint_from_shared_state<E>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
) -> CudaResult<DeviceAllocation<E>>
where
    E: FieldExtension<BF> + Field + 'static,
{
    let mut buf: DeviceAllocation<E> = context.alloc(2, AllocationPlacement::Top)?;
    let mut host_slot = unsafe { context.alloc_host_uninit_slice::<E>(2) };
    let accessor = host_slot.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            let state = shared_state.get();
            let dst = accessor.get_mut();
            dst[0] = state.lookup_multiplicative_challenge;
            dst[1] = state.lookup_additive_challenge;
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut buf, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok(buf)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn populate_backward_workflow_state<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
    initial_output_layer_idx: usize,
    top_layer_claims: BTreeMap<GKRAddress, E>,
    evaluation_point: Vec<E>,
    seed: Seed,
    batching_challenge: E,
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) where
    E: FieldExtension<BF> + Field,
{
    let state = unsafe { shared_state.get_mut() };
    state.claims_for_layers =
        BTreeMap::from([(initial_output_layer_idx, top_layer_claims.clone())]);
    state.points_for_claims_at_layer =
        BTreeMap::from([(initial_output_layer_idx, evaluation_point.clone())]);
    state.current_claims = top_layer_claims;
    state.current_claim_point = evaluation_point;
    state.current_batching_challenge = batching_challenge;
    state.lookup_multiplicative_challenge = lookup_multiplicative_challenge;
    state.lookup_additive_challenge = lookup_additive_challenge;
    state.seed = seed;
}

pub(crate) fn clone_backward_claim_point_for_layer<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
    layer_idx: usize,
) -> Vec<E>
where
    E: FieldExtension<BF> + Field + Clone,
{
    unsafe { shared_state.get() }
        .points_for_claims_at_layer
        .get(&layer_idx)
        .cloned()
        .expect("missing backward claim point for layer")
}

pub(crate) fn fill_backward_claim_point_for_layer<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
    layer_idx: usize,
    dst: &mut [E],
) where
    E: FieldExtension<BF> + Field + Copy,
{
    let state = unsafe { shared_state.get() };
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
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
    layer_idx: usize,
) -> BTreeMap<GKRAddress, E>
where
    E: FieldExtension<BF> + Field + Clone,
{
    unsafe { shared_state.get() }
        .claims_for_layers
        .get(&layer_idx)
        .cloned()
        .expect("missing backward claims for layer")
}

pub(crate) fn current_backward_batching_challenge<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
) -> E
where
    E: FieldExtension<BF> + Field + Copy,
{
    unsafe { shared_state.get() }.current_batching_challenge
}

pub(crate) fn current_backward_seed<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
) -> Seed
where
    E: FieldExtension<BF> + Field,
{
    unsafe { shared_state.get() }.seed
}

pub(crate) fn apply_base_layer_extra_evaluations_to_workflow_state<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
    extra_evaluations_addresses: &[GKRAddress],
    extra_evaluations_values: &[E],
) where
    E: FieldExtension<BF> + Field + Copy,
    [(); E::DEGREE]: Sized,
{
    debug_assert_eq!(
        extra_evaluations_addresses.len(),
        extra_evaluations_values.len(),
    );
    if extra_evaluations_addresses.is_empty() {
        return;
    }

    // The only durable side-effect production needs is committing the extras
    // values into the rolling transcript seed; downstream WHIR setup reads
    // the seed via `current_backward_seed`. The historical extends of
    // `claims_for_layers[0]` and `current_claims` are dead in production
    // (`mirror_layer_to_host` is false on the prove path, so the per-layer
    // claim BTreeMap is never populated, and `current_claims` is no longer
    // mirrored across the post-backward boundary).
    let state = unsafe { shared_state.get_mut() };
    commit_field_els::<BF, E>(&mut state.seed, extra_evaluations_values);
}

pub(crate) fn take_backward_execution_from_shared_state<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
) -> GpuGKRBackwardExecution<E>
where
    E: FieldExtension<BF> + Field,
{
    let state = unsafe { shared_state.get_mut() };
    GpuGKRBackwardExecution {
        claims_for_layers: std::mem::take(&mut state.claims_for_layers),
        points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
        next_batching_challenge: state.current_batching_challenge,
        updated_seed: state.seed,
    }
}

pub(super) fn challenge_storage_into_host_keepalive<E>(
    storage: ScheduledChallengeStorage<E>,
) -> HostScheduledChallengeStorage<E> {
    let ScheduledChallengeStorage {
        callbacks,
        device: _,
    } = storage;
    HostScheduledChallengeStorage {
        callbacks,
        _phantom: std::marker::PhantomData,
    }
}

pub(super) fn upload_into_host_keepalive<T>(upload: ScheduledUpload<T>) -> HostScheduledUpload<T> {
    let ScheduledUpload {
        callbacks,
        device: _,
        scheduler_host,
    } = upload;
    HostScheduledUpload {
        callbacks,
        scheduler_host,
        _phantom: std::marker::PhantomData,
    }
}

pub(super) fn schedule_immediate_field_upload<E: Field + Send + Sync + 'static>(
    context: &ProverContext,
    padded_len: usize,
    values: &[E],
) -> CudaResult<(ScheduledChallengeStorage<E>, ScheduledChallengeBuffer<E>)> {
    assert!(values.len() <= padded_len);
    let values = values.to_vec();
    let mut storage =
        ScheduledChallengeStorage::new(context.alloc(padded_len, AllocationPlacement::Top)?);
    let buffer = schedule_packed_round_challenge_upload(
        context,
        storage.device_accessor(),
        &mut storage.callbacks,
        0,
        padded_len,
        move |slice| {
            slice[..values.len()].copy_from_slice(&values);
        },
    )?;
    Ok((storage, buffer))
}

pub(super) fn schedule_packed_round_challenge_upload<E: Field + 'static>(
    context: &ProverContext,
    device: UnsafeAccessor<SharedChallengeDevice<E>>,
    callbacks: &mut Callbacks<'static>,
    offset: usize,
    len: usize,
    fill: impl Fn(&mut [E]) + Send + Sync + 'static,
) -> CudaResult<ScheduledChallengeBuffer<E>> {
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
            device.get().slice_mut(offset, len),
            &host,
            context.get_exec_stream(),
        )?;
    }
    drop(host);

    Ok(ScheduledChallengeBuffer {
        device,
        offset,
        len,
    })
}

pub(super) fn schedule_callback_populated_field_upload<'a, E: Field + 'a>(
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

pub(super) fn schedule_callback_populated_upload<'a, T: Copy + 'a>(
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
        scheduler_host: None,
    })
}

pub(super) fn field_pow<E: Field>(base: E, exponent: usize) -> E {
    let mut result = E::ONE;
    for _ in 0..exponent {
        result.mul_assign(&base);
    }
    result
}

pub(super) fn main_layer_round_challenge_len(step: usize) -> usize {
    match step {
        1 => 1,
        2 => 2,
        _ => 1,
    }
}

pub(super) fn empty_round0_host_launch_descriptors<B, E>(
    context: &ProverContext,
) -> GpuSumcheckRound0HostLaunchDescriptors<B, E> {
    GpuSumcheckRound0HostLaunchDescriptors {
        base_field_inputs: unsafe { context.alloc_host_uninit_slice(0) },
        extension_field_inputs: unsafe { context.alloc_host_uninit_slice(0) },
        base_field_outputs: unsafe { context.alloc_host_uninit_slice(0) },
        extension_field_outputs: unsafe { context.alloc_host_uninit_slice(0) },
    }
}

pub(super) const GKR_DIM_REDUCING_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(super) const GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK: u32 = 512;
pub(super) const GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK: usize = 4;
pub(super) const GKR_EQ_GROUP_SIZE: usize = 8;
pub(super) const GKR_EQ_GROUP_TABLE_LEN: usize = 1 << GKR_EQ_GROUP_SIZE;

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
    GpuDimensionReducingBuildEqGroupTablesFromPairs<T>,
    eq_pair_values: *const T,
    challenge_count: u32,
    eq_group_tables: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingBuildEqGroupTablesFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    eq_group_tables: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingBuildEqValuesFromGroupTables<T>,
    eq_group_tables: *const T,
    challenge_count: u32,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingFoldEqValues<T>,
    eq_values: *mut T,
    half_len: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingTraceHolderBlockPartials<T>,
    raw_values: *const BF,
    eq_values: *const T,
    block_partials: *mut T,
    trace_len: u32,
    column_start: u32,
    chunk_cols: u32,
    blocks_count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingRound0BatchedCompact<T>,
    batch: GpuGKRDimensionReducingRound0BatchCompact<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingRound1BatchedCompact<T>,
    batch: GpuGKRDimensionReducingContinuationBatchCompact<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingContinuationBatchedCompact<T>,
    batch: GpuGKRDimensionReducingContinuationBatchCompact<T>,
    acc_size: u32,
    step: u32,
);

pub(crate) trait GpuDimensionReducingKernelSet: Reduce + Copy + Sized {
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
    const CONTINUATION_BATCHED_COMPACT: GpuDimensionReducingContinuationBatchedCompactSignature<
        Self,
    >;
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
                [<ab_gkr_dim_reducing_build_eq_group_tables_from_pairs_ $type:lower _kernel>](
                    eq_pair_values: *const $type,
                    challenge_count: u32,
                    eq_group_tables: *mut $type,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_build_eq_group_tables_from_point_ $type:lower _kernel>](
                    claim_point: *const $type,
                    challenge_offset: u32,
                    challenge_count: u32,
                    eq_group_tables: *mut $type,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_build_eq_values_from_group_tables_ $type:lower _kernel>](
                    eq_group_tables: *const $type,
                    challenge_count: u32,
                    eq_values: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_fold_eq_values_ $type:lower _kernel>](
                    eq_values: *mut $type,
                    half_len: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_trace_holder_block_partials_ $type:lower _kernel>](
                    raw_values: *const BF,
                    eq_values: *const $type,
                    block_partials: *mut $type,
                    trace_len: u32,
                    column_start: u32,
                    chunk_cols: u32,
                    blocks_count: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_round0_batched_compact_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingRound0BatchCompact<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_round1_batched_compact_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingContinuationBatchCompact<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_continuation_batched_compact_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingContinuationBatchCompact<$type>,
                    acc_size: u32,
                    step: u32,
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
                const BUILD_EQ_GROUP_TABLES_FROM_PAIRS: GpuDimensionReducingBuildEqGroupTablesFromPairsSignature<Self> =
                    [<ab_gkr_dim_reducing_build_eq_group_tables_from_pairs_ $type:lower _kernel>];
                const BUILD_EQ_GROUP_TABLES_FROM_POINT: GpuDimensionReducingBuildEqGroupTablesFromPointSignature<Self> =
                    [<ab_gkr_dim_reducing_build_eq_group_tables_from_point_ $type:lower _kernel>];
                const BUILD_EQ_VALUES_FROM_GROUP_TABLES: GpuDimensionReducingBuildEqValuesFromGroupTablesSignature<Self> =
                    [<ab_gkr_dim_reducing_build_eq_values_from_group_tables_ $type:lower _kernel>];
                const FOLD_EQ_VALUES: GpuDimensionReducingFoldEqValuesSignature<Self> =
                    [<ab_gkr_dim_reducing_fold_eq_values_ $type:lower _kernel>];
                const TRACE_HOLDER_BLOCK_PARTIALS: GpuDimensionReducingTraceHolderBlockPartialsSignature<Self> =
                    [<ab_gkr_dim_reducing_trace_holder_block_partials_ $type:lower _kernel>];
                const ROUND0_BATCHED_COMPACT: GpuDimensionReducingRound0BatchedCompactSignature<Self> =
                    [<ab_gkr_dim_reducing_round0_batched_compact_ $type:lower _kernel>];
                const ROUND1_BATCHED_COMPACT: GpuDimensionReducingRound1BatchedCompactSignature<Self> =
                    [<ab_gkr_dim_reducing_round1_batched_compact_ $type:lower _kernel>];
                const CONTINUATION_BATCHED_COMPACT: GpuDimensionReducingContinuationBatchedCompactSignature<Self> =
                    [<ab_gkr_dim_reducing_continuation_batched_compact_ $type:lower _kernel>];
            }
        }
    };
}

gkr_dim_reducing_kernels!(E4);

/// Dispatches the fused per-round backward-sumcheck state update kernel.
/// Currently only implemented for `E4`; the single impl exists to let the
/// generic scheduler in `backward.rs` invoke the kernel without losing type
/// parametricity in the surrounding code.
pub(crate) trait GpuBackwardSumcheckRoundUpdateKernel: Sized {
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
}

impl GpuBackwardSumcheckRoundUpdateKernel for E4 {
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
        crate::ops::blake2s::backward_sumcheck_round_update(
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
}

pub(super) fn gkr_dim_reducing_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_DIM_REDUCING_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(super) fn gkr_trace_holder_partials_launch_config(
    blocks_count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    CudaLaunchConfig::basic(
        blocks_count,
        GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    )
}

pub(super) fn launch_pairwise_round0<E: GpuDimensionReducingKernelSet>(
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

pub(super) fn launch_lookup_round0<E: GpuDimensionReducingKernelSet>(
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

pub(super) fn launch_pairwise_continuation<E: GpuDimensionReducingKernelSet>(
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

pub(super) fn launch_lookup_continuation<E: GpuDimensionReducingKernelSet>(
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

pub(super) fn launch_dim_reducing_round0_batched_compact<
    E: GpuDimensionReducingKernelSet + Field,
>(
    batch: &GpuGKRDimensionReducingRound0BatchCompact<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound0BatchedCompactArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound0BatchedCompactFunction(E::ROUND0_BATCHED_COMPACT)
        .launch(&config, &args)
}

pub(super) fn launch_dim_reducing_round1_batched_compact<
    E: GpuDimensionReducingKernelSet + Field,
>(
    batch: &GpuGKRDimensionReducingContinuationBatchCompact<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound1BatchedCompactArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound1BatchedCompactFunction(E::ROUND1_BATCHED_COMPACT)
        .launch(&config, &args)
}

pub(super) fn launch_dim_reducing_continuation_batched_compact<
    E: GpuDimensionReducingKernelSet + Field,
>(
    batch: &GpuGKRDimensionReducingContinuationBatchCompact<E>,
    acc_size: usize,
    step: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingContinuationBatchedCompactArguments::new(
        *batch,
        acc_size as u32,
        step as u32,
    );
    GpuDimensionReducingContinuationBatchedCompactFunction(E::CONTINUATION_BATCHED_COMPACT)
        .launch(&config, &args)
}

pub(crate) fn launch_build_eq_values_from_point<E: GpuDimensionReducingKernelSet>(
    claim_point: *const E,
    challenge_offset: usize,
    challenge_count: usize,
    eq_group_tables: *mut E,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(challenge_offset <= u32::MAX as usize);
    assert!(challenge_count <= u32::MAX as usize);
    assert!(acc_size <= u32::MAX as usize);
    let group_count = eq_group_count(challenge_count);
    if group_count > 0 {
        let config = CudaLaunchConfig::basic(
            group_count as u32,
            GKR_EQ_GROUP_TABLE_LEN as u32,
            context.get_exec_stream(),
        );
        let args = GpuDimensionReducingBuildEqGroupTablesFromPointArguments::new(
            claim_point,
            challenge_offset as u32,
            challenge_count as u32,
            eq_group_tables,
        );
        GpuDimensionReducingBuildEqGroupTablesFromPointFunction(
            E::BUILD_EQ_GROUP_TABLES_FROM_POINT,
        )
        .launch(&config, &args)?;
    }

    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingBuildEqValuesFromGroupTablesArguments::new(
        eq_group_tables,
        challenge_count as u32,
        eq_values,
        acc_size as u32,
    );
    GpuDimensionReducingBuildEqValuesFromGroupTablesFunction(E::BUILD_EQ_VALUES_FROM_GROUP_TABLES)
        .launch(&config, &args)
}

pub(crate) fn round0_eq_pair_values_len(folding_steps: usize) -> usize {
    2 * folding_steps.saturating_sub(1)
}

pub(crate) fn eq_group_count(challenge_count: usize) -> usize {
    challenge_count.div_ceil(GKR_EQ_GROUP_SIZE)
}

pub(crate) fn eq_group_tables_len(challenge_count: usize) -> usize {
    eq_group_count(challenge_count) * GKR_EQ_GROUP_TABLE_LEN
}

pub(crate) fn round0_eq_group_tables_len(folding_steps: usize) -> usize {
    eq_group_tables_len(folding_steps.saturating_sub(1))
}

pub(crate) fn launch_build_round0_eq_values_from_pairs<E: GpuDimensionReducingKernelSet>(
    eq_pair_values: *const E,
    challenge_count: usize,
    eq_group_tables: *mut E,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(challenge_count <= u32::MAX as usize);
    assert!(acc_size <= u32::MAX as usize);
    let group_count = eq_group_count(challenge_count);
    if group_count > 0 {
        let config = CudaLaunchConfig::basic(
            group_count as u32,
            GKR_EQ_GROUP_TABLE_LEN as u32,
            context.get_exec_stream(),
        );
        let args = GpuDimensionReducingBuildEqGroupTablesFromPairsArguments::new(
            eq_pair_values,
            challenge_count as u32,
            eq_group_tables,
        );
        GpuDimensionReducingBuildEqGroupTablesFromPairsFunction(
            E::BUILD_EQ_GROUP_TABLES_FROM_PAIRS,
        )
        .launch(&config, &args)?;
    }

    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingBuildEqValuesFromGroupTablesArguments::new(
        eq_group_tables,
        challenge_count as u32,
        eq_values,
        acc_size as u32,
    );
    GpuDimensionReducingBuildEqValuesFromGroupTablesFunction(E::BUILD_EQ_VALUES_FROM_GROUP_TABLES)
        .launch(&config, &args)
}

pub(crate) fn launch_fold_eq_values_in_place<E: GpuDimensionReducingKernelSet>(
    eq_values: *mut E,
    half_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(half_len <= u32::MAX as usize);
    let config = gkr_dim_reducing_launch_config(half_len as u32, context);
    let args = GpuDimensionReducingFoldEqValuesArguments::new(eq_values, half_len as u32);
    GpuDimensionReducingFoldEqValuesFunction(E::FOLD_EQ_VALUES).launch(&config, &args)
}

pub(crate) fn launch_trace_holder_block_partials<E: GpuDimensionReducingKernelSet>(
    raw_values: *const BF,
    eq_values: *const E,
    block_partials: *mut E,
    trace_len: usize,
    column_start: usize,
    chunk_cols: usize,
    blocks_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    assert!(column_start <= u32::MAX as usize);
    assert!(chunk_cols <= u32::MAX as usize);
    assert!(blocks_count <= u32::MAX as usize);
    let config = gkr_trace_holder_partials_launch_config(blocks_count as u32, context);
    let args = GpuDimensionReducingTraceHolderBlockPartialsArguments::new(
        raw_values,
        eq_values,
        block_partials,
        trace_len as u32,
        column_start as u32,
        chunk_cols as u32,
        blocks_count as u32,
    );

    GpuDimensionReducingTraceHolderBlockPartialsFunction(E::TRACE_HOLDER_BLOCK_PARTIALS)
        .launch(&config, &args)
}

pub(super) fn apply_eq_and_reduce_accumulator<E>(
    eq_values: &DeviceAllocation<E>,
    accumulator: &mut DeviceAllocation<E>,
    reduction_output: &mut DeviceAllocation<E>,
    reduction_temp_storage: &mut DeviceAllocation<u8>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + Reduce,
    Mul: BinaryOp<E, E, E>,
{
    let stream = context.get_exec_stream();
    let eq_values = DeviceVectorChunk::new(eq_values, 0, acc_size);
    let reduction_temp = unsafe {
        DeviceSlice::from_raw_parts_mut(
            reduction_temp_storage.as_mut_ptr(),
            reduction_temp_storage.len(),
        )
    };

    {
        let mut low_half = DeviceVectorChunkMut::new(accumulator, 0, acc_size);
        mul_into_y(&eq_values, &mut low_half, stream)?;
        reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &low_half,
            &mut reduction_output[0],
            stream,
        )?;
    }

    {
        let mut high_half = DeviceVectorChunkMut::new(accumulator, acc_size, acc_size);
        mul_into_y(&eq_values, &mut high_half, stream)?;
        reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &high_half,
            &mut reduction_output[1],
            stream,
        )?;
    }

    Ok(())
}

#[cfg(test)]
mod compact_descriptor_tests {
    use std::mem::size_of;

    use super::*;
    use crate::primitives::field::E4;
    use crate::prover::gkr::gkr_address_audit::{
        KERNEL_ARG_HARD_CEILING_BYTES, KERNEL_ARG_SOFT_TARGET_BYTES,
    };

    #[test]
    fn pack_source_u16_round_trips() {
        for first_access in [false, true] {
            for ptr_idx in 0u8..(GKR_DIM_REDUCING_BASE_SLOTS as u8) {
                for &poly_idx in &[0u16, 1, 2, 17, 255, 1024, 0x07FF] {
                    let packed = pack_source_u16(first_access, ptr_idx, poly_idx);
                    let (fa, p, q) = unpack_source_u16(packed);
                    assert_eq!(fa, first_access);
                    assert_eq!(p, ptr_idx);
                    assert_eq!(q, poly_idx);
                }
            }
        }
    }

    #[test]
    fn pack_source_u16_layout_bits() {
        // bit 15 = first_access, bits 14..11 = ptr_idx (4 bits, 16 slots),
        // bits 10..0 = poly_idx (11 bits, max 2048).
        assert_eq!(pack_source_u16(false, 0, 0), 0);
        assert_eq!(pack_source_u16(true, 0, 0), 0x8000);
        assert_eq!(pack_source_u16(false, 0xF, 0), 0x7800);
        assert_eq!(pack_source_u16(false, 0, 0x07FF), 0x07FF);
        assert_eq!(pack_source_u16(true, 0xF, 0x07FF), 0xFFFF);
    }

    #[test]
    fn compact_descriptor_sizes_under_kernel_arg_ceiling() {
        let r0 = size_of::<GpuGKRDimensionReducingRound0BatchCompact<E4>>();
        let cont = size_of::<GpuGKRDimensionReducingContinuationBatchCompact<E4>>();
        // Both must fit comfortably under the soft 16 KB target (and well
        // under the 32 KB hard ceiling enforced by `cudaLaunchKernelExC`).
        assert!(
            r0 <= KERNEL_ARG_SOFT_TARGET_BYTES,
            "round0 compact = {r0} B exceeds soft target {KERNEL_ARG_SOFT_TARGET_BYTES}"
        );
        assert!(
            cont <= KERNEL_ARG_SOFT_TARGET_BYTES,
            "continuation compact = {cont} B exceeds soft target {KERNEL_ARG_SOFT_TARGET_BYTES}"
        );
        assert!(r0 < KERNEL_ARG_HARD_CEILING_BYTES);
        assert!(cont < KERNEL_ARG_HARD_CEILING_BYTES);
    }

    #[test]
    fn compact_record_is_16_bytes() {
        // Audit's projected post-compaction footprint depends on this size.
        assert_eq!(
            size_of::<GpuGKRDimensionReducingBatchRecordCompact>(),
            16,
            "compact batch record size drift breaks Phase 0 size projection"
        );
    }
}
