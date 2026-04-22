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
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor, UnsafeMutAccessor,
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
pub(super) const MAX_INLINE_ROUND_BATCH_BYTES: usize = 12 * 1024;

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
pub(crate) struct GpuGKRMainLayerConstraintHostMetadata<E> {
    pub(crate) quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(crate) linear_terms: Vec<GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(crate) constant_offset: E,
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

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainLayerPayloadRange {
    pub(super) offset: u32,
    pub(super) count: u32,
}

impl Default for GpuGKRMainLayerPayloadRange {
    fn default() -> Self {
        Self {
            offset: 0,
            count: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct GpuGKRMainLayerRound3HostDescriptors<E: Copy> {
    pub(super) step: usize,
    pub(super) descriptors: GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRDimensionReducingRound0BatchRecord {
    pub(super) kind: u32,
    pub(super) _reserved0: u32,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_outputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
}

impl Default for GpuGKRDimensionReducingRound0BatchRecord {
    fn default() -> Self {
        Self {
            kind: GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            _reserved0: 0,
            extension_inputs: GpuGKRMainLayerPayloadRange::default(),
            extension_outputs: GpuGKRMainLayerPayloadRange::default(),
            batch_challenge_offset: 0,
            batch_challenge_count: 0,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRDimensionReducingContinuationBatchRecord {
    pub(super) kind: u32,
    pub(super) _reserved0: u32,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
}

impl Default for GpuGKRDimensionReducingContinuationBatchRecord {
    fn default() -> Self {
        Self {
            kind: GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            _reserved0: 0,
            extension_inputs: GpuGKRMainLayerPayloadRange::default(),
            batch_challenge_offset: 0,
            batch_challenge_count: 0,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound0Batch<E> {
    pub(super) record_count: u32,
    pub(super) _reserved0: u32,
    pub(super) _reserved1: u32,
    pub(super) _reserved2: u32,
    pub(super) eq_values: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) contributions: *mut E,
    pub(super) records:
        [GpuGKRDimensionReducingRound0BatchRecord; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound0Batch<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            _reserved1: 0,
            _reserved2: 0,
            eq_values: null(),
            batch_challenge_base: null(),
            contributions: null_mut(),
            records: [GpuGKRDimensionReducingRound0BatchRecord::default();
                GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound1Batch<E> {
    pub(super) record_count: u32,
    pub(super) _reserved0: u32,
    pub(super) _reserved1: u32,
    pub(super) _reserved2: u32,
    pub(super) eq_values: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) explicit_form: bool,
    pub(super) _padding: [u8; 7],
    pub(super) records:
        [GpuGKRDimensionReducingContinuationBatchRecord; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound1Batch<E> {
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
            records: [GpuGKRDimensionReducingContinuationBatchRecord::default();
                GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound2Batch<E> {
    pub(super) record_count: u32,
    pub(super) _reserved0: u32,
    pub(super) _reserved1: u32,
    pub(super) _reserved2: u32,
    pub(super) eq_values: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) explicit_form: bool,
    pub(super) _padding: [u8; 7],
    pub(super) records:
        [GpuGKRDimensionReducingContinuationBatchRecord; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound2Batch<E> {
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
            records: [GpuGKRDimensionReducingContinuationBatchRecord::default();
                GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound3Batch<E> {
    pub(super) record_count: u32,
    pub(super) _reserved0: u32,
    pub(super) _reserved1: u32,
    pub(super) _reserved2: u32,
    pub(super) eq_values: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) explicit_form: bool,
    pub(super) _padding: [u8; 7],
    pub(super) records:
        [GpuGKRDimensionReducingContinuationBatchRecord; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound3Batch<E> {
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
            records: [GpuGKRDimensionReducingContinuationBatchRecord::default();
                GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct GpuGKRDimensionReducingRound3HostDescriptors<E: Copy> {
    pub(super) step: usize,
    pub(super) descriptors: GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E>,
}

#[derive(Clone)]
pub(super) struct GpuGKRDimensionReducingRound3BatchTemplate<E> {
    pub(super) step: usize,
    pub(super) batch: GpuGKRDimensionReducingRound3Batch<E>,
}

pub(super) struct InlinePayloadBuilder {
    pub(super) bytes: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
    pub(super) len: usize,
}

impl InlinePayloadBuilder {
    pub(super) fn new() -> Self {
        Self {
            bytes: [0; MAX_INLINE_ROUND_BATCH_BYTES],
            len: 0,
        }
    }

    pub(super) fn mark(&self) -> usize {
        self.len
    }

    pub(super) fn restore(&mut self, mark: usize) {
        self.len = mark;
    }

    pub(super) fn try_push_copy<T: Copy>(
        &mut self,
        values: &[T],
    ) -> Option<GpuGKRMainLayerPayloadRange> {
        if values.is_empty() {
            return Some(GpuGKRMainLayerPayloadRange::default());
        }
        let start = align_up(self.len, align_of::<T>());
        let bytes = as_bytes(values);
        let end = start.checked_add(bytes.len())?;
        if end > self.bytes.len() {
            return None;
        }
        self.bytes[start..end].copy_from_slice(bytes);
        self.len = end;
        Some(GpuGKRMainLayerPayloadRange {
            offset: start as u32,
            count: values.len() as u32,
        })
    }

    pub(super) fn into_bytes(self) -> [u8; MAX_INLINE_ROUND_BATCH_BYTES] {
        self.bytes
    }
}

pub(super) fn align_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + (align - 1)) & !(align - 1)
}

pub(super) fn as_bytes<T: Copy>(values: &[T]) -> &[u8] {
    // SAFETY: `T: Copy` and the returned byte slice has the same lifetime as the input slice.
    unsafe { slice::from_raw_parts(values.as_ptr().cast::<u8>(), std::mem::size_of_val(values)) }
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
    pub(super) round0_descriptors: Vec<GpuSumcheckRound0LaunchDescriptors<B, E>>,
    pub(super) round0_batch_template: GpuGKRDimensionReducingRound0Batch<E>,
    pub(super) round1_batch_template: GpuGKRDimensionReducingRound1Batch<E>,
    pub(super) round2_batch_template: Option<GpuGKRDimensionReducingRound2Batch<E>>,
    pub(super) round3_batch_templates: Vec<GpuGKRDimensionReducingRound3BatchTemplate<E>>,
    pub(super) round_scratch: GpuGKRDimensionReducingRoundScratch<E>,
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
}

pub(super) struct HostScheduledUpload<T> {
    pub(super) callbacks: Callbacks<'static>,
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
    pub(super) combined_claim_desc_upload: Option<ScheduledUpload<u32>>,
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
    pub(super) kernel_plans: Vec<GpuGKRMainLayerKernelPlan<E>>,
    pub(super) round0_descriptors: Vec<GpuSumcheckRound0LaunchDescriptors<BF, E>>,
    pub(super) flat_round0_template: Option<super::backward_flat::FlatRound0BuildPlan<E>>,
    /// Device allocations for compiled recipe headers and terms (uploaded once at prepare time).
    pub(super) flat_recipe_headers:
        Option<DeviceAllocation<crate::ops::eval_recipes::GpuRecipeHeader>>,
    pub(super) flat_recipe_terms:
        Option<DeviceAllocation<crate::ops::eval_recipes::GpuPrefactorTerm>>,
    /// Device buffer for eval_recipes output (delegation L0 round 0 only; others write to __constant__).
    pub(super) flat_coeff_device_buf: Option<DeviceAllocation<E>>,
    /// Device buffer for 4 challenge scalars fed to eval_recipes.
    pub(super) flat_challenges_buf: Option<DeviceAllocation<E>>,
    /// Whether round 0 uses __constant__ for coefficients (false only for delegation L0).
    pub(super) flat_use_constant: bool,
    /// Flat continuation plan for rounds 1+ (shared term arrays + per-step source tables).
    pub(super) flat_continuation_plan: Option<super::backward_flat::FlatContinuationBuildPlan<E>>,
    /// Per-step static descriptions for flat round 3+ kernels (intermediate for building unified descs).
    pub(super) flat_continuation_descs: Vec<(
        usize,
        Box<super::backward_flat::GpuFlatContinuationStaticDesc>,
    )>,
    /// Device allocations for continuation recipe headers and terms.
    pub(super) flat_cont_recipe_headers:
        Option<DeviceAllocation<crate::ops::eval_recipes::GpuRecipeHeader>>,
    pub(super) flat_cont_recipe_terms:
        Option<DeviceAllocation<crate::ops::eval_recipes::GpuPrefactorTerm>>,
    /// Static description for flat round 1 kernel (intermediate for building unified desc).
    pub(super) flat_round1_desc: Option<Box<super::backward_flat::GpuFlatRound1StaticDesc>>,
    /// Combined descriptor for the unified round 1 kernel (sources + mixed terms).
    pub(super) flat_round1_unified_desc:
        Option<Box<super::backward_flat::GpuFlatRound1UnifiedDesc>>,
    /// Static description for flat round 2 kernel (intermediate for building unified desc).
    pub(super) flat_round2_desc: Option<Box<super::backward_flat::GpuFlatRound2StaticDesc>>,
    /// Combined descriptor for the unified round 2 kernel (sources + mixed terms).
    pub(super) flat_round2_unified_desc:
        Option<Box<super::backward_flat::GpuFlatRound2UnifiedDesc>>,
    /// Per-step unified descriptors for flat round 3+ kernels (tiled warp-split).
    pub(super) flat_continuation_unified_descs: Vec<(
        usize,
        Box<super::backward_flat::GpuFlatContinuationUnifiedDesc>,
    )>,
    pub(super) round_scratch: GpuGKRMainLayerRoundScratch<E>,
    /// Keeps pinned-staging callbacks alive for recipe H2D copies scheduled at prepare time.
    /// Moved into `GpuGKRMainLayerScheduledLayerExecution` during `schedule_execute_*`.
    pub(super) recipe_upload_callbacks: Callbacks<'static>,
}

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
    pub(super) combined_claim_desc_upload: Option<ScheduledUpload<u32>>,
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
    #[allow(dead_code)] // Keeps test-path initial-staging callbacks alive until the stream consumes them.
    pub(super) initial_callbacks: Callbacks<'static>,
}

pub(crate) struct GpuGKRDimensionReducingHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) combined_claim_desc_upload: Option<HostScheduledUpload<u32>>,
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
    pub(super) combined_claim_desc_upload: Option<HostScheduledUpload<u32>>,
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
    let mut host_slot = unsafe {
        context.alloc_host_uninit_slice::<u32>(crate::ops::blake2s::STATE_SIZE)
    };
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
    extra_evaluations_from_caching_relations: &BTreeMap<GKRAddress, E>,
    extra_evaluations_transcript_batches: &[Vec<E>],
) where
    E: FieldExtension<BF> + Field + Copy,
    [(); E::DEGREE]: Sized,
{
    if extra_evaluations_from_caching_relations.is_empty() {
        return;
    }

    let state = unsafe { shared_state.get_mut() };
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
    } = upload;
    HostScheduledUpload {
        callbacks,
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
    })
}

/// Upload a per-layer combined-claim `(exp, claim_idx)` descriptor via the
/// standard pinned-staging → H2D pattern. `desc_pairs` is pure compiled-
/// circuit static; the upload carries both the device buffer and the
/// stream-ordered fill callback that populates the pinned staging slot.
pub(super) fn schedule_combined_claim_desc_upload(
    context: &ProverContext,
    desc_pairs: Vec<u32>,
) -> CudaResult<ScheduledUpload<u32>> {
    // Always allocate at least one element so downstream `.device[..]`
    // indexing has a valid pointer even in the degenerate zero-term case.
    let alloc_len = desc_pairs.len().max(1);
    let payload = desc_pairs;
    let mut callbacks = Callbacks::new();
    let mut upload =
        schedule_callback_populated_upload(context, alloc_len, &mut callbacks, move |dst| {
            if !payload.is_empty() {
                dst[..payload.len()].copy_from_slice(&payload);
            }
        })?;
    upload.callbacks = callbacks;
    Ok(upload)
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
    GpuDimensionReducingRound0Batched<T>,
    batch: GpuGKRDimensionReducingRound0Batch<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingRound1Batched<T>,
    batch: GpuGKRDimensionReducingRound1Batch<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingRound2Batched<T>,
    batch: GpuGKRDimensionReducingRound2Batch<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingRound3Batched<T>,
    batch: GpuGKRDimensionReducingRound3Batch<T>,
    acc_size: u32,
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
    const ROUND0_BATCHED: GpuDimensionReducingRound0BatchedSignature<Self>;
    const ROUND1_BATCHED: GpuDimensionReducingRound1BatchedSignature<Self>;
    const ROUND2_BATCHED: GpuDimensionReducingRound2BatchedSignature<Self>;
    const ROUND3_BATCHED: GpuDimensionReducingRound3BatchedSignature<Self>;
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
                [<ab_gkr_dim_reducing_round0_batched_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingRound0Batch<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_round1_batched_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingRound1Batch<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_round2_batched_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingRound2Batch<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_round3_batched_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingRound3Batch<$type>,
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
                const ROUND0_BATCHED: GpuDimensionReducingRound0BatchedSignature<Self> =
                    [<ab_gkr_dim_reducing_round0_batched_ $type:lower _kernel>];
                const ROUND1_BATCHED: GpuDimensionReducingRound1BatchedSignature<Self> =
                    [<ab_gkr_dim_reducing_round1_batched_ $type:lower _kernel>];
                const ROUND2_BATCHED: GpuDimensionReducingRound2BatchedSignature<Self> =
                    [<ab_gkr_dim_reducing_round2_batched_ $type:lower _kernel>];
                const ROUND3_BATCHED: GpuDimensionReducingRound3BatchedSignature<Self> =
                    [<ab_gkr_dim_reducing_round3_batched_ $type:lower _kernel>];
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

pub(super) fn launch_dim_reducing_round0_batched<E: GpuDimensionReducingKernelSet + Field>(
    batch: &GpuGKRDimensionReducingRound0Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound0BatchedArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound0BatchedFunction(E::ROUND0_BATCHED).launch(&config, &args)
}

pub(super) fn launch_dim_reducing_round1_batched<E: GpuDimensionReducingKernelSet + Field>(
    batch: &GpuGKRDimensionReducingRound1Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound1BatchedArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound1BatchedFunction(E::ROUND1_BATCHED).launch(&config, &args)
}

pub(super) fn launch_dim_reducing_round2_batched<E: GpuDimensionReducingKernelSet + Field>(
    batch: &GpuGKRDimensionReducingRound2Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound2BatchedArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound2BatchedFunction(E::ROUND2_BATCHED).launch(&config, &args)
}

pub(super) fn launch_dim_reducing_round3_batched<E: GpuDimensionReducingKernelSet + Field>(
    batch: &GpuGKRDimensionReducingRound3Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound3BatchedArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound3BatchedFunction(E::ROUND3_BATCHED).launch(&config, &args)
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

