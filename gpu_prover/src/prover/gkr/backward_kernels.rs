use std::cell::UnsafeCell;
use std::collections::{BTreeMap, VecDeque};
use std::mem::align_of;
use std::ptr::{null, null_mut};
use std::slice;
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

use super::backward::evaluate_constraint_prefactor;
use super::{
    alloc_host_and_schedule_copy, GpuBaseFieldPolySource,
    GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuGKRStorage, GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0LaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1HostLaunchDescriptors,
    GpuSumcheckRound1PreparedStorage, GpuSumcheckRound1ScheduledLaunchDescriptors,
    GpuSumcheckRound2HostLaunchDescriptors, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondHostLaunchDescriptors,
    GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    get_reduce_temp_storage_bytes, reduce, Reduce, ReduceOperation,
};
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E2, E4, E6};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

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
    LookupUnbalanced = 7,
    LookupWithCachedDensAndSetup = 8,
    EnforceConstraintsMaxQuadratic = 9,
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
#[repr(u32)]
pub(super) enum GpuGKRDimensionReducingBatchRecordMode {
    InlineDescriptors = 0,
    PointerDescriptors = 1,
}

impl GpuGKRDimensionReducingBatchRecordMode {
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
pub(super) struct GpuGKRMainLayerConstraintHostMetadata<E> {
    pub(super) quadratic_terms: Vec<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(super) linear_terms: Vec<GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(super) constant_offset: E,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GpuGKRMainLayerConstraintChallengeTerm {
    pub(super) coeff: BF,
    pub(super) power: u32,
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
pub(super) struct GpuGKRMainLayerConstraintMetadataDevicePointers<E> {
    pub(super) quadratic_terms: *const GpuGKRMainLayerConstraintQuadraticTerm<E>,
    pub(super) quadratic_terms_count: u32,
    pub(super) linear_terms: *const GpuGKRMainLayerConstraintLinearTerm<E>,
    pub(super) linear_terms_count: u32,
    pub(super) constant_offset: E,
}

impl<E: Field> Default for GpuGKRMainLayerConstraintMetadataDevicePointers<E> {
    fn default() -> Self {
        Self {
            quadratic_terms: null(),
            quadratic_terms_count: 0,
            linear_terms: null(),
            linear_terms_count: 0,
            constant_offset: E::ZERO,
        }
    }
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

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound0BatchRecord<E> {
    pub(super) kind: u32,
    pub(super) record_mode: u32,
    pub(super) metadata_inline: u32,
    pub(super) _reserved: u32,
    pub(super) base_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) base_outputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_outputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
    pub(super) quadratic_terms: GpuGKRMainLayerPayloadRange,
    pub(super) linear_terms: GpuGKRMainLayerPayloadRange,
    pub(super) auxiliary_challenge: E,
    pub(super) constant_offset: E,
}

impl<E: Field> Default for GpuGKRMainRound0BatchRecord<E> {
    fn default() -> Self {
        Self {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32(),
            metadata_inline: 0,
            _reserved: 0,
            base_inputs: GpuGKRMainLayerPayloadRange::default(),
            extension_inputs: GpuGKRMainLayerPayloadRange::default(),
            base_outputs: GpuGKRMainLayerPayloadRange::default(),
            extension_outputs: GpuGKRMainLayerPayloadRange::default(),
            batch_challenge_offset: 0,
            batch_challenge_count: 0,
            quadratic_terms: GpuGKRMainLayerPayloadRange::default(),
            linear_terms: GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E::ZERO,
            constant_offset: E::ZERO,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound1BatchRecord<E> {
    pub(super) kind: u32,
    pub(super) record_mode: u32,
    pub(super) metadata_inline: u32,
    pub(super) _reserved: u32,
    pub(super) base_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
    pub(super) quadratic_terms: GpuGKRMainLayerPayloadRange,
    pub(super) linear_terms: GpuGKRMainLayerPayloadRange,
    pub(super) auxiliary_challenge: E,
    pub(super) constant_offset: E,
}

impl<E: Field> Default for GpuGKRMainRound1BatchRecord<E> {
    fn default() -> Self {
        Self {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32(),
            metadata_inline: 0,
            _reserved: 0,
            base_inputs: GpuGKRMainLayerPayloadRange::default(),
            extension_inputs: GpuGKRMainLayerPayloadRange::default(),
            batch_challenge_offset: 0,
            batch_challenge_count: 0,
            quadratic_terms: GpuGKRMainLayerPayloadRange::default(),
            linear_terms: GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E::ZERO,
            constant_offset: E::ZERO,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound2BatchRecord<E> {
    pub(super) kind: u32,
    pub(super) record_mode: u32,
    pub(super) metadata_inline: u32,
    pub(super) _reserved: u32,
    pub(super) base_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
    pub(super) quadratic_terms: GpuGKRMainLayerPayloadRange,
    pub(super) linear_terms: GpuGKRMainLayerPayloadRange,
    pub(super) auxiliary_challenge: E,
    pub(super) constant_offset: E,
}

impl<E: Field> Default for GpuGKRMainRound2BatchRecord<E> {
    fn default() -> Self {
        Self {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32(),
            metadata_inline: 0,
            _reserved: 0,
            base_inputs: GpuGKRMainLayerPayloadRange::default(),
            extension_inputs: GpuGKRMainLayerPayloadRange::default(),
            batch_challenge_offset: 0,
            batch_challenge_count: 0,
            quadratic_terms: GpuGKRMainLayerPayloadRange::default(),
            linear_terms: GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E::ZERO,
            constant_offset: E::ZERO,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound3BatchRecord<E> {
    pub(super) kind: u32,
    pub(super) record_mode: u32,
    pub(super) metadata_inline: u32,
    pub(super) _reserved: u32,
    pub(super) base_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
    pub(super) quadratic_terms: GpuGKRMainLayerPayloadRange,
    pub(super) linear_terms: GpuGKRMainLayerPayloadRange,
    pub(super) auxiliary_challenge: E,
    pub(super) constant_offset: E,
}

impl<E: Field> Default for GpuGKRMainRound3BatchRecord<E> {
    fn default() -> Self {
        Self {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32(),
            metadata_inline: 0,
            _reserved: 0,
            base_inputs: GpuGKRMainLayerPayloadRange::default(),
            extension_inputs: GpuGKRMainLayerPayloadRange::default(),
            batch_challenge_offset: 0,
            batch_challenge_count: 0,
            quadratic_terms: GpuGKRMainLayerPayloadRange::default(),
            linear_terms: GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E::ZERO,
            constant_offset: E::ZERO,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound0Batch<E> {
    pub(super) record_count: u32,
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
    pub(super) records: [GpuGKRMainRound0BatchRecord<E>; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRMainRound0Batch<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            contributions: null_mut(),
            spill_payload: null(),
            records: [GpuGKRMainRound0BatchRecord::default(); GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound1Batch<E> {
    pub(super) record_count: u32,
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
    pub(super) explicit_form: bool,
    pub(super) _padding: [u8; 7],
    pub(super) records: [GpuGKRMainRound1BatchRecord<E>; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRMainRound1Batch<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            folding_challenge: null(),
            contributions: null_mut(),
            spill_payload: null(),
            explicit_form: false,
            _padding: [0; 7],
            records: [GpuGKRMainRound1BatchRecord::default(); GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound2Batch<E> {
    pub(super) record_count: u32,
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenges: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
    pub(super) explicit_form: bool,
    pub(super) _padding: [u8; 7],
    pub(super) records: [GpuGKRMainRound2BatchRecord<E>; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRMainRound2Batch<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            folding_challenges: null(),
            contributions: null_mut(),
            spill_payload: null(),
            explicit_form: false,
            _padding: [0; 7],
            records: [GpuGKRMainRound2BatchRecord::default(); GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRMainRound3Batch<E> {
    pub(super) record_count: u32,
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
    pub(super) explicit_form: bool,
    pub(super) _padding: [u8; 7],
    pub(super) records: [GpuGKRMainRound3BatchRecord<E>; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRMainRound3Batch<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            folding_challenge: null(),
            contributions: null_mut(),
            spill_payload: null(),
            explicit_form: false,
            _padding: [0; 7],
            records: [GpuGKRMainRound3BatchRecord::default(); GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
            inline_payload: [0; MAX_INLINE_ROUND_BATCH_BYTES],
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct GpuGKRMainLayerRound3HostDescriptors<E: Copy> {
    pub(super) step: usize,
    pub(super) descriptors: GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E>,
}

#[derive(Clone)]
pub(super) struct GpuGKRMainLayerRound3BatchTemplate<E> {
    pub(super) step: usize,
    pub(super) batch: GpuGKRMainRound3Batch<E>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRDimensionReducingRound0BatchRecord {
    pub(super) kind: u32,
    pub(super) record_mode: u32,
    pub(super) _reserved0: u32,
    pub(super) _reserved1: u32,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) extension_outputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
}

impl Default for GpuGKRDimensionReducingRound0BatchRecord {
    fn default() -> Self {
        Self {
            kind: GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
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
    pub(super) record_mode: u32,
    pub(super) _reserved0: u32,
    pub(super) _reserved1: u32,
    pub(super) extension_inputs: GpuGKRMainLayerPayloadRange,
    pub(super) batch_challenge_offset: u32,
    pub(super) batch_challenge_count: u32,
}

impl Default for GpuGKRDimensionReducingContinuationBatchRecord {
    fn default() -> Self {
        Self {
            kind: GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
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
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
    pub(super) records:
        [GpuGKRDimensionReducingRound0BatchRecord; GKR_BACKWARD_MAX_KERNELS_PER_LAYER],
    pub(super) inline_payload: [u8; MAX_INLINE_ROUND_BATCH_BYTES],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound0Batch<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            contributions: null_mut(),
            spill_payload: null(),
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
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
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
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            folding_challenge: null(),
            contributions: null_mut(),
            spill_payload: null(),
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
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
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
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            folding_challenge: null(),
            contributions: null_mut(),
            spill_payload: null(),
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
    pub(super) challenge_offset: u32,
    pub(super) challenge_count: u32,
    pub(super) _reserved: u32,
    pub(super) claim_point: *const E,
    pub(super) batch_challenge_base: *const E,
    pub(super) folding_challenge: *const E,
    pub(super) contributions: *mut E,
    pub(super) spill_payload: *const u8,
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
            challenge_offset: 0,
            challenge_count: 0,
            _reserved: 0,
            claim_point: null(),
            batch_challenge_base: null(),
            folding_challenge: null(),
            contributions: null_mut(),
            spill_payload: null(),
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

#[derive(Default)]
pub(super) struct SpillPayloadBuilder {
    pub(super) bytes: Vec<u8>,
}

impl SpillPayloadBuilder {
    pub(super) fn push_copy<T: Copy>(&mut self, values: &[T]) -> GpuGKRMainLayerPayloadRange {
        if values.is_empty() {
            return GpuGKRMainLayerPayloadRange::default();
        }
        let start = align_up(self.bytes.len(), align_of::<T>());
        if start > self.bytes.len() {
            self.bytes.resize(start, 0);
        }
        let bytes = as_bytes(values);
        self.bytes.extend_from_slice(bytes);
        GpuGKRMainLayerPayloadRange {
            offset: start as u32,
            count: values.len() as u32,
        }
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
    pub(super) static_spill_bytes: Vec<u8>,
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
    pub(crate) proof: SumcheckIntermediateProofValues<BF, E>,
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
    pub(super) callbacks: Arc<Callbacks<'static>>,
    pub(super) device: Arc<SharedChallengeDevice<E>>,
    pub(super) offset: usize,
    pub(super) len: usize,
}

impl<E> ScheduledChallengeBuffer<E> {
    pub(super) fn as_ptr(&self) -> *const E {
        self.device.as_ptr(self.offset)
    }

    #[cfg(test)]
    pub(super) fn device_slice(&self) -> &DeviceSlice<E> {
        // SAFETY: buffer views only expose ranges created from valid packed offsets.
        unsafe { self.device.slice(self.offset, self.len) }
    }
}

pub(super) struct HostScheduledChallengeBuffer<E> {
    pub(super) callbacks: Arc<Callbacks<'static>>,
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

pub(super) struct ScheduledMainLayerConstraintMetadataUpload<E> {
    pub(super) callbacks: Callbacks<'static>,
    pub(super) quadratic_terms: ScheduledUpload<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(super) linear_terms: ScheduledUpload<GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(super) constant_offset: ScheduledUpload<E>,
    pub(super) constant_offset_value: E,
}

pub(super) struct HostScheduledMainLayerConstraintMetadataUpload<E> {
    pub(super) callbacks: Callbacks<'static>,
    pub(super) quadratic_terms: HostScheduledUpload<GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(super) linear_terms: HostScheduledUpload<GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(super) constant_offset: HostScheduledUpload<E>,
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
    pub(super) internal_round_coefficients: Vec<[E; 4]>,
    pub(super) result: Option<GpuGKRDimensionReducingLayerExecution<E>>,
}

pub(super) struct ScheduledMainLayerExecutionState<E: FieldExtension<BF> + Field> {
    pub(super) seed: Seed,
    pub(super) claim: E,
    pub(super) eq_prefactor: E,
    pub(super) folding_challenges: Vec<E>,
    pub(super) internal_round_coefficients: Vec<[E; 4]>,
    pub(super) result: Option<GpuGKRMainLayerExecution<E>>,
}

pub(crate) struct GpuGKRDimensionReducingScheduledLayerExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    // Keeps layer-start callbacks alive until the stream consumes them.
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) static_spill_upload: Option<ScheduledUpload<u8>>,
    #[allow(dead_code)]
    pub(super) round_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    pub(super) shared_state: Arc<Mutex<ScheduledDimensionReducingLayerExecutionState<E>>>,
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
    pub(super) auxiliary_challenge: E,
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
    pub(super) kernel_plans: Vec<GpuGKRMainLayerKernelPlan<E>>,
    pub(super) round0_descriptors: Vec<GpuSumcheckRound0LaunchDescriptors<BF, E>>,
    pub(super) round0_batch_template: GpuGKRMainRound0Batch<E>,
    pub(super) round1_batch_template: GpuGKRMainRound1Batch<E>,
    pub(super) round2_batch_template: GpuGKRMainRound2Batch<E>,
    pub(super) round3_batch_templates: Vec<GpuGKRMainLayerRound3BatchTemplate<E>>,
    pub(super) static_spill_bytes: Vec<u8>,
    pub(super) round_scratch: GpuGKRMainLayerRoundScratch<E>,
}

impl<E: Copy + Field> GpuGKRMainLayerKernelPlan<E> {
    pub(crate) fn auxiliary_challenge_summary(&self) -> Option<E> {
        Some(self.auxiliary_challenge)
    }

    pub(crate) fn constraint_metadata_summary(&self) -> Option<(usize, usize, E)> {
        self.constraint_metadata_summary
    }
}

pub(crate) struct GpuGKRMainLayerBackwardState<E> {
    #[allow(dead_code)]
    pub(super) forward_tracing_ranges: Vec<Range>,
    pub(super) storage: GpuGKRStorage<BF, E>,
    pub(super) pending_layers: VecDeque<(usize, GKRLayerDescription)>,
    pub(super) trace_len: usize,
    pub(super) lookup_additive_challenge: E,
    pub(super) constraint_batch_challenge: E,
    pub(super) num_base_layer_memory_polys: usize,
    pub(super) num_base_layer_witness_polys: usize,
}

pub(crate) struct GpuGKRMainLayerExecution<E: FieldExtension<BF> + Field> {
    pub(crate) proof: SumcheckIntermediateProofValues<BF, E>,
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
    pub(super) static_spill_upload: Option<ScheduledUpload<u8>>,
    #[allow(dead_code)]
    pub(super) round_challenge_buffers: Vec<ScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    pub(super) shared_state: Arc<Mutex<ScheduledMainLayerExecutionState<E>>>,
}

pub(crate) struct ScheduledBackwardWorkflowState<E: FieldExtension<BF> + Field> {
    pub(super) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(super) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(super) current_claims: BTreeMap<GKRAddress, E>,
    pub(super) current_claim_point: Vec<E>,
    pub(super) current_batching_challenge: E,
    pub(super) lookup_additive_challenge: E,
    pub(super) constraint_batch_challenge: E,
    pub(super) seed: Seed,
    pub(super) proofs: BTreeMap<usize, SumcheckIntermediateProofValues<BF, E>>,
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
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) dimension_reducing_layers: Vec<GpuGKRDimensionReducingScheduledLayerExecution<B, E>>,
    #[allow(dead_code)]
    pub(super) main_layers: Vec<GpuGKRMainLayerScheduledLayerExecution<E>>,
    pub(super) shared_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
}

pub(crate) struct GpuGKRDimensionReducingHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) static_spill_upload: Option<HostScheduledUpload<u8>>,
    #[allow(dead_code)]
    pub(super) round_challenge_buffers: Vec<HostScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    pub(super) _phantom: std::marker::PhantomData<B>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    pub(super) shared_state: Arc<Mutex<ScheduledDimensionReducingLayerExecutionState<E>>>,
}

pub(crate) struct GpuGKRMainLayerHostKeepalive<E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) static_spill_upload: Option<HostScheduledUpload<u8>>,
    #[allow(dead_code)]
    pub(super) round_challenge_buffers: Vec<HostScheduledChallengeBuffer<E>>,
    #[allow(dead_code)]
    pub(super) reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    pub(super) final_readback: ScheduledDimensionReducingFinalReadback<E>,
    #[allow(dead_code)]
    pub(super) shared_state: Arc<Mutex<ScheduledMainLayerExecutionState<E>>>,
}

pub(crate) struct GpuGKRBackwardHostKeepalive<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    pub(super) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(super) dimension_reducing_layers: Vec<GpuGKRDimensionReducingHostKeepalive<B, E>>,
    #[allow(dead_code)]
    pub(super) main_layers: Vec<GpuGKRMainLayerHostKeepalive<E>>,
    #[allow(dead_code)]
    pub(super) shared_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
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

pub(super) fn challenge_buffer_into_host_keepalive<E>(
    buffer: ScheduledChallengeBuffer<E>,
) -> HostScheduledChallengeBuffer<E> {
    let ScheduledChallengeBuffer {
        callbacks,
        device: _,
        offset: _,
        len: _,
    } = buffer;
    HostScheduledChallengeBuffer {
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

pub(super) fn constraint_upload_into_host_keepalive<E>(
    upload: ScheduledMainLayerConstraintMetadataUpload<E>,
) -> HostScheduledMainLayerConstraintMetadataUpload<E> {
    let ScheduledMainLayerConstraintMetadataUpload {
        callbacks,
        quadratic_terms,
        linear_terms,
        constant_offset,
        constant_offset_value: _,
    } = upload;
    HostScheduledMainLayerConstraintMetadataUpload {
        callbacks,
        quadratic_terms: upload_into_host_keepalive(quadratic_terms),
        linear_terms: upload_into_host_keepalive(linear_terms),
        constant_offset: upload_into_host_keepalive(constant_offset),
    }
}

pub(super) fn schedule_immediate_field_upload<E: Field + Send + Sync + 'static>(
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

pub(super) fn schedule_packed_round_challenge_upload<E: Field + 'static>(
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

pub(super) fn schedule_static_spill_upload(
    context: &ProverContext,
    bytes: &[u8],
) -> CudaResult<Option<ScheduledUpload<u8>>> {
    if bytes.is_empty() {
        return Ok(None);
    }
    let payload = bytes.to_vec();
    let mut callbacks = Callbacks::new();
    let mut upload =
        schedule_callback_populated_upload(context, payload.len(), &mut callbacks, move |dst| {
            dst.copy_from_slice(&payload);
        })?;
    upload.callbacks = callbacks;
    Ok(Some(upload))
}

pub(super) fn schedule_deferred_main_layer_constraint_metadata_upload<
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
        constant_offset_value: E::ZERO,
    })
}

pub(super) fn schedule_main_layer_auxiliary_upload<E: Field + 'static>(
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

pub(super) fn schedule_main_layer_constraint_metadata_upload<
    E: Field + FieldExtension<BF> + 'static,
>(
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
                constant_offset_value: metadata.constant_offset,
            }))
        }
    }
}

pub(super) fn schedule_uploaded_main_layer_constraint_metadata<
    E: Field + FieldExtension<BF> + 'static,
>(
    metadata: &GpuGKRMainLayerConstraintHostMetadata<E>,
    context: &ProverContext,
) -> CudaResult<ScheduledMainLayerConstraintMetadataUpload<E>> {
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
    let constant_offset = schedule_callback_populated_upload(context, 1, &mut callbacks, {
        let constant = metadata.constant_offset;
        move |dst: &mut [E]| {
            dst[0] = constant;
        }
    })?;
    Ok(ScheduledMainLayerConstraintMetadataUpload {
        callbacks,
        quadratic_terms,
        linear_terms,
        constant_offset,
        constant_offset_value: metadata.constant_offset,
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
    const BUILD_EQ: GpuDimensionReducingBuildEqSignature<Self>;
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
                [<ab_gkr_dim_reducing_build_eq_ $type:lower _kernel>](
                    claim_point: *const $type,
                    challenge_offset: u32,
                    challenge_count: u32,
                    eq_values: *mut $type,
                    acc_size: u32,
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
                const BUILD_EQ: GpuDimensionReducingBuildEqSignature<Self> =
                    [<ab_gkr_dim_reducing_build_eq_ $type:lower _kernel>];
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

cuda_kernel_signature_arguments_and_function!(GpuGKRMainRound0Batched<T>, batch: GpuGKRMainRound0Batch<T>, acc_size: u32,);

cuda_kernel_signature_arguments_and_function!(GpuGKRMainRound1Batched<T>, batch: GpuGKRMainRound1Batch<T>, acc_size: u32,);

cuda_kernel_signature_arguments_and_function!(GpuGKRMainRound2Batched<T>, batch: GpuGKRMainRound2Batch<T>, acc_size: u32,);

cuda_kernel_signature_arguments_and_function!(GpuGKRMainRound3Batched<T>, batch: GpuGKRMainRound3Batch<T>, acc_size: u32,);

pub(super) trait GpuMainLayerKernelSet: GpuDimensionReducingKernelSet {
    const MAIN_ROUND0: GpuGKRMainRound0Signature<Self>;
    const MAIN_ROUND1: GpuGKRMainRound1Signature<Self>;
    const MAIN_ROUND2: GpuGKRMainRound2Signature<Self>;
    const MAIN_ROUND3: GpuGKRMainRound3Signature<Self>;
    const MAIN_ROUND0_BATCHED: GpuGKRMainRound0BatchedSignature<Self>;
    const MAIN_ROUND1_BATCHED: GpuGKRMainRound1BatchedSignature<Self>;
    const MAIN_ROUND2_BATCHED: GpuGKRMainRound2BatchedSignature<Self>;
    const MAIN_ROUND3_BATCHED: GpuGKRMainRound3BatchedSignature<Self>;
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
            cuda_kernel_declaration!(
                [<ab_gkr_main_round0_batched_ $type:lower _kernel>](
                    batch: GpuGKRMainRound0Batch<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_main_round1_batched_ $type:lower _kernel>](
                    batch: GpuGKRMainRound1Batch<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_main_round2_batched_ $type:lower _kernel>](
                    batch: GpuGKRMainRound2Batch<$type>,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_main_round3_batched_ $type:lower _kernel>](
                    batch: GpuGKRMainRound3Batch<$type>,
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
                const MAIN_ROUND0_BATCHED: GpuGKRMainRound0BatchedSignature<Self> =
                    [<ab_gkr_main_round0_batched_ $type:lower _kernel>];
                const MAIN_ROUND1_BATCHED: GpuGKRMainRound1BatchedSignature<Self> =
                    [<ab_gkr_main_round1_batched_ $type:lower _kernel>];
                const MAIN_ROUND2_BATCHED: GpuGKRMainRound2BatchedSignature<Self> =
                    [<ab_gkr_main_round2_batched_ $type:lower _kernel>];
                const MAIN_ROUND3_BATCHED: GpuGKRMainRound3BatchedSignature<Self> =
                    [<ab_gkr_main_round3_batched_ $type:lower _kernel>];
            }
        }
    };
}

gkr_main_layer_kernels!(E2);
gkr_main_layer_kernels!(E4);
gkr_main_layer_kernels!(E6);

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

pub(super) fn constraint_metadata_args<E>(
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

pub(super) fn constraint_metadata_device_pointers<E: Field>(
    metadata: Option<&ScheduledMainLayerConstraintMetadataUpload<E>>,
) -> GpuGKRMainLayerConstraintMetadataDevicePointers<E> {
    if let Some(metadata) = metadata {
        GpuGKRMainLayerConstraintMetadataDevicePointers {
            quadratic_terms: metadata.quadratic_terms.device.as_ptr(),
            quadratic_terms_count: metadata.quadratic_terms.device.len() as u32,
            linear_terms: metadata.linear_terms.device.as_ptr(),
            linear_terms_count: metadata.linear_terms.device.len() as u32,
            constant_offset: metadata.constant_offset_value,
        }
    } else {
        GpuGKRMainLayerConstraintMetadataDevicePointers::default()
    }
}

pub(super) fn launch_main_round0<E: GpuMainLayerKernelSet + Field>(
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

pub(super) fn launch_main_round1<E: GpuMainLayerKernelSet + Field>(
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

pub(super) fn launch_main_round2<E: GpuMainLayerKernelSet + Field>(
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

pub(super) fn launch_main_round3<E: GpuMainLayerKernelSet + Field>(
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

pub(super) fn launch_main_round0_batched<E: GpuMainLayerKernelSet + Field>(
    batch: &GpuGKRMainRound0Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound0BatchedArguments::new(*batch, acc_size as u32);
    GpuGKRMainRound0BatchedFunction(E::MAIN_ROUND0_BATCHED).launch(&config, &args)
}

pub(super) fn launch_main_round1_batched<E: GpuMainLayerKernelSet + Field>(
    batch: &GpuGKRMainRound1Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound1BatchedArguments::new(*batch, acc_size as u32);
    GpuGKRMainRound1BatchedFunction(E::MAIN_ROUND1_BATCHED).launch(&config, &args)
}

pub(super) fn launch_main_round2_batched<E: GpuMainLayerKernelSet + Field>(
    batch: &GpuGKRMainRound2Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound2BatchedArguments::new(*batch, acc_size as u32);
    GpuGKRMainRound2BatchedFunction(E::MAIN_ROUND2_BATCHED).launch(&config, &args)
}

pub(super) fn launch_main_round3_batched<E: GpuMainLayerKernelSet + Field>(
    batch: &GpuGKRMainRound3Batch<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKRMainRound3BatchedArguments::new(*batch, acc_size as u32);
    GpuGKRMainRound3BatchedFunction(E::MAIN_ROUND3_BATCHED).launch(&config, &args)
}
