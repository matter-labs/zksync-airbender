use std::collections::BTreeMap;
use std::ops::DerefMut;
use std::ptr::null;

use cs::definitions::{
    gkr::{RamWordRepresentation, DECODER_LOOKUP_FORMAL_SET_INDEX},
    GKRAddress, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, GKRCircuitArtifact,
    GKRLayerDescription, NoFieldGKRCacheRelation, NoFieldGKRRelation, OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::GKRExternalChallenges;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::forward::schedule_ext_poly_readback;
use super::setup::{GpuGKRForwardSetup, GpuGKRSetupTransfer};
use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{
    add_into_y, mul_into_y, set_by_ref, set_by_val, sub_into_x, Add, BinaryOp, Mul, SetByRef,
    SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceVectorChunk;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

pub(crate) struct GpuGKRForwardOutput<B, E> {
    pub(super) tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub(crate) initial_layer_for_sumcheck: usize,
    pub(crate) dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

pub(crate) struct GpuGKRTranscriptHandoff<E> {
    pub(super) _tracing_ranges: Vec<Range>,
    pub(super) explicit_evaluations: BTreeMap<OutputType, [HostAllocation<[E]>; 2]>,
}

impl<E: Copy> GpuGKRTranscriptHandoff<E> {
    pub(crate) fn explicit_evaluation_accessors(
        &self,
    ) -> BTreeMap<OutputType, [UnsafeAccessor<[E]>; 2]> {
        self.explicit_evaluations
            .iter()
            .map(|(output_type, evals)| {
                (
                    *output_type,
                    [evals[0].get_accessor(), evals[1].get_accessor()],
                )
            })
            .collect()
    }

    pub(crate) fn final_explicit_evaluations(&self) -> BTreeMap<OutputType, [Vec<E>; 2]> {
        self.explicit_evaluations
            .iter()
            .map(|(output_type, evals)| {
                let copied =
                    std::array::from_fn(|idx| unsafe { evals[idx].get_accessor().get() }.to_vec());
                (*output_type, copied)
            })
            .collect()
    }

    pub(crate) fn flattened_transcript_evaluations(&self) -> Vec<E> {
        let capacity = self
            .explicit_evaluations
            .values()
            .map(|evals| {
                evals
                    .iter()
                    .map(|poly| unsafe { poly.get_accessor().get() }.len())
                    .sum::<usize>()
            })
            .sum();
        let mut flattened = Vec::with_capacity(capacity);
        for evals in self.explicit_evaluations.values() {
            for poly in evals.iter() {
                flattened.extend_from_slice(unsafe { poly.get_accessor().get() });
            }
        }

        flattened
    }
}

impl<B, E: Copy> GpuGKRForwardOutput<B, E> {
    pub(crate) fn schedule_transcript_handoff(
        &self,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRTranscriptHandoff<E>> {
        let mut tracing_ranges = Vec::new();
        let reduced_outputs = self
            .dimension_reducing_inputs
            .get(&self.initial_layer_for_sumcheck)
            .expect("reduced outputs for initial sumcheck layer must exist");
        let mut explicit_evaluations = BTreeMap::new();
        for (output_type, reduced_io) in reduced_outputs.iter() {
            let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
                .output
                .clone()
                .try_into()
                .expect("transcript handoff expects exactly two reduced outputs per type");
            let first = schedule_ext_poly_readback(&self.storage, first_addr, context)?;
            let second = schedule_ext_poly_readback(&self.storage, second_addr, context)?;
            explicit_evaluations.insert(*output_type, [first, second]);
        }

        Ok(GpuGKRTranscriptHandoff {
            _tracing_ranges: tracing_ranges,
            explicit_evaluations,
        })
    }
}

impl<B, E> GpuGKRForwardOutput<B, E> {
    pub(crate) fn into_dimension_reducing_backward_state(
        self,
    ) -> GpuGKRDimensionReducingBackwardState<B, E> {
        GpuGKRDimensionReducingBackwardState::new(
            self.tracing_ranges,
            self.storage,
            self.initial_layer_for_sumcheck,
            self.dimension_reducing_inputs,
        )
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct ForwardLookupUsage {
    pub(super) last_generic_mapping_layer: Option<usize>,
    pub(super) last_range_mapping_layer: Option<usize>,
    pub(super) last_timestamp_mapping_layer: Option<usize>,
    pub(super) last_generic_lookup_layer: Option<usize>,
}

pub(super) const GKR_FORWARD_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(super) const GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK: u32 = 8;
pub(super) const GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK: u32 =
    1 << GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
pub(super) const GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS: usize =
    GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK as usize;
pub(super) const MAX_CACHE_RELATIONS_PER_LAYER: usize = 20;
pub(super) const MEMORY_TUPLE_LINEAR_TERMS: usize = 8;
pub(super) const MEMORY_TUPLE_ADDRESS_LOW_TERM: usize = 0;
pub(super) const MEMORY_TUPLE_ADDRESS_HIGH_TERM: usize = 1;
pub(super) const MEMORY_TUPLE_TIMESTAMP_LOW_TERM: usize = 2;
pub(super) const MEMORY_TUPLE_TIMESTAMP_HIGH_TERM: usize = 3;
pub(super) const MEMORY_TUPLE_VALUE_LOW_TERM: usize = 4;
pub(super) const MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM: usize = 5;
pub(super) const MEMORY_TUPLE_VALUE_HIGH_TERM: usize = 6;
pub(super) const MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM: usize = 7;

pub(super) struct FlatForwardPlan<E> {
    pub(super) desc: Box<GpuFlatForwardStaticDesc<E>>,
    pub(super) computed_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
    pub(super) aliased_base_outputs: Vec<(GKRAddress, GpuBaseFieldPoly<BF>)>,
    pub(super) aliased_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum GpuGKRForwardCacheKind {
    #[default]
    Empty = 0,
    SingleColumnLookup = 1,
    VectorizedLookup = 2,
    VectorizedLookupSetup = 3,
    MemoryTuple = 4,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum GpuGKRForwardCacheAddressSpaceKind {
    #[default]
    Empty = 0,
    Constant = 1,
    Is = 2,
    Not = 3,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRForwardCacheDescriptor<E> {
    pub(super) kind: GpuGKRForwardCacheKind,
    pub(super) address_space_kind: GpuGKRForwardCacheAddressSpaceKind,
    pub(super) mapping: *const u32,
    pub(super) setup_values: *const BF,
    pub(super) setup_source_kind: GpuBaseFieldSourceKind,
    pub(super) generic_lookup: *const E,
    pub(super) decoder_mask: *const BF,
    pub(super) decoder_fill_value: *const E,
    pub(super) base_output: *mut BF,
    pub(super) ext_output: *mut E,
    pub(super) generic_lookup_len: u32,
    pub(super) address_space_ptr: *const BF,
    pub(super) address_space_constant: BF,
    pub(super) constant_term: E,
    pub(super) linear_inputs: [*const BF; MEMORY_TUPLE_LINEAR_TERMS],
    pub(super) linear_challenges: [E; MEMORY_TUPLE_LINEAR_TERMS],
}

impl<E: Field> Default for GpuGKRForwardCacheDescriptor<E> {
    fn default() -> Self {
        Self {
            kind: GpuGKRForwardCacheKind::Empty,
            address_space_kind: GpuGKRForwardCacheAddressSpaceKind::Empty,
            mapping: null(),
            setup_values: null(),
            setup_source_kind: GpuBaseFieldSourceKind::Empty,
            generic_lookup: null(),
            decoder_mask: null(),
            decoder_fill_value: null(),
            base_output: null::<BF>().cast_mut(),
            ext_output: null::<E>().cast_mut(),
            generic_lookup_len: 0,
            address_space_ptr: null(),
            address_space_constant: BF::ZERO,
            constant_term: E::ZERO,
            linear_inputs: [null(); MEMORY_TUPLE_LINEAR_TERMS],
            linear_challenges: [E::ZERO; MEMORY_TUPLE_LINEAR_TERMS],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRForwardCacheBatch<E> {
    pub(super) count: u32,
    pub(super) descriptors: [GpuGKRForwardCacheDescriptor<E>; MAX_CACHE_RELATIONS_PER_LAYER],
}

impl<E: Field> Default for GpuGKRForwardCacheBatch<E> {
    fn default() -> Self {
        Self {
            count: 0,
            descriptors: [GpuGKRForwardCacheDescriptor::default(); MAX_CACHE_RELATIONS_PER_LAYER],
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRForwardCache<T>,
    batch: GpuGKRForwardCacheBatch<T>,
    trace_len: u32,
);

pub(crate) trait GpuGKRForwardCacheKernelSet: Copy + Sized {
    const FORWARD_CACHE: GpuGKRForwardCacheSignature<Self>;
}

macro_rules! gkr_forward_cache_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_forward_cache_ $type:lower _kernel>](
                    batch: GpuGKRForwardCacheBatch<$type>,
                    trace_len: u32,
                )
            );

            impl GpuGKRForwardCacheKernelSet for $type {
                const FORWARD_CACHE: GpuGKRForwardCacheSignature<Self> =
                    [<ab_gkr_forward_cache_ $type:lower _kernel>];
            }
        }
    };
}

gkr_forward_cache_kernels!(E4);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRVirtualBaseAccum<T>,
    source_kind: GpuBaseFieldSourceKind,
    scalar: T,
    dst: *mut T,
    count: u32,
);

pub(crate) trait GpuGKRVirtualBaseAccumKernelSet: Copy + Sized {
    const VIRTUAL_BASE_ACCUM: GpuGKRVirtualBaseAccumSignature<Self>;
}

macro_rules! gkr_virtual_base_accum_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_virtual_base_accum_ $type:lower _kernel>](
                    source_kind: GpuBaseFieldSourceKind,
                    scalar: $type,
                    dst: *mut $type,
                    count: u32,
                )
            );

            impl GpuGKRVirtualBaseAccumKernelSet for $type {
                const VIRTUAL_BASE_ACCUM: GpuGKRVirtualBaseAccumSignature<Self> =
                    [<ab_gkr_virtual_base_accum_ $type:lower _kernel>];
            }
        }
    };
}

gkr_virtual_base_accum_kernels!(E4);

// Per-slot tower batch: one kernel launch per slot, covering up to
// `GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS` consecutive halving rounds.
// Slots are PairwiseProduct (1 buffer) or LookupPair (2 buffers, num/den).
#[repr(C)]
pub(super) struct GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    pub(super) input: *const E,
    pub(super) round_outputs: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(super) input_len: u32,
    pub(super) round_count: u32,
}

impl<E> Copy for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    fn default() -> Self {
        Self {
            input: null(),
            round_outputs: [null::<E>().cast_mut(); GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
            input_len: 0,
            round_count: 0,
        }
    }
}

// SAFETY: raw pointers are kept alive by the GpuGKRStorage allocations that
// back them; the scheduler ensures kernel launches happen stream-ordered after
// the pointers are written and before they are freed.
unsafe impl<E> Send for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {}
unsafe impl<E> Sync for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {}

#[repr(C)]
pub(super) struct GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    pub(super) input_num: *const E,
    pub(super) input_den: *const E,
    pub(super) round_outputs_num: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(super) round_outputs_den: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(super) input_len: u32,
    pub(super) round_count: u32,
}

impl<E> Copy for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    fn default() -> Self {
        Self {
            input_num: null(),
            input_den: null(),
            round_outputs_num: [null::<E>().cast_mut(); GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
            round_outputs_den: [null::<E>().cast_mut(); GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
            input_len: 0,
            round_count: 0,
        }
    }
}

unsafe impl<E> Send for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {}
unsafe impl<E> Sync for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRDimensionReducingForwardTowerPairwise<T>,
    batch: GpuGKRDimensionReducingForwardTowerPairwiseBatch<T>,
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRDimensionReducingForwardTowerLookup<T>,
    batch: GpuGKRDimensionReducingForwardTowerLookupBatch<T>,
);

pub(crate) trait GpuGKRDimensionReducingForwardTowerKernelSet: Copy + Sized {
    const DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE:
        GpuGKRDimensionReducingForwardTowerPairwiseSignature<Self>;
    const DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP:
        GpuGKRDimensionReducingForwardTowerLookupSignature<Self>;
}

macro_rules! gkr_dim_reducing_forward_tower_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_forward_tower_pairwise_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingForwardTowerPairwiseBatch<$type>,
                )
            );

            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_forward_tower_lookup_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingForwardTowerLookupBatch<$type>,
                )
            );

            impl GpuGKRDimensionReducingForwardTowerKernelSet for $type {
                const DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE:
                    GpuGKRDimensionReducingForwardTowerPairwiseSignature<Self> =
                    [<ab_gkr_dim_reducing_forward_tower_pairwise_ $type:lower _kernel>];
                const DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP:
                    GpuGKRDimensionReducingForwardTowerLookupSignature<Self> =
                    [<ab_gkr_dim_reducing_forward_tower_lookup_ $type:lower _kernel>];
            }
        }
    };
}

gkr_dim_reducing_forward_tower_kernels!(E4);

pub(super) fn gkr_forward_cache_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(super) fn launch_forward_cache<E: GpuGKRForwardCacheKernelSet>(
    batch: GpuGKRForwardCacheBatch<E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let config = gkr_forward_cache_launch_config(trace_len as u32, context);
    let args = GpuGKRForwardCacheArguments::new(batch, trace_len as u32);
    GpuGKRForwardCacheFunction(E::FORWARD_CACHE).launch(&config, &args)
}

pub(super) fn launch_virtual_base_accum<E: GpuGKRVirtualBaseAccumKernelSet>(
    source_kind: GpuBaseFieldSourceKind,
    scalar: E,
    dst: *mut E,
    count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(count <= u32::MAX as usize);
    let config = gkr_forward_cache_launch_config(count as u32, context);
    let args = GpuGKRVirtualBaseAccumArguments::new(source_kind, scalar, dst, count as u32);
    GpuGKRVirtualBaseAccumFunction(E::VIRTUAL_BASE_ACCUM).launch(&config, &args)
}

pub(super) fn launch_dimension_reducing_forward_tower_pairwise<
    E: GpuGKRDimensionReducingForwardTowerKernelSet,
>(
    batch: &GpuGKRDimensionReducingForwardTowerPairwiseBatch<E>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_size = GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK;
    let input_len = batch.input_len;
    assert!(input_len > 0, "tower pairwise batch has empty input");
    let grid_dim = input_len.div_ceil(block_size).max(1);
    let dynamic_smem_bytes = block_size as usize * std::mem::size_of::<E>();
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(block_size)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(stream)
        .build();
    let args = GpuGKRDimensionReducingForwardTowerPairwiseArguments::new(*batch);
    GpuGKRDimensionReducingForwardTowerPairwiseFunction(
        E::DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE,
    )
    .launch(&config, &args)
}

pub(super) fn launch_dimension_reducing_forward_tower_lookup<
    E: GpuGKRDimensionReducingForwardTowerKernelSet,
>(
    batch: &GpuGKRDimensionReducingForwardTowerLookupBatch<E>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_size = GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK;
    let input_len = batch.input_len;
    assert!(input_len > 0, "tower lookup batch has empty input");
    let grid_dim = input_len.div_ceil(block_size).max(1);
    let dynamic_smem_bytes = 2 * block_size as usize * std::mem::size_of::<E>();
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(block_size)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(stream)
        .build();
    let args = GpuGKRDimensionReducingForwardTowerLookupArguments::new(*batch);
    GpuGKRDimensionReducingForwardTowerLookupFunction(E::DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP)
        .launch(&config, &args)
}

pub(super) fn gkr_forward_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_FORWARD_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

// ---------------------------------------------------------------------------
// Flat forward kernel (Phase 1 skeleton — not yet wired in)
// ---------------------------------------------------------------------------
//
// Mirrors `flat_forward_static_desc<E>` in native/prover/gkr/flat_forward.cuh.
// The Rust lowering that populates these descriptors will be added in Phase 2
// (new file `forward_flat.rs`); for now the types just need to exist so the
// kernel binding and launch path compile.

pub(super) const FLAT_FWD_MAX_SOURCES: usize = 256;
pub(super) const FLAT_FWD_MAX_PER_CATEGORY: usize = 64;

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdProductEntry<E> {
    pub(super) src_a: u16,
    pub(super) src_b: u16,
    pub(super) dst: *mut E,
}

impl<E> Copy for GpuFlatFwdProductEntry<E> {}

impl<E> Clone for GpuFlatFwdProductEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdMaskEntry<E> {
    pub(super) src_mask: u16,
    pub(super) src_input: u16,
    pub(super) dst: *mut E,
}

impl<E> Copy for GpuFlatFwdMaskEntry<E> {}

impl<E> Clone for GpuFlatFwdMaskEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdLookup4Entry<E> {
    pub(super) src_a: u16,
    pub(super) src_b: u16,
    pub(super) src_c: u16,
    pub(super) src_d: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdLookup4Entry<E> {}

impl<E> Clone for GpuFlatFwdLookup4Entry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdBfPairEntry<E> {
    pub(super) src_b: u16,
    pub(super) src_d: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdBfPairEntry<E> {}

impl<E> Clone for GpuFlatFwdBfPairEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdE4PairEntry<E> {
    pub(super) src_b: u16,
    pub(super) src_d: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdE4PairEntry<E> {}

impl<E> Clone for GpuFlatFwdE4PairEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdCachedDensEntry<E> {
    pub(super) src_a: u16,
    pub(super) src_b: u16,
    pub(super) src_c: u16,
    pub(super) src_d: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdCachedDensEntry<E> {}

impl<E> Clone for GpuFlatFwdCachedDensEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdBfMinusMultEntry<E> {
    pub(super) src_b: u16,
    pub(super) src_c: u16,
    pub(super) src_d: u16,
    pub(super) _pad: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdBfMinusMultEntry<E> {}

impl<E> Clone for GpuFlatFwdBfMinusMultEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdE4MinusMultEntry<E> {
    pub(super) src_b: u16,
    pub(super) src_c: u16,
    pub(super) src_d: u16,
    pub(super) _pad: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdE4MinusMultEntry<E> {}

impl<E> Clone for GpuFlatFwdE4MinusMultEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdBfUnbalancedEntry<E> {
    pub(super) src_a: u16,
    pub(super) src_b: u16,
    pub(super) src_d: u16,
    pub(super) _pad: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdBfUnbalancedEntry<E> {}

impl<E> Clone for GpuFlatFwdBfUnbalancedEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuFlatFwdE4UnbalancedEntry<E> {
    pub(super) src_a: u16,
    pub(super) src_b: u16,
    pub(super) src_d: u16,
    pub(super) _pad: u16,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuFlatFwdE4UnbalancedEntry<E> {}

impl<E> Clone for GpuFlatFwdE4UnbalancedEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Static description for the flat forward kernel.
///
/// Mirrors `flat_forward_static_desc<E>` in native/prover/gkr/flat_forward.cuh.
/// Passed as `__grid_constant__`. Sources are encoded as raw pointers: real
/// device pointers for memory-backed sources, low-bit-tagged null pointers
/// for virtual base sources (range checks / inits+teardowns).
#[repr(C)]
pub(super) struct GpuFlatForwardStaticDesc<E> {
    pub(super) sources: [*const u8; FLAT_FWD_MAX_SOURCES],
    pub(super) num_sources: u32,

    pub(super) gamma: *const E,

    pub(super) products: [GpuFlatFwdProductEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_products: u32,

    pub(super) masks: [GpuFlatFwdMaskEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_masks: u32,

    pub(super) lookup4s: [GpuFlatFwdLookup4Entry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_lookup4s: u32,

    pub(super) bf_pairs: [GpuFlatFwdBfPairEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_bf_pairs: u32,

    pub(super) e4_pairs: [GpuFlatFwdE4PairEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_e4_pairs: u32,

    pub(super) cached_denses: [GpuFlatFwdCachedDensEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_cached_denses: u32,

    pub(super) bf_minus_mults: [GpuFlatFwdBfMinusMultEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_bf_minus_mults: u32,

    pub(super) e4_minus_mults: [GpuFlatFwdE4MinusMultEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_e4_minus_mults: u32,

    pub(super) bf_unbalanceds: [GpuFlatFwdBfUnbalancedEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_bf_unbalanceds: u32,

    pub(super) e4_unbalanceds: [GpuFlatFwdE4UnbalancedEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(super) num_e4_unbalanceds: u32,
}

// The descriptor contains only POD data (pointers, indices, counts). Raw
// pointers aren't auto-Send/Sync; safety is the caller's responsibility — the
// Rust lowering (Phase 2) ensures source pointers outlive the kernel launch.
unsafe impl<E> Send for GpuFlatForwardStaticDesc<E> {}
unsafe impl<E> Sync for GpuFlatForwardStaticDesc<E> {}

impl<E: Copy> Copy for GpuFlatForwardStaticDesc<E> {}

impl<E: Copy> Clone for GpuFlatForwardStaticDesc<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuFlatForwardStaticDesc<E> {
    fn default() -> Self {
        Self {
            sources: [null::<u8>(); FLAT_FWD_MAX_SOURCES],
            num_sources: 0,
            gamma: null(),
            products: std::array::from_fn(|_| GpuFlatFwdProductEntry {
                src_a: 0,
                src_b: 0,
                dst: null::<E>().cast_mut(),
            }),
            num_products: 0,
            masks: std::array::from_fn(|_| GpuFlatFwdMaskEntry {
                src_mask: 0,
                src_input: 0,
                dst: null::<E>().cast_mut(),
            }),
            num_masks: 0,
            lookup4s: std::array::from_fn(|_| GpuFlatFwdLookup4Entry {
                src_a: 0,
                src_b: 0,
                src_c: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_lookup4s: 0,
            bf_pairs: std::array::from_fn(|_| GpuFlatFwdBfPairEntry {
                src_b: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_bf_pairs: 0,
            e4_pairs: std::array::from_fn(|_| GpuFlatFwdE4PairEntry {
                src_b: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_e4_pairs: 0,
            cached_denses: std::array::from_fn(|_| GpuFlatFwdCachedDensEntry {
                src_a: 0,
                src_b: 0,
                src_c: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_cached_denses: 0,
            bf_minus_mults: std::array::from_fn(|_| GpuFlatFwdBfMinusMultEntry {
                src_b: 0,
                src_c: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_bf_minus_mults: 0,
            e4_minus_mults: std::array::from_fn(|_| GpuFlatFwdE4MinusMultEntry {
                src_b: 0,
                src_c: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_e4_minus_mults: 0,
            bf_unbalanceds: std::array::from_fn(|_| GpuFlatFwdBfUnbalancedEntry {
                src_a: 0,
                src_b: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_bf_unbalanceds: 0,
            e4_unbalanceds: std::array::from_fn(|_| GpuFlatFwdE4UnbalancedEntry {
                src_a: 0,
                src_b: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_e4_unbalanceds: 0,
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRFlatForwardLayer<T>,
    desc: GpuFlatForwardStaticDesc<T>,
    count: u32,
);

pub(crate) trait GpuGKRFlatForwardKernelSet: Copy + Sized {
    const FLAT_FORWARD_LAYER: GpuGKRFlatForwardLayerSignature<Self>;
}

macro_rules! gkr_flat_forward_layer_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_flat_forward_layer_ $type:lower _kernel>](
                    desc: GpuFlatForwardStaticDesc<$type>,
                    count: u32,
                )
            );

            impl GpuGKRFlatForwardKernelSet for $type {
                const FLAT_FORWARD_LAYER: GpuGKRFlatForwardLayerSignature<Self> =
                    [<ab_gkr_flat_forward_layer_ $type:lower _kernel>];
            }
        }
    };
}

gkr_flat_forward_layer_kernels!(E4);

pub(super) fn launch_flat_forward_layer<E: GpuGKRFlatForwardKernelSet>(
    desc: &GpuFlatForwardStaticDesc<E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let count = trace_len as u32;
    let config = gkr_forward_launch_config(count, context);
    let args = GpuGKRFlatForwardLayerArguments::new(*desc, count);
    GpuGKRFlatForwardLayerFunction(E::FLAT_FORWARD_LAYER).launch(&config, &args)
}

/// True iff the flat descriptor has any gate entry. Used by the scheduler to
/// skip the flat kernel launch when no gates were migrated.
pub(super) fn flat_desc_has_work<E>(desc: &GpuFlatForwardStaticDesc<E>) -> bool {
    desc.num_products
        | desc.num_masks
        | desc.num_lookup4s
        | desc.num_bf_pairs
        | desc.num_e4_pairs
        | desc.num_cached_denses
        | desc.num_bf_minus_mults
        | desc.num_e4_minus_mults
        | desc.num_bf_unbalanceds
        | desc.num_e4_unbalanceds
        != 0
}
