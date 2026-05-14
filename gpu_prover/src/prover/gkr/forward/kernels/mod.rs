use std::ffi::c_void;
use std::ptr::{null, null_mut};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;

use super::super::{GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly};
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::upstream::{Field, GKRAddress};

#[derive(Clone, Copy, Default)]
pub(crate) struct ForwardLookupUsage {
    pub(crate) last_generic_mapping_layer: Option<usize>,
    pub(crate) last_range_mapping_layer: Option<usize>,
    pub(crate) last_timestamp_mapping_layer: Option<usize>,
    pub(crate) last_generic_lookup_layer: Option<usize>,
}

pub(crate) const GKR_FORWARD_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK: u32 = 8;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK: u32 =
    1 << GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS: usize =
    GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK as usize;
pub(crate) const MAX_CACHE_RELATIONS_PER_LAYER: usize = 20;
pub(crate) const MEMORY_TUPLE_LINEAR_TERMS: usize = 8;
pub(crate) const MEMORY_TUPLE_ADDRESS_LOW_TERM: usize = 0;
pub(crate) const MEMORY_TUPLE_ADDRESS_HIGH_TERM: usize = 1;
pub(crate) const MEMORY_TUPLE_TIMESTAMP_LOW_TERM: usize = 2;
pub(crate) const MEMORY_TUPLE_TIMESTAMP_HIGH_TERM: usize = 3;
pub(crate) const MEMORY_TUPLE_VALUE_LOW_TERM: usize = 4;
pub(crate) const MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM: usize = 5;
pub(crate) const MEMORY_TUPLE_VALUE_HIGH_TERM: usize = 6;
pub(crate) const MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM: usize = 7;

pub(crate) struct FlatForwardPlan<E> {
    pub(crate) descs: Vec<Box<GpuFlatForwardStaticDesc<E>>>,
    pub(crate) computed_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
    pub(crate) aliased_base_outputs: Vec<(GKRAddress, GpuBaseFieldPoly<BF>)>,
    pub(crate) aliased_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum GpuGKRForwardCacheKind {
    #[default]
    Empty = 0,
    SingleColumnLookup = 1,
    VectorizedLookup = 2,
    VectorizedLookupSetup = 3,
    MemoryTuple = 4,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum GpuGKRForwardCacheAddressSpaceKind {
    #[default]
    Empty = 0,
    Constant = 1,
    Is = 2,
    Not = 3,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRForwardCacheDescriptor<E> {
    pub(crate) kind: GpuGKRForwardCacheKind,
    pub(crate) address_space_kind: GpuGKRForwardCacheAddressSpaceKind,
    pub(crate) mapping: *const u32,
    pub(crate) setup_values: *const BF,
    pub(crate) setup_source_kind: GpuBaseFieldSourceKind,
    pub(crate) generic_lookup: *const E,
    pub(crate) decoder_mask: *const BF,
    pub(crate) decoder_fill_value: *const E,
    pub(crate) base_output: *mut BF,
    pub(crate) ext_output: *mut E,
    pub(crate) generic_lookup_len: u32,
    pub(crate) address_space_ptr: *const BF,
    pub(crate) address_space_constant: BF,
    pub(crate) constant_term: E,
    pub(crate) linear_inputs: [*const BF; MEMORY_TUPLE_LINEAR_TERMS],
    pub(crate) linear_challenges: [E; MEMORY_TUPLE_LINEAR_TERMS],
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
pub(crate) struct GpuGKRForwardCacheBatch<E> {
    pub(crate) count: u32,
    pub(crate) descriptors: [GpuGKRForwardCacheDescriptor<E>; MAX_CACHE_RELATIONS_PER_LAYER],
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
    pub(crate) GpuGKRForwardCache<T>,
    batch: GpuGKRForwardCacheBatch<T>,
    trace_len: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_forward_cache_e4_kernel(
        batch: GpuGKRForwardCacheBatch<E4>,
        trace_len: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRVirtualBaseAccum<T>,
    source_kind: GpuBaseFieldSourceKind,
    scalar: T,
    dst: *mut T,
    count: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_virtual_base_accum_e4_kernel(
        source_kind: GpuBaseFieldSourceKind,
        scalar: E4,
        dst: *mut E4,
        count: u32,
    )
);

// Per-slot tower batch: one kernel launch per slot, covering up to
// `GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS` consecutive halving rounds.
// Slots are PairwiseProduct (1 buffer) or LookupPair (2 buffers, num/den).
#[repr(C)]
pub(crate) struct GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    pub(crate) input: *const E,
    pub(crate) round_outputs: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(crate) input_len: u32,
    pub(crate) round_count: u32,
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
pub(crate) struct GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    pub(crate) input_num: *const E,
    pub(crate) input_den: *const E,
    pub(crate) round_outputs_num: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(crate) round_outputs_den: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(crate) input_len: u32,
    pub(crate) round_count: u32,
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
    pub(crate) GpuGKRDimensionReducingForwardTowerPairwise<T>,
    batch: GpuGKRDimensionReducingForwardTowerPairwiseBatch<T>,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRDimensionReducingForwardTowerLookup<T>,
    batch: GpuGKRDimensionReducingForwardTowerLookupBatch<T>,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_forward_tower_pairwise_e4_kernel(
        batch: GpuGKRDimensionReducingForwardTowerPairwiseBatch<E4>,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_forward_tower_lookup_e4_kernel(
        batch: GpuGKRDimensionReducingForwardTowerLookupBatch<E4>,
    )
);

extern "C" {
    static ab_gkr_lookup_gamma_consts: [E4; 3];
}

fn get_lookup_gamma_consts_device_ptr() -> *mut E4 {
    use std::sync::OnceLock;

    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: ab_gkr_lookup_gamma_consts is a valid __constant__ e4[3]
        // symbol defined in native/prover/gkr/flat_forward_layer.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_lookup_gamma_consts as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_lookup_gamma_consts");
        p as usize
    });
    ptr as *mut E4
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRLookupGammaConstsPrelude,
    gamma: *const E4,
    staging: *mut E4,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_lookup_gamma_consts_prelude(gamma: *const E4, staging: *mut E4)
);

pub(crate) fn schedule_lookup_gamma_consts_prelude_e4(
    gamma: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(1, 1, context.get_exec_stream());
    let args =
        GpuGKRLookupGammaConstsPreludeArguments::new(gamma, get_lookup_gamma_consts_device_ptr());
    GpuGKRLookupGammaConstsPreludeFunction(ab_gkr_lookup_gamma_consts_prelude)
        .launch(&config, &args)
}

pub(crate) fn gkr_forward_cache_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(crate) fn launch_forward_cache<E: crate::prover::gkr::GpuKernels>(
    batch: GpuGKRForwardCacheBatch<E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let config = gkr_forward_cache_launch_config(trace_len as u32, context);
    let args = GpuGKRForwardCacheArguments::new(batch, trace_len as u32);
    GpuGKRForwardCacheFunction(E::FORWARD_CACHE).launch(&config, &args)
}

pub(crate) fn launch_virtual_base_accum<E: crate::prover::gkr::GpuKernels>(
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

pub(crate) fn launch_dimension_reducing_forward_tower_pairwise<E: crate::prover::gkr::GpuKernels>(
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

pub(crate) fn launch_dimension_reducing_forward_tower_lookup<E: crate::prover::gkr::GpuKernels>(
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

pub(crate) fn gkr_forward_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_FORWARD_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

mod flat;

pub(in crate::prover::gkr) use flat::*;
pub(crate) use flat::GpuFlatForwardStaticDesc;
