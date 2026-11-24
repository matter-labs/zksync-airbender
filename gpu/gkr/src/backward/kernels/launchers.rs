use era_cudart::{cuda_kernel_signature_and_arguments, execution::CudaLaunchConfig};
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_prover_context::ProverContext;

pub(crate) const GKR_DIM_REDUCING_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(crate) const GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK: u32 = 512;
pub(crate) const GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK: usize = 4;

pub(crate) const GKR_EQ_GROUP_SIZE: usize = 8;
pub const GKR_EQ_GROUP_TABLE_LEN: usize = 1 << GKR_EQ_GROUP_SIZE;
// Number of warp-uniform high slabs in the strict 3-slot eq layout.
// Mirrors `GKR_EQ_HIGH_SLOTS` in
// `gpu/gkr/native/gkr/support/descriptors.cuh`.
pub const GKR_EQ_HIGH_SLOTS: usize = 2;

/// Rust-side mirror of the CUDA `gkr_eq_sizes` struct in
/// `gpu/gkr/native/gkr/support/descriptors.cuh`. Holds per-slot bit
/// widths for the strict 3-slot eq layout `[high[0], high[1], low]`. Field
/// types and layout MUST match the CUDA side (`unsigned high[2]; unsigned low`).
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct GkrEqSizes {
    pub(crate) high: [u32; GKR_EQ_HIGH_SLOTS],
    pub(crate) low: u32,
}

const _: () = {
    assert!(std::mem::size_of::<GkrEqSizes>() == 12);
    assert!(std::mem::align_of::<GkrEqSizes>() == 4);
    assert!(std::mem::offset_of!(GkrEqSizes, high) == 0);
    assert!(std::mem::offset_of!(GkrEqSizes, low) == 8);
};

impl GkrEqSizes {
    /// Zero-initialised descriptor; used as the `Default` impl for the compact
    /// batch structs before the scheduler fills in the real sizes from
    /// [`make_eq_sizes`].
    pub(crate) const fn zeroed() -> Self {
        Self {
            high: [0; GKR_EQ_HIGH_SLOTS],
            low: 0,
        }
    }
}

/// Builds the strict 3-slot eq-sizes descriptor for a fresh factored-eq
/// build. Mirrors the build kernel's natural grouping: top groups go to
/// `high[0..]` (size 8 each until the last group), the last group goes to
/// `low`. For small `challenge_count`, unused high slots have size 0 and
/// the inline-eq reads slot[0] (the build kernel writes `E::ONE()` there
/// as a sentinel).
pub fn make_eq_sizes(challenge_count: usize) -> GkrEqSizes {
    let g_count = eq_group_count(challenge_count);
    let mut high = [0u32; GKR_EQ_HIGH_SLOTS];
    let mut low: u32 = 0;
    let mut consumed = 0usize;
    let mut high_idx = 0usize;
    for g in 0..g_count {
        let remaining = challenge_count - consumed;
        let g_size = remaining.min(GKR_EQ_GROUP_SIZE) as u32;
        if g + 1 == g_count {
            low = g_size;
        } else {
            assert!(high_idx < GKR_EQ_HIGH_SLOTS);
            high[high_idx] = g_size;
            high_idx += 1;
        }
        consumed += g_size as usize;
    }
    GkrEqSizes { high, low }
}

cuda_kernel_signature_and_arguments!(
    pub(crate) GpuDimensionReducingBuildEqGroupTablesFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    eq_group_tables: *mut T,
);

cuda_kernel_signature_and_arguments!(
    pub(crate) GpuDimensionReducingBuildEqHighLowFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    high_0: *mut T,
    high_1: *mut T,
    low_buffer: *mut T,
);

cuda_kernel_signature_and_arguments!(
    pub(crate) GpuDimensionReducingBuildEqValuesFromGroupTables<T>,
    eq_group_tables: *const T,
    challenge_count: u32,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_and_arguments!(
    pub(crate) GpuDimensionReducingTraceHolderColumnSums<T>,
    block_partials: *const T,
    column_sums: *mut T,
    blocks_count: u32,
);
pub fn gkr_dim_reducing_launch_config(count: u32, context: &ProverContext) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_DIM_REDUCING_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub fn eq_group_count(challenge_count: usize) -> usize {
    challenge_count.div_ceil(GKR_EQ_GROUP_SIZE)
}

pub fn eq_group_tables_len(challenge_count: usize) -> usize {
    eq_group_count(challenge_count) * GKR_EQ_GROUP_TABLE_LEN
}
