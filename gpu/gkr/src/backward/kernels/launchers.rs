use std::ffi::c_void;

use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};

use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_gkr_compiler::KERNEL_ARGUMENT_CEILING_BYTES;
use gpu_prover_context::ProverContext;

pub(crate) const GKR_DIM_REDUCING_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(crate) const GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK: u32 = 512;
// Mirrors the deferred-extras entry in native/gkr/backward/dim_reducing.cu.
pub(crate) const GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK: u32 = 128;
pub(crate) const GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK: usize = 4;
// Mirrors extras_batch_columns in native/gkr/backward/dim_reducing.cu.
pub(crate) const GKR_EXTRAS_BATCH_CAPACITY: usize = 4090;

#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub(crate) struct ExtrasBatchColumns {
    values: [*const BF; GKR_EXTRAS_BATCH_CAPACITY],
}

const _: () = {
    assert!(std::mem::size_of::<*const BF>() == 8);
    assert!(std::mem::size_of::<ExtrasBatchColumns>() == 32720);
    assert!(std::mem::align_of::<ExtrasBatchColumns>() == 8);
    // The current kernel arguments after the blob occupy 40 bytes, including padding.
    assert!(std::mem::size_of::<ExtrasBatchColumns>() + 40 <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(std::mem::size_of::<ExtrasBatchColumns>() + 48 > KERNEL_ARGUMENT_CEILING_BYTES);
};

impl ExtrasBatchColumns {
    fn new(pointers: impl ExactSizeIterator<Item = *const BF>) -> Self {
        assert!((1..=GKR_EXTRAS_BATCH_CAPACITY).contains(&pointers.len()));
        let mut result = Self {
            values: [std::ptr::null(); GKR_EXTRAS_BATCH_CAPACITY],
        };
        for (slot, pointer) in result.values.iter_mut().zip(pointers) {
            assert_eq!(pointer as usize % 16, 0);
            *slot = pointer;
        }
        result
    }
}

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

cuda_struct_and_stub! {
    static ab_gkr_eq_high: [[E4; GKR_EQ_GROUP_TABLE_LEN]; GKR_EQ_HIGH_SLOTS];
}

/// Returns the device pointer to the `__constant__` `ab_gkr_eq_high`
/// symbol — a single contiguous block of
/// `GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN` E4 elements. Used by the
/// build / fold launchers (which need a writable device pointer through
/// `cudaGetSymbolAddress`) and by consumer kernels via the inline-eq
/// helper.
pub(crate) fn get_eq_high_constant_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    unsafe { cudaGetSymbolAddress(&mut ptr, &ab_gkr_eq_high as *const _ as *const c_void) }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_eq_high");
    ptr as *mut E4
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqGroupTablesFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    eq_group_tables: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqHighLowFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    high_0: *mut T,
    high_1: *mut T,
    low_buffer: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqValuesFromGroupTables<T>,
    eq_group_tables: *const T,
    challenge_count: u32,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingTraceHolderBlockPartials<T>,
    raw_values: *const BF,
    eq_values: *const T,
    block_partials: *mut T,
    trace_len: u32,
    column_start: u32,
    chunk_cols: u32,
    blocks_count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingTraceHolderBlockPartialsEqInline<T>,
    raw_values: *const BF,
    eq_low: *const T,
    sizes: GkrEqSizes,
    block_partials: *mut T,
    trace_len: u32,
    columns_count: u32,
    blocks_count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingTraceHolderColumnSums<T>,
    block_partials: *const T,
    column_sums: *mut T,
    blocks_count: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel(
        claim_point: *const E4,
        challenge_offset: u32,
        challenge_count: u32,
        eq_group_tables: *mut E4,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_high_low_from_point_e4_kernel(
        claim_point: *const E4,
        challenge_offset: u32,
        challenge_count: u32,
        high_0: *mut E4,
        high_1: *mut E4,
        low_buffer: *mut E4,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel(
        eq_group_tables: *const E4,
        challenge_count: u32,
        eq_values: *mut E4,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel(
        raw_values: *const BF,
        eq_values: *const E4,
        block_partials: *mut E4,
        trace_len: u32,
        column_start: u32,
        chunk_cols: u32,
        blocks_count: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_trace_holder_block_partials_eq_inline_e4_kernel(
        raw_values: *const BF,
        eq_low: *const E4,
        sizes: GkrEqSizes,
        block_partials: *mut E4,
        trace_len: u32,
        columns_count: u32,
        blocks_count: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_trace_holder_block_partials_eq_inline_bf8_e4_kernel(
        raw_values: *const BF,
        eq_low: *const E4,
        sizes: GkrEqSizes,
        block_partials: *mut E4,
        trace_len: u32,
        columns_count: u32,
        blocks_count: u32,
    )
);
cuda_kernel!(DeferredExtras, ab_gkr_extras_deferred_eq_kernel(
    columns: ExtrasBatchColumns,
    eq_low: *const E4,
    sizes: GkrEqSizes,
    block_partials: *mut E4,
    trace_len: u32,
    columns_count: u32,
));

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_trace_holder_column_sums_e4_kernel(
        block_partials: *const E4,
        column_sums: *mut E4,
        blocks_count: u32,
    )
);
pub fn gkr_dim_reducing_launch_config(count: u32, context: &ProverContext) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_DIM_REDUCING_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(crate) fn gkr_trace_holder_partials_launch_config(
    blocks_count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    CudaLaunchConfig::basic(
        blocks_count,
        GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    )
}

pub fn launch_build_eq_values_from_point(
    claim_point: *const E4,
    challenge_offset: usize,
    challenge_count: usize,
    eq_group_tables: *mut E4,
    eq_values: *mut E4,
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
            ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel,
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
    GpuDimensionReducingBuildEqValuesFromGroupTablesFunction(
        ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel,
    )
    .launch(&config, &args)
}

/// Builds the factored eq representation directly from a claim point:
/// high groups 0..(G-2) land in `high_slab` (the `__constant__`
/// `ab_gkr_eq_high` symbol, accessed via the device pointer from
/// [`get_eq_high_constant_device_ptr`]), and the last (low) group lands in
/// `low_buffer`. Used by the backward GKR sumcheck factored-eq path; WHIR
/// continues to use [`launch_build_eq_values_from_point`] for the
/// materialized eq path.
///
/// The grid is sized `max(groups_count, GKR_EQ_HIGH_SLOTS)` so that thread 0
/// of every block initializes its high slot's `[0]` entry to `E::ONE()` —
/// degenerate slots (small `challenge_count`) need this sentinel because
/// the inline-eq read is unconditional.
pub(crate) fn launch_build_eq_high_and_low_groups_from_point(
    claim_point: *const E4,
    challenge_offset: usize,
    challenge_count: usize,
    high_slab: *mut E4,
    low_buffer: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    launch_build_eq_independent_groups_from_point(
        claim_point,
        challenge_offset,
        challenge_count,
        high_slab,
        high_slab.wrapping_add(GKR_EQ_GROUP_TABLE_LEN),
        low_buffer,
        context,
    )
}

/// Builds the same strict three-slot factored Eq representation as
/// [`launch_build_eq_high_and_low_groups_from_point`], but permits each slot
/// to have an independent exact-capacity owner. This is used by DR
/// continuations so inactive high sentinels do not force three full tables.
pub(crate) fn launch_build_eq_independent_groups_from_point(
    claim_point: *const E4,
    challenge_offset: usize,
    challenge_count: usize,
    high_0: *mut E4,
    high_1: *mut E4,
    low_buffer: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(challenge_offset <= u32::MAX as usize);
    assert!(challenge_count <= u32::MAX as usize);
    let group_count = eq_group_count(challenge_count);
    let block_count = group_count.max(GKR_EQ_HIGH_SLOTS);
    if block_count == 0 {
        return Ok(());
    }
    let config = CudaLaunchConfig::basic(
        block_count as u32,
        GKR_EQ_GROUP_TABLE_LEN as u32,
        context.get_exec_stream(),
    );
    let args = GpuDimensionReducingBuildEqHighLowFromPointArguments::new(
        claim_point,
        challenge_offset as u32,
        challenge_count as u32,
        high_0,
        high_1,
        low_buffer,
    );
    GpuDimensionReducingBuildEqHighLowFromPointFunction(
        ab_gkr_dim_reducing_build_eq_high_low_from_point_e4_kernel,
    )
    .launch(&config, &args)
}

pub fn eq_group_count(challenge_count: usize) -> usize {
    challenge_count.div_ceil(GKR_EQ_GROUP_SIZE)
}

pub fn eq_group_tables_len(challenge_count: usize) -> usize {
    eq_group_count(challenge_count) * GKR_EQ_GROUP_TABLE_LEN
}

pub(crate) fn launch_trace_holder_block_partials(
    raw_values: *const BF,
    eq_values: *const E4,
    block_partials: *mut E4,
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

    GpuDimensionReducingTraceHolderBlockPartialsFunction(
        ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel,
    )
    .launch(&config, &args)
}

// Keep chunk indices out of grid x: it is also the partials row pitch.
// The y/z projection covers ceil(u32::MAX / 4) chunks without exceeding
// 32768 in either extra dimension. Empty holders are skipped by the caller.
fn trace_holder_claim_chunk_grid(columns: usize) -> Option<(u32, u32)> {
    assert!(columns <= u32::MAX as usize);
    let chunks = columns.div_ceil(GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK);
    if chunks == 0 {
        return None;
    }
    let y = chunks.min(32768);
    let z = chunks.div_ceil(y);
    assert!(z <= 32768);
    Some((y as u32, z as u32))
}

// Every column base is aligned when the holder base is aligned and its row
// length is a multiple of the pack width. Keep BF4 for the existing domain.
fn trace_holder_claim_uses_bf8(address: usize, trace_len: usize) -> bool {
    address % 32 == 0 && trace_len > 0 && trace_len % 8 == 0
}

pub(crate) fn launch_trace_holder_block_partials_eq_inline(
    raw_values: *const BF,
    eq_low: *const E4,
    sizes: GkrEqSizes,
    block_partials: *mut E4,
    trace_len: usize,
    columns_count: usize,
    blocks_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    assert!(blocks_count > 0 && blocks_count <= u32::MAX as usize);
    let (y, z) = trace_holder_claim_chunk_grid(columns_count)
        .expect("empty trace holders must skip claim scanning");
    let config = CudaLaunchConfig::basic(
        Dim3::new(blocks_count as u32, y, z),
        GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    );
    let args = GpuDimensionReducingTraceHolderBlockPartialsEqInlineArguments::new(
        raw_values,
        eq_low,
        sizes,
        block_partials,
        trace_len as u32,
        columns_count as u32,
        blocks_count as u32,
    );
    let function = if trace_holder_claim_uses_bf8(raw_values as usize, trace_len) {
        ab_gkr_dim_reducing_trace_holder_block_partials_eq_inline_bf8_e4_kernel
    } else {
        ab_gkr_dim_reducing_trace_holder_block_partials_eq_inline_e4_kernel
    };
    GpuDimensionReducingTraceHolderBlockPartialsEqInlineFunction(function).launch(&config, &args)
}

pub(crate) fn launch_trace_holder_block_partials_eq_deferred(
    pointers: impl ExactSizeIterator<Item = *const BF>,
    eq_low: *const E4,
    sizes: GkrEqSizes,
    block_partials: *mut E4,
    trace_len: usize,
    blocks_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(sizes.low >= 2);
    let period = 1usize << (sizes.low + sizes.high[1]);
    assert_eq!(
        blocks_count
            .checked_mul(GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK as usize * 4)
            .unwrap()
            % period,
        0
    );
    assert!(trace_len <= u32::MAX as usize && trace_len % 4 == 0);
    assert!(blocks_count > 0 && blocks_count <= u32::MAX as usize);
    let columns_count = pointers.len();
    let columns = ExtrasBatchColumns::new(pointers);
    let config = CudaLaunchConfig::basic(
        Dim3::new(blocks_count as u32, columns_count as u32, 1),
        GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    );
    let args = DeferredExtrasArguments::new(
        columns,
        eq_low,
        sizes,
        block_partials,
        trace_len as u32,
        columns_count as u32,
    );
    DeferredExtrasFunction::default().launch(&config, &args)
}

pub(crate) fn launch_trace_holder_column_sums(
    block_partials: *const E4,
    column_sums: *mut E4,
    columns_count: usize,
    blocks_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(columns_count <= u32::MAX as usize);
    assert!(blocks_count <= u32::MAX as usize);
    let config =
        CudaLaunchConfig::basic(columns_count as u32, WARP_SIZE, context.get_exec_stream());
    let args = GpuDimensionReducingTraceHolderColumnSumsArguments::new(
        block_partials,
        column_sums,
        blocks_count as u32,
    );
    GpuDimensionReducingTraceHolderColumnSumsFunction(
        ab_gkr_dim_reducing_trace_holder_column_sums_e4_kernel,
    )
    .launch(&config, &args)
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn cpu_claim_chunk_grid_boundaries() {
        for (columns, expected) in [
            (0, None),
            (1, Some((1, 1))),
            (4, Some((1, 1))),
            (5, Some((2, 1))),
            (131068, Some((32767, 1))),
            (131072, Some((32768, 1))),
            (131073, Some((32768, 2))),
            (262145, Some((32768, 3))),
            (u32::MAX as usize, Some((32768, 32768))),
        ] {
            assert_eq!(trace_holder_claim_chunk_grid(columns), expected);
        }
    }

    #[test]
    fn cpu_extras_pointer_blob_preserves_live_prefix_and_null_padding() {
        for count in [
            1,
            15,
            246,
            GKR_EXTRAS_BATCH_CAPACITY - 1,
            GKR_EXTRAS_BATCH_CAPACITY,
        ] {
            let pointers: Vec<_> = (1..=count).map(|n| (n * 16) as *const BF).collect();
            let blob = ExtrasBatchColumns::new(pointers.iter().copied());
            assert_eq!(&blob.values[..count], pointers);
            assert!(blob.values[count..].iter().all(|p| p.is_null()));
        }
    }

    #[test]
    fn cpu_claim_pack_selection_preserves_bf4_domain() {
        for bits in 2..=31 {
            let len = 1usize << bits;
            for address in (0..128).step_by(4) {
                let selected = trace_holder_claim_uses_bf8(address, len);
                assert_eq!(selected, bits >= 3 && address % 32 == 0);
                if selected {
                    for column in [0, 1, 3, 4, 162] {
                        assert_eq!((address + column * len * 4) % 32, 0);
                    }
                }
            }
        }
        for len in [0, 4, 12, 20] {
            assert!(!trace_holder_claim_uses_bf8(32, len));
        }
        for len in [8, 16, 24] {
            assert!(trace_holder_claim_uses_bf8(32, len));
        }
    }
}
