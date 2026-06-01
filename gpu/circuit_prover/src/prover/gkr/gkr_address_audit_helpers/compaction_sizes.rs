use crate::prover::gkr::backward::flat::{
    FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES, FLAT_CONT_MAX_SOURCES,
    FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES, FLAT_CONT_UNIFIED_MAX_TERMS, FLAT_CONT_UNIFIED_MAX_TILES,
    FLAT_ROUND0_MAX_C0_BF, FLAT_ROUND0_MAX_C0_EXT, FLAT_ROUND0_MAX_C1_BF_BF,
    FLAT_ROUND0_MAX_C1_BF_E4, FLAT_ROUND0_MAX_C1_E4_E4, FLAT_ROUND0_MAX_C1_LINEAR,
    FLAT_ROUND0_MAX_SOURCES,
};
use crate::prover::gkr::backward::kernels::GKR_BACKWARD_MAX_KERNELS_PER_LAYER;

use super::{KERNEL_ARG_HARD_CEILING_BYTES, KERNEL_ARG_SOFT_TARGET_BYTES};

/// Post-compaction descriptor sizes, given the planned encoding. Reported per
/// descriptor type so we know each launch fits the 32 KB inline ceiling
/// without driver H2D before any code that bakes the encoding into a kernel
/// ABI lands.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PostCompactionSizes {
    pub(crate) dim_reducing_round0_batch: usize,
    pub(crate) dim_reducing_continuation_batch: usize,
    pub(crate) flat_round0_static_desc: usize,
    pub(crate) flat_round1_unified_desc: usize,
    pub(crate) flat_round2_unified_desc: usize,
    pub(crate) flat_continuation_unified_desc: usize,
}

// `bases:[*const u8;N] + log2_stride:[u32;N]`, where
// `N = GKR_DIM_REDUCING_BASE_SLOTS`.
const TABLES_BYTES: usize =
    crate::prover::gkr::backward::kernels::GKR_DIM_REDUCING_BASE_SLOTS * (8 + 4);
const HEADER_HOT_PTRS_BYTES: usize = 8 * 8; // four hot pointers (eq, batch_challenge, fold_challenge, contributions) + slack
const RECORD_BYTES: usize = 16; // BatchRecord { inputs: PayloadRange16, outputs: PayloadRange16 }

/// What the post-compaction `inline_payload` (in dual-u16 source records) expands to in
/// bytes. Kept separate so the worst-case payload size plugs in as a constant
/// and the resulting struct size stays visible.
fn dim_reducing_struct_bytes(inline_record_budget: usize) -> usize {
    HEADER_HOT_PTRS_BYTES
        + TABLES_BYTES
        + GKR_BACKWARD_MAX_KERNELS_PER_LAYER * RECORD_BYTES
        + 4 * inline_record_budget
}

/// Compute the post-compaction descriptor sizes for the planned encoding.
pub(crate) fn projected_post_compaction_sizes() -> PostCompactionSizes {
    // Reserve enough u16s to fit the largest measured layer's source list.
    // FLAT_ROUND0_MAX_SOURCES is the pessimistic bound (each source = one u16).
    let inline_record_budget = FLAT_ROUND0_MAX_SOURCES;

    let dim_reducing = dim_reducing_struct_bytes(inline_record_budget);

    // Round struct size up to its natural alignment (8 B, set by the
    // `*const u8` pointers in `tables`). Rust `#[repr(C)]` rounds the total
    // struct size to a multiple of the max member alignment; this matches
    // `std::mem::size_of::<...>()`.
    fn align_up(n: usize, align: usize) -> usize {
        (n + align - 1) & !(align - 1)
    }
    const STRUCT_ALIGN: usize = 8;

    // Flat round 0: dual-u16 source records + u32 counts + tables + term tables.
    let flat_round0 = align_up(
        4 // num_sources
            + FLAT_ROUND0_MAX_SOURCES * 4
            + TABLES_BYTES
            + 4 + FLAT_ROUND0_MAX_C0_BF * 2 // GpuFlatC0Ref { source_idx: u16 }
            + 4 + FLAT_ROUND0_MAX_C0_EXT * 2
            + 4 + FLAT_ROUND0_MAX_C1_BF_BF * 4  // GpuFlatC1Pair { source_a: u16, source_b: u16 }
            + 4 + FLAT_ROUND0_MAX_C1_E4_E4 * 4
            + 4 + FLAT_ROUND0_MAX_C1_BF_E4 * 4
            + 4 + FLAT_ROUND0_MAX_C1_LINEAR * 2,
        STRUCT_ALIGN,
    );

    // Continuation/round1/round2 unified descs: source entries become 4-byte
    // dual-u16 records instead of larger entries that hold pointers, then term
    // tables stay the same (4 B/term), tile metadata stays.
    // GpuFlatUnifiedTerm = 8 B (source_a:u16, source_b:u16, term_type:u16, coeff_idx:u16).
    const TERM_BYTES: usize = 8;
    const TILE_OFFSETS_BYTES: usize = 2 * (FLAT_CONT_UNIFIED_MAX_TILES + 1) * 2;
    const FOLD_SOURCES_BYTES: usize = FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES * 2;

    let flat_round1 = align_up(
        TABLES_BYTES
            + 4 + 4 // base_layer_half_size, next_layer_size
            + FLAT_CONT_MAX_BASE_SOURCES * 4 // base source records
            + 4 + FLAT_CONT_MAX_EXT_SOURCES * 4
            + 4 + FLAT_CONT_UNIFIED_MAX_TERMS * TERM_BYTES
            + 4 + 4 // num_constant_terms, num_tiles
            + TILE_OFFSETS_BYTES
            + FOLD_SOURCES_BYTES,
        STRUCT_ALIGN,
    );
    // Round 2: same shape as round 1, plus an extra `base_quarter_size` u32.
    let flat_round2 = flat_round1 + 4;
    let flat_continuation = align_up(
        TABLES_BYTES
            + crate::prover::gkr::backward::kernels::GKR_DIM_REDUCING_BASE_SLOTS * 4 * 2 // prev_per_poly_offset[N], cache_per_poly_offset[N] (per-slot)
            + 4 + FLAT_CONT_MAX_SOURCES * 4 // single source record array
            + 4 + FLAT_CONT_UNIFIED_MAX_TERMS * TERM_BYTES
            + 4 + 4
            + TILE_OFFSETS_BYTES
            + FOLD_SOURCES_BYTES,
        STRUCT_ALIGN,
    );

    PostCompactionSizes {
        dim_reducing_round0_batch: dim_reducing,
        dim_reducing_continuation_batch: dim_reducing,
        flat_round0_static_desc: flat_round0,
        flat_round1_unified_desc: flat_round1,
        flat_round2_unified_desc: flat_round2,
        flat_continuation_unified_desc: flat_continuation,
    }
}

pub(crate) fn log_post_compaction_sizes(sizes: &PostCompactionSizes) {
    let report = |name: &str, bytes: usize| {
        let status = if bytes <= KERNEL_ARG_SOFT_TARGET_BYTES {
            "SOFT_TARGET"
        } else if bytes <= KERNEL_ARG_HARD_CEILING_BYTES {
            "OVER_SOFT_TARGET"
        } else {
            "OVER_HARD_CEILING"
        };
        log::info!(
            "[gkr-audit] post-compaction size: {} = {} B (soft={}KB hard={}KB) [{}]",
            name,
            bytes,
            KERNEL_ARG_SOFT_TARGET_BYTES / 1024,
            KERNEL_ARG_HARD_CEILING_BYTES / 1024,
            status,
        );
    };
    report("dim_reducing_round0_batch", sizes.dim_reducing_round0_batch);
    report(
        "dim_reducing_continuation_batch",
        sizes.dim_reducing_continuation_batch,
    );
    report("flat_round0_static_desc", sizes.flat_round0_static_desc);
    report("flat_round1_unified_desc", sizes.flat_round1_unified_desc);
    report("flat_round2_unified_desc", sizes.flat_round2_unified_desc);
    report(
        "flat_continuation_unified_desc",
        sizes.flat_continuation_unified_desc,
    );
}

pub(crate) fn check_descriptor_sizes_under_hard_ceiling(
    sizes: &PostCompactionSizes,
) -> Result<(), String> {
    let pairs = [
        ("dim_reducing_round0_batch", sizes.dim_reducing_round0_batch),
        (
            "dim_reducing_continuation_batch",
            sizes.dim_reducing_continuation_batch,
        ),
        ("flat_round0_static_desc", sizes.flat_round0_static_desc),
        ("flat_round1_unified_desc", sizes.flat_round1_unified_desc),
        ("flat_round2_unified_desc", sizes.flat_round2_unified_desc),
        (
            "flat_continuation_unified_desc",
            sizes.flat_continuation_unified_desc,
        ),
    ];
    for (name, bytes) in pairs.iter() {
        if *bytes > KERNEL_ARG_HARD_CEILING_BYTES {
            return Err(format!(
                "{} = {} B exceeds 32 KB inline kernel-arg ceiling",
                name, bytes,
            ));
        }
    }
    Ok(())
}
