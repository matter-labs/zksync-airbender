//! Rust half of the segmented backward VM ABI.
//!
//! The matching CUDA definitions and offset assertions live in
//! `native/gkr/backward/segmented_vm.cuh`.

use core::mem::{align_of, size_of};

use gpu_gkr_compiler::KIND_ORDER;
use gpu_gkr_compiler::{
    CoefficientRecipeId, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES,
    LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES,
    MAX_BACKWARD_COEFFICIENT_RECIPES, MAX_BACKWARD_SOURCES, MAX_COEFFICIENT_ENCODINGS,
    MAX_SOURCE_WINDOWS, PUBLISH_TARGET_DEPTH, SOURCE_NONE, SOURCE_WINDOW_COLUMNS,
    WINDOW_COEFFICIENT_BANK_BIAS, WINDOW_MAX_COEFFICIENT_PLANS,
};

use crate::backward::GkrEqSizes;
use gpu_core::primitives::field::E4;
use gpu_core::primitives::utils::WARP_SIZE;

/// Maximum by-value kernel argument size.
pub(crate) const BWD_SEG_DESC_CAP: usize = 32_764;
/// Keeps the inline program 16-byte aligned.
pub(crate) const BWD_SEG_DESC_ALIGN: usize = 16;

pub(crate) const BWD_SEG_MAX_K: usize = 16;

/// Slots in the device output coefficient bank, including the reserved `±1`
/// entries. Sized for the widest arm — the windowed executor's interned plans —
/// not for the per-round arm's recipe count.
pub(crate) const BWD_SEG_OUTPUT_BANK: usize = 1_792;

/// [`BwdSegDesc::c_init_coeff`] for a layer with no `acc_c0` seed.
///
/// A sentinel is unavoidable here: `0` is `CoefficientRecipeId::ONE`, a perfectly
/// legal seed. `u32::MAX` is chosen over the thirteen-bit id space's first unused
/// value so that a byte-level truncation cannot turn absence into a live id.
pub(crate) const BWD_SEG_C_INIT_NONE: u32 = u32::MAX;

pub(crate) const BWD_SEG_ADDR_SLOTS: usize = 64;
const _: () = assert!(BWD_SEG_ADDR_SLOTS == MAX_SOURCE_WINDOWS);

/// Fold-weight bank slots hold only q >= 1 (the q = 0
/// coefficient is the difference form's implicit 1), packed per delta.
pub(crate) const BWD_SEG_FOLD_WEIGHT_SLOTS: usize = 11;

/// First slot of each delta's packed run. A depth-DELTA fold reads only its own
/// run, so a launch's fold-weight reads are the union of the runs its live
/// source records name. Only the Task-8 read census needs the split.
#[cfg(test)]
pub(crate) const BWD_SEG_FOLD_WEIGHT_BASE_D1: usize = 0;
#[cfg(test)]
pub(crate) const BWD_SEG_FOLD_WEIGHT_BASE_D2: usize = 1;
#[cfg(test)]
pub(crate) const BWD_SEG_FOLD_WEIGHT_BASE_D3: usize = 4;

#[cfg(test)]
const _: () = {
    assert!(BWD_SEG_FOLD_WEIGHT_BASE_D2 == BWD_SEG_FOLD_WEIGHT_BASE_D1 + 1);
    assert!(BWD_SEG_FOLD_WEIGHT_BASE_D3 == BWD_SEG_FOLD_WEIGHT_BASE_D2 + 3);
    assert!(BWD_SEG_FOLD_WEIGHT_SLOTS == BWD_SEG_FOLD_WEIGHT_BASE_D3 + 7);
};

/// Source-table slots rounded to a 16-slot boundary.
pub(crate) const BWD_SEG_MAX_SOURCES: usize = 1_072;

/// Inline immediate-table capacity, mirrored from the compiler ISA.
pub(crate) const BWD_SEG_MAX_IMMEDIATES: usize = 512;

const _: () = {
    assert!(BWD_SEG_DESC_CAP == KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(BWD_SEG_DESC_ALIGN == DESCRIPTOR_ALIGNMENT_BYTES);

    // One warp per list, and the block is the cap.
    assert!(BWD_SEG_MAX_K * WARP_SIZE as usize == 512);
    // `k` and every `list_offset` entry are u16.
    assert!(BWD_SEG_MAX_K <= u16::MAX as usize);
    assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS <= u16::MAX as usize);
    assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES == LEAN_DESCRIPTOR_PROGRAM_WORDS * size_of::<u16>());
    // The immediate array is the WIRE cap exactly: not a byte more (an unearned
    // 4-byte slot rides every launch) and not a byte less (a table the encoder can
    // emit must fit). The mirror direction is GPU-imports-ISA.
    assert!(BWD_SEG_MAX_IMMEDIATES == LEAN_MAX_IMMEDIATES);
    // A live count rides the descriptor as a u16.
    assert!(BWD_SEG_MAX_IMMEDIATES <= u16::MAX as usize);

    // The bank covers every reserved-inclusive coefficient id either arm can
    // name, stays inside the thirteen coefficient bits that name it, and fits the
    // per-module constant budget.
    assert!(
        BWD_SEG_OUTPUT_BANK
            >= MAX_BACKWARD_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
    );
    assert!(
        BWD_SEG_OUTPUT_BANK >= WINDOW_MAX_COEFFICIENT_PLANS + WINDOW_COEFFICIENT_BANK_BIAS as usize
    );
    assert!(BWD_SEG_OUTPUT_BANK <= MAX_COEFFICIENT_ENCODINGS);
    assert!(BWD_SEG_OUTPUT_BANK * size_of::<E4>() == 28 * 1_024);
    assert!(BWD_SEG_OUTPUT_BANK * size_of::<E4>() <= 64 * 1_024);

    assert!(BWD_SEG_MAX_SOURCES == MAX_BACKWARD_SOURCES);
    assert!(BWD_SEG_MAX_SOURCES.is_multiple_of(16));
    // A slot index rides the lean wire as a u16 whose 0xFFFF is the "no second
    // source" sentinel, so the capacity must stay strictly below it.
    assert!(BWD_SEG_MAX_SOURCES < SOURCE_NONE as usize);

    assert!(BWD_COEFF_PUBLISH_TARGET_DEPTH == PUBLISH_TARGET_DEPTH);
};

#[cfg(test)]
mod cuda_abi_tests {
    use super::*;
    use crate::backward::vm::seg_coeff_eval::{
        BWD_SEG_CHALLENGE_CLAIM_BATCHING, BWD_SEG_CHALLENGE_SLOTS, BWD_SEG_COEFF_CHUNK_MONOMIALS,
        BWD_SEG_COEFF_CHUNK_RECIPES, BWD_SEG_COEFF_PLAN_DIRECT, BWD_SEG_COEFF_PLAN_LINEAR_BASIS,
        BWD_SEG_COEFF_PLAN_SCALED, BWD_SEG_EVAL_MONOMIALS, BWD_SEG_EVAL_RECIPES,
        BWD_SEG_WINDOW_PLANS,
    };
    use crate::backward::vm::seg_lower::SourceClass;
    use gpu_gkr_compiler::{
        ImmediateId, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS, LEAN_CLASS_SHIFT,
        LEAN_COEFFICIENT_SHIFT, LEAN_CONT_GROUP_HEADER_CLASS, LEAN_CONT_OPCODES,
        LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_R0_OPCODES, LEAN_WORDS_PER_TERM,
    };

    const CUDA_VM: &str = include_str!("../../../native/gkr/backward/segmented_vm.cuh");
    const CUDA_COEFF: &str = include_str!("../../../native/gkr/backward/seg_coeff_eval.cuh");

    fn cpp_literal(source: &str, name: &str) -> u64 {
        let marker = format!("{name} = ");
        let expression = source
            .lines()
            .find_map(|line| {
                let line = line.trim();
                line.starts_with("constexpr ")
                    .then(|| line.split_once(&marker).map(|(_, value)| value))
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing CUDA ABI constant {name}"));
        let expression = expression
            .split_once(';')
            .map_or(expression, |(value, _)| value)
            .trim_end_matches(['u', 'U', 'l', 'L']);
        if let Some(hex) = expression.strip_prefix("0x") {
            u64::from_str_radix(hex, 16).unwrap_or_else(|_| {
                panic!("CUDA ABI constant {name} is not a literal: {expression}")
            })
        } else {
            expression.parse().unwrap_or_else(|_| {
                panic!("CUDA ABI constant {name} is not a literal: {expression}")
            })
        }
    }

    #[test]
    fn cpu_backward_cuda_abi_matches_rust() {
        for (name, value) in [
            (
                "BWD_COEFF_HEADER_COEFFICIENT_BITS",
                HEADER_COEFFICIENT_BITS as u64,
            ),
            ("BWD_COEFF_HEADER_OPCODE_BITS", HEADER_OPCODE_BITS as u64),
            (
                "BWD_COEFF_PUBLISH_TARGET_DEPTH",
                PUBLISH_TARGET_DEPTH as u64,
            ),
            ("BWD_SEG_ADDR_NONE", SOURCE_NONE as u64),
            (
                "BWD_SEG_ADDR_COLUMN_BITS",
                SOURCE_WINDOW_COLUMNS.trailing_zeros() as u64,
            ),
            ("BWD_SEG_DESC_CAP", BWD_SEG_DESC_CAP as u64),
            ("BWD_SEG_DESC_ALIGN", BWD_SEG_DESC_ALIGN as u64),
            ("BWD_SEG_MAX_K", BWD_SEG_MAX_K as u64),
            (
                "BWD_SEG_FOLD_WEIGHT_SLOTS",
                BWD_SEG_FOLD_WEIGHT_SLOTS as u64,
            ),
            (
                "BWD_SEG_FOLD_WEIGHT_BASE_D1",
                BWD_SEG_FOLD_WEIGHT_BASE_D1 as u64,
            ),
            (
                "BWD_SEG_FOLD_WEIGHT_BASE_D2",
                BWD_SEG_FOLD_WEIGHT_BASE_D2 as u64,
            ),
            (
                "BWD_SEG_FOLD_WEIGHT_BASE_D3",
                BWD_SEG_FOLD_WEIGHT_BASE_D3 as u64,
            ),
            ("BWD_SEG_OUTPUT_BANK", BWD_SEG_OUTPUT_BANK as u64),
            ("BWD_SEG_C_INIT_NONE", BWD_SEG_C_INIT_NONE as u64),
            ("BWD_SEG_MAX_SOURCES", BWD_SEG_MAX_SOURCES as u64),
            (
                "BWD_SEG_PROGRAM_WORD_CAP",
                LEAN_DESCRIPTOR_PROGRAM_WORDS as u64,
            ),
            ("BWD_SEG_ADDR_SLOTS", BWD_SEG_ADDR_SLOTS as u64),
            ("BWD_SEG_MAX_IMMEDIATES", BWD_SEG_MAX_IMMEDIATES as u64),
            ("BWD_SEG_WORDS_PER_TERM", LEAN_WORDS_PER_TERM as u64),
            ("BWD_SEG_COEFFICIENT_SHIFT", LEAN_COEFFICIENT_SHIFT as u64),
        ] {
            assert_eq!(cpp_literal(CUDA_VM, name), value, "{name}");
        }
        assert!(CUDA_VM
            .contains("constexpr u32 BWD_SEG_CLASS_SHIFT = BWD_COEFF_HEADER_COEFFICIENT_BITS;"));
        assert_eq!(LEAN_CLASS_SHIFT, HEADER_COEFFICIENT_BITS);
        for (name, value) in [
            (
                "BWD_COEFF_ORIGIN_READ_BASE",
                BWD_COEFF_ORIGIN_READ_BASE as u64,
            ),
            (
                "BWD_COEFF_ORIGIN_READ_EXT",
                BWD_COEFF_ORIGIN_READ_EXT as u64,
            ),
            (
                "BWD_COEFF_ORIGIN_PROCEDURAL",
                BWD_COEFF_ORIGIN_PROCEDURAL as u64,
            ),
            (
                "BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS",
                BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS as u64,
            ),
            (
                "BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP",
                BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP as u64,
            ),
            (
                "BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW",
                BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW as u64,
            ),
            (
                "BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH",
                BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH as u64,
            ),
            (
                "BWD_COEFF_PROCEDURAL_NONE",
                BWD_COEFF_PROCEDURAL_NONE as u64,
            ),
            ("BWD_SEG_R0_CLASS_C0_LINEAR_BF", LEAN_R0_OPCODES[0].0 as u64),
            ("BWD_SEG_R0_CLASS_C0_LINEAR_E4", LEAN_R0_OPCODES[1].0 as u64),
            (
                "BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF",
                LEAN_R0_OPCODES[2].0 as u64,
            ),
            (
                "BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4",
                LEAN_R0_OPCODES[3].0 as u64,
            ),
            (
                "BWD_SEG_R0_CLASS_C2_PRODUCT_E4_E4",
                LEAN_R0_OPCODES[4].0 as u64,
            ),
            (
                "BWD_SEG_EXT_CLASS_C0_LINEAR_E4",
                LEAN_CONT_OPCODES[0].0 as u64,
            ),
            (
                "BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4",
                LEAN_CONT_OPCODES[1].0 as u64,
            ),
            (
                "BWD_SEG_EXT_CLASS_GROUP_HEADER",
                LEAN_CONT_GROUP_HEADER_CLASS as u64,
            ),
            ("BWD_SEG_GROUP_FLAG_C0", LEAN_GROUP_FLAG_C0 as u64),
            ("BWD_SEG_GROUP_FLAG_C2", LEAN_GROUP_FLAG_C2 as u64),
            ("BWD_SEG_IMMEDIATE_ONE", ImmediateId::ONE.0 as u64),
            ("BWD_SEG_IMMEDIATE_NEG_ONE", ImmediateId::NEG_ONE.0 as u64),
            ("BWD_SEG_IMMEDIATE_RESERVED", ImmediateId::RESERVED as u64),
            (
                "BWD_SEG_SOURCE_CLASS_BF_DIRECT",
                SourceClass::BfDirect.code() as u64,
            ),
            (
                "BWD_SEG_SOURCE_CLASS_BF_INLINE_D1",
                SourceClass::BfInlineD1.code() as u64,
            ),
            (
                "BWD_SEG_SOURCE_CLASS_BF_INLINE_D2",
                SourceClass::BfInlineD2.code() as u64,
            ),
            (
                "BWD_SEG_SOURCE_CLASS_E4_DIRECT",
                SourceClass::E4Direct.code() as u64,
            ),
            (
                "BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE",
                SourceClass::ProceduralInline.code() as u64,
            ),
        ] {
            assert_eq!(cpp_literal(CUDA_VM, name), value, "{name}");
        }
        for (name, value) in [
            (
                "BWD_SEG_CHALLENGE_CLAIM_BATCHING",
                BWD_SEG_CHALLENGE_CLAIM_BATCHING as u64,
            ),
            ("BWD_SEG_CHALLENGE_SLOTS", BWD_SEG_CHALLENGE_SLOTS as u64),
            ("BWD_SEG_EVAL_RECIPES", BWD_SEG_EVAL_RECIPES as u64),
            ("BWD_SEG_EVAL_MONOMIALS", BWD_SEG_EVAL_MONOMIALS as u64),
            ("BWD_SEG_WINDOW_PLANS", BWD_SEG_WINDOW_PLANS as u64),
            (
                "BWD_SEG_WINDOW_BANK_BIAS",
                WINDOW_COEFFICIENT_BANK_BIAS as u64,
            ),
            (
                "BWD_SEG_COEFF_CHUNK_RECIPES",
                BWD_SEG_COEFF_CHUNK_RECIPES as u64,
            ),
            (
                "BWD_SEG_COEFF_CHUNK_MONOMIALS",
                BWD_SEG_COEFF_CHUNK_MONOMIALS as u64,
            ),
            (
                "BWD_SEG_COEFF_PLAN_DIRECT",
                BWD_SEG_COEFF_PLAN_DIRECT as u64,
            ),
            (
                "BWD_SEG_COEFF_PLAN_SCALED",
                BWD_SEG_COEFF_PLAN_SCALED as u64,
            ),
            (
                "BWD_SEG_COEFF_PLAN_LINEAR_BASIS",
                BWD_SEG_COEFF_PLAN_LINEAR_BASIS as u64,
            ),
        ] {
            assert_eq!(cpp_literal(CUDA_COEFF, name), value, "{name}");
        }
    }
}

/// Window origin: a base-field matrix backing.
pub(crate) const BWD_COEFF_ORIGIN_READ_BASE: u8 = 0;
/// Window origin: an extension-field matrix backing.
pub(crate) const BWD_COEFF_ORIGIN_READ_EXT: u8 = 1;
/// Window origin: a procedurally produced (virtual-setup) source. Row-dependent
/// and never materialized from a matrix.
pub(crate) const BWD_COEFF_ORIGIN_PROCEDURAL: u8 = 2;

pub(crate) const BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS: u8 = 0;
pub(crate) const BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP: u8 = 1;
pub(crate) const BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW: u8 = 2;
pub(crate) const BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH: u8 = 3;
/// A window whose origin is a real matrix carries no procedural kind.
pub(crate) const BWD_COEFF_PROCEDURAL_NONE: u8 = 0xff;
/// Procedural kinds the format admits.
pub(crate) const BWD_COEFF_PROCEDURAL_KINDS: usize = 4;

/// First target depth published by the fold prologue.
pub(crate) const BWD_COEFF_PUBLISH_TARGET_DEPTH: u8 = 3;

/// D0..D3: the bounded lazy-fold depths the JAOT prologue materializes over.
/// Equal to [`BWD_COEFF_PUBLISH_TARGET_DEPTH`] by construction — asserted in the
/// `const` block below, which is what bounds the round-to-depth map
/// [`seg_lower::bwd_coeff_fold_depth`](super::seg_lower::bwd_coeff_fold_depth).
pub(crate) const BWD_COEFF_MAX_FOLD_DEPTH: u8 = 3;

const _: () = {
    use crate::upstream::VirtualSetupKind::*;
    assert!(BWD_COEFF_PROCEDURAL_KINDS == KIND_ORDER.len());
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS as usize],
        RangeCheck16Bits
    ));
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP as usize],
        RangeCheckTimestamp
    ));
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW as usize],
        InitsAndTeardownsLow
    ));
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH as usize],
        InitsAndTeardownsHigh
    ));
    assert!(BWD_COEFF_PROCEDURAL_NONE as usize >= BWD_COEFF_PROCEDURAL_KINDS);
    assert!(BWD_COEFF_MAX_FOLD_DEPTH == BWD_COEFF_PUBLISH_TARGET_DEPTH);
};

// ── Address table ────────────────────────────────────────────────────────────

/// One addressing slot: a backing's base pointer and its column stride, plus the
/// two facts that belong to the BACKING rather than to a source — which kind of
/// leaves it holds and, when it holds none, the procedural kind that synthesizes
/// them.
///
/// Sources and destinations index the same table. A destination slot's `base`
/// includes the round offset, so the table is rebuilt per launch.
///
/// A slot is keyed by BACKING, never by a run of referenced columns. That is what
/// keeps the count proportional to how many matrices a layer touches rather than
/// to how the artifact groups its columns: two sources reading the same matrix
/// share a slot whatever their column numbers, and a source whose fold buffer is
/// packed differently from its matrix just names a different slot on its other
/// lane.
///
/// `log2_stride` is in elements of the lane's requested type. A raw
/// column stride is the poly length and a fold region stride is `2 *
/// size_after_one_fold`.
///
/// Every backing is LSB-dense at its own depth: a column holds the target-depth
/// value of logical index `u = 2 * row + b` at `u`, so a row's two endpoints are
/// adjacent and the `2^delta` leaves a depth-`delta` fold consumes sit adjacently
/// at `(u << delta) + q`.
///
/// `origin` is the BACKING field, not the width of the values read through the
/// slot: a continuation program folds a base matrix into E4, and operand width
/// comes from the term class.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct BwdSegAddrSlot {
    pub base: *const u8,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: u8,
    pub reserved: [u8; 5],
}

const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSegAddrSlot>() == 16);
    assert!(align_of::<BwdSegAddrSlot>() == 8);
    assert!(offset_of!(BwdSegAddrSlot, base) == 0);
    assert!(offset_of!(BwdSegAddrSlot, log2_stride) == 8);
    assert!(offset_of!(BwdSegAddrSlot, origin) == 9);
    assert!(offset_of!(BwdSegAddrSlot, procedural_kind) == 10);
    assert!(offset_of!(BwdSegAddrSlot, reserved) == 11);
};

/// One addressing LANE: `slot:6 << 7 | column:7`.
///
/// The split is the WIRE's own ([`MAX_SOURCE_WINDOWS`] `= 64` slots,
/// [`SOURCE_WINDOW_COLUMNS`] `= 128` columns), so the descriptor table holds
/// exactly what six bits address and a slot covers exactly what seven bits do —
/// 64 x 128 = 8,192 addressable columns, against the 1,012 blake2's widest
/// backward layer references.
pub(crate) const BWD_SEG_ADDR_COLUMN_BITS: u32 = 7;
/// "This source has no destination this round."
pub(crate) const BWD_SEG_ADDR_NONE: u16 = u16::MAX;

/// Pack a `(slot, column)` pair into a lane, or `None` if either is out of range.
pub(crate) fn bwd_seg_lane(slot: usize, column: usize) -> Option<u16> {
    if slot >= BWD_SEG_ADDR_SLOTS || column >= SOURCE_WINDOW_COLUMNS {
        return None;
    }
    Some(((slot << BWD_SEG_ADDR_COLUMN_BITS) | column) as u16)
}

/// The slot a lane names. Callers must not pass [`BWD_SEG_ADDR_NONE`].
pub(crate) fn bwd_seg_lane_slot(lane: u16) -> usize {
    debug_assert_ne!(lane, BWD_SEG_ADDR_NONE);
    usize::from(lane >> BWD_SEG_ADDR_COLUMN_BITS)
}

const _: () = {
    assert!(SOURCE_WINDOW_COLUMNS == 1 << BWD_SEG_ADDR_COLUMN_BITS);
    // A live lane can never collide with the absence sentinel.
    assert!((BWD_SEG_ADDR_SLOTS << BWD_SEG_ADDR_COLUMN_BITS) <= BWD_SEG_ADDR_NONE as usize);
};

/// One entry of the per-launch source table: where a source is read from, and
/// how this round resolves it.
///
/// `class` describes source production and is independent from the lean term
/// class in `gpu_gkr_compiler::backward`.
#[repr(C, align(2))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BwdSegSourceRecord {
    /// READ address, as a lane into [`BwdSegDesc::slot`].
    pub src: u16,
    /// Destination address, in the same encoding, or
    /// [`BWD_SEG_ADDR_NONE`] when this source publishes nothing this round.
    pub cache: u16,
    /// This round's source class (see the struct doc).
    pub class: u8,
    /// This round's fold depth for this source (`target_depth - backing_depth`).
    /// Per SOURCE, not per slot: two artifact windows may read the same matrix at
    /// different depths.
    pub delta: u8,
}

const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSegSourceRecord>() == 6);
    assert!(align_of::<BwdSegSourceRecord>() == 2);
    assert!(offset_of!(BwdSegSourceRecord, src) == 0);
    assert!(offset_of!(BwdSegSourceRecord, cache) == 2);
    assert!(offset_of!(BwdSegSourceRecord, class) == 4);
    assert!(offset_of!(BwdSegSourceRecord, delta) == 5);
    // Both lanes are 13 bits of a u16, so both halves of the split must fit.
    assert!(BWD_SEG_ADDR_SLOTS <= MAX_SOURCE_WINDOWS);
    assert!(SOURCE_WINDOW_COLUMNS <= u8::MAX as usize + 1);
};

/// By-value `__grid_constant__` kernel argument.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct BwdSegDesc {
    /// The lean term stream, embedded by value. Warp `w` walks
    /// `program[list_offset[w]..list_offset[w + 1]]`.
    pub program: [u16; LEAN_DESCRIPTOR_PROGRAM_WORDS],
    /// `k + 1` word offsets into [`Self::program`]: entry `w` is warp `w`'s
    /// first word and `list_offset[k]` is the END of the stream. This is why the
    /// descriptor needs no separate program-length field.
    pub list_offset: [u16; BWD_SEG_MAX_K + 1],
    /// Term lists, i.e. warps in the block. `blockDim == 32 * k`.
    pub k: u16,
    /// Leading entries of [`Self::fold_source`] the prologue folds.
    pub num_foldable: u16,
    /// Source slots the prologue folds; warp `w` takes `w, w + k, ...`.
    pub fold_source: [u16; BWD_SEG_MAX_SOURCES],
    pub source: [BwdSegSourceRecord; BWD_SEG_MAX_SOURCES],
    /// Live source windows.
    pub slot: [BwdSegAddrSlot; BWD_SEG_ADDR_SLOTS],
    /// The per-thread `acc_c0` seed as a COEFFICIENT ID, or
    /// [`BWD_SEG_C_INIT_NONE`] when the layer has none.
    pub c_init_coeff: u32,
    /// Base-field scalars referenced by grouped terms.
    pub immediates: [u32; BWD_SEG_MAX_IMMEDIATES],
    /// Production factored-eq low table; high tables remain in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// Interleaved c0/c2 partials, two entries per warp row.
    pub contributions: *mut E4,
    pub eq_sizes: GkrEqSizes,
    /// Rows this launch evaluates.
    pub logical_rows: u32,
}

// The layout, pinned against the same literals `segmented_vm.cuh` will
// `static_assert`. A change to either struct fails one of the two builds.
const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSegDesc>() == 24_672);
    assert!(align_of::<BwdSegDesc>() == BWD_SEG_DESC_ALIGN);
    // The FINAL authority on the descriptor's shape.
    assert!(size_of::<BwdSegDesc>() <= BWD_SEG_DESC_CAP);
    assert!(offset_of!(BwdSegDesc, program) == 0);
    assert!(offset_of!(BwdSegDesc, list_offset) == 12_944);
    assert!(offset_of!(BwdSegDesc, k) == 12_978);
    assert!(offset_of!(BwdSegDesc, num_foldable) == 12_980);
    assert!(offset_of!(BwdSegDesc, fold_source) == 12_982);
    assert!(offset_of!(BwdSegDesc, source) == 15_126);
    // Two bytes of implicit padding precede the 8-byte-aligned slot array.
    assert!(offset_of!(BwdSegDesc, slot) == 21_560);
    assert!(offset_of!(BwdSegDesc, c_init_coeff) == 22_584);
    assert!(offset_of!(BwdSegDesc, immediates) == 22_588);
    assert!(offset_of!(BwdSegDesc, eq_low) == 24_640);
    assert!(offset_of!(BwdSegDesc, contributions) == 24_648);
    assert!(offset_of!(BwdSegDesc, eq_sizes) == 24_656);
    assert!(offset_of!(BwdSegDesc, logical_rows) == 24_668);
    // The program stream starts on a 16-byte boundary and can be buffered
    // through wide loads.
    assert!(offset_of!(BwdSegDesc, program) % BWD_SEG_DESC_ALIGN == 0);
    assert!(size_of::<BwdSegDesc>().is_multiple_of(BWD_SEG_DESC_ALIGN));
};
