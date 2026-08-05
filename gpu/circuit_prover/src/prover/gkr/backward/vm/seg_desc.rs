//! The SEGMENTED lean VM's by-value launch descriptors (segmented-lean-VM
//! design §3, §5, §7).
//!
//! THIS FILE IS ONE HALF OF AN ABI. Its CUDA half is
//! `native/prover/gkr/backward/segmented_vm.cuh`, which carries the same field
//! offsets under `static_assert`. Neither half may move without the other in the
//! same commit. Three separate mechanisms cover the three drift directions:
//!
//!   1. **Rust-side drift is a BUILD failure.** The `const _: () = assert!(...)`
//!      blocks below tie every literal to its authority in `gpu_gkr_compiler`.
//!   2. **CUDA-side STRUCT drift is a BUILD failure too.** The `.cuh`'s
//!      `static_assert`s on every field offset and size run under nvcc during
//!      `cargo check` — but they are CUDA-vs-CUDA, not CUDA-vs-Rust.
//!   3. **CUDA-side CONSTANT drift is a TEST failure only.**
//!      [`seg_abi_tests`](super::seg_abi_tests)'s header-text matchers read
//!      `segmented_vm.cuh` and compare each mirrored literal against the Rust
//!      value — and they are `#[cfg(test)]`, so `cargo check` alone does not run
//!      them. Do not skip them after editing the header.
//!
//! # What this lineage does NOT carry
//!
//! The absences relative to the retired cell-era descriptor are load-bearing:
//!
//!   * **No challenge pointer.** Fold challenges have exactly ONE authority, the
//!     `ab_gkr_main_layer_claim_point` `__constant__` symbol (the incumbent
//!     route), so `round_challenges` / `n_round_challenges` are gone.
//!   * **No `cell_budget`.** There is no cell file and no residency genome: the
//!     prologue folds sources into registers, the eval loop reads them.
//!   * **No `num_words`.** [`BwdSegDesc::list_offset`] carries the program
//!     length: `list_offset[k]` IS the end of the stream.
//!   * **The seed path DOES carry a coefficient recipe index** — see
//!     [`BwdSegDesc::c_init_coeff`]. It carried resolved limbs until production
//!     wiring showed the host has no value to resolve: the bank is filled on the
//!     device.
//!
//! [`BwdSegAddrSlot`] and the origin / procedural-kind / publication
//! constants below are the ONE thing the retired cell-era descriptor left behind:
//! they were shared by both lineages and were rehomed here verbatim — same field
//! order, same offsets (`procedural_kind` at 28), same numbering — when that
//! lineage was deleted. Their `BWD_COEFF_` prefix is kept precisely so the CUDA
//! half and the ABI matchers stay word-for-word comparable across the move.
//!
//! # The program stream
//!
//! `program` is the LEAN wire (`gpu_gkr_compiler::backward`): one fixed
//! 8-byte header-first record per term, `[class:3 @13 | coeff_idx:13 @0]` then
//! two source slots and a reserved word. It is embedded BY VALUE in the
//! `__grid_constant__` parameter; [`BwdSegProgPtrDesc`] is the spike-only A/B
//! twin that reads it from device memory instead (§5).

use core::mem::{align_of, size_of};

use gpu_gkr_compiler::backward::{
    CoefficientRecipeId, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES,
    LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES,
    MAX_BACKWARD_COEFFICIENT_RECIPES, MAX_BACKWARD_RECORDS, MAX_BACKWARD_SOURCES,
    MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS, PUBLISH_TARGET_DEPTH, SOURCE_NONE,
    SOURCE_WINDOW_COLUMNS,
};
use gpu_gkr_compiler::forward::source::KIND_ORDER;

use crate::primitives::field::E4;
use crate::primitives::utils::WARP_SIZE;
use crate::prover::gkr::backward::GkrEqSizes;

// ── Capacities and launch geometry ───────────────────────────────────────────

/// The by-value kernel-argument cap. `size_of::<BwdSegDesc>() <=
/// BWD_SEG_DESC_CAP` is the FINAL authority on the descriptor's shape.
pub(crate) const BWD_SEG_DESC_CAP: usize = 32_764;
/// Descriptor alignment. Load-bearing rather than cosmetic: it is what places
/// [`BwdSegDesc::program`] — the descriptor's FIRST field — on a 16-byte
/// boundary, which is the only reason the lean census's one-word round-up to
/// [`LEAN_DESCRIPTOR_PROGRAM_WORDS`] buys anything.
pub(crate) const BWD_SEG_DESC_ALIGN: usize = 16;

/// Warps a block may run, i.e. the largest legal `K` of the round-robin term
/// split. One warp per term list, `blockDim = 32 * k`, so `K` tops out exactly
/// where the CUDA block does.
pub(crate) const BWD_SEG_MAX_K: usize = 32;
/// The CUDA hardware maximum block size, which is what caps [`BWD_SEG_MAX_K`].
pub(crate) const BWD_SEG_MAX_THREADS_PER_BLOCK: usize = 1_024;

/// Slots in this lineage's OWN `__constant__` coefficient bank
/// (`ab_gkr_bwd_seg_coeff_bank`, declared on the CUDA side in Task 7). No
/// `backward::flat` symbol is involved.
///
/// **RR ruling 2026-07-27: the two reserved literal ids are MATERIALIZED at the
/// bank head** — `bank[0] = ONE`, `bank[1] = NEG_ONE`, banked recipes from index
/// [`CoefficientRecipeId::RESERVED`] on — so the kernel resolves every
/// coefficient with ONE uniform `bank[coeff_idx]` load: no ±ONE fast path, no
/// branch, no offset subtraction. The census is why: 149 of 15,860 terms carry
/// `+1` and none carries `−1`, so a per-term branch to save 0.94% of the e4
/// multiplies is a net loss. Host lowering (Task 6) owns the materialization;
/// wire coefficient ids are reserved-INCLUSIVE and the kernel indexes raw.
///
/// Sized from the census (`1,138` recipes `+ 2` literals `= 1,140`), rounded up
/// so the bank is exactly 18 KiB of the 64 KB per-module `__constant__` budget —
/// 12 slots of slack, which [`seg_abi_tests`](super::seg_abi_tests) prints.
pub(crate) const BWD_SEG_CONST_BANK: usize = 1_152;

/// [`BwdSegDesc::c_init_coeff`] for a layer with no `acc_c0` seed.
///
/// A sentinel is unavoidable here: `0` is `CoefficientRecipeId::ONE`, a perfectly
/// legal seed. `u32::MAX` is chosen over the thirteen-bit id space's first unused
/// value so that a byte-level truncation cannot turn absence into a live id.
pub(crate) const BWD_SEG_C_INIT_NONE: u32 = u32::MAX;

/// Descriptor CAPACITY for source windows — deliberately NOT
/// [`in_scope::MAX_SOURCE_WINDOWS_USED`], which is a corpus MEASUREMENT.
///
/// The two are different kinds of fact and conflating them cost a circuit: the
/// array used to be sized by the measurement (17, the observed artifact-level max
/// for blake2 L0 R0), so when the binder's re-windowing split that layer's 17
/// artifact windows into 18 production windows, lowering REJECTED a circuit that
/// the format has room for four times over. An observed number belongs in a
/// census; a capacity belongs here.
///
/// Sized generously because a window is cheap: 32 bytes, so 128 of them are 4 KiB
/// of a descriptor with ~6 KiB of headroom under [`BWD_SEG_DESC_CAP`], which stays
/// the final authority.
///
/// [`MAX_SOURCE_WINDOWS`] `== 64` is NOT the ceiling here, and treating it as one
/// was the same conflation one level down. That constant is the WIRE's
/// `source_window:6` field, which bounds the windows an ARTIFACT may name; these
/// windows are the binder's re-partition of those, they live only in this
/// descriptor, and the program stream never re-encodes them. Their real ceiling is
/// [`BwdSegSourceRecord::window`], a byte.
///
/// 128 because production storage splits one artifact window into as many pieces
/// as it has differently-strided backings, and that is a property of storage, not
/// of the artifact: blake2 L0 Ext's 13 artifact windows need 115. The split itself
/// is free — each piece is a pointer and a stride — so the only thing that ever
/// had to grow is this number.
pub(crate) const BWD_SEG_ADDR_SLOTS: usize = 64;
const _: () = assert!(BWD_SEG_ADDR_SLOTS == MAX_SOURCE_WINDOWS);

/// [`BwdSegDesc::output`]: the incumbent per-row ACCUMULATOR layout — `2 *
/// logical_rows` entries, consumed by the separate reduction + round-update tail.
/// The default, and what the bench's per-row CPU oracle compares against.
pub(crate) const BWD_SEG_OUTPUT_ROWS: u32 = 0;
/// [`BwdSegDesc::output`]: ONE `(c0, c2)` pair per block — per 32-row tile — at
/// the incumbent warp-partial layout (`partials[i * 2]`, `[i * 2 + 1]`), consumed
/// directly by `ab_gkr_backward_dual_finalize_from_partials_e4_kernel`.
///
/// The kernel keeps the row-axis reduction instead of handing 32x the bytes to a
/// separate one: it costs one 5-step `shfl_xor` per accumulator in warp 0 only,
/// and no shared memory. Values are unchanged — field addition is exact and
/// associative, so the pair is the bit-identical sum of the rows it replaces.
pub(crate) const BWD_SEG_OUTPUT_PARTIALS: u32 = 1;

/// Fold-weight bank shape (spec §4.1): slots hold only q >= 1 (the q = 0
/// coefficient is the difference form's implicit 1), packed per delta.
pub(crate) const BWD_SEG_FOLD_WEIGHT_SLOTS: usize = 11;
pub(crate) const BWD_SEG_FOLD_WEIGHT_BASE_D1: usize = 0;
pub(crate) const BWD_SEG_FOLD_WEIGHT_BASE_D2: usize = 1;
pub(crate) const BWD_SEG_FOLD_WEIGHT_BASE_D3: usize = 4;
const _: () = assert!(BWD_SEG_FOLD_WEIGHT_BASE_D2 == BWD_SEG_FOLD_WEIGHT_BASE_D1 + 1);
const _: () = assert!(BWD_SEG_FOLD_WEIGHT_BASE_D3 == BWD_SEG_FOLD_WEIGHT_BASE_D2 + 3);
const _: () = assert!(BWD_SEG_FOLD_WEIGHT_SLOTS == BWD_SEG_FOLD_WEIGHT_BASE_D3 + 7);

/// Source-table slots the descriptor can hold: the census maximum of 1,062
/// rounded up to a multiple of 16 slots, which makes both source-indexed arrays
/// ([`BwdSegDesc::fold_source`] and [`BwdSegDesc::source`]) a whole number of
/// 16-byte lines.
pub(crate) const BWD_SEG_MAX_SOURCES: usize = 1_072;

/// Inline capacity of [`BwdSegDesc::immediates`] — the per-launch immediate table
/// grouped coefficients scale their shared core by (spec §4.5).
///
/// NOT a measurement: it is the WIRE cap `LEAN_MAX_IMMEDIATES`, mirrored here so
/// the descriptor can hold any table the encoder will ever emit. The mirror is a
/// build failure rather than a convention (asserted in the block below), and it
/// runs in this direction only: the GPU crate imports `gpu_gkr_compiler`, never the
/// reverse, so the ISA's constant stays the authority and this one the copy.
pub(crate) const BWD_SEG_MAX_IMMEDIATES: usize = 512;

const _: () = {
    assert!(BWD_SEG_DESC_CAP == KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(BWD_SEG_DESC_ALIGN == DESCRIPTOR_ALIGNMENT_BYTES);

    // One warp per list, and the block is the cap.
    assert!(BWD_SEG_MAX_K * WARP_SIZE as usize == BWD_SEG_MAX_THREADS_PER_BLOCK);
    assert!(BWD_SEG_MAX_THREADS_PER_BLOCK == 1_024);
    // `k` and every `list_offset` entry are u16.
    assert!(BWD_SEG_MAX_K <= u16::MAX as usize);
    assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS <= u16::MAX as usize);
    assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES == LEAN_DESCRIPTOR_PROGRAM_WORDS * size_of::<u16>());
    // `record_count` is a u16 as well, and it counts RECORDS — terms plus the group
    // headers grouping adds — so the census maximum it must hold is `MAX_RECORDS`.
    assert!(MAX_BACKWARD_RECORDS <= u16::MAX as usize);

    // The immediate array is the WIRE cap exactly: not a byte more (an unearned
    // 4-byte slot rides every launch) and not a byte less (a table the encoder can
    // emit must fit). The mirror direction is GPU-imports-ISA.
    assert!(BWD_SEG_MAX_IMMEDIATES == LEAN_MAX_IMMEDIATES);
    // A live count rides the descriptor as a u16.
    assert!(BWD_SEG_MAX_IMMEDIATES <= u16::MAX as usize);

    // The bank covers every reserved-inclusive coefficient id the corpus can
    // name, stays inside the thirteen coefficient bits that name it, and fits the
    // per-module constant budget.
    assert!(BWD_SEG_CONST_BANK >= MAX_BACKWARD_COEFFICIENT_RECIPES + 2);
    assert!(
        MAX_BACKWARD_COEFFICIENT_RECIPES + 2
            == MAX_BACKWARD_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
    );
    assert!(BWD_SEG_CONST_BANK <= MAX_COEFFICIENT_ENCODINGS);
    assert!(BWD_SEG_CONST_BANK * size_of::<E4>() == 18 * 1_024);
    assert!(BWD_SEG_CONST_BANK * size_of::<E4>() <= 64 * 1_024);

    // The source capacity is the MEASUREMENT rounded up by strictly less than one
    // 16-slot quantum, so it cannot silently drift into headroom.
    assert!(BWD_SEG_MAX_SOURCES >= MAX_BACKWARD_SOURCES);
    assert!(BWD_SEG_MAX_SOURCES - MAX_BACKWARD_SOURCES < 16);
    assert!(BWD_SEG_MAX_SOURCES % 16 == 0);
    // A slot index rides the lean wire as a u16 whose 0xFFFF is the "no second
    // source" sentinel, so the capacity must stay strictly below it.
    assert!(BWD_SEG_MAX_SOURCES < SOURCE_NONE as usize);

    // The window struct's publication policy: publish on first physical access
    // iff `target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH`. Tied to `gpu_gkr_compiler`
    // so the rehoming out of the retired cell-era descriptor cannot have quietly
    // changed the threshold this lineage was measured under.
    assert!(BWD_COEFF_PUBLISH_TARGET_DEPTH == PUBLISH_TARGET_DEPTH);
};

// ── Source-window origin (§10.2) ─────────────────────────────────────────────
//
// Rehomed verbatim from the retired cell-era descriptor, together with
// [`BwdSegAddrSlot`] below: the two lineages shared this struct and these
// numbers, and the segmented executor still resolves a window through them.

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
/// A window whose origin is a real matrix carries no procedural kind. Zero would
/// alias [`BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS`], so the absent marker is
/// `0xff` and [`BwdSegAddrSlot::default`] uses it.
pub(crate) const BWD_COEFF_PROCEDURAL_NONE: u8 = 0xff;
/// Procedural kinds the format admits.
pub(crate) const BWD_COEFF_PROCEDURAL_KINDS: usize = 4;

/// §10.2's static materialization policy: publish on first physical access iff
/// `target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH`. One tunable constant, not
/// a scheduling decision or a genome.
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
    // §10.2's publication threshold is what bounds the resolver set: past it a
    // backing is at most one fold behind.
    assert!(BWD_COEFF_MAX_FOLD_DEPTH == BWD_COEFF_PUBLISH_TARGET_DEPTH);
};

// ── Address table ────────────────────────────────────────────────────────────

/// One addressing slot: a backing's base pointer and its column stride, plus the
/// two facts that belong to the BACKING rather than to a source — which kind of
/// leaves it holds and, when it holds none, the procedural kind that synthesizes
/// them.
///
/// Sources and destinations index the SAME table, exactly as the incumbent flat
/// path's `tables.bases` / `tables.log2_stride` do (`support/descriptors.cuh`): a
/// fold buffer is a base and a stride like any other backing. A destination
/// slot's `base` includes the round's slot offset within its region, which is why
/// a slot is per `(backing, round)` and the table is rebuilt per launch.
///
/// A slot is keyed by BACKING, never by a run of referenced columns. That is what
/// keeps the count proportional to how many matrices a layer touches rather than
/// to how the artifact groups its columns: two sources reading the same matrix
/// share a slot whatever their column numbers, and a source whose fold buffer is
/// packed differently from its matrix just names a different slot on its other
/// lane.
///
/// `log2_stride` is in ELEMENT units of whatever type the lane is read as — the
/// incumbent's convention. Every production stride is a power of two: a raw
/// column stride is the poly length and a fold region stride is `2 *
/// size_after_one_fold`.
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

impl Default for BwdSegAddrSlot {
    /// A dead slot. `procedural_kind` is [`BWD_COEFF_PROCEDURAL_NONE`], NOT
    /// zero — zero is a live kind.
    fn default() -> Self {
        Self {
            base: std::ptr::null(),
            log2_stride: 0,
            origin: BWD_COEFF_ORIGIN_READ_BASE,
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: [0; 5],
        }
    }
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

/// The column a lane names. Callers must not pass [`BWD_SEG_ADDR_NONE`].
pub(crate) fn bwd_seg_lane_column(lane: u16) -> usize {
    debug_assert_ne!(lane, BWD_SEG_ADDR_NONE);
    usize::from(lane) & (SOURCE_WINDOW_COLUMNS - 1)
}

const _: () = {
    assert!(SOURCE_WINDOW_COLUMNS == 1 << BWD_SEG_ADDR_COLUMN_BITS);
    // A live lane can never collide with the absence sentinel.
    assert!((BWD_SEG_ADDR_SLOTS << BWD_SEG_ADDR_COLUMN_BITS) <= BWD_SEG_ADDR_NONE as usize);
};

// ── Source table ─────────────────────────────────────────────────────────────

/// One entry of the per-launch source table: where a source is read from, and
/// how this round resolves it.
///
/// `class` is the per-`(source, round)` SOURCE class assigned by Task 6's round
/// lowering — `BfDirect = 0`, `BfInlineD1 = 1`, `BfInlineD2 = 2`, `E4Direct = 3`,
/// `ProceduralInline = 4` — and is NOT the lean wire's three-bit TERM class
/// (`gpu_gkr_compiler::backward::LEAN_CLASS_SHIFT`). The two are independent
/// axes: the term class fixes the projection and arity of an operation, the
/// source class fixes how the operand behind a slot is produced. The enum with
/// those discriminants is Task 6's, so it is the authority; this field is the
/// byte it travels in.
///
/// `align(4)` mirrors the CUDA `alignas(4)`: it STATES the record's own requirement
/// that a slot address be 0 mod 4, the precondition for ever reading the record as
/// one 32-bit word. It used to also MOVE the array — `list_offset` is 33 u16s, which
/// left the descriptor tail at 2 mod 4 — but [`BwdSegDesc::num_immediates`] is the
/// fifth u16 of the count block and brings the tail back to 0 mod 4, so both arrays
/// are now naturally aligned and the attribute costs nothing. It stays so the
/// record's alignment is a declared property rather than an accident of whatever
/// precedes it. On CUDA 13.3 the alignment ALONE changes no SASS and no register
/// count — the CUDA half carries that measurement.
#[repr(C, align(2))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BwdSegSourceRecord {
    /// READ address, as a lane into [`BwdSegDesc::slot`].
    pub src: u16,
    /// DESTINATION address, same table and same encoding, or
    /// [`BWD_SEG_ADDR_NONE`] when this source publishes nothing this round.
    /// "Does this source publish" is this field, which is why no `materialize`
    /// flag survives.
    pub cache: u16,
    /// This round's source class (see the struct doc).
    pub class: u8,
    /// This round's fold depth for this source (`target_depth - backing_depth`).
    /// Per SOURCE, not per slot: two artifact windows may read the same matrix at
    /// different depths.
    pub delta: u8,
}

impl Default for BwdSegSourceRecord {
    /// A dead record: both lanes absent, so a reader past `num_sources` cannot
    /// resolve an address at all. `src` is the sentinel rather than zero, which
    /// would name slot 0 column 0 — a live address.
    fn default() -> Self {
        Self {
            src: BWD_SEG_ADDR_NONE,
            cache: BWD_SEG_ADDR_NONE,
            class: 0,
            delta: 0,
        }
    }
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

// ── The inline-program descriptor ────────────────────────────────────────────

/// The complete by-value launch descriptor, passed as a single
/// `__grid_constant__` kernel parameter (§3).
///
/// Field order is chosen so `program` sits at offset 0 — 16-byte aligned by the
/// descriptor's own alignment, at no cost in padding — and so the launch tail's
/// pointers land naturally aligned after the arrays.
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
    /// Lean RECORDS across all `k` lists, so
    /// `list_offset[k] == LEAN_WORDS_PER_TERM * record_count`.
    ///
    /// Records, not terms: the grouped wire (spec §4.4) spends one fixed-width
    /// HEADER record per group on top of its member terms, so the two counts
    /// diverge and only the record count multiplies out to the stream length. An
    /// ungrouped program has no headers and the two coincide, which is why the
    /// field's VALUE did not change when it was renamed.
    pub record_count: u16,
    /// Live entries of [`Self::source`].
    pub num_sources: u16,
    /// Leading entries of [`Self::fold_source`] the prologue folds.
    pub num_foldable: u16,
    /// Live entries of [`Self::immediates`]. Zero for an ungrouped program.
    pub num_immediates: u16,
    /// Source slots the JAOT prologue folds, in FOLD order: warp `w` takes
    /// `s = w, w + k, w + 2k, …`. The order is a performance contract (§7) — the
    /// sources the eval loop touches EARLIEST are folded LAST, so they are the
    /// warmest in L1 when eval starts.
    pub fold_source: [u16; BWD_SEG_MAX_SOURCES],
    /// The per-launch source table. Entries at and past [`Self::num_sources`]
    /// are zero-filled and never read.
    pub source: [BwdSegSourceRecord; BWD_SEG_MAX_SOURCES],
    /// Live source windows, IMPORTED from the cell-era descriptor rather than
    /// forked (`procedural_kind` at offset 28 included), so both lineages share
    /// one window layout and one publication policy
    /// ([`BWD_COEFF_PUBLISH_TARGET_DEPTH`]).
    pub slot: [BwdSegAddrSlot; BWD_SEG_ADDR_SLOTS],
    /// The per-thread `acc_c0` seed as a COEFFICIENT ID, or
    /// [`BWD_SEG_C_INIT_NONE`] when the layer has none.
    ///
    /// It used to be resolved E4 limbs, and that could not survive production. The
    /// seed's value is `bank[id]`, the bank is filled ON THE DEVICE from challenges
    /// the transcript squeezes there ([`super::seg_coeff_eval`]), and this
    /// descriptor is a by-value kernel argument built on the host at scheduling
    /// time — so the host has no value to put here. The id it does have, and the
    /// device already holds the bank the executors index for every other
    /// coefficient, so the seed resolves through the same accessor.
    ///
    /// Zero is a LIVE id (`CoefficientRecipeId::ONE`), which is why absence needs a
    /// sentinel rather than the old all-zero limbs.
    pub c_init_coeff: u32,
    /// Padding that keeps this field's 16-byte footprint, and with it the
    /// descriptor's whole tail layout, unchanged across the limbs-to-id move: the
    /// note on [`Self::immediates`] is what depends on it. Never read by the kernel.
    pub c_init_pad: [u32; 3],
    /// This launch's immediate table (spec §4.5): the BASE-field scalars a grouped
    /// term multiplies its group's shared core coefficient by, in the encoder's
    /// ascending-deduplicated order, as raw Montgomery-form limbs.
    ///
    /// Indexed by a member record's `ImmediateId`, which rides the wire in the
    /// member's coefficient field. Entries at and past [`Self::num_immediates`] are
    /// zero-filled and never read; the `±1` immediates are wire-level reserved ids
    /// and consume no slot here.
    ///
    /// Placed after the 16-byte `c_init` block so the descriptor's pointer tail
    /// keeps its natural alignment: `[u32; 512]` is 2 KiB, a whole number of
    /// 16-byte quanta, so every following offset shifts by exactly that.
    pub immediates: [u32; BWD_SEG_MAX_IMMEDIATES],
    /// Evaluated E4 coefficients for the `ptr` loader specialization. The
    /// `const` loader reads this lineage's `__constant__` bank and ignores it.
    /// Reserved-inclusive either way: `[ONE, NEG_ONE, recipes…]`.
    pub coefficients: *const E4,
    /// Production factored-eq low table; high tables remain in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// `2 * logical_rows` entries: `eq * acc_c0` in `[0, logical_rows)` and
    /// `eq * acc_c2` in `[logical_rows, 2 * logical_rows)`.
    pub contributions: *mut E4,
    pub eq_sizes: GkrEqSizes,
    /// Bank entries, reserved literals included.
    pub n_coefficients: u32,
    /// Rows this launch evaluates. Also the contribution half-stride: the
    /// incumbent `acc_size`.
    pub logical_rows: u32,
    /// What the epilogue writes: [`BWD_SEG_OUTPUT_ROWS`] (per-row contributions)
    /// or [`BWD_SEG_OUTPUT_PARTIALS`] (one warp-partial pair per 32-row tile).
    /// Occupies the word that used to be explicit trailing padding, so the
    /// descriptor's size and every field offset are unchanged.
    pub output: u32,
}

impl BwdSegDesc {
    /// An empty descriptor: null pointers, no windows, no program.
    ///
    /// `[u16; LEAN_DESCRIPTOR_PROGRAM_WORDS]` is far past the arity `Default` is
    /// derived for, so this is written out rather than derived.
    /// ABI-GATE ONLY, and the `cfg_attr` says so rather than a blanket `allow`:
    /// under `cfg(test)` there is no suppression, so if
    /// [`seg_abi_tests`](super::seg_abi_tests) ever stops calling this, it goes
    /// back to warning instead of sitting here forever. Production lowering builds
    /// a descriptor field-by-field from a real round binding
    /// ([`seg_lower::lower_bwd_seg`](super::seg_lower::lower_bwd_seg)) and never
    /// starts from a zeroed one.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn empty() -> Self {
        Self {
            program: [0; LEAN_DESCRIPTOR_PROGRAM_WORDS],
            list_offset: [0; BWD_SEG_MAX_K + 1],
            k: 0,
            record_count: 0,
            num_sources: 0,
            num_foldable: 0,
            num_immediates: 0,
            fold_source: [0; BWD_SEG_MAX_SOURCES],
            source: [BwdSegSourceRecord::default(); BWD_SEG_MAX_SOURCES],
            slot: [BwdSegAddrSlot::default(); BWD_SEG_ADDR_SLOTS],
            c_init_coeff: BWD_SEG_C_INIT_NONE,
            c_init_pad: [0; 3],
            immediates: [0; BWD_SEG_MAX_IMMEDIATES],
            coefficients: std::ptr::null(),
            eq_low: std::ptr::null(),
            contributions: std::ptr::null_mut(),
            eq_sizes: GkrEqSizes::zeroed(),
            n_coefficients: 0,
            logical_rows: 0,
            output: BWD_SEG_OUTPUT_ROWS,
        }
    }
}

// ── The device-program A/B twin (§5) ─────────────────────────────────────────

/// [`BwdSegDesc`] field-for-field, with the inline `program` array REPLACED by a
/// device pointer and its length.
///
/// Dropping the array is the whole point: keeping it and merely not reading it
/// would leave 17,248 bytes resident in every launch's parameter space and
/// measure nothing. Inline fit proves the ABI is feasible, not that `K` warps
/// streaming a 17 KiB param-space program alongside an 18 KiB `__constant__`
/// coefficient bank wins on constant-cache behaviour — this twin is the one
/// comparison point that answers it.
///
/// Lowering leaves `program` NULL; the harness uploads
/// `BwdSegSetup::program_words` to a device buffer and patches the pointer into
/// its host copy of the descriptor before launch — the descriptor is a by-value
/// kernel parameter, so patching the host copy IS the mechanism. Ownership of
/// the staging buffer is the caller's, exactly as for the coefficient bank.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct BwdSegProgPtrDesc {
    /// Device-resident lean term stream, `program_words` u16 words long.
    pub program: *const u16,
    pub program_words: u32,
    /// See [`BwdSegDesc::list_offset`]; offsets index the DEVICE stream here.
    pub list_offset: [u16; BWD_SEG_MAX_K + 1],
    pub k: u16,
    /// See [`BwdSegDesc::record_count`]: RECORDS, terms plus group headers.
    pub record_count: u16,
    pub num_sources: u16,
    pub num_foldable: u16,
    /// See [`BwdSegDesc::num_immediates`].
    pub num_immediates: u16,
    pub fold_source: [u16; BWD_SEG_MAX_SOURCES],
    pub source: [BwdSegSourceRecord; BWD_SEG_MAX_SOURCES],
    pub slot: [BwdSegAddrSlot; BWD_SEG_ADDR_SLOTS],
    /// See [`BwdSegDesc::c_init_coeff`].
    pub c_init_coeff: u32,
    /// See [`BwdSegDesc::c_init_pad`].
    pub c_init_pad: [u32; 3],
    /// See [`BwdSegDesc::immediates`]. Inline in BOTH twins: only the PROGRAM moves
    /// to device memory in this A/B, so the immediate table stays by value and the
    /// comparison isolates the program's residency.
    pub immediates: [u32; BWD_SEG_MAX_IMMEDIATES],
    pub coefficients: *const E4,
    pub eq_low: *const E4,
    pub contributions: *mut E4,
    pub eq_sizes: GkrEqSizes,
    pub n_coefficients: u32,
    pub logical_rows: u32,
    /// See [`BwdSegDesc::output`].
    pub output: u32,
    /// Two words rather than three now that `output` took one: the head is 12
    /// bytes here instead of 17,248, so the tail lands elsewhere modulo 16.
    /// Never read by the kernel.
    pub pad: [u32; 2],
}

impl BwdSegProgPtrDesc {
    /// An empty descriptor; ABI-gate only, for the same reason and under the same
    /// `cfg_attr` as [`BwdSegDesc::empty`].
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn empty() -> Self {
        Self {
            program: std::ptr::null(),
            program_words: 0,
            list_offset: [0; BWD_SEG_MAX_K + 1],
            k: 0,
            record_count: 0,
            num_sources: 0,
            num_foldable: 0,
            num_immediates: 0,
            fold_source: [0; BWD_SEG_MAX_SOURCES],
            source: [BwdSegSourceRecord::default(); BWD_SEG_MAX_SOURCES],
            slot: [BwdSegAddrSlot::default(); BWD_SEG_ADDR_SLOTS],
            c_init_coeff: BWD_SEG_C_INIT_NONE,
            c_init_pad: [0; 3],
            immediates: [0; BWD_SEG_MAX_IMMEDIATES],
            coefficients: std::ptr::null(),
            eq_low: std::ptr::null(),
            contributions: std::ptr::null_mut(),
            eq_sizes: GkrEqSizes::zeroed(),
            n_coefficients: 0,
            logical_rows: 0,
            output: BWD_SEG_OUTPUT_ROWS,
            pad: [0; 2],
        }
    }
}

// ── Kernel-argument budget ───────────────────────────────────────────────────

/// Param-space bytes a formal list occupies under the C parameter-packing rules
/// both nvcc and this side follow: each formal starts at the next multiple of its
/// own alignment.
///
/// `formals` is `(size, align)` in DECLARATION order.
///
/// ABI-GATE ONLY: no launch reads this. The launcher hands nvcc a descriptor and
/// nvcc does the packing, so the budget is a CLAIM about the launch ABI that only
/// [`seg_abi_tests::seg_kernel_argument_bytes_are_pinned_for_both_launcher_shapes`](super::seg_abi_tests)
/// can check. `cfg_attr(not(test), ...)` rather than a blanket `allow` so losing
/// that test brings the warning back.
#[cfg_attr(not(test), allow(dead_code))]
const fn kernel_argument_bytes(formals: &[(usize, usize)]) -> usize {
    let mut total: usize = 0;
    let mut index = 0;
    while index < formals.len() {
        let (size, align) = formals[index];
        total = total.next_multiple_of(align) + size;
        index += 1;
    }
    total
}

/// Total kernel-argument bytes one launch of the inline-program family consumes.
///
/// The ASSUMED formal-parameter list is `(BwdSegDesc desc)` and nothing else —
/// everything else a launch needs is out of band: fold challenges in the
/// `ab_gkr_main_layer_claim_point` `__constant__` symbol, the coefficient bank in
/// this lineage's own `__constant__` symbol (or, under the `ptr` loader, behind
/// [`BwdSegDesc::coefficients`]), the epilogue plane in DYNAMIC shared memory,
/// and `k` in [`BwdSegDesc::k`]. If a launcher signature grows a formal, add it
/// here and update the pin in [`seg_abi_tests`](super::seg_abi_tests) in the same
/// commit.
///
/// ABI-GATE ONLY — see [`kernel_argument_bytes`].
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) const BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES: usize =
    kernel_argument_bytes(&[(size_of::<BwdSegDesc>(), align_of::<BwdSegDesc>())]);

/// Total kernel-argument bytes one launch of the progptr family consumes; the
/// assumed formal list is `(BwdSegProgPtrDesc desc)`. ABI-GATE ONLY; see
/// [`BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES`].
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) const BWD_SEG_PROGPTR_KERNEL_ARGUMENT_BYTES: usize = kernel_argument_bytes(&[(
    size_of::<BwdSegProgPtrDesc>(),
    align_of::<BwdSegProgPtrDesc>(),
)]);

// The layout, pinned against the same literals `segmented_vm.cuh` will
// `static_assert`. A change to either struct fails one of the two builds.
const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSegDesc>() == 29_040);
    assert!(align_of::<BwdSegDesc>() == BWD_SEG_DESC_ALIGN);
    // The FINAL authority on the descriptor's shape.
    assert!(size_of::<BwdSegDesc>() <= BWD_SEG_DESC_CAP);
    assert!(offset_of!(BwdSegDesc, program) == 0);
    assert!(offset_of!(BwdSegDesc, list_offset) == 17_248);
    assert!(offset_of!(BwdSegDesc, k) == 17_314);
    assert!(offset_of!(BwdSegDesc, record_count) == 17_316);
    assert!(offset_of!(BwdSegDesc, num_sources) == 17_318);
    assert!(offset_of!(BwdSegDesc, num_foldable) == 17_320);
    assert!(offset_of!(BwdSegDesc, num_immediates) == 17_322);
    assert!(offset_of!(BwdSegDesc, fold_source) == 17_324);
    assert!(offset_of!(BwdSegDesc, source) == 19_468);
    // Four bytes of implicit padding precede `window`: the source array is
    // 4-byte-aligned and the window array is 8-byte-aligned. nvcc inserts the
    // same gap by the same rule, and the offsets on both sides are asserted, so
    // it needs no explicit field.
    assert!(offset_of!(BwdSegDesc, slot) == 25_904);
    assert!(offset_of!(BwdSegDesc, c_init_coeff) == 26_928);
    assert!(offset_of!(BwdSegDesc, immediates) == 26_944);
    assert!(offset_of!(BwdSegDesc, coefficients) == 28_992);
    assert!(offset_of!(BwdSegDesc, eq_low) == 29_000);
    assert!(offset_of!(BwdSegDesc, contributions) == 29_008);
    assert!(offset_of!(BwdSegDesc, eq_sizes) == 29_016);
    assert!(offset_of!(BwdSegDesc, n_coefficients) == 29_028);
    assert!(offset_of!(BwdSegDesc, logical_rows) == 29_032);
    assert!(offset_of!(BwdSegDesc, output) == 29_036);
    // The program stream starts on a 16-byte boundary and can be buffered
    // through wide loads.
    assert!(offset_of!(BwdSegDesc, program) % BWD_SEG_DESC_ALIGN == 0);
    // `pad` is the tail, and it is what makes the size a whole number of
    // alignment quanta.
    assert!(offset_of!(BwdSegDesc, output) + size_of::<u32>() == size_of::<BwdSegDesc>());
    assert!(size_of::<BwdSegDesc>() % BWD_SEG_DESC_ALIGN == 0);

    assert!(size_of::<BwdSegProgPtrDesc>() == 11_808);
    assert!(align_of::<BwdSegProgPtrDesc>() == BWD_SEG_DESC_ALIGN);
    assert!(size_of::<BwdSegProgPtrDesc>() <= BWD_SEG_DESC_CAP);
    assert!(offset_of!(BwdSegProgPtrDesc, program) == 0);
    assert!(offset_of!(BwdSegProgPtrDesc, program_words) == 8);
    assert!(offset_of!(BwdSegProgPtrDesc, list_offset) == 12);
    assert!(offset_of!(BwdSegProgPtrDesc, k) == 78);
    assert!(offset_of!(BwdSegProgPtrDesc, record_count) == 80);
    assert!(offset_of!(BwdSegProgPtrDesc, num_sources) == 82);
    assert!(offset_of!(BwdSegProgPtrDesc, num_foldable) == 84);
    assert!(offset_of!(BwdSegProgPtrDesc, num_immediates) == 86);
    assert!(offset_of!(BwdSegProgPtrDesc, fold_source) == 88);
    assert!(offset_of!(BwdSegProgPtrDesc, source) == 2_232);
    // No gap here: with a 4-byte-aligned record the progptr `source` array ends
    // exactly at `window`.
    assert!(offset_of!(BwdSegProgPtrDesc, slot) == 8_664);
    assert!(offset_of!(BwdSegProgPtrDesc, c_init_coeff) == 9_688);
    assert!(offset_of!(BwdSegProgPtrDesc, immediates) == 9_704);
    assert!(offset_of!(BwdSegProgPtrDesc, coefficients) == 11_752);
    assert!(offset_of!(BwdSegProgPtrDesc, eq_low) == 11_760);
    assert!(offset_of!(BwdSegProgPtrDesc, contributions) == 11_768);
    assert!(offset_of!(BwdSegProgPtrDesc, eq_sizes) == 11_776);
    assert!(offset_of!(BwdSegProgPtrDesc, n_coefficients) == 11_788);
    assert!(offset_of!(BwdSegProgPtrDesc, logical_rows) == 11_792);
    assert!(offset_of!(BwdSegProgPtrDesc, output) == 11_796);
    assert!(offset_of!(BwdSegProgPtrDesc, pad) == 11_800);
    assert!(
        offset_of!(BwdSegProgPtrDesc, pad) + size_of::<[u32; 2]>()
            == size_of::<BwdSegProgPtrDesc>()
    );
    assert!(size_of::<BwdSegProgPtrDesc>() % BWD_SEG_DESC_ALIGN == 0);
    // The A/B twin really drops the array rather than leaving it resident.
    assert!(
        size_of::<BwdSegDesc>() - size_of::<BwdSegProgPtrDesc>()
            >= LEAN_DESCRIPTOR_PROGRAM_BYTES - BWD_SEG_DESC_ALIGN
    );
};
