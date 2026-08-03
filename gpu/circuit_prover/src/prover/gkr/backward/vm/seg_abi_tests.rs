//! The Rust-side ABI gate for the SEGMENTED lean VM's launch descriptors.
//!
//! Since the cell-era lineage was retired this is the WHOLE Rust-side ABI gate for
//! the backward COEFFICIENT-ISA lineage: the two descriptors, the source record,
//! the source window, and every capacity and constant either side mirrors. (The
//! incumbent FLAT lineage — `backward::flat`, `continuation.cuh`, `compact/` — is
//! production and has its own guards; nothing here covers it.) The CUDA half —
//! `native/prover/gkr/backward/segmented_vm.cuh` — `static_assert`s every field
//! offset and both descriptor sizes against the literals below, so a CUDA-side
//! STRUCT edit is a build failure.
//!
//! The header-text matchers that catch a CUDA-only CONSTANT edit (the failure
//! direction neither compiler sees) are
//! [`seg_cuda_constants_match_the_rust_mirror`] and
//! [`seg_cuda_layout_asserts_match_the_rust_layout`]. Many of the header's
//! constants are layout-bearing and are therefore already pinned by its own
//! `static_assert`s; these are the ones that are NOT, and each is a silent wrong
//! answer rather than a build error:
//!
//!   * [`BWD_SEG_CONST_BANK`] sizes a `__constant__` symbol nothing on this side
//!     can see — a CUDA-side shrink would let the host's bank upload write past the
//!     symbol with no build error anywhere;
//!   * the five SOURCE-CLASS numbers, which the header pins only against its own
//!     restatements — their authority is Rust's [`SourceClass`] enum; and
//!   * the `BWD_COEFF_*` block REHOMED into `segmented_vm.cuh` when the cell-era
//!     header was deleted — the window ORIGIN values, the procedural kinds and the
//!     absent marker, the publication threshold, the lean header's bit widths, and
//!     the frozen opcode numbering. Their previous matcher died with
//!     `abi_tests.rs`; the window's field OFFSETS came back the same way, because
//!     the header's own asserts on them are CUDA-vs-CUDA and a consistent
//!     same-width field swap satisfies all of them.
//!
//! Either way the checks here pin EXACT numbers rather than bounds: an offset or a
//! size that moves is a silent Rust↔CUDA divergence.
//!
//! [`seg_desc`](super::seg_desc) already carries `const _: () = assert!(...)`
//! blocks for everything that can be const, which makes Rust-side drift a BUILD
//! failure. The tests below re-state the load-bearing ones so the failure is
//! READABLE, and add the ones that need a runtime value (`size_of` totals,
//! per-field accounting, `empty()` behaviour).

use std::mem::{align_of, offset_of, size_of};

use gkr_eval_isa::bwd::coeff::lean::{
    LEAN_CLASS_MASK, LEAN_CLASS_SHIFT, LEAN_COEFFICIENT_MASK, LEAN_COEFFICIENT_SHIFT,
    LEAN_CONT_OPCODES, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_GROUP_FLAG_MASK,
    LEAN_R0_OPCODES, LEAN_WORDS_PER_TERM, SOURCE_NONE,
};
use gkr_eval_isa::bwd::coeff::limits::{
    continuation_opcode, in_scope, r0_opcode, TermCategory, CONTINUATION_LIVE_OPCODES,
    DESCRIPTOR_ALIGNMENT_BYTES, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS,
    KERNEL_ARGUMENT_CEILING_BYTES, LEAN_CONT_GROUP_HEADER_CLASS, LEAN_DESCRIPTOR_PROGRAM_BYTES,
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_REALIZED_PROGRAM_WORDS, MAX_COEFFICIENT_ENCODINGS,
    PUBLISH_TARGET_DEPTH, R0_LIVE_OPCODES,
};
use gkr_eval_isa::bwd::coeff::model::{CoefficientRecipeId, ImmediateId};

use super::seg_coeff_eval::{
    SegCoeffEvalDesc, SegCoeffMonomial, SegCoeffRecipe, BWD_SEG_CHALLENGE_ABSENT,
    BWD_SEG_CHALLENGE_CLAIM_BATCHING, BWD_SEG_CHALLENGE_CONSTRAINT_AGGREGATION,
    BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE, BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE,
    BWD_SEG_CHALLENGE_PERM_ADDITIVE, BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE,
    BWD_SEG_CHALLENGE_SLOTS, BWD_SEG_COEFF_MAX_MONOMIALS,
};
use super::seg_desc::BWD_SEG_C_INIT_NONE;
use super::seg_desc::{
    BwdCoeffSourceWindow, BwdSegDesc, BwdSegProgPtrDesc, BwdSegSourceRecord,
    BWD_COEFF_MAX_FOLD_DEPTH, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH,
    BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW, BWD_COEFF_PROCEDURAL_NONE,
    BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS, BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP,
    BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_SEG_CONST_BANK, BWD_SEG_DESC_ALIGN, BWD_SEG_DESC_CAP,
    BWD_SEG_SOURCE_WINDOW_CAP,
    BWD_SEG_FOLD_WEIGHT_BASE_D1, BWD_SEG_FOLD_WEIGHT_BASE_D2, BWD_SEG_FOLD_WEIGHT_BASE_D3,
    BWD_SEG_FOLD_WEIGHT_SLOTS, BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES, BWD_SEG_MAX_IMMEDIATES,
    BWD_SEG_MAX_K, BWD_SEG_MAX_SOURCES, BWD_SEG_MAX_THREADS_PER_BLOCK,
    BWD_SEG_PROGPTR_KERNEL_ARGUMENT_BYTES,
};
use super::seg_lower::SourceClass;
use crate::primitives::field::E4;
use crate::primitives::utils::WARP_SIZE;
use crate::prover::gkr::backward::GkrEqSizes;

/// The CUDA half of the ABI, read as TEXT so a constant-only edit there cannot slip
/// past both builds: nvcc's own `static_assert`s are CUDA-vs-CUDA and cannot compare
/// against Rust.
const SEG_CUDA_HEADER: &str =
    include_str!("../../../../../native/prover/gkr/backward/segmented_vm.cuh");

/// The coefficient-evaluator half of this lineage's ABI, read as text for the same
/// third drift direction [`SEG_CUDA_HEADER`] covers.
const SEG_COEFF_EVAL_CUDA_HEADER: &str =
    include_str!("../../../../../native/prover/gkr/backward/seg_coeff_eval.cuh");

/// The pinned size of the inline-program descriptor.
const INLINE_DESC_BYTES: usize = 26_896;
/// The pinned size of the device-program A/B twin.
const PROGPTR_DESC_BYTES: usize = 9_664;
/// Implicit padding rustc (and nvcc, by the same C rules) inserts to align the
/// 8-byte-aligned `window` array after the 4-byte-aligned `source` array. This is
/// the gap before `window` ONLY — the descriptor's total implicit padding is this
/// plus [`INLINE_PRE_SOURCE_PAD_BYTES`], and it is the sum that the size pins.
const INLINE_IMPLICIT_PAD_BYTES: usize = 4;
/// Padding before the `source` array: NONE, in both twins. `fold_source` used to
/// end 2 mod 4 — the whole descriptor tail was, because `list_offset` is 33 x u16 —
/// and `BwdSegSourceRecord` is `align(4)`, so two bytes of the gap before `window`
/// moved here. `num_immediates` is the FIFTH u16 of the count block, which brings
/// `fold_source` back to 0 mod 4 and gives those two bytes back: the count field
/// pays for itself and the pad is gone on both sides.
const INLINE_PRE_SOURCE_PAD_BYTES: usize = 0;
/// The gap before `window` in the progptr twin, whose head is 12 bytes instead of
/// 17,248: with a 4-byte-aligned record the `source` array ends exactly at
/// `window`, so there is none.
const PROGPTR_IMPLICIT_PAD_BYTES: usize = 0;
/// The progptr twin's padding before `source`, by the same rule as the inline
/// descriptor's: also none, and for the same reason.
const PROGPTR_PRE_SOURCE_PAD_BYTES: usize = 0;

// ── The inline-program descriptor ────────────────────────────────────────────

#[test]
fn seg_descriptor_fits_the_by_value_kernel_argument_cap() {
    let size = size_of::<BwdSegDesc>();
    let margin = BWD_SEG_DESC_CAP - size;
    eprintln!(
        "BwdSegDesc: size={size} B, align={} B, cap={BWD_SEG_DESC_CAP} B, margin={margin} B",
        align_of::<BwdSegDesc>()
    );
    eprintln!(
        "  program[{LEAN_DESCRIPTOR_PROGRAM_WORDS}] = {LEAN_DESCRIPTOR_PROGRAM_BYTES} B at offset {}",
        offset_of!(BwdSegDesc, program)
    );
    eprintln!(
        "  fold_source[{BWD_SEG_MAX_SOURCES}] = {} B at offset {}",
        BWD_SEG_MAX_SOURCES * size_of::<u16>(),
        offset_of!(BwdSegDesc, fold_source)
    );
    eprintln!(
        "  source[{BWD_SEG_MAX_SOURCES}] = {} B at offset {}",
        BWD_SEG_MAX_SOURCES * size_of::<BwdSegSourceRecord>(),
        offset_of!(BwdSegDesc, source)
    );
    eprintln!(
        "  window[{}] = {} B at offset {}",
        BWD_SEG_SOURCE_WINDOW_CAP,
        BWD_SEG_SOURCE_WINDOW_CAP * size_of::<BwdCoeffSourceWindow>(),
        offset_of!(BwdSegDesc, window)
    );
    assert_eq!(size, INLINE_DESC_BYTES);
    assert_eq!(align_of::<BwdSegDesc>(), BWD_SEG_DESC_ALIGN);
    assert!(size <= BWD_SEG_DESC_CAP);
    assert_eq!(BWD_SEG_DESC_CAP, KERNEL_ARGUMENT_CEILING_BYTES);
    assert_eq!(BWD_SEG_DESC_ALIGN, DESCRIPTOR_ALIGNMENT_BYTES);
}

#[test]
fn seg_descriptor_layout_is_pinned_field_for_field() {
    assert_eq!(offset_of!(BwdSegDesc, program), 0);
    assert_eq!(offset_of!(BwdSegDesc, list_offset), 17_248);
    assert_eq!(offset_of!(BwdSegDesc, k), 17_314);
    assert_eq!(offset_of!(BwdSegDesc, record_count), 17_316);
    assert_eq!(offset_of!(BwdSegDesc, num_sources), 17_318);
    assert_eq!(offset_of!(BwdSegDesc, num_foldable), 17_320);
    assert_eq!(offset_of!(BwdSegDesc, num_immediates), 17_322);
    assert_eq!(offset_of!(BwdSegDesc, fold_source), 17_324);
    assert_eq!(offset_of!(BwdSegDesc, source), 19_468);
    assert_eq!(offset_of!(BwdSegDesc, window), 23_760);
    assert_eq!(offset_of!(BwdSegDesc, c_init_coeff), 24_784);
    assert_eq!(offset_of!(BwdSegDesc, immediates), 24_800);
    assert_eq!(offset_of!(BwdSegDesc, coefficients), 26_848);
    assert_eq!(offset_of!(BwdSegDesc, eq_low), 26_856);
    assert_eq!(offset_of!(BwdSegDesc, contributions), 26_864);
    assert_eq!(offset_of!(BwdSegDesc, eq_sizes), 26_872);
    assert_eq!(offset_of!(BwdSegDesc, n_coefficients), 26_884);
    assert_eq!(offset_of!(BwdSegDesc, logical_rows), 26_888);
    assert_eq!(offset_of!(BwdSegDesc, output), 26_892);

    // The program is the descriptor's HEAD here (the cell-era desc put it last),
    // so the 16-byte descriptor alignment places it on a 16-byte boundary for
    // free — which is the only reason the one-word round-up of the lean census
    // buys anything.
    assert_eq!(offset_of!(BwdSegDesc, program) % BWD_SEG_DESC_ALIGN, 0);
    // The eight-byte-aligned window array is the only field that needs implicit
    // padding in front of it; everything after it is naturally aligned.
    assert_eq!(
        offset_of!(BwdSegDesc, window) % align_of::<BwdCoeffSourceWindow>(),
        0
    );
    assert_eq!(
        offset_of!(BwdSegDesc, coefficients) % align_of::<*const E4>(),
        0
    );
}

#[test]
fn seg_descriptor_has_no_unaccounted_bytes() {
    // Every field, in declaration order, with its byte count. If a field is ever
    // ADDED to the descriptor without being added here, this test fails — which
    // is how the "no challenge pointer anywhere in the descriptor" rule is
    // enforced structurally rather than by review. Fold challenges have exactly
    // ONE authority, the `ab_gkr_main_layer_claim_point` `__constant__` symbol;
    // `round_challenges` / `n_round_challenges` are deliberately absent, as are
    // `cell_budget` and `num_words` (no cell file, and the K-list offsets carry
    // the program length).
    let fields = [
        ("program", LEAN_DESCRIPTOR_PROGRAM_BYTES),
        ("list_offset", (BWD_SEG_MAX_K + 1) * size_of::<u16>()),
        ("k", size_of::<u16>()),
        ("record_count", size_of::<u16>()),
        ("num_sources", size_of::<u16>()),
        ("num_foldable", size_of::<u16>()),
        ("num_immediates", size_of::<u16>()),
        ("fold_source", BWD_SEG_MAX_SOURCES * size_of::<u16>()),
        (
            "source",
            BWD_SEG_MAX_SOURCES * size_of::<BwdSegSourceRecord>(),
        ),
        (
            "window",
            BWD_SEG_SOURCE_WINDOW_CAP * size_of::<BwdCoeffSourceWindow>(),
        ),
        // The seed's id plus the padding that preserves its 16-byte footprint.
        ("c_init_coeff", size_of::<u32>()),
        ("c_init_pad", 3 * size_of::<u32>()),
        ("immediates", BWD_SEG_MAX_IMMEDIATES * size_of::<u32>()),
        ("coefficients", size_of::<*const E4>()),
        ("eq_low", size_of::<*const E4>()),
        ("contributions", size_of::<*mut E4>()),
        ("eq_sizes", size_of::<GkrEqSizes>()),
        ("n_coefficients", size_of::<u32>()),
        ("logical_rows", size_of::<u32>()),
        ("output", size_of::<u32>()),
    ];
    let payload: usize = fields.iter().map(|(_, bytes)| bytes).sum();
    let implicit_pad = INLINE_PRE_SOURCE_PAD_BYTES + INLINE_IMPLICIT_PAD_BYTES;
    eprintln!(
        "BwdSegDesc accounting: {payload} B of fields + {INLINE_PRE_SOURCE_PAD_BYTES} B pad before \
         `source` + {INLINE_IMPLICIT_PAD_BYTES} B pad before `window` = {INLINE_DESC_BYTES} B"
    );
    assert_eq!(payload + implicit_pad, INLINE_DESC_BYTES);
    assert_eq!(payload, size_of::<BwdSegDesc>() - implicit_pad);
    // `output` occupies the word that used to be explicit trailing pad, so it
    // is what makes the SIZE a multiple of the alignment without trailing
    // padding the two languages would have to agree on implicitly.
    assert_eq!(size_of::<BwdSegDesc>() % BWD_SEG_DESC_ALIGN, 0);
    assert_eq!(
        offset_of!(BwdSegDesc, output) + size_of::<u32>(),
        size_of::<BwdSegDesc>()
    );
}

// ── The device-program A/B twin ──────────────────────────────────────────────

#[test]
fn seg_progptr_descriptor_layout_is_pinned_field_for_field() {
    let size = size_of::<BwdSegProgPtrDesc>();
    eprintln!(
        "BwdSegProgPtrDesc: size={size} B, align={} B (inline twin {INLINE_DESC_BYTES} B)",
        align_of::<BwdSegProgPtrDesc>()
    );
    assert_eq!(size, PROGPTR_DESC_BYTES);
    assert_eq!(align_of::<BwdSegProgPtrDesc>(), BWD_SEG_DESC_ALIGN);
    assert!(size <= BWD_SEG_DESC_CAP);

    // Field ORDER is identical to the inline descriptor's, with the inline
    // `program` array replaced by a device pointer plus its length.
    assert_eq!(offset_of!(BwdSegProgPtrDesc, program), 0);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, program_words), 8);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, list_offset), 12);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, k), 78);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, record_count), 80);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, num_sources), 82);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, num_foldable), 84);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, num_immediates), 86);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, fold_source), 88);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, source), 2_232);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, window), 6_520);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, c_init_coeff), 7_544);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, immediates), 7_560);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, coefficients), 9_608);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, eq_low), 9_616);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, contributions), 9_624);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, eq_sizes), 9_632);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, n_coefficients), 9_644);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, logical_rows), 9_648);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, output), 9_652);
    assert_eq!(offset_of!(BwdSegProgPtrDesc, pad), 9_656);
    assert_eq!(size % BWD_SEG_DESC_ALIGN, 0);
    assert_eq!(
        offset_of!(BwdSegProgPtrDesc, pad) + 2 * size_of::<u32>(),
        size
    );
}

#[test]
fn seg_progptr_descriptor_actually_drops_the_inline_program() {
    // The POINT of the A/B twin is that the param-space program is GONE, not
    // merely unused: an unused-but-present array would leave the 17,248 bytes
    // resident in the launch's parameter space and measure nothing (spec §5).
    let saved = size_of::<BwdSegDesc>() - size_of::<BwdSegProgPtrDesc>();
    eprintln!(
        "progptr saves {saved} B of param space \
         (program array {LEAN_DESCRIPTOR_PROGRAM_BYTES} B, replaced by ptr+len)"
    );
    assert!(saved >= LEAN_DESCRIPTOR_PROGRAM_BYTES - BWD_SEG_DESC_ALIGN);
    assert!(size_of::<BwdSegProgPtrDesc>() < size_of::<BwdSegDesc>());

    // Same accounting gate as the inline descriptor: a field added to one twin
    // and not the other is a divergence, and this catches it on this side.
    let fields = [
        ("program", size_of::<*const u16>()),
        ("program_words", size_of::<u32>()),
        ("list_offset", (BWD_SEG_MAX_K + 1) * size_of::<u16>()),
        ("k", size_of::<u16>()),
        ("record_count", size_of::<u16>()),
        ("num_sources", size_of::<u16>()),
        ("num_foldable", size_of::<u16>()),
        ("num_immediates", size_of::<u16>()),
        ("fold_source", BWD_SEG_MAX_SOURCES * size_of::<u16>()),
        (
            "source",
            BWD_SEG_MAX_SOURCES * size_of::<BwdSegSourceRecord>(),
        ),
        (
            "window",
            BWD_SEG_SOURCE_WINDOW_CAP * size_of::<BwdCoeffSourceWindow>(),
        ),
        // The seed's id plus the padding that preserves its 16-byte footprint.
        ("c_init_coeff", size_of::<u32>()),
        ("c_init_pad", 3 * size_of::<u32>()),
        ("immediates", BWD_SEG_MAX_IMMEDIATES * size_of::<u32>()),
        ("coefficients", size_of::<*const E4>()),
        ("eq_low", size_of::<*const E4>()),
        ("contributions", size_of::<*mut E4>()),
        ("eq_sizes", size_of::<GkrEqSizes>()),
        ("n_coefficients", size_of::<u32>()),
        ("logical_rows", size_of::<u32>()),
        ("pad", 3 * size_of::<u32>()),
    ];
    let payload: usize = fields.iter().map(|(_, bytes)| bytes).sum();
    assert_eq!(
        payload + PROGPTR_PRE_SOURCE_PAD_BYTES + PROGPTR_IMPLICIT_PAD_BYTES,
        PROGPTR_DESC_BYTES
    );
}

// ── Kernel-argument budget ───────────────────────────────────────────────────

#[test]
fn seg_kernel_argument_bytes_are_pinned_for_both_launcher_shapes() {
    // ASSUMED FORMAL-PARAMETER LIST (Task 7 owns the signatures; if one grows a
    // formal, `seg_desc`'s `BWD_SEG_*_KERNEL_ARGUMENT_BYTES` and this pin must be
    // updated in the same commit):
    //
    //   ab_gkr_bwd_seg_{r0,cont}_{const,ptr}_epi_{staged,plane,wide}_kernel(
    //       BwdSegDesc desc)
    //   ab_gkr_bwd_seg_cont_const_progptr_epi_{staged,plane,wide}_kernel(
    //       BwdSegProgPtrDesc desc)
    //
    // i.e. ONE by-value descriptor and nothing else. Everything a launch also
    // needs is out of band: fold challenges in `ab_gkr_main_layer_claim_point`,
    // the fold weights in `ab_gkr_bwd_seg_fold_weights`, the coefficient bank in
    // this lineage's own `__constant__` symbol (or, in the `ptr` loader, in
    // `desc.coefficients`), the epilogue plane in DYNAMIC shared memory, `k` in
    // `desc.k`, and the program in `desc.program` (inline) or behind
    // `desc.program` (progptr).
    //
    // The fold-weight prelude is the ONE exception, and takes no descriptor at
    // all:
    //
    //   ab_gkr_bwd_seg_build_fold_weights_kernel(E4 *fold_weights, u32 round)
    //
    // `fold_weights` being the weight symbol's own address rather than a buffer
    // is why it needs no descriptor and no budget of its own.
    eprintln!(
        "kernel-argument bytes: inline={BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES} B, \
         progptr={BWD_SEG_PROGPTR_KERNEL_ARGUMENT_BYTES} B, ceiling={KERNEL_ARGUMENT_CEILING_BYTES} B"
    );
    assert_eq!(BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES, INLINE_DESC_BYTES);
    assert_eq!(BWD_SEG_PROGPTR_KERNEL_ARGUMENT_BYTES, PROGPTR_DESC_BYTES);
    assert!(BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(BWD_SEG_PROGPTR_KERNEL_ARGUMENT_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
    let prelude_bytes = size_of::<*mut E4>() + size_of::<u32>();
    eprintln!("fold-weight prelude argument bytes: {prelude_bytes} B");
    assert!(prelude_bytes <= KERNEL_ARGUMENT_CEILING_BYTES);
}

// ── Capacities ──────────────────────────────────────────────────────────────

#[test]
fn seg_coefficient_bank_materializes_the_reserved_literals() {
    // RR ruling 2026-07-27: the bank holds the two reserved literals AT ITS HEAD
    // (`bank[0] = ONE`, `bank[1] = NEG_ONE`, recipes from index 2), so the kernel
    // resolves every coefficient with ONE uniform `bank[coeff_idx]` load — no
    // ±ONE fast path, no branch, no offset subtraction.
    let needed = in_scope::MAX_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize;
    eprintln!(
        "coefficient bank: {BWD_SEG_CONST_BANK} slots ({} B) for {needed} reserved-inclusive ids \
         (census {} recipes + {} literals), slack {} slots",
        BWD_SEG_CONST_BANK * size_of::<E4>(),
        in_scope::MAX_COEFFICIENT_RECIPES,
        CoefficientRecipeId::RESERVED,
        BWD_SEG_CONST_BANK - needed
    );
    assert_eq!(CoefficientRecipeId::RESERVED, 2);
    assert_eq!(needed, 1_140);
    assert!(BWD_SEG_CONST_BANK >= needed);
    // Every bank slot must be nameable by the lean header's 13 coefficient bits.
    assert!(BWD_SEG_CONST_BANK <= MAX_COEFFICIENT_ENCODINGS);
    // ... and the whole bank must fit the 64 KB per-module `__constant__` budget
    // it shares with nothing else in this lineage.
    assert!(BWD_SEG_CONST_BANK * size_of::<E4>() <= 64 * 1_024);
}

#[test]
fn seg_source_capacity_covers_the_census() {
    eprintln!(
        "sources: {BWD_SEG_MAX_SOURCES} slots for census {} (pad {} slots)",
        in_scope::MAX_SOURCES,
        BWD_SEG_MAX_SOURCES - in_scope::MAX_SOURCES
    );
    assert!(BWD_SEG_MAX_SOURCES >= in_scope::MAX_SOURCES);
    // The round-up is strictly less than the 16-slot quantum that makes both
    // source-indexed arrays 16-byte-sized, so it cannot drift into headroom.
    assert!(BWD_SEG_MAX_SOURCES - in_scope::MAX_SOURCES < 16);
    assert_eq!(
        BWD_SEG_MAX_SOURCES * size_of::<u16>() % BWD_SEG_DESC_ALIGN,
        0
    );
    assert_eq!(
        BWD_SEG_MAX_SOURCES * size_of::<BwdSegSourceRecord>() % BWD_SEG_DESC_ALIGN,
        0
    );
    // A slot index is a u16 on the lean wire, where 0xFFFF is the "no second
    // source" sentinel, so the capacity must stay strictly below it.
    assert!(BWD_SEG_MAX_SOURCES < SOURCE_NONE as usize);
    // `fold_source` holds slot indices too.
    assert!(BWD_SEG_MAX_SOURCES <= u16::MAX as usize);
}

#[test]
fn seg_source_record_is_a_four_byte_triple() {
    assert_eq!(size_of::<BwdSegSourceRecord>(), 4);
    assert_eq!(align_of::<BwdSegSourceRecord>(), 4);
    assert_eq!(offset_of!(BwdSegSourceRecord, window), 0);
    assert_eq!(offset_of!(BwdSegSourceRecord, class), 1);
    assert_eq!(offset_of!(BwdSegSourceRecord, column), 2);
    // `window` is a u8 index into the descriptor's window array, and `class` is
    // the per-round source class Task 6 assigns (BfDirect=0, BfInlineD1=1,
    // BfInlineD2=2, E4Direct=3, ProceduralInline=4) — five values, so both fit a
    // byte with room to spare.
    assert!(BWD_SEG_SOURCE_WINDOW_CAP <= u8::MAX as usize);
    // `column` is window-relative, and a window covers at most 128 columns.
    assert!(gkr_eval_isa::bwd::coeff::limits::SOURCE_WINDOW_COLUMNS <= u16::MAX as usize + 1);
}

#[test]
fn seg_k_split_geometry_is_the_thousand_twenty_four_thread_block() {
    // One warp per list, `blockDim = 32 * k`, so K tops out where the block does.
    assert_eq!(
        BWD_SEG_MAX_K * WARP_SIZE as usize,
        BWD_SEG_MAX_THREADS_PER_BLOCK
    );
    assert_eq!(BWD_SEG_MAX_THREADS_PER_BLOCK, 1_024);
    assert!(BWD_SEG_MAX_K <= u16::MAX as usize);
    // `list_offset` is K+1 word offsets: warp `w` walks
    // `program[list_offset[w]..list_offset[w + 1]]`, and `list_offset[k]` is the
    // end of the whole program.
    let list_offsets =
        (offset_of!(BwdSegDesc, k) - offset_of!(BwdSegDesc, list_offset)) / size_of::<u16>();
    assert_eq!(list_offsets, BWD_SEG_MAX_K + 1);
    // A word offset must be representable in the u16 the array holds.
    assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS <= u16::MAX as usize);
}

#[test]
fn seg_program_array_is_the_lean_census_rounded_to_alignment() {
    assert_eq!(LEAN_DESCRIPTOR_PROGRAM_WORDS, 8_624);
    assert_eq!(LEAN_DESCRIPTOR_PROGRAM_BYTES, 17_248);
    assert_eq!(
        LEAN_DESCRIPTOR_PROGRAM_BYTES,
        LEAN_DESCRIPTOR_PROGRAM_WORDS * size_of::<u16>()
    );
    // The census measurement is the fixed-width identity over RECORDS — terms plus
    // the one header record per group the grouped wire spends — and the array is
    // that measurement rounded up by strictly less than one 16-byte quantum.
    assert_eq!(
        LEAN_MAX_REALIZED_PROGRAM_WORDS,
        LEAN_WORDS_PER_TERM * in_scope::MAX_RECORDS
    );
    assert!(in_scope::MAX_RECORDS > in_scope::MAX_TERMS);
    assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS >= LEAN_MAX_REALIZED_PROGRAM_WORDS);
    assert!(
        (LEAN_DESCRIPTOR_PROGRAM_WORDS - LEAN_MAX_REALIZED_PROGRAM_WORDS) * size_of::<u16>()
            < BWD_SEG_DESC_ALIGN
    );
    // `record_count` is a u16, and the census maximum has to fit it.
    assert!(in_scope::MAX_RECORDS <= u16::MAX as usize);
}

#[test]
fn seg_c_init_is_a_sentinel_bearing_coefficient_id() {
    // This lineage carried the seed as RESOLVED E4 limbs until production wiring
    // showed the host has no value to resolve: the bank is filled on the device
    // from challenges squeezed there, and the descriptor is built at scheduling
    // time. So the id travels and the device resolves it through the same bank
    // accessor as every other coefficient.
    //
    // Which makes the sentinel load-bearing: `0` is `CoefficientRecipeId::ONE`, a
    // legal seed, so absence cannot be spelled as a zeroed field the way the limbs
    // could. An `empty()` descriptor defaulting to `0` would seed EVERY layer with
    // `+1` — a wrong proof with no error channel.
    let empty = BwdSegDesc::empty();
    assert_eq!(
        empty.c_init_coeff, BWD_SEG_C_INIT_NONE,
        "absent c_init is the sentinel, and must not be the live id 0"
    );
    assert_eq!(BwdSegProgPtrDesc::empty().c_init_coeff, BWD_SEG_C_INIT_NONE);
    assert_ne!(
        BWD_SEG_C_INIT_NONE,
        CoefficientRecipeId::ONE.0,
        "the sentinel must not alias a coefficient id"
    );
    assert!(
        BWD_SEG_C_INIT_NONE as usize >= MAX_COEFFICIENT_ENCODINGS,
        "the sentinel must sit outside everything thirteen coefficient bits can name"
    );
    // The 16-byte footprint the descriptor's tail alignment depends on survived the
    // move: one id plus three padding words.
    assert_eq!(
        size_of::<u32>() + 3 * size_of::<u32>(),
        size_of::<E4>(),
        "the seed block must still occupy exactly what the limbs did"
    );
}

#[test]
fn seg_descriptor_reuses_the_window_struct_unforked() {
    // The window struct is IMPORTED from the cell-era descriptor, not forked, so
    // the segmented lineage inherits its layout and its publication policy
    // verbatim — including `procedural_kind` at offset 28, whose absent marker is
    // 0xff because zero is a live kind.
    assert_eq!(size_of::<BwdCoeffSourceWindow>(), 32);
    assert_eq!(align_of::<BwdCoeffSourceWindow>(), 8);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, procedural_kind), 28);
    assert_eq!(BWD_COEFF_PROCEDURAL_NONE, 0xff);
    // 32 windows x 32 B: the array is a CAPACITY, so this pins what it costs
    // (1 KiB of a ~27 KB descriptor) rather than what any circuit has used.
    assert_eq!(
        BWD_SEG_SOURCE_WINDOW_CAP * size_of::<BwdCoeffSourceWindow>(),
        1_024
    );
    // The publication threshold is imported, never duplicated.
    assert_eq!(BWD_COEFF_PUBLISH_TARGET_DEPTH, 3);
    assert_eq!(BWD_COEFF_PUBLISH_TARGET_DEPTH, PUBLISH_TARGET_DEPTH);
}

#[test]
fn seg_empty_descriptors_are_inert() {
    let inline = BwdSegDesc::empty();
    assert!(inline.coefficients.is_null());
    assert!(inline.eq_low.is_null());
    assert!(inline.contributions.is_null());
    assert_eq!(inline.k, 0);
    assert_eq!(inline.record_count, 0);
    assert_eq!(inline.num_sources, 0);
    assert_eq!(inline.num_foldable, 0);
    assert_eq!(inline.num_immediates, 0);
    assert_eq!(inline.n_coefficients, 0);
    assert_eq!(inline.logical_rows, 0);
    assert!(inline.program.iter().all(|word| *word == 0));
    assert!(inline.list_offset.iter().all(|word| *word == 0));
    assert!(inline.fold_source.iter().all(|slot| *slot == 0));
    assert!(inline.immediates.iter().all(|limb| *limb == 0));
    assert!(inline
        .source
        .iter()
        .all(|record| *record == BwdSegSourceRecord::default()));
    // A dead window slot must NOT claim procedural kind zero.
    assert!(inline
        .window
        .iter()
        .all(|window| window.procedural_kind == BWD_COEFF_PROCEDURAL_NONE));

    let progptr = BwdSegProgPtrDesc::empty();
    assert!(progptr.program.is_null());
    assert_eq!(progptr.program_words, 0);
    assert!(progptr.coefficients.is_null());
    assert_eq!(progptr.num_foldable, 0);
    assert_eq!(progptr.num_immediates, 0);
    assert!(progptr.immediates.iter().all(|limb| *limb == 0));
}

// ── The CUDA header, as text ─────────────────────────────────────────────────
//
// The third drift direction. Rust-side drift is a build failure (`seg_desc`'s
// `const _: () = assert!(...)` blocks); CUDA-side STRUCT drift is a build failure
// under nvcc; a CUDA-side edit to a constant that changes no layout is seen by
// NEITHER compiler, and these are what close it. Same shape as
// `abi_tests::cuda_constants_match_the_rust_mirror` for the cell-era header,
// deliberately: one reader should recognize both.

/// The value `segmented_vm.cuh` defines `name` as, for a LITERAL definition.
///
/// An expression-valued constant cannot be parsed and must be pinned through the
/// header's own `static_assert` instead, so this panics rather than guessing.
fn seg_cuda_literal(name: &str) -> u64 {
    let needle = format!(" {name} = ");
    let start = SEG_CUDA_HEADER
        .find(&needle)
        .unwrap_or_else(|| panic!("segmented_vm.cuh does not define {name}"))
        + needle.len();
    let rest = &SEG_CUDA_HEADER[start..];
    let end = rest
        .find(';')
        .unwrap_or_else(|| panic!("{name} has no terminated definition"));
    let raw = rest[..end].trim().trim_end_matches(['u', 'U']);
    let parsed = if let Some(hex) = raw.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).ok()
    } else {
        raw.parse::<u64>().ok()
    };
    parsed.unwrap_or_else(|| {
        panic!("{name} is defined as the expression `{raw}`; pin it with a static_assert instead")
    })
}

/// The value `segmented_vm.cuh` gives an ENUMERATOR of `bwd_seg_epilogue`.
///
/// A second parser rather than a flag on [`seg_cuda_literal`]: an enumerator's
/// definition runs to a COMMA, not a semicolon, and conflating the two terminators
/// is exactly how a matcher starts silently reading the rest of the enum body.
fn seg_cuda_enumerator(name: &str) -> u64 {
    let needle = format!("  {name} = ");
    let start = SEG_CUDA_HEADER
        .find(&needle)
        .unwrap_or_else(|| panic!("segmented_vm.cuh does not define enumerator {name}"))
        + needle.len();
    let rest = &SEG_CUDA_HEADER[start..];
    let end = rest
        .find(',')
        .unwrap_or_else(|| panic!("{name} has no terminated enumerator"));
    rest[..end]
        .trim()
        .parse::<u64>()
        .unwrap_or_else(|error| panic!("enumerator {name} is not a plain literal: {error}"))
}

/// Does `haystack` contain this exact `static_assert` claim?
///
/// The trailing comma is LOAD-BEARING, exactly as in `abi_tests`: every claim sits
/// inside a `static_assert(<claim>, "message");`, and without the terminator the
/// needle is a plain substring — Rust `== 17` would match a header asserting
/// `== 1712`. A check whose whole job is catching silent drift must not itself pass
/// silently.
fn seg_asserts_in(haystack: &str, claim: &str) -> bool {
    haystack.contains(&format!("{claim},"))
}

fn seg_header_asserts(claim: &str) -> bool {
    seg_asserts_in(SEG_CUDA_HEADER, claim)
}

fn assert_seg_header_asserts(claim: &str) {
    assert!(
        seg_header_asserts(claim),
        "segmented_vm.cuh does not static_assert `{claim}`"
    );
}

#[test]
fn the_seg_static_assert_matcher_rejects_a_numeric_prefix() {
    let drifted = r#"static_assert(sizeof(bwd_seg_desc) == 214560, "m");"#;
    assert!(!seg_asserts_in(drifted, "sizeof(bwd_seg_desc) == 21456"));
    assert!(seg_asserts_in(drifted, "sizeof(bwd_seg_desc) == 214560"));
    // Against the real header: a true claim holds, a prefix of one does not, and a
    // needle that is simply absent is a miss rather than a pass.
    assert!(seg_header_asserts(&format!(
        "sizeof(bwd_seg_desc) == {}",
        size_of::<BwdSegDesc>()
    )));
    assert!(seg_header_asserts("BWD_SEG_SOURCE_WINDOW_CAP == 32"));
    assert!(!seg_header_asserts("BWD_SEG_SOURCE_WINDOW_CAP == 1"));
    assert!(!seg_header_asserts(
        "__builtin_offsetof(bwd_seg_desc, no_such_field) == 0"
    ));
}

/// Every numeric constant this lineage mirrors is present in the CUDA header with
/// the same value.
///
/// Three groups matter more than the rest and are the reason this test is mandatory:
///
///   * [`BWD_SEG_CONST_BANK`] sizes a `__constant__` symbol. The host uploads its
///     coefficient payload straight to that symbol's address, and lowering bounds
///     the payload with the RUST number — so a CUDA-side shrink is an out-of-bounds
///     `__constant__` write with no build error on either side.
///   * the five SOURCE-CLASS numbers travel in a descriptor byte the kernel
///     switches on. Their authority is [`SourceClass`]'s discriminants; the header
///     pins them only against its own restatements, which is no cross-language
///     check at all.
///   * the `BWD_COEFF_*` block REHOMED out of the retired cell-era header, whose
///     only text matcher (`abi_tests::cuda_constants_match_the_rust_mirror`) died
///     with that lineage. `origin` is the sharpest case: `seg_resolve_e4` in
///     `segmented_vm.cu` branches on it to pick a window's backing field, so a
///     CUDA-only swap of `READ_BASE`/`READ_EXT` passes nvcc, passes `cargo check`,
///     passes every `static_assert` in the header (they are CUDA-vs-CUDA), and
///     mis-resolves every window — with only the GPU parity ladder behind it. Same
///     shape for the procedural BASE value and the `NONE` absent marker, which the
///     header's contiguity asserts pin only relative to each other.
#[test]
fn seg_cuda_constants_match_the_rust_mirror() {
    // The FROZEN opcode numbering the lean class tables are densified from. Its
    // authority is `gkr_eval_isa`, not `seg_desc.rs` — the Rust side of this
    // lineage deliberately does not restate it — so the needles are built from
    // `limits::{r0_opcode, continuation_opcode}` directly.
    let r0_opcode_of = |category| {
        u64::from(
            r0_opcode(category).unwrap_or_else(|| panic!("{category:?} has no frozen R0 opcode")),
        )
    };
    let cont_opcode_of = |category| {
        u64::from(
            continuation_opcode(category)
                .unwrap_or_else(|| panic!("{category:?} has no frozen continuation opcode")),
        )
    };

    let expected: &[(&str, u64)] = &[
        ("BWD_SEG_DESC_CAP", BWD_SEG_DESC_CAP as u64),
        ("BWD_SEG_DESC_ALIGN", BWD_SEG_DESC_ALIGN as u64),
        ("BWD_SEG_MAX_K", BWD_SEG_MAX_K as u64),
        (
            "BWD_SEG_MAX_THREADS_PER_BLOCK",
            BWD_SEG_MAX_THREADS_PER_BLOCK as u64,
        ),
        ("BWD_SEG_WARP_LANES", WARP_SIZE as u64),
        // The `__constant__` bank the host uploads into. MANDATORY.
        ("BWD_SEG_CONST_BANK", BWD_SEG_CONST_BANK as u64),
        // The seed's absent marker. Neither compiler can see a one-sided edit here,
        // and a disagreement seeds every continuation layer with `bank[huge]` or with
        // `+1` — see `seg_c_init_is_a_sentinel_bearing_coefficient_id`.
        ("BWD_SEG_C_INIT_NONE", u64::from(BWD_SEG_C_INIT_NONE)),
        ("BWD_SEG_MAX_SOURCES", BWD_SEG_MAX_SOURCES as u64),
        // The immediate table capacity, which mirrors the WIRE cap.
        ("BWD_SEG_MAX_IMMEDIATES", BWD_SEG_MAX_IMMEDIATES as u64),
        (
            "BWD_SEG_PROGRAM_WORD_CAP",
            LEAN_DESCRIPTOR_PROGRAM_WORDS as u64,
        ),
        ("BWD_SEG_WORDS_PER_TERM", LEAN_WORDS_PER_TERM as u64),
        (
            "BWD_SEG_COEFFICIENT_SHIFT",
            u64::from(LEAN_COEFFICIENT_SHIFT),
        ),
        ("BWD_SEG_SOURCE_NONE", u64::from(SOURCE_NONE)),
        // The five source classes. MANDATORY: `SourceClass` is the authority.
        (
            "BWD_SEG_SOURCE_CLASS_BF_DIRECT",
            u64::from(SourceClass::BfDirect.code()),
        ),
        (
            "BWD_SEG_SOURCE_CLASS_BF_INLINE_D1",
            u64::from(SourceClass::BfInlineD1.code()),
        ),
        (
            "BWD_SEG_SOURCE_CLASS_BF_INLINE_D2",
            u64::from(SourceClass::BfInlineD2.code()),
        ),
        (
            "BWD_SEG_SOURCE_CLASS_E4_DIRECT",
            u64::from(SourceClass::E4Direct.code()),
        ),
        (
            "BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE",
            u64::from(SourceClass::ProceduralInline.code()),
        ),
        ("BWD_SEG_SOURCE_CLASSES", 5),
        ("BWD_SEG_MAX_INLINE_FOLD_DEPTH", 2),
        // The fold-weight bank. MANDATORY for the same reason
        // [`BWD_SEG_CONST_BANK`] is: the slot count sizes a `__constant__`
        // symbol the host writes through its own address, and the three base
        // offsets are the PHYSICAL slot order — a CUDA-only renumber gives every
        // catch-up the wrong challenge product, which no compiler sees.
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
        // ── The block rehomed out of the retired `coefficient_vm.cuh` ──────────
        //
        // Window ORIGIN. MANDATORY: `seg_resolve_e4` selects the backing field off
        // this byte, so a CUDA-only renumber is a wrong answer, not a build error.
        (
            "BWD_COEFF_ORIGIN_READ_BASE",
            u64::from(BWD_COEFF_ORIGIN_READ_BASE),
        ),
        (
            "BWD_COEFF_ORIGIN_READ_EXT",
            u64::from(BWD_COEFF_ORIGIN_READ_EXT),
        ),
        (
            "BWD_COEFF_ORIGIN_PROCEDURAL",
            u64::from(BWD_COEFF_ORIGIN_PROCEDURAL),
        ),
        // Procedural kinds. The header asserts each kind's offset FROM the base and
        // that `NONE` is outside the range, but nothing there pins the base itself
        // or the marker's value — `bwd_coeff_procedural_source_kind` adds the base
        // to `GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS`, so a nonzero base
        // shifts every procedural column by that amount.
        (
            "BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS",
            u64::from(BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS),
        ),
        (
            "BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP",
            u64::from(BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP),
        ),
        (
            "BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW",
            u64::from(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW),
        ),
        (
            "BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH",
            u64::from(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH),
        ),
        (
            "BWD_COEFF_PROCEDURAL_NONE",
            u64::from(BWD_COEFF_PROCEDURAL_NONE),
        ),
        // The publication threshold and the prologue's depth bound.
        (
            "BWD_COEFF_PUBLISH_TARGET_DEPTH",
            u64::from(BWD_COEFF_PUBLISH_TARGET_DEPTH),
        ),
        (
            "BWD_COEFF_MAX_FOLD_DEPTH",
            u64::from(BWD_COEFF_MAX_FOLD_DEPTH),
        ),
        // The lean header's two bit widths. `BWD_SEG_{COEFFICIENT,CLASS}_MASK` and
        // `BWD_SEG_CLASS_SHIFT` are all derived from these, so pinning them here
        // makes the derivation's inputs cross-checked as well as its outputs.
        (
            "BWD_COEFF_HEADER_COEFFICIENT_BITS",
            u64::from(HEADER_COEFFICIENT_BITS),
        ),
        (
            "BWD_COEFF_HEADER_OPCODE_BITS",
            u64::from(HEADER_OPCODE_BITS),
        ),
        // The FROZEN opcode numbering. Transitively covered by the
        // `BWD_SEG_*_CLASS_* == BWD_COEFF_*_OP_*` static_asserts plus the
        // `BWD_SEG_*` rows above, but pinned directly so the chain does not have to
        // be reasoned through — and so the two `MOVE` rows, which no `BWD_SEG_*`
        // constant mentions, are covered at all.
        (
            "BWD_COEFF_R0_OP_C0_LINEAR_BF",
            r0_opcode_of(TermCategory::C0LinearBf),
        ),
        (
            "BWD_COEFF_R0_OP_C0_LINEAR_E4",
            r0_opcode_of(TermCategory::C0LinearE4),
        ),
        (
            "BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF",
            r0_opcode_of(TermCategory::C2ProductBfBf),
        ),
        (
            "BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4",
            r0_opcode_of(TermCategory::C2ProductBfE4),
        ),
        (
            "BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4",
            r0_opcode_of(TermCategory::C2ProductE4E4),
        ),
        (
            "BWD_COEFF_R0_OP_MOVE_BF",
            r0_opcode_of(TermCategory::MoveBf),
        ),
        (
            "BWD_COEFF_R0_OP_MOVE_E4",
            r0_opcode_of(TermCategory::MoveE4),
        ),
        ("BWD_COEFF_R0_LIVE_OPCODES", R0_LIVE_OPCODES as u64),
        (
            "BWD_COEFF_EXT_OP_C0_LINEAR_E4",
            cont_opcode_of(TermCategory::C0LinearE4),
        ),
        (
            "BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4",
            cont_opcode_of(TermCategory::DualProductE4),
        ),
        (
            "BWD_COEFF_EXT_OP_MOVE_E4",
            cont_opcode_of(TermCategory::MoveE4),
        ),
        (
            "BWD_COEFF_EXT_LIVE_OPCODES",
            CONTINUATION_LIVE_OPCODES as u64,
        ),
    ];
    for (name, value) in expected {
        assert_eq!(seg_cuda_literal(name), *value, "CUDA {name}");
    }

    // The epilogue enumerators. The launcher selects a SYMBOL rather than passing
    // one of these, but the header's `bwd_seg_epilogue_smem_bytes` switches on them
    // — so a renumbering here silently re-sizes the plane a launch allocates.
    for (name, value) in [
        ("BWD_SEG_EPILOGUE_STAGED", 0),
        ("BWD_SEG_EPILOGUE_PLANE", 1),
        ("BWD_SEG_EPILOGUE_WIDE", 2),
    ] {
        assert_eq!(seg_cuda_enumerator(name), value, "CUDA {name}");
    }

    // The output-shape enumerators. These DO travel in the descriptor, so a
    // renumbering silently swaps per-row contributions for warp partials — a
    // wrong-shaped write into a buffer sized for the other shape.
    for (name, value) in [
        ("BWD_SEG_OUTPUT_ROWS", u64::from(super::seg_desc::BWD_SEG_OUTPUT_ROWS)),
        (
            "BWD_SEG_OUTPUT_PARTIALS",
            u64::from(super::seg_desc::BWD_SEG_OUTPUT_PARTIALS),
        ),
    ] {
        assert_eq!(seg_cuda_enumerator(name), value, "CUDA {name}");
    }

    // The lean class tables, against the wire tables `gkr_eval_isa` owns.
    let r0_class = |category| {
        LEAN_R0_OPCODES
            .iter()
            .find(|(_, listed)| *listed == category)
            .map(|(class, _)| u64::from(*class))
            .unwrap_or_else(|| panic!("{category:?} is not a live R0 class"))
    };
    let cont_class = |category| {
        LEAN_CONT_OPCODES
            .iter()
            .find(|(_, listed)| *listed == category)
            .map(|(class, _)| u64::from(*class))
            .unwrap_or_else(|| panic!("{category:?} is not a live continuation class"))
    };
    for (name, value) in [
        (
            "BWD_SEG_R0_CLASS_C0_LINEAR_BF",
            r0_class(TermCategory::C0LinearBf),
        ),
        (
            "BWD_SEG_R0_CLASS_C0_LINEAR_E4",
            r0_class(TermCategory::C0LinearE4),
        ),
        (
            "BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF",
            r0_class(TermCategory::C2ProductBfBf),
        ),
        (
            "BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4",
            r0_class(TermCategory::C2ProductBfE4),
        ),
        (
            "BWD_SEG_R0_CLASS_C2_PRODUCT_E4_E4",
            r0_class(TermCategory::C2ProductE4E4),
        ),
        ("BWD_SEG_R0_LIVE_CLASSES", LEAN_R0_OPCODES.len() as u64),
        (
            "BWD_SEG_EXT_CLASS_C0_LINEAR_E4",
            cont_class(TermCategory::C0LinearE4),
        ),
        (
            "BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4",
            cont_class(TermCategory::DualProductE4),
        ),
        ("BWD_SEG_EXT_LIVE_CLASSES", LEAN_CONT_OPCODES.len() as u64),
        // The grouped wire (spec §4.4). MANDATORY for the same reason the source
        // classes are: the walk in `segmented_vm.cu` branches on the control code to
        // decide whether word1/word2 are two source slots or a member count plus the
        // accumulator-side flags, and reads the flag bits to decide which
        // accumulator the core multiplies into — so a CUDA-only edit here is a
        // wrong answer at every grouped coordinate, not a build error.
        (
            "BWD_SEG_EXT_CLASS_GROUP_HEADER",
            u64::from(LEAN_CONT_GROUP_HEADER_CLASS),
        ),
        ("BWD_SEG_GROUP_FLAG_C0", u64::from(LEAN_GROUP_FLAG_C0)),
        ("BWD_SEG_GROUP_FLAG_C2", u64::from(LEAN_GROUP_FLAG_C2)),
        // The immediate id space. `RESERVED` is the offset the kernel subtracts
        // before indexing `bwd_seg_desc::immediates`, and the two literal ids are
        // what select the add / sub fast paths — an off-by-one here reads the wrong
        // table slot with the right sign, or the right slot with the wrong one.
        ("BWD_SEG_IMMEDIATE_ONE", u64::from(ImmediateId::ONE.0)),
        (
            "BWD_SEG_IMMEDIATE_NEG_ONE",
            u64::from(ImmediateId::NEG_ONE.0),
        ),
        (
            "BWD_SEG_IMMEDIATE_RESERVED",
            u64::from(ImmediateId::RESERVED),
        ),
    ] {
        assert_eq!(seg_cuda_literal(name), value, "CUDA {name}");
    }
    // Expression-valued, so it is pinned through the header's own `static_assert`
    // with the expected number built from the Rust mirror.
    assert_seg_header_asserts(&format!(
        "BWD_SEG_GROUP_FLAG_MASK == {}",
        LEAN_GROUP_FLAG_MASK
    ));

    // The expression-valued constants cannot be parsed as literals, so they are
    // pinned by the header's own `static_assert`s — with the expected number built
    // from the Rust mirror, never hand-written here.
    for claim in [
        format!("BWD_SEG_CLASS_SHIFT == {LEAN_CLASS_SHIFT}"),
        format!("BWD_SEG_COEFFICIENT_MASK == {LEAN_COEFFICIENT_MASK:#x}u"),
        format!("BWD_SEG_CLASS_MASK == {LEAN_CLASS_MASK:#x}u"),
        format!("BWD_SEG_PROGRAM_BYTE_CAP == {LEAN_DESCRIPTOR_PROGRAM_BYTES}"),
        format!("BWD_SEG_SOURCE_WINDOW_CAP == {BWD_SEG_SOURCE_WINDOW_CAP}"),
        format!("BWD_SEG_MAX_FOLD_DEPTH == {BWD_COEFF_PUBLISH_TARGET_DEPTH}"),
        format!("BWD_SEG_LANE_INDEX_MASK == {}", WARP_SIZE - 1),
        // Rehomed and expression-valued: `1u << BWD_COEFF_HEADER_COEFFICIENT_BITS`.
        // Its own `static_assert` is the pin, and the number here comes from the
        // Rust mirror.
        format!("BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == {MAX_COEFFICIENT_ENCODINGS}"),
    ] {
        assert_seg_header_asserts(&claim);
    }

    // The three epilogue footprints. They are the launch's dynamic-smem argument and
    // are mirrored by HAND on the two sides, so a disagreement is an out-of-bounds
    // shared access rather than a build error — the one number in this ABI whose
    // drift a GPU run discovers.
    for claim in [
        "bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_STAGED, 1) == 0".to_string(),
        format!(
            "bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_STAGED, BWD_SEG_MAX_K) == {}",
            2 * WARP_SIZE as usize * size_of::<E4>()
        ),
        format!(
            "bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_PLANE, BWD_SEG_MAX_K) == {}",
            (BWD_SEG_MAX_K - 1) * WARP_SIZE as usize * size_of::<E4>()
        ),
        format!(
            "bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_WIDE, BWD_SEG_MAX_K) == {}",
            2 * (BWD_SEG_MAX_K - 1) * WARP_SIZE as usize * size_of::<E4>()
        ),
    ] {
        assert_seg_header_asserts(&claim);
    }
}

/// Every offset and size Rust computes is `static_assert`ed with the same number on
/// the CUDA side. The needles are BUILT from `offset_of!`, so there is no
/// hand-maintained number here.
#[test]
fn seg_cuda_layout_asserts_match_the_rust_layout() {
    let inline: &[(&str, usize)] = &[
        ("program", offset_of!(BwdSegDesc, program)),
        ("list_offset", offset_of!(BwdSegDesc, list_offset)),
        ("k", offset_of!(BwdSegDesc, k)),
        ("record_count", offset_of!(BwdSegDesc, record_count)),
        ("num_sources", offset_of!(BwdSegDesc, num_sources)),
        ("num_foldable", offset_of!(BwdSegDesc, num_foldable)),
        ("num_immediates", offset_of!(BwdSegDesc, num_immediates)),
        ("fold_source", offset_of!(BwdSegDesc, fold_source)),
        ("source", offset_of!(BwdSegDesc, source)),
        ("window", offset_of!(BwdSegDesc, window)),
        ("c_init_coeff", offset_of!(BwdSegDesc, c_init_coeff)),
        ("c_init_pad", offset_of!(BwdSegDesc, c_init_pad)),
        ("immediates", offset_of!(BwdSegDesc, immediates)),
        ("coefficients", offset_of!(BwdSegDesc, coefficients)),
        ("eq_low", offset_of!(BwdSegDesc, eq_low)),
        ("contributions", offset_of!(BwdSegDesc, contributions)),
        ("eq_sizes", offset_of!(BwdSegDesc, eq_sizes)),
        ("n_coefficients", offset_of!(BwdSegDesc, n_coefficients)),
        ("logical_rows", offset_of!(BwdSegDesc, logical_rows)),
        ("output", offset_of!(BwdSegDesc, output)),
    ];
    for (field, offset) in inline {
        assert_seg_header_asserts(&format!(
            "__builtin_offsetof(bwd_seg_desc, {field}) == {offset}"
        ));
    }
    let progptr: &[(&str, usize)] = &[
        ("program", offset_of!(BwdSegProgPtrDesc, program)),
        (
            "program_words",
            offset_of!(BwdSegProgPtrDesc, program_words),
        ),
        ("list_offset", offset_of!(BwdSegProgPtrDesc, list_offset)),
        ("k", offset_of!(BwdSegProgPtrDesc, k)),
        ("record_count", offset_of!(BwdSegProgPtrDesc, record_count)),
        ("num_sources", offset_of!(BwdSegProgPtrDesc, num_sources)),
        ("num_foldable", offset_of!(BwdSegProgPtrDesc, num_foldable)),
        (
            "num_immediates",
            offset_of!(BwdSegProgPtrDesc, num_immediates),
        ),
        ("fold_source", offset_of!(BwdSegProgPtrDesc, fold_source)),
        ("source", offset_of!(BwdSegProgPtrDesc, source)),
        ("window", offset_of!(BwdSegProgPtrDesc, window)),
        ("c_init_coeff", offset_of!(BwdSegProgPtrDesc, c_init_coeff)),
        ("c_init_pad", offset_of!(BwdSegProgPtrDesc, c_init_pad)),
        ("immediates", offset_of!(BwdSegProgPtrDesc, immediates)),
        ("coefficients", offset_of!(BwdSegProgPtrDesc, coefficients)),
        ("eq_low", offset_of!(BwdSegProgPtrDesc, eq_low)),
        (
            "contributions",
            offset_of!(BwdSegProgPtrDesc, contributions),
        ),
        ("eq_sizes", offset_of!(BwdSegProgPtrDesc, eq_sizes)),
        (
            "n_coefficients",
            offset_of!(BwdSegProgPtrDesc, n_coefficients),
        ),
        ("logical_rows", offset_of!(BwdSegProgPtrDesc, logical_rows)),
        ("output", offset_of!(BwdSegProgPtrDesc, output)),
        ("pad", offset_of!(BwdSegProgPtrDesc, pad)),
    ];
    for (field, offset) in progptr {
        assert_seg_header_asserts(&format!(
            "__builtin_offsetof(bwd_seg_progptr_desc, {field}) == {offset}"
        ));
    }
    for claim in [
        format!("sizeof(bwd_seg_desc) == {}", size_of::<BwdSegDesc>()),
        format!(
            "sizeof(bwd_seg_progptr_desc) == {}",
            size_of::<BwdSegProgPtrDesc>()
        ),
        format!("alignof(bwd_seg_desc) == BWD_SEG_DESC_ALIGN"),
    ] {
        assert_seg_header_asserts(&claim);
    }
    // The source record, whose three offsets are the descriptor's per-source ABI.
    for (field, offset) in [
        ("window", offset_of!(BwdSegSourceRecord, window)),
        ("source_class", offset_of!(BwdSegSourceRecord, class)),
        ("column", offset_of!(BwdSegSourceRecord, column)),
    ] {
        assert_seg_header_asserts(&format!(
            "__builtin_offsetof(bwd_seg_source_record, {field}) == {offset}"
        ));
    }
    // The SOURCE WINDOW, rehomed here with the rest of the cell-era block. Its
    // offsets were Rust-pinned by `abi_tests::cuda_layout_asserts_match_the_rust_layout`
    // until that lineage was deleted; without these needles the struct is
    // CUDA-vs-CUDA only, and a CONSISTENT same-width field swap — say
    // `read_stride_bytes` and `publish_stride_bytes` exchanged on both sides with
    // their literals updated — satisfies nvcc, `cargo check` and every
    // `static_assert` in the header while transposing what a publish writes and a
    // read loads. Built from `offset_of!`, so no number is maintained by hand.
    for (field, offset) in [
        ("read_base", offset_of!(BwdCoeffSourceWindow, read_base)),
        (
            "publish_base",
            offset_of!(BwdCoeffSourceWindow, publish_base),
        ),
        (
            "read_stride_bytes",
            offset_of!(BwdCoeffSourceWindow, read_stride_bytes),
        ),
        (
            "publish_stride_bytes",
            offset_of!(BwdCoeffSourceWindow, publish_stride_bytes),
        ),
        (
            "backing_depth",
            offset_of!(BwdCoeffSourceWindow, backing_depth),
        ),
        (
            "target_depth",
            offset_of!(BwdCoeffSourceWindow, target_depth),
        ),
        ("origin", offset_of!(BwdCoeffSourceWindow, origin)),
        ("materialize", offset_of!(BwdCoeffSourceWindow, materialize)),
        (
            "procedural_kind",
            offset_of!(BwdCoeffSourceWindow, procedural_kind),
        ),
        ("reserved", offset_of!(BwdCoeffSourceWindow, reserved)),
    ] {
        assert_seg_header_asserts(&format!(
            "__builtin_offsetof(bwd_coeff_source_window, {field}) == {offset}"
        ));
    }
    for claim in [
        format!(
            "sizeof(bwd_coeff_source_window) == {}",
            size_of::<BwdCoeffSourceWindow>()
        ),
        format!(
            "alignof(bwd_coeff_source_window) == {}",
            align_of::<BwdCoeffSourceWindow>()
        ),
    ] {
        assert_seg_header_asserts(&claim);
    }
    // The two implicit gaps before `window`, which neither language spells.
    assert_seg_header_asserts(&format!(
        "__builtin_offsetof(bwd_seg_desc, window) - (__builtin_offsetof(bwd_seg_desc, source) + sizeof(bwd_seg_desc::source)) == {INLINE_IMPLICIT_PAD_BYTES}"
    ));
    assert_seg_header_asserts(&format!(
        "__builtin_offsetof(bwd_seg_progptr_desc, window) - (__builtin_offsetof(bwd_seg_progptr_desc, source) + sizeof(bwd_seg_progptr_desc::source)) == {PROGPTR_IMPLICIT_PAD_BYTES}"
    ));
}

/// The coefficient evaluator's ABI: the challenge-slab layout and the two struct
/// layouts, pinned in the same three directions as the descriptor's.
///
/// The slab constants are the interesting half. They are `u8` slot numbers with no
/// layout consequence at all, so nvcc and `cargo check` are both blind to a
/// one-sided edit — and a slot mismatch does not fail, it silently evaluates a
/// coefficient against the WRONG challenge. That is a wrong proof with no error
/// channel, which is exactly the class of drift this file exists for.
#[test]
fn seg_coeff_eval_cuda_abi_matches_the_rust_mirror() {
    let literal = |name: &str| -> u64 {
        let needle = format!(" {name} = ");
        let start = SEG_COEFF_EVAL_CUDA_HEADER
            .find(&needle)
            .unwrap_or_else(|| panic!("seg_coeff_eval.cuh does not define {name}"))
            + needle.len();
        let rest = &SEG_COEFF_EVAL_CUDA_HEADER[start..];
        let end = rest
            .find(';')
            .unwrap_or_else(|| panic!("{name} has no terminated definition"));
        let raw = rest[..end].trim().trim_end_matches(['u', 'U']);
        if let Some(hex) = raw.strip_prefix("0x") {
            u64::from_str_radix(hex, 16)
        } else {
            raw.parse::<u64>()
        }
        .unwrap_or_else(|_| {
            panic!("{name} is defined as the expression `{raw}`; pin it with a static_assert")
        })
    };
    for (name, value) in [
        (
            "BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE",
            u64::from(BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE),
        ),
        (
            "BWD_SEG_CHALLENGE_PERM_ADDITIVE",
            u64::from(BWD_SEG_CHALLENGE_PERM_ADDITIVE),
        ),
        (
            "BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE",
            u64::from(BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE),
        ),
        (
            "BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE",
            u64::from(BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE),
        ),
        (
            "BWD_SEG_CHALLENGE_CONSTRAINT_AGGREGATION",
            u64::from(BWD_SEG_CHALLENGE_CONSTRAINT_AGGREGATION),
        ),
        (
            "BWD_SEG_CHALLENGE_CLAIM_BATCHING",
            u64::from(BWD_SEG_CHALLENGE_CLAIM_BATCHING),
        ),
        ("BWD_SEG_CHALLENGE_SLOTS", BWD_SEG_CHALLENGE_SLOTS as u64),
        (
            "BWD_SEG_CHALLENGE_ABSENT",
            u64::from(BWD_SEG_CHALLENGE_ABSENT),
        ),
        // The inline monomial array's capacity. Not decoration: it is what makes the
        // recipe header's `u16` offset exact, and the census is gated against it.
        (
            "BWD_SEG_COEFF_MAX_MONOMIALS",
            BWD_SEG_COEFF_MAX_MONOMIALS as u64,
        ),
    ] {
        assert_eq!(literal(name), value, "CUDA {name}");
    }

    // The struct layouts, built from `offset_of!` so no number is hand-maintained.
    // The DESCRIPTOR is here too: it rides the kernel's parameter space by value, so
    // its size is an ABI surface exactly like `bwd_seg_desc`'s — and its two capacity
    // constants are what the corpus census is gated against.
    for claim in [
        format!(
            "sizeof(bwd_seg_coeff_eval_desc) == {}",
            size_of::<SegCoeffEvalDesc>()
        ),
        format!(
            "__builtin_offsetof(bwd_seg_coeff_eval_desc, monomials) == {}",
            offset_of!(SegCoeffEvalDesc, monomials)
        ),
        format!(
            "__builtin_offsetof(bwd_seg_coeff_eval_desc, num_coefficients) == {}",
            offset_of!(SegCoeffEvalDesc, num_coefficients)
        ),
        format!(
            "sizeof(bwd_seg_coeff_recipe) == {}",
            size_of::<SegCoeffRecipe>()
        ),
        format!(
            "sizeof(bwd_seg_coeff_monomial) == {}",
            size_of::<SegCoeffMonomial>()
        ),
        format!(
            "__builtin_offsetof(bwd_seg_coeff_monomial, batch_power) == {}",
            offset_of!(SegCoeffMonomial, batch_power)
        ),
        format!(
            "__builtin_offsetof(bwd_seg_coeff_monomial, challenge_idx_0) == {}",
            offset_of!(SegCoeffMonomial, challenge_idx_0)
        ),
        format!(
            "__builtin_offsetof(bwd_seg_coeff_monomial, power_0) == {}",
            offset_of!(SegCoeffMonomial, power_0)
        ),
    ] {
        assert!(
            seg_asserts_in(SEG_COEFF_EVAL_CUDA_HEADER, &claim),
            "seg_coeff_eval.cuh does not static_assert `{claim}`"
        );
    }

    // The one launched symbol, with the formal list the Rust launcher passes — the
    // descriptor BY VALUE, then the two device pointers.
    let symbol = "ab_gkr_bwd_seg_eval_coefficients_kernel(__grid_constant__ const bwd_seg_coeff_eval_desc desc, const e4 *challenges, e4 *coefficients)";
    assert!(
        include_str!("../../../../../native/prover/gkr/backward/seg_coeff_eval.cu")
            .contains(symbol),
        "seg_coeff_eval.cu does not define `{symbol}`"
    );
}

/// Every kernel symbol the Rust launcher declares is DECLARED in the header, and
/// with the formal list the launcher passes — the descriptor type for the fifteen
/// matrix cells, the weight-bank alias and the round for the prelude.
///
/// Symbol names, not numbers, so there is no prefix hazard: `EXTERN` makes the bare
/// name the ABI, and a launcher naming a symbol the header does not declare fails at
/// LINK time — but a launcher naming the WRONG one of two live symbols does not.
#[test]
fn seg_cuda_header_declares_every_launched_kernel() {
    let mut declared = 0usize;
    for regime in ["r0", "cont"] {
        for coeff in ["const", "ptr"] {
            for epilogue in ["staged", "plane", "wide"] {
                let symbol =
                    format!("ab_gkr_bwd_seg_{regime}_{coeff}_epi_{epilogue}_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc)");
                assert!(
                    SEG_CUDA_HEADER.contains(&symbol),
                    "segmented_vm.cuh does not declare `{symbol}`"
                );
                declared += 1;
            }
        }
    }
    for epilogue in ["staged", "plane", "wide"] {
        let symbol = format!(
            "ab_gkr_bwd_seg_cont_const_progptr_epi_{epilogue}_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_progptr_desc desc)"
        );
        assert!(
            SEG_CUDA_HEADER.contains(&symbol),
            "segmented_vm.cuh does not declare `{symbol}`"
        );
        declared += 1;
    }
    // The device-program family has ONE cell by design (spec §5: it measures the
    // program-source axis alone), so the matrix is twelve plus three, not twenty-four.
    assert_eq!(declared, 15);
    // The fold-weight prelude is launched but is NOT a matrix cell, so it is
    // asserted apart from the count — with its formal list, which is the only
    // signature in this lineage that is not one by-value descriptor.
    assert!(SEG_CUDA_HEADER
        .contains("ab_gkr_bwd_seg_build_fold_weights_kernel(e4 *fold_weights, u32 round)"));
    // The three `__constant__` symbols a launch stages into, named rather than
    // matched numerically.
    assert!(SEG_CUDA_HEADER
        .contains("ab_gkr_bwd_seg_coeff_bank[airbender::prover::gkr::BWD_SEG_CONST_BANK]"));
    assert!(SEG_CUDA_HEADER.contains("ab_gkr_main_layer_claim_point["));
    assert!(SEG_CUDA_HEADER.contains(
        "ab_gkr_bwd_seg_fold_weights[airbender::prover::gkr::BWD_SEG_FOLD_WEIGHT_SLOTS]"
    ));
}
