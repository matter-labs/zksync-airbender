//! The Rust↔CUDA ABI gate for the backward coefficient-term ISA.
//!
//! Three kinds of check live here, and they cover three different failure
//! directions:
//!
//!   1. **Rust-side drift** is already a BUILD failure: `desc.rs` carries
//!      `const _: () = assert!(...)` blocks tying every literal to its authority
//!      in `gkr_eval_isa`. The tests here re-state the important ones so the
//!      failure is readable, and add the ones that need a `HashMap` or a `.cuh`
//!      file and therefore cannot be const.
//!   2. **CUDA-side drift in a STRUCT** is already a build failure too: the
//!      `static_assert`s in `coefficient_vm.cuh` run under nvcc during
//!      `cargo check`.
//!   3. **CUDA-side drift in a CONSTANT** is what
//!      [`cuda_constants_match_the_rust_mirror`] and
//!      [`cuda_layout_asserts_match_the_rust_layout`] close: they read the
//!      header as text and compare every mirrored literal against the Rust
//!      value. Without them a CUDA-only edit could pass both builds and be
//!      discovered on the GPU.

use std::collections::HashMap;
use std::mem::{align_of, offset_of, size_of};

use gkr_eval_isa::bwd::coeff::bind::{BoundColumn, BoundSourceWindow, CoeffSourceBinding};
use gkr_eval_isa::bwd::coeff::encode::{
    EncodedProgram, CELL_ENDPOINT0_LANE_SHIFT, HEADER_OPCODE_SHIFT, LANE_MASK, MODE_CELL,
};
use gkr_eval_isa::bwd::coeff::limits::{
    continuation_opcode, in_scope, r0_opcode, TermCategory, DESCRIPTOR_ALIGNMENT_BYTES,
    KERNEL_ARGUMENT_CEILING_BYTES, MAX_SOURCE_WINDOWS,
};
use gkr_eval_isa::bwd::coeff::model::{CoeffSource, CoefficientRecipeId, SourceId};
use gkr_eval_isa::bwd::coeff::schedule::CellBudget;
use gkr_eval_isa::bwd::coeff::stats::{window_family, WindowFamily};
use gkr_eval_isa::bwd::source::OriginLeaf;
use gkr_eval_isa::fwd::source::{virtual_setup_kind_code, KIND_ORDER};

use super::desc::*;
use super::lower::{
    lower_bwd_coeff, BwdCoeffLowerError, BwdCoeffRoundBinding, ResolvedBwdCoeffSourceWindow,
};
use super::{bwd_coeff_dynamic_smem_bytes, bwd_coeff_fold_depth, BwdCoeffBank};
use crate::primitives::field::E4;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::upstream::{BwdRegime, Field};

/// The CUDA half of the ABI, read as text so a constant-only edit there cannot
/// slip past both builds.
const CUDA_HEADER: &str =
    include_str!("../../../../../native/prover/gkr/backward/coefficient_vm.cuh");

// ── Descriptor layout ────────────────────────────────────────────────────────

#[test]
fn descriptor_fits_the_by_value_kernel_argument_cap() {
    let size = size_of::<BwdCoeffDesc>();
    let margin = BWD_COEFF_DESC_CAP - size;
    eprintln!(
        "BwdCoeffDesc: size={size} B, align={} B, cap={BWD_COEFF_DESC_CAP} B, margin={margin} B",
        align_of::<BwdCoeffDesc>()
    );
    eprintln!(
        "  program[{BWD_COEFF_PROGRAM_WORD_CAP}] = {BWD_COEFF_PROGRAM_BYTE_CAP} B at offset {}",
        offset_of!(BwdCoeffDesc, program)
    );
    eprintln!(
        "  source_windows[{BWD_COEFF_SOURCE_WINDOW_CAP}] = {} B at offset {}",
        BWD_COEFF_SOURCE_WINDOW_CAP * size_of::<BwdCoeffSourceWindow>(),
        offset_of!(BwdCoeffDesc, source_windows)
    );
    assert_eq!(size, 12_144);
    assert!(size <= BWD_COEFF_DESC_CAP);
    assert_eq!(BWD_COEFF_DESC_CAP, KERNEL_ARGUMENT_CEILING_BYTES);
}

#[test]
fn descriptor_layout_is_pinned_field_for_field() {
    assert_eq!(offset_of!(BwdCoeffDesc, coefficients), 0);
    assert_eq!(offset_of!(BwdCoeffDesc, round_challenges), 8);
    assert_eq!(offset_of!(BwdCoeffDesc, eq_low), 16);
    assert_eq!(offset_of!(BwdCoeffDesc, contributions), 24);
    assert_eq!(offset_of!(BwdCoeffDesc, source_windows), 32);
    assert_eq!(offset_of!(BwdCoeffDesc, eq_sizes), 576);
    assert_eq!(offset_of!(BwdCoeffDesc, num_words), 588);
    assert_eq!(offset_of!(BwdCoeffDesc, n_source_windows), 592);
    assert_eq!(offset_of!(BwdCoeffDesc, n_round_challenges), 596);
    assert_eq!(offset_of!(BwdCoeffDesc, n_coefficients), 600);
    assert_eq!(offset_of!(BwdCoeffDesc, logical_rows), 604);
    assert_eq!(offset_of!(BwdCoeffDesc, cell_budget), 608);
    assert_eq!(offset_of!(BwdCoeffDesc, c_init), 612);
    assert_eq!(offset_of!(BwdCoeffDesc, pad), 614);
    assert_eq!(offset_of!(BwdCoeffDesc, program), 624);

    assert_eq!(size_of::<BwdCoeffSourceWindow>(), 32);
    assert_eq!(align_of::<BwdCoeffSourceWindow>(), 8);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, read_base), 0);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, publish_base), 8);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, read_stride_bytes), 16);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, publish_stride_bytes), 20);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, backing_depth), 24);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, target_depth), 25);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, origin), 26);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, materialize), 27);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, procedural_kind), 28);
    assert_eq!(offset_of!(BwdCoeffSourceWindow, reserved), 29);
}

/// `DESCRIPTOR_ALIGNMENT_BYTES` is KEPT at 16, and it is load-bearing rather
/// than cosmetic.
///
/// The descriptor declares `align(16)` and carries an explicit `pad` so that
/// `program` starts on a 16-byte boundary; §9.1's "buffer the stream through
/// aligned wide loads" is therefore available to the executor. Task 8's
/// one-word round-up of the measured 5,759 is what keeps the ARRAY a whole
/// number of 16-byte quanta, and it is free: because a 16-byte-aligned struct's
/// size is already rounded to 16, a 5,759-word array would produce the SAME
/// 12,144-byte descriptor with two bytes of tail padding instead of one spare
/// word. The final assertion below states exactly that, so nobody "saves" the
/// word later and loses the alignment for nothing.
#[test]
fn descriptor_alignment_is_load_bearing() {
    assert_eq!(BWD_COEFF_DESC_ALIGN, DESCRIPTOR_ALIGNMENT_BYTES);
    assert_eq!(align_of::<BwdCoeffDesc>(), BWD_COEFF_DESC_ALIGN);
    assert_eq!(offset_of!(BwdCoeffDesc, program) % BWD_COEFF_DESC_ALIGN, 0);
    assert_eq!(BWD_COEFF_PROGRAM_BYTE_CAP % BWD_COEFF_DESC_ALIGN, 0);
    assert_eq!(size_of::<BwdCoeffDesc>() % BWD_COEFF_DESC_ALIGN, 0);
    // The array is the MEASUREMENT rounded up by strictly less than one
    // alignment quantum, and not one word further.
    assert_eq!(
        BWD_COEFF_PROGRAM_WORD_CAP,
        in_scope::DESCRIPTOR_PROGRAM_WORDS
    );
    assert_eq!(in_scope::MAX_REALIZED_PROGRAM_WORDS, 5_759);
    assert_eq!(
        BWD_COEFF_PROGRAM_WORD_CAP - in_scope::MAX_REALIZED_PROGRAM_WORDS,
        1
    );
    // The round-up costs ZERO bytes: an un-rounded array lands in the same
    // 16-byte-aligned descriptor size.
    let unrounded = offset_of!(BwdCoeffDesc, program) + 2 * in_scope::MAX_REALIZED_PROGRAM_WORDS;
    assert_eq!(
        unrounded.div_ceil(BWD_COEFF_DESC_ALIGN) * BWD_COEFF_DESC_ALIGN,
        size_of::<BwdCoeffDesc>()
    );
}

/// The two array capacities come from Task 8's MEASUREMENTS, not from what the
/// wire format can express. The encoding limits are a separate claim.
#[test]
fn by_value_capacities_are_the_measured_corpus_maxima() {
    assert_eq!(
        BWD_COEFF_SOURCE_WINDOW_CAP,
        in_scope::MAX_SOURCE_WINDOWS_USED
    );
    assert_eq!(BWD_COEFF_SOURCE_WINDOW_CAP, 17);
    assert_eq!(BWD_COEFF_PROGRAM_WORD_CAP, 5_760);
    assert_eq!(
        BWD_COEFF_PROGRAM_BYTE_CAP,
        in_scope::DESCRIPTOR_PROGRAM_BYTES
    );
    assert_eq!(BWD_COEFF_PROGRAM_BYTE_CAP, 11_520);

    // ...and the encoding still permits 64 windows and 128 columns. Sizing the
    // array from 64 would hide the drift the measurement exists to catch.
    assert_eq!(BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS, MAX_SOURCE_WINDOWS);
    assert_eq!(BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS, 64);
    assert!(BWD_COEFF_SOURCE_WINDOW_CAP < BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS);
    assert_eq!(BWD_COEFF_SOURCE_WINDOW_COLUMNS, 128);

    // The maximum is at c3, not c16: program length is not monotone in the
    // budget, so nothing may assume the largest budget is worst-case.
    assert_eq!(in_scope::MAX_REALIZED_PROGRAM_CELLS, 3);
    assert_eq!(
        in_scope::MAX_REALIZED_PROGRAM_COORDINATE,
        "blake2_with_extended_control_layout_gkr.json L0 Ext"
    );
}

/// There is no device program pointer and no format version: `program` is the
/// descriptor's tail and the only program storage that exists.
#[test]
fn the_program_is_embedded_by_value_with_no_pointer_path() {
    assert_eq!(
        size_of::<BwdCoeffDesc>(),
        offset_of!(BwdCoeffDesc, program) + BWD_COEFF_PROGRAM_BYTE_CAP
    );
    // The ONE pointer to coefficient data is the sanctioned exception, and the
    // constant specialization does not read it.
    let desc = BwdCoeffDesc::empty();
    assert!(desc.coefficients.is_null());
    assert_eq!(desc.num_words, 0);
}

#[test]
fn an_empty_descriptor_marks_c_init_and_procedural_kind_absent() {
    let desc = BwdCoeffDesc::empty();
    assert_eq!(desc.c_init, BWD_COEFF_C_INIT_NONE);
    for window in desc.source_windows {
        // Zero would alias a LIVE procedural kind.
        assert_eq!(window.procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
        assert_ne!(
            window.procedural_kind,
            BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS
        );
    }
    assert_eq!(desc.pad, [0; 5]);
}

/// `u16::MAX` is the descriptor-only absent-`c_init` sentinel. It is NOT a
/// program coefficient encoding, and thirteen coefficient bits cannot reach it.
#[test]
fn the_c_init_sentinel_is_unreachable_as_a_coefficient_index() {
    assert_eq!(BWD_COEFF_C_INIT_NONE, u16::MAX);
    assert_eq!(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS, 8_192);
    let largest_encodable = (BWD_COEFF_MAX_COEFFICIENT_ENCODINGS - 1) as u16;
    assert!(largest_encodable < BWD_COEFF_C_INIT_NONE);
    assert_eq!(
        largest_encodable & BWD_COEFF_HEADER_COEFFICIENT_MASK,
        largest_encodable
    );
    assert_ne!(
        BWD_COEFF_C_INIT_NONE & BWD_COEFF_HEADER_COEFFICIENT_MASK,
        BWD_COEFF_C_INIT_NONE
    );
    // The two reserved literals are indices, not sentinels.
    assert_eq!(u32::from(BWD_COEFF_INDEX_ONE), CoefficientRecipeId::ONE.0);
    assert_eq!(
        u32::from(BWD_COEFF_INDEX_NEG_ONE),
        CoefficientRecipeId::NEG_ONE.0
    );
    assert_eq!(
        u32::from(BWD_COEFF_INDEX_RESERVED),
        CoefficientRecipeId::RESERVED
    );
}

// ── Wire format ──────────────────────────────────────────────────────────────

#[test]
fn opcode_numbers_match_the_frozen_tables() {
    for (mirror, category) in [
        (BWD_COEFF_R0_OP_C0_LINEAR_BF, TermCategory::C0LinearBf),
        (BWD_COEFF_R0_OP_C0_LINEAR_E4, TermCategory::C0LinearE4),
        (
            BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF,
            TermCategory::C2ProductBfBf,
        ),
        (
            BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4,
            TermCategory::C2ProductBfE4,
        ),
        (
            BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4,
            TermCategory::C2ProductE4E4,
        ),
        (BWD_COEFF_R0_OP_MOVE_BF, TermCategory::MoveBf),
        (BWD_COEFF_R0_OP_MOVE_E4, TermCategory::MoveE4),
    ] {
        assert_eq!(
            Some(mirror),
            r0_opcode(category),
            "R0 opcode of {}",
            category.label()
        );
    }
    assert_eq!(r0_opcode(TermCategory::DualProductE4), None);
    assert_eq!(BWD_COEFF_R0_LIVE_OPCODES, 7);

    for (mirror, category) in [
        (BWD_COEFF_EXT_OP_C0_LINEAR_E4, TermCategory::C0LinearE4),
        (
            BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4,
            TermCategory::DualProductE4,
        ),
        (BWD_COEFF_EXT_OP_MOVE_E4, TermCategory::MoveE4),
    ] {
        assert_eq!(
            Some(mirror),
            continuation_opcode(category),
            "continuation opcode of {}",
            category.label()
        );
    }
    assert_eq!(BWD_COEFF_EXT_LIVE_OPCODES, 3);
    // Every live opcode fits the three header bits, in both regimes.
    for opcode in [BWD_COEFF_R0_OP_MOVE_E4, BWD_COEFF_EXT_OP_MOVE_E4] {
        assert_eq!(opcode & BWD_COEFF_HEADER_OPCODE_MASK, opcode);
    }
}

/// ABI FACT 1. Bit 2 is a mode-discriminated overlay: `first_access` in a
/// source-bearing input word, `Endpoint0` lane bit 0 in a cell or plan word,
/// and lane bit 2 in a bare lane word. A decoder that extracts `first_access`
/// before dispatching on the mode reads a lane bit as a materialization flag.
#[test]
fn bit_two_is_a_mode_discriminated_overlay() {
    assert_eq!(
        BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT,
        BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT
    );
    assert_eq!(
        BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT,
        BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT
    );
    let bit2 = 1u16 << BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT;

    // Same bit, four readings — and none of them is derivable from the word.
    let input_word = bit2 | BWD_COEFF_MODE_DIRECT_SOURCE;
    assert_eq!(
        (input_word >> BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT) & 1,
        1,
        "an input word reads bit 2 as first_access"
    );
    let cell_word = bit2 | BWD_COEFF_MODE_CELL;
    assert_eq!(
        (cell_word >> BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT) & BWD_COEFF_LANE_MASK,
        1,
        "a cell word reads bit 2 as Endpoint0 lane bit 0"
    );
    let plan_word = bit2;
    assert_eq!(
        (plan_word >> BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT) & BWD_COEFF_LANE_MASK,
        1,
        "a plan word reads bit 2 as Endpoint0 lane bit 0"
    );
    let lane_word = bit2;
    assert_eq!(
        (lane_word >> BWD_COEFF_LANE_WORD_SHIFT) & BWD_COEFF_LANE_MASK,
        4,
        "a bare lane word reads bit 2 as lane bit 2"
    );

    // The window field starts one bit above it, so there is no spare bit that
    // would let the overlay be flattened away on one side only.
    assert_eq!(
        BWD_COEFF_INPUT_WINDOW_SHIFT,
        BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT + 1
    );
    assert_eq!(BWD_COEFF_INPUT_COLUMN_SHIFT + 7, 16);
}

/// ABI FACT 2. The packed pair `Cell` form is opcode-scoped: `DualProductE4`
/// and only `DualProductE4` reads bits 10..15 as the `Delta` lane. There is no
/// tag in the word, so the opcode is the only discriminator.
#[test]
fn the_packed_pair_cell_form_is_opcode_scoped() {
    assert!(bwd_coeff_cell_word_is_pair_form(
        false,
        BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4
    ));
    for opcode in [BWD_COEFF_EXT_OP_C0_LINEAR_E4, BWD_COEFF_EXT_OP_MOVE_E4] {
        assert!(!bwd_coeff_cell_word_is_pair_form(false, opcode));
    }
    // R0 has no native dual factor. In particular the R0 opcode numerically
    // equal to the continuation dual opcode is C0LinearE4, not a pair.
    assert_eq!(
        BWD_COEFF_R0_OP_C0_LINEAR_E4,
        BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4
    );
    for opcode in 0..=BWD_COEFF_HEADER_OPCODE_MASK {
        assert!(!bwd_coeff_cell_word_is_pair_form(true, opcode));
    }

    // A `Cell` word whose high payload is nonzero is a pair under the dual
    // opcode and a REJECTED program under any other.
    let packed = (5u16 << BWD_COEFF_CELL_DELTA_LANE_SHIFT)
        | (8u16 << BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT)
        | BWD_COEFF_MODE_CELL;
    assert_eq!(
        (packed >> BWD_COEFF_CELL_DELTA_LANE_SHIFT) & BWD_COEFF_LANE_MASK,
        5
    );
    assert_eq!(
        (packed >> BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT) & BWD_COEFF_LANE_MASK,
        8
    );
    // The cell and plan words share ONE lane geometry, so a decoder needs one
    // pair-of-lanes extractor rather than two.
    assert_eq!(
        BWD_COEFF_CELL_DELTA_LANE_SHIFT,
        BWD_COEFF_PLAN_DELTA_LANE_SHIFT
    );
    assert_eq!(
        BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT,
        BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT
    );
}

#[test]
fn six_lane_bits_address_exactly_the_largest_cell_file() {
    assert_eq!(BWD_COEFF_LANE_BITS, 6);
    assert_eq!(u32::from(BWD_COEFF_LANE_MASK) + 1, 64);
    assert_eq!(
        u32::from(BWD_COEFF_LANE_MASK) + 1,
        BWD_COEFF_MAX_BUDGET_CELLS * BWD_COEFF_LANES_PER_CELL
    );
    assert_eq!(BWD_COEFF_MIN_BUDGET_CELLS, 2);
    assert_eq!(BWD_COEFF_MAX_BUDGET_CELLS, 16);
}

// ── Source-window origin ─────────────────────────────────────────────────────

/// The window descriptor's procedural kind must agree with BOTH the compiler's
/// `WindowFamily` tag and the device kind order the forward VM already uses.
#[test]
fn procedural_kinds_agree_with_the_compiler_and_the_device_order() {
    let cross = HashMap::new();
    for (kind, code) in [
        (
            crate::upstream::VirtualSetupKind::RangeCheck16Bits,
            BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS,
        ),
        (
            crate::upstream::VirtualSetupKind::RangeCheckTimestamp,
            BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP,
        ),
        (
            crate::upstream::VirtualSetupKind::InitsAndTeardownsLow,
            BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW,
        ),
        (
            crate::upstream::VirtualSetupKind::InitsAndTeardownsHigh,
            BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH,
        ),
    ] {
        assert_eq!(virtual_setup_kind_code(&kind), u32::from(code));
        assert_eq!(KIND_ORDER[usize::from(code)], kind);
        // ...and the binder's own tag, which is what actually reaches the
        // descriptor.
        let source = CoeffSource {
            origin: OriginLeaf::VirtualSetup { kind },
            field: cs::gkr_compiler::dag_ir::FieldKind::Base,
        };
        let (family, _) = window_family(&source, &cross);
        assert_eq!(family, WindowFamily::VirtualSetup { kind: code });
    }
    assert_eq!(BWD_COEFF_PROCEDURAL_KINDS, KIND_ORDER.len());
    assert!(usize::from(BWD_COEFF_PROCEDURAL_NONE) >= BWD_COEFF_PROCEDURAL_KINDS);
    assert_eq!(BWD_COEFF_ORIGIN_READ_BASE, 0);
    assert_eq!(BWD_COEFF_ORIGIN_READ_EXT, 1);
    assert_eq!(BWD_COEFF_ORIGIN_PROCEDURAL, 2);
}

#[test]
fn the_materialization_threshold_is_one_static_constant() {
    assert_eq!(
        BWD_COEFF_PUBLISH_TARGET_DEPTH,
        gkr_eval_isa::bwd::coeff::schedule::PUBLISH_TARGET_DEPTH
    );
    assert_eq!(BWD_COEFF_PUBLISH_TARGET_DEPTH, 3);
    // A layer-wide binding carries the same flag the descriptor does.
    let binding = CoeffSourceBinding {
        target_depth: 4,
        materialize: true,
        windows: Vec::new(),
        uses: Vec::new(),
    };
    assert_eq!(
        binding.materialize,
        binding.target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH
    );
}

// ── Launch geometry ──────────────────────────────────────────────────────────

/// §11's geometry: ONE thread per logical row, 128 logical rows per block. The
/// two-half role split is gone, so rows per block equals the block width.
#[test]
fn launch_geometry_is_one_thread_per_logical_row() {
    assert_eq!(BWD_COEFF_THREADS_PER_BLOCK, 128);
    assert_eq!(BWD_COEFF_ROWS_PER_BLOCK, BWD_COEFF_THREADS_PER_BLOCK);
    assert_eq!(BWD_COEFF_THREADS_PER_BLOCK % BWD_COEFF_WARP_LANES, 0);
    for (rows, blocks) in [(1u32, 1u32), (128, 1), (129, 2), (4096, 32)] {
        assert_eq!(rows.div_ceil(BWD_COEFF_ROWS_PER_BLOCK), blocks);
    }
}

#[test]
fn dynamic_shared_memory_is_the_private_cell_file_of_every_thread() {
    for cells in BWD_COEFF_MIN_BUDGET_CELLS..=BWD_COEFF_MAX_BUDGET_CELLS {
        assert_eq!(
            bwd_coeff_dynamic_smem_bytes(cells),
            cells as usize * size_of::<E4>() * BWD_COEFF_THREADS_PER_BLOCK as usize
        );
    }
    assert_eq!(size_of::<E4>(), 16);
    // c16 at 128 threads is 32 KiB, the whole default per-block budget.
    assert_eq!(bwd_coeff_dynamic_smem_bytes(16), 32_768);
}

#[test]
fn fold_depth_mapping_is_exact_and_bounded() {
    assert_eq!(bwd_coeff_fold_depth(0), 0);
    assert_eq!(bwd_coeff_fold_depth(1), 1);
    assert_eq!(bwd_coeff_fold_depth(2), 2);
    assert_eq!(bwd_coeff_fold_depth(3), 3);
    // Past the publication threshold every materializing source is published,
    // so a backing is at most one fold behind.
    for round in 4..=24 {
        assert_eq!(bwd_coeff_fold_depth(round), 1);
    }
    for round in 0..=24u8 {
        assert!(bwd_coeff_fold_depth(round) <= BWD_COEFF_MAX_FOLD_DEPTH);
    }
    assert_eq!(BWD_COEFF_MAX_FOLD_DEPTH, BWD_COEFF_PUBLISH_TARGET_DEPTH);
}

#[test]
fn the_coefficient_bank_choice_is_launch_wide() {
    assert_eq!(BwdCoeffBank::Constant.capacity(), FLAT_CONST_MAX);
    assert_eq!(FLAT_CONST_MAX, 1_024);
    // The corpus needs more than the constant symbol holds, which is exactly
    // why the device-pointer specialization exists.
    assert!(in_scope::MAX_COEFFICIENT_RECIPES > FLAT_CONST_MAX);
    assert!(
        in_scope::MAX_COEFFICIENT_RECIPES <= BwdCoeffBank::DevicePointer.capacity(),
        "the device-pointer bank must cover the corpus maximum"
    );
}

// ── The CUDA half, read as text ──────────────────────────────────────────────

/// Parse `constexpr <type> <name> = <integer literal>;` out of the header.
///
/// Panics for a constant whose right-hand side is an expression — those are
/// pinned by the header's own `static_assert`s and are checked with
/// [`assert_header_asserts`] instead.
fn cuda_literal(name: &str) -> u64 {
    let needle = format!(" {name} = ");
    let start = CUDA_HEADER
        .find(&needle)
        .unwrap_or_else(|| panic!("coefficient_vm.cuh does not define {name}"))
        + needle.len();
    let rest = &CUDA_HEADER[start..];
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

/// Does `haystack` contain this exact `static_assert` claim?
///
/// The trailing comma is LOAD-BEARING. Every claim checked here sits inside a
/// `static_assert(<claim>, "message");`, and without the terminator the needle
/// is a plain substring: Rust `== 600` would match a CUDA header that asserts
/// `== 6000`, and `== 12144` would match `== 121440`. A check whose whole job is
/// catching silent drift must not itself pass silently, so the claim must run
/// to the end of the `static_assert`'s first argument.
fn asserts_in(haystack: &str, claim: &str) -> bool {
    haystack.contains(&format!("{claim},"))
}

fn header_asserts(claim: &str) -> bool {
    asserts_in(CUDA_HEADER, claim)
}

/// The header `static_assert`s this exact claim.
fn assert_header_asserts(claim: &str) {
    assert!(
        header_asserts(claim),
        "coefficient_vm.cuh does not static_assert `{claim}`"
    );
}

/// The header mentions this text at all. For symbol NAMES, which are not
/// numeric and therefore have no prefix hazard.
fn assert_header_mentions(text: &str) {
    assert!(
        CUDA_HEADER.contains(text),
        "coefficient_vm.cuh is missing `{text}`"
    );
}

/// The terminator in [`asserts_in`] actually closes the prefix hole, and a
/// missing claim is still a miss.
#[test]
fn the_static_assert_matcher_rejects_a_numeric_prefix() {
    // The exact hole the reviewer demonstrated: a Rust-side value that is a
    // PREFIX of the number the header really asserts.
    let drifted =
        r#"static_assert(__builtin_offsetof(bwd_coeff_desc, n_coefficients) == 6000, "m");"#;
    assert!(!asserts_in(
        drifted,
        "__builtin_offsetof(bwd_coeff_desc, n_coefficients) == 600"
    ));
    assert!(asserts_in(
        drifted,
        "__builtin_offsetof(bwd_coeff_desc, n_coefficients) == 6000"
    ));
    let wide = r#"static_assert(sizeof(bwd_coeff_desc) == 121440, "m");"#;
    assert!(!asserts_in(wide, "sizeof(bwd_coeff_desc) == 12144"));
    assert!(asserts_in(wide, "sizeof(bwd_coeff_desc) == 121440"));

    // Against the real header: the true claims hold and a prefix of one does
    // not.
    assert!(header_asserts(&format!(
        "__builtin_offsetof(bwd_coeff_desc, n_coefficients) == {}",
        offset_of!(BwdCoeffDesc, n_coefficients)
    )));
    assert!(!header_asserts(
        "__builtin_offsetof(bwd_coeff_desc, n_coefficients) == 60"
    ));
    // A needle that is simply absent must be a miss, not a pass.
    assert!(!header_asserts(
        "__builtin_offsetof(bwd_coeff_desc, no_such_field) == 0"
    ));
}

/// Every numeric constant this crate mirrors is present in the CUDA header with
/// the same value. This is the only check that catches a CUDA-side constant
/// edit: nvcc's own `static_assert`s cannot compare against Rust.
#[test]
fn cuda_constants_match_the_rust_mirror() {
    let expected: &[(&str, u64)] = &[
        ("BWD_COEFF_DESC_CAP", BWD_COEFF_DESC_CAP as u64),
        ("BWD_COEFF_DESC_ALIGN", BWD_COEFF_DESC_ALIGN as u64),
        (
            "BWD_COEFF_SOURCE_WINDOW_CAP",
            BWD_COEFF_SOURCE_WINDOW_CAP as u64,
        ),
        (
            "BWD_COEFF_PROGRAM_WORD_CAP",
            BWD_COEFF_PROGRAM_WORD_CAP as u64,
        ),
        (
            "BWD_COEFF_HEADER_COEFFICIENT_BITS",
            BWD_COEFF_HEADER_COEFFICIENT_BITS as u64,
        ),
        (
            "BWD_COEFF_HEADER_COEFFICIENT_SHIFT",
            BWD_COEFF_HEADER_COEFFICIENT_SHIFT as u64,
        ),
        (
            "BWD_COEFF_HEADER_OPCODE_BITS",
            BWD_COEFF_HEADER_OPCODE_BITS as u64,
        ),
        ("BWD_COEFF_INDEX_ONE", BWD_COEFF_INDEX_ONE as u64),
        ("BWD_COEFF_INDEX_NEG_ONE", BWD_COEFF_INDEX_NEG_ONE as u64),
        ("BWD_COEFF_INDEX_RESERVED", BWD_COEFF_INDEX_RESERVED as u64),
        (
            "BWD_COEFF_INPUT_MODE_SHIFT",
            BWD_COEFF_INPUT_MODE_SHIFT as u64,
        ),
        (
            "BWD_COEFF_INPUT_MODE_MASK",
            BWD_COEFF_INPUT_MODE_MASK as u64,
        ),
        (
            "BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT",
            BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT as u64,
        ),
        (
            "BWD_COEFF_INPUT_WINDOW_SHIFT",
            BWD_COEFF_INPUT_WINDOW_SHIFT as u64,
        ),
        (
            "BWD_COEFF_INPUT_WINDOW_MASK",
            BWD_COEFF_INPUT_WINDOW_MASK as u64,
        ),
        (
            "BWD_COEFF_INPUT_COLUMN_SHIFT",
            BWD_COEFF_INPUT_COLUMN_SHIFT as u64,
        ),
        (
            "BWD_COEFF_INPUT_COLUMN_MASK",
            BWD_COEFF_INPUT_COLUMN_MASK as u64,
        ),
        ("BWD_COEFF_LANE_BITS", BWD_COEFF_LANE_BITS as u64),
        ("BWD_COEFF_LANES_PER_CELL", BWD_COEFF_LANES_PER_CELL as u64),
        (
            "BWD_COEFF_MIN_BUDGET_CELLS",
            BWD_COEFF_MIN_BUDGET_CELLS as u64,
        ),
        (
            "BWD_COEFF_MAX_BUDGET_CELLS",
            BWD_COEFF_MAX_BUDGET_CELLS as u64,
        ),
        (
            "BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT",
            BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT as u64,
        ),
        (
            "BWD_COEFF_CELL_DELTA_LANE_SHIFT",
            BWD_COEFF_CELL_DELTA_LANE_SHIFT as u64,
        ),
        (
            "BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT",
            BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT as u64,
        ),
        (
            "BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT",
            BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT as u64,
        ),
        (
            "BWD_COEFF_PLAN_DELTA_ACTION_SHIFT",
            BWD_COEFF_PLAN_DELTA_ACTION_SHIFT as u64,
        ),
        (
            "BWD_COEFF_PLAN_DELTA_LANE_SHIFT",
            BWD_COEFF_PLAN_DELTA_LANE_SHIFT as u64,
        ),
        (
            "BWD_COEFF_PLAN_ACTION_MASK",
            BWD_COEFF_PLAN_ACTION_MASK as u64,
        ),
        (
            "BWD_COEFF_LANE_WORD_SHIFT",
            BWD_COEFF_LANE_WORD_SHIFT as u64,
        ),
        (
            "BWD_COEFF_MODE_DIRECT_SOURCE",
            BWD_COEFF_MODE_DIRECT_SOURCE as u64,
        ),
        ("BWD_COEFF_MODE_CELL", BWD_COEFF_MODE_CELL as u64),
        (
            "BWD_COEFF_MODE_FILL_SOURCE",
            BWD_COEFF_MODE_FILL_SOURCE as u64,
        ),
        (
            "BWD_COEFF_MODE_PLANNED_SOURCE",
            BWD_COEFF_MODE_PLANNED_SOURCE as u64,
        ),
        ("BWD_COEFF_ACTION_DIRECT", BWD_COEFF_ACTION_DIRECT as u64),
        (
            "BWD_COEFF_ACTION_USE_RESIDENT",
            BWD_COEFF_ACTION_USE_RESIDENT as u64,
        ),
        ("BWD_COEFF_ACTION_FILL", BWD_COEFF_ACTION_FILL as u64),
        ("BWD_COEFF_ACTION_INVALID", BWD_COEFF_ACTION_INVALID as u64),
        (
            "BWD_COEFF_R0_OP_C0_LINEAR_BF",
            BWD_COEFF_R0_OP_C0_LINEAR_BF as u64,
        ),
        (
            "BWD_COEFF_R0_OP_C0_LINEAR_E4",
            BWD_COEFF_R0_OP_C0_LINEAR_E4 as u64,
        ),
        (
            "BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF",
            BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF as u64,
        ),
        (
            "BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4",
            BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4 as u64,
        ),
        (
            "BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4",
            BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4 as u64,
        ),
        ("BWD_COEFF_R0_OP_MOVE_BF", BWD_COEFF_R0_OP_MOVE_BF as u64),
        ("BWD_COEFF_R0_OP_MOVE_E4", BWD_COEFF_R0_OP_MOVE_E4 as u64),
        (
            "BWD_COEFF_R0_LIVE_OPCODES",
            BWD_COEFF_R0_LIVE_OPCODES as u64,
        ),
        (
            "BWD_COEFF_EXT_OP_C0_LINEAR_E4",
            BWD_COEFF_EXT_OP_C0_LINEAR_E4 as u64,
        ),
        (
            "BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4",
            BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4 as u64,
        ),
        ("BWD_COEFF_EXT_OP_MOVE_E4", BWD_COEFF_EXT_OP_MOVE_E4 as u64),
        (
            "BWD_COEFF_EXT_LIVE_OPCODES",
            BWD_COEFF_EXT_LIVE_OPCODES as u64,
        ),
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
        (
            "BWD_COEFF_PUBLISH_TARGET_DEPTH",
            BWD_COEFF_PUBLISH_TARGET_DEPTH as u64,
        ),
        (
            "BWD_COEFF_THREADS_PER_BLOCK",
            BWD_COEFF_THREADS_PER_BLOCK as u64,
        ),
        ("BWD_COEFF_WARP_LANES", BWD_COEFF_WARP_LANES as u64),
        (
            "BWD_COEFF_FOLD_FACTOR_CAP",
            BWD_COEFF_FOLD_FACTOR_CAP as u64,
        ),
        ("BWD_COEFF_MAX_FOLD_DEPTH", BWD_COEFF_MAX_FOLD_DEPTH as u64),
        // Both weight-group bases: the prelude WRITES the split and
        // `fold_factor_base` READS it, and this is the only direction that catches
        // a CUDA-only edit to either.
        (
            "BWD_COEFF_FOLD_FACTOR_SHALLOW_BASE",
            BWD_COEFF_FOLD_FACTOR_SHALLOW_BASE as u64,
        ),
        (
            "BWD_COEFF_FOLD_FACTOR_DEEP_BASE",
            BWD_COEFF_FOLD_FACTOR_DEEP_BASE as u64,
        ),
        ("BWD_COEFF_C_INIT_NONE", BWD_COEFF_C_INIT_NONE as u64),
    ];
    for (name, value) in expected {
        assert_eq!(cuda_literal(name), *value, "CUDA {name}");
    }
    // The expression-valued constants cannot be parsed as literals, so they are
    // pinned by the header's own `static_assert`s — with the expected number
    // built from the Rust mirror, never hand-written here.
    for claim in [
        format!("BWD_COEFF_PROGRAM_BYTE_CAP == {BWD_COEFF_PROGRAM_BYTE_CAP}"),
        format!("BWD_COEFF_HEADER_COEFFICIENT_MASK == {BWD_COEFF_HEADER_COEFFICIENT_MASK:#x}u"),
        format!("BWD_COEFF_HEADER_OPCODE_SHIFT == {BWD_COEFF_HEADER_OPCODE_SHIFT}"),
        format!("BWD_COEFF_HEADER_OPCODE_MASK == {BWD_COEFF_HEADER_OPCODE_MASK:#x}u"),
        format!("BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == {BWD_COEFF_MAX_COEFFICIENT_ENCODINGS}"),
        format!(
            "BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS == {BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS}"
        ),
        format!("BWD_COEFF_SOURCE_WINDOW_COLUMNS == {BWD_COEFF_SOURCE_WINDOW_COLUMNS}"),
        format!("BWD_COEFF_ROWS_PER_BLOCK == {BWD_COEFF_ROWS_PER_BLOCK}"),
    ] {
        assert_header_asserts(&claim);
    }
    assert_eq!(BWD_COEFF_HEADER_COEFFICIENT_MASK, 0x1fff);
    assert_eq!(BWD_COEFF_HEADER_OPCODE_MASK, 0x7);
}

/// Every offset, size and alignment Rust computes is `static_assert`ed with the
/// same number on the CUDA side. The needles are BUILT from `offset_of!`, so
/// there is no hand-maintained number in this test.
#[test]
fn cuda_layout_asserts_match_the_rust_layout() {
    let desc: &[(&str, usize)] = &[
        ("coefficients", offset_of!(BwdCoeffDesc, coefficients)),
        (
            "round_challenges",
            offset_of!(BwdCoeffDesc, round_challenges),
        ),
        ("eq_low", offset_of!(BwdCoeffDesc, eq_low)),
        ("contributions", offset_of!(BwdCoeffDesc, contributions)),
        ("source_windows", offset_of!(BwdCoeffDesc, source_windows)),
        ("eq_sizes", offset_of!(BwdCoeffDesc, eq_sizes)),
        ("num_words", offset_of!(BwdCoeffDesc, num_words)),
        (
            "n_source_windows",
            offset_of!(BwdCoeffDesc, n_source_windows),
        ),
        (
            "n_round_challenges",
            offset_of!(BwdCoeffDesc, n_round_challenges),
        ),
        ("n_coefficients", offset_of!(BwdCoeffDesc, n_coefficients)),
        ("logical_rows", offset_of!(BwdCoeffDesc, logical_rows)),
        ("cell_budget", offset_of!(BwdCoeffDesc, cell_budget)),
        ("c_init", offset_of!(BwdCoeffDesc, c_init)),
        ("pad", offset_of!(BwdCoeffDesc, pad)),
        ("program", offset_of!(BwdCoeffDesc, program)),
    ];
    for (field, offset) in desc {
        assert_header_asserts(&format!(
            "__builtin_offsetof(bwd_coeff_desc, {field}) == {offset}"
        ));
    }
    let window: &[(&str, usize)] = &[
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
    ];
    for (field, offset) in window {
        assert_header_asserts(&format!(
            "__builtin_offsetof(bwd_coeff_source_window, {field}) == {offset}"
        ));
    }
    assert_header_asserts(&format!(
        "sizeof(bwd_coeff_desc) == {}",
        size_of::<BwdCoeffDesc>()
    ));
    assert_header_asserts(&format!(
        "sizeof(bwd_coeff_source_window) == {}",
        size_of::<BwdCoeffSourceWindow>()
    ));
    assert_header_asserts(&format!(
        "alignof(bwd_coeff_source_window) == {}",
        align_of::<BwdCoeffSourceWindow>()
    ));
    assert_header_asserts("sizeof(bwd_coeff_desc) <= BWD_COEFF_DESC_CAP");
    assert_header_asserts("alignof(bwd_coeff_desc) == BWD_COEFF_DESC_ALIGN");
}

/// The launched symbol names ARE the ABI (kernels are `extern "C"`), so the ten
/// release executors plus the fold-factor prelude must all be declared by the
/// header this crate binds against.
#[test]
fn every_launched_symbol_is_declared_by_the_cuda_header() {
    for symbol in [
        "ab_gkr_bwd_coeff_build_fold_factors_kernel",
        "ab_gkr_bwd_coeff_r0_const_kernel",
        "ab_gkr_bwd_coeff_r0_ptr_kernel",
        "ab_gkr_bwd_coeff_ext_d0_const_kernel",
        "ab_gkr_bwd_coeff_ext_d0_ptr_kernel",
        "ab_gkr_bwd_coeff_ext_d1_const_kernel",
        "ab_gkr_bwd_coeff_ext_d1_ptr_kernel",
        "ab_gkr_bwd_coeff_ext_d2_const_kernel",
        "ab_gkr_bwd_coeff_ext_d2_ptr_kernel",
        "ab_gkr_bwd_coeff_ext_d3_const_kernel",
        "ab_gkr_bwd_coeff_ext_d3_ptr_kernel",
        "ab_gkr_bwd_coeff_fold_factors",
    ] {
        assert_header_mentions(symbol);
    }
    // The retired generic backward DAG VM is GONE, not switchable: no symbol,
    // no descriptor, no compatibility path.
    for retired in ["bwd_vm_desc", "ab_gkr_bwd_vm_", "eval_vm_exec.cuh"] {
        assert!(
            !CUDA_HEADER.contains(retired),
            "coefficient_vm.cuh still references the retired generic VM: {retired}"
        );
    }
}

// ── Lowering ─────────────────────────────────────────────────────────────────
//
// Fabricated, never-dereferenced device addresses. The lowering only does
// pointer ARITHMETIC and range comparison; nothing here touches the GPU.

const FAKE_READ_BASE: usize = 0x1000_0000;
const FAKE_PUBLISH_BASE: usize = 0x2000_0000;
const BF_STRIDE: u32 = 4 * 64;
const E4_STRIDE: u32 = 16 * 64;

fn bf_column(base: usize) -> ResolvedColumn {
    ResolvedColumn {
        is_e4: false,
        ptr: base as *const u8,
        matrix_base: base as *mut u8,
        stride_bytes: BF_STRIDE,
    }
}

/// A PUBLISH backing is always E4: §10.2 publishes `2 * rows` E4 per column and
/// the device stores through it as E4 unconditionally, which `lower_window`
/// enforces (`PublishBackingNotExt`). Modelling it as BF would encode the wrong
/// shape as legal.
fn e4_column(base: usize) -> ResolvedColumn {
    ResolvedColumn {
        is_e4: true,
        ptr: base as *const u8,
        matrix_base: base as *mut u8,
        stride_bytes: E4_STRIDE,
    }
}

fn matrix_binding(windows: usize, target_depth: u8) -> CoeffSourceBinding {
    CoeffSourceBinding {
        target_depth,
        materialize: target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH,
        windows: (0..windows)
            .map(|w| BoundSourceWindow {
                family: WindowFamily::BaseLayerWitness,
                first_column: w * BWD_COEFF_SOURCE_WINDOW_COLUMNS,
                columns: vec![BoundColumn {
                    column: w * BWD_COEFF_SOURCE_WINDOW_COLUMNS,
                    source: SourceId(w as u32),
                }],
            })
            .collect(),
        uses: Vec::new(),
    }
}

fn resolved_windows(windows: usize, target_depth: u8) -> Vec<ResolvedBwdCoeffSourceWindow> {
    let materialize = target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH;
    (0..windows)
        .map(|w| ResolvedBwdCoeffSourceWindow {
            read: Some(bf_column(FAKE_READ_BASE + w * 0x1_0000)),
            publish: materialize.then(|| e4_column(FAKE_PUBLISH_BASE + w * 0x1_0000)),
            backing_depth: target_depth,
            target_depth,
            materialize,
        })
        .collect()
}

/// The round is the windows' own target depth: `lower_bwd_coeff` requires the
/// two to agree, because the fold prelude derives its weights from the round
/// while the device derives its catch-up from the window's depths.
fn round_binding(windows: &[ResolvedBwdCoeffSourceWindow]) -> BwdCoeffRoundBinding<'_> {
    let round = windows.first().map_or(0, |window| window.target_depth);
    BwdCoeffRoundBinding {
        round,
        rows: 4_096,
        round_challenges: if round == 0 {
            std::ptr::null()
        } else {
            0x6000_0000 as *const E4
        },
        n_round_challenges: u32::from(round),
        windows,
        eq_low: 0x3000_0000 as *const E4,
        eq_sizes: GkrEqSizes::zeroed(),
        contributions: 0x4000_0000 as *mut E4,
    }
}

/// `Result::expect_err` needs `Debug` on the Ok type, and `BwdCoeffDesc`
/// cannot have it: `[u16; 5760]` is far past the arity `Debug` is derived for.
fn lower_err(
    result: Result<super::lower::BwdCoeffSetup, BwdCoeffLowerError>,
    message: &str,
) -> BwdCoeffLowerError {
    match result {
        Ok(_) => panic!("{message}"),
        Err(error) => error,
    }
}

/// A stream of `words` u16s that is structurally WALKABLE but semantically inert.
///
/// Every even word is a `C0Linear` header naming [`CoefficientRecipeId::ONE`] — a
/// reserved literal, so it consumes no bank entry — and every odd word is a `Cell`
/// record with a varying lane, giving a two-word record. The lowering does not
/// interpret operands, but it DOES walk headers to bound the coefficient bank
/// (`CoefficientIndexPastBank`), so an arbitrary word soup would make these
/// fixtures name random bank indices. The lanes vary so the descriptor's
/// copy-verbatim assertion is not satisfiable by the zero-initialized array.
fn inert_words(words: usize) -> Vec<u16> {
    (0..words)
        .map(|w| {
            if w % 2 == 0 {
                (0 << HEADER_OPCODE_SHIFT) | CoefficientRecipeId::ONE.0 as u16
            } else {
                MODE_CELL | (((w / 2) as u16 & LANE_MASK) << CELL_ENDPOINT0_LANE_SHIFT)
            }
        })
        .collect()
}

fn program(words: usize, c_init: Option<CoefficientRecipeId>) -> EncodedProgram {
    EncodedProgram {
        regime: BwdRegime::R0,
        budget: CellBudget::new(2).unwrap(),
        c_init,
        words: inert_words(words),
    }
}

/// The regime `round` belongs to: R0 IS round zero, every later round is
/// continuation. The depth-policy tests are about depths, not regimes, so they
/// take the program the round actually admits.
fn program_for_round(round: u8, words: usize) -> EncodedProgram {
    EncodedProgram {
        regime: if round == 0 {
            BwdRegime::R0
        } else {
            BwdRegime::Ext
        },
        budget: CellBudget::new(2).unwrap(),
        c_init: None,
        words: inert_words(words),
    }
}

#[test]
fn lowering_fills_the_descriptor_from_the_bound_program() {
    let binding = matrix_binding(3, 0);
    let bound = resolved_windows(3, 0);
    let runtime = round_binding(&bound);
    let encoded = program(12, Some(CoefficientRecipeId::from_bank_index(1)));
    let setup = lower_bwd_coeff(
        &encoded,
        &binding,
        &runtime,
        vec![E4::ZERO; 4],
        std::ptr::null(),
        BwdCoeffBank::Constant,
    )
    .expect("a well-formed round must lower");

    assert_eq!(setup.desc.num_words, 12);
    assert_eq!(&setup.desc.program[..12], encoded.words.as_slice());
    assert!(setup.desc.program[12..].iter().all(|&word| word == 0));
    assert_eq!(setup.desc.n_source_windows, 3);
    assert_eq!(setup.desc.logical_rows, 4_096);
    assert_eq!(setup.desc.cell_budget, 2);
    assert_eq!(setup.desc.n_coefficients, 4);
    assert_eq!(setup.desc.c_init, u16::from(BWD_COEFF_INDEX_RESERVED) + 1);
    assert_eq!(setup.fold_depth, 0);
    assert_eq!(setup.regime, BwdRegime::R0);
    // The Constant bank leaves the coefficient pointer null: the specialization
    // that reads it is not the one this setup launches.
    assert!(setup.desc.coefficients.is_null());

    for window in &setup.desc.source_windows[..3] {
        assert_eq!(window.origin, BWD_COEFF_ORIGIN_READ_BASE);
        assert_eq!(window.procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
        assert_eq!(window.read_stride_bytes, BF_STRIDE);
        assert_eq!(window.materialize, 0);
        assert!(window.publish_base.is_null());
    }
    // Unused slots stay dead.
    for window in &setup.desc.source_windows[3..] {
        assert!(window.read_base.is_null());
        assert_eq!(window.procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
    }
}

#[test]
fn lowering_marks_an_absent_c_init_with_the_sentinel() {
    let binding = matrix_binding(1, 0);
    let bound = resolved_windows(1, 0);
    let setup = lower_bwd_coeff(
        &program(2, None),
        &binding,
        &round_binding(&bound),
        Vec::new(),
        std::ptr::null(),
        BwdCoeffBank::Constant,
    )
    .expect("a c_init-free layer must lower");
    assert_eq!(setup.desc.c_init, BWD_COEFF_C_INIT_NONE);
}

/// A program that does not fit the by-value array is an ERROR, not a fallback
/// to a device pointer (§9.1).
#[test]
fn an_oversized_program_is_rejected_rather_than_spilled_to_a_pointer() {
    let binding = matrix_binding(1, 0);
    let bound = resolved_windows(1, 0);
    let error = lower_err(
        lower_bwd_coeff(
            &program(BWD_COEFF_PROGRAM_WORD_CAP + 1, None),
            &binding,
            &round_binding(&bound),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        ),
        "an oversized program must be rejected",
    );
    assert_eq!(
        error,
        BwdCoeffLowerError::ProgramOverflow {
            words: BWD_COEFF_PROGRAM_WORD_CAP + 1,
            cap: BWD_COEFF_PROGRAM_WORD_CAP,
        }
    );
    // The exact measured maximum still fits.
    assert!(lower_bwd_coeff(
        &program(in_scope::MAX_REALIZED_PROGRAM_WORDS, None),
        &binding,
        &round_binding(&bound),
        Vec::new(),
        std::ptr::null(),
        BwdCoeffBank::Constant,
    )
    .is_ok());
}

#[test]
fn more_windows_than_the_measured_maximum_are_rejected() {
    let windows = BWD_COEFF_SOURCE_WINDOW_CAP + 1;
    let binding = matrix_binding(windows, 0);
    let bound = resolved_windows(windows, 0);
    let error = lower_err(
        lower_bwd_coeff(
            &program(2, None),
            &binding,
            &round_binding(&bound),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        ),
        "more than the measured window maximum must be rejected",
    );
    assert_eq!(
        error,
        BwdCoeffLowerError::SourceWindowOverflow {
            windows,
            cap: BWD_COEFF_SOURCE_WINDOW_CAP,
        }
    );
}

#[test]
fn a_materializing_round_needs_a_publish_backing() {
    let depth = BWD_COEFF_PUBLISH_TARGET_DEPTH;
    let binding = matrix_binding(1, depth);
    let mut bound = resolved_windows(1, depth);
    assert_eq!(bound[0].materialize, true);
    bound[0].publish = None;
    let error = lower_err(
        lower_bwd_coeff(
            &program_for_round(depth, 2),
            &binding,
            &round_binding(&bound),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        ),
        "a materializing window without a publish backing must be rejected",
    );
    assert_eq!(
        error,
        BwdCoeffLowerError::MissingPublishBacking { window: 0 }
    );

    // ...and the policy is static: a non-materializing depth may not opt in.
    let shallow = matrix_binding(1, 0);
    let mut opted_in = resolved_windows(1, 0);
    opted_in[0].materialize = true;
    let error = lower_err(
        lower_bwd_coeff(
            &program(2, None),
            &shallow,
            &round_binding(&opted_in),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        ),
        "the materialization policy is not a per-window choice",
    );
    assert_eq!(
        error,
        BwdCoeffLowerError::MaterializationPolicyMismatch {
            window: 0,
            target_depth: 0,
            materialize: true,
        }
    );
}

#[test]
fn a_c_init_outside_the_bank_is_rejected() {
    let binding = matrix_binding(1, 0);
    let bound = resolved_windows(1, 0);
    let error = lower_err(
        lower_bwd_coeff(
            &program(2, Some(CoefficientRecipeId::from_bank_index(7))),
            &binding,
            &round_binding(&bound),
            vec![E4::ZERO; 2],
            std::ptr::null(),
            BwdCoeffBank::Constant,
        ),
        "a c_init past the bank must be rejected",
    );
    assert_eq!(
        error,
        BwdCoeffLowerError::InvalidCInit {
            index: CoefficientRecipeId::from_bank_index(7).0,
        }
    );
    // The two reserved literals are always available: they never touch a bank.
    for reserved in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE] {
        let setup = lower_bwd_coeff(
            &program(2, Some(reserved)),
            &binding,
            &round_binding(&bound),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        )
        .expect("a reserved literal c_init needs no bank entry");
        assert_eq!(u32::from(setup.desc.c_init), reserved.0);
    }
}

/// A supplied bank must COVER the program's term headers, not merely fit the
/// storage cap.
///
/// `coeff_bank_pointer::operator[]` has no bound of its own, so this is the only
/// thing between a short coefficient vector and an out-of-bounds device read — a
/// stale `ab_gkr_flat_coefficients` slot on the `Constant` bank, past-the-buffer on
/// `DevicePointer`. `c_init` had this check; term headers did not.
#[test]
fn a_term_coefficient_outside_the_bank_is_rejected() {
    let binding = matrix_binding(1, 0);
    let bound = resolved_windows(1, 0);
    // One `C0Linear` header naming bank entry 3, then its `Cell` record.
    let mut words = inert_words(2);
    words[0] = (0 << HEADER_OPCODE_SHIFT) | CoefficientRecipeId::from_bank_index(3).0 as u16;
    let named = EncodedProgram {
        regime: BwdRegime::R0,
        budget: CellBudget::new(2).unwrap(),
        c_init: None,
        words,
    };

    for bank in [BwdCoeffBank::Constant, BwdCoeffBank::DevicePointer] {
        assert_eq!(
            lower_err(
                lower_bwd_coeff(
                    &named,
                    &binding,
                    &round_binding(&bound),
                    vec![E4::ZERO; 3],
                    0x5000_0000 as *const E4,
                    bank,
                ),
                "a bank that does not reach the program's largest index must be rejected",
            ),
            BwdCoeffLowerError::CoefficientIndexPastBank {
                index: 3,
                entries: 3
            }
        );
        // One more entry and the same program lowers: the check is the COVERAGE
        // relation, not a blanket rejection of banked indices.
        lower_bwd_coeff(
            &named,
            &binding,
            &round_binding(&bound),
            vec![E4::ZERO; 4],
            0x5000_0000 as *const E4,
            bank,
        )
        .expect("a bank that covers the largest index must lower");
    }
}

/// A publish backing that is not E4 is rejected.
///
/// The device stores 16-byte E4 endpoint pairs through `window_publish_column`
/// unconditionally (§10.2), so a BF publish column would be written four times past
/// its own element width. `check_column_geometry` cannot see it: a BF column's
/// stride IS a whole number of BF elements.
#[test]
fn a_publish_backing_that_is_not_ext_is_rejected() {
    let depth = BWD_COEFF_PUBLISH_TARGET_DEPTH;
    let binding = matrix_binding(1, depth);
    let mut bound = resolved_windows(1, depth);
    assert!(
        bound[0].publish.is_some_and(|publish| publish.is_e4),
        "the fixture must model a publish backing as E4 — that is the shape §10.2 defines"
    );
    bound[0].publish = Some(bf_column(FAKE_PUBLISH_BASE));
    assert_eq!(
        lower_err(
            lower_bwd_coeff(
                &program_for_round(depth, 2),
                &binding,
                &round_binding(&bound),
                Vec::new(),
                std::ptr::null(),
                BwdCoeffBank::Constant,
            ),
            "a BF publish backing must be rejected",
        ),
        BwdCoeffLowerError::PublishBackingNotExt { window: 0 }
    );
}

#[test]
fn a_publish_range_may_not_alias_a_read_range() {
    let depth = BWD_COEFF_PUBLISH_TARGET_DEPTH;
    let binding = matrix_binding(1, depth);
    let mut bound = resolved_windows(1, depth);
    bound[0].publish = Some(e4_column(FAKE_READ_BASE));
    let error = lower_err(
        lower_bwd_coeff(
            &program_for_round(depth, 2),
            &binding,
            &round_binding(&bound),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        ),
        "publishing into a read range must be rejected",
    );
    assert_eq!(
        error,
        BwdCoeffLowerError::UnsafePublishAlias {
            window: 0,
            other: 0,
        }
    );
}

#[test]
fn the_device_pointer_bank_needs_a_pointer_when_it_has_entries() {
    let binding = matrix_binding(1, 0);
    let bound = resolved_windows(1, 0);
    let error = lower_err(
        lower_bwd_coeff(
            &program(2, None),
            &binding,
            &round_binding(&bound),
            vec![E4::ZERO; 2_000],
            std::ptr::null(),
            BwdCoeffBank::DevicePointer,
        ),
        "a populated device-pointer bank needs its pointer",
    );
    assert_eq!(error, BwdCoeffLowerError::MissingCoefficientPointer);

    // A bank larger than the constant symbol is exactly why the specialization
    // exists; with the pointer supplied it lowers.
    let setup = lower_bwd_coeff(
        &program(2, None),
        &binding,
        &round_binding(&bound),
        vec![E4::ZERO; 2_000],
        0x5000_0000 as *const E4,
        BwdCoeffBank::DevicePointer,
    )
    .expect("a device-pointer bank past FLAT_CONST_MAX must lower");
    assert_eq!(setup.desc.n_coefficients, 2_000);
    assert!(!setup.desc.coefficients.is_null());
    assert!(2_000 > FLAT_CONST_MAX);
}

// ── Round binding: depth policy and catch-up distances ───────────────────────

/// A window whose backing sits `target_depth - backing_depth` folds behind.
fn resolved_window_at(backing_depth: u8, target_depth: u8) -> ResolvedBwdCoeffSourceWindow {
    let materialize = target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH;
    ResolvedBwdCoeffSourceWindow {
        read: Some(bf_column(FAKE_READ_BASE)),
        publish: materialize.then(|| e4_column(FAKE_PUBLISH_BASE)),
        backing_depth,
        target_depth,
        materialize,
    }
}

fn lower_one(
    bound: &[ResolvedBwdCoeffSourceWindow],
    target_depth: u8,
) -> Result<super::lower::BwdCoeffSetup, BwdCoeffLowerError> {
    lower_bwd_coeff(
        &program_for_round(target_depth, 2),
        &matrix_binding(1, target_depth),
        &round_binding(bound),
        Vec::new(),
        std::ptr::null(),
        BwdCoeffBank::Constant,
    )
}

/// §10.2's materialization policy is ONE static constant, and the constant is
/// three: below it nothing publishes, at or above it every source publishes on
/// its first physical access. It is not a scheduling decision, not a per-window
/// choice and not a search parameter, so the binder rejects a window that
/// disagrees with the threshold in either direction.
#[test]
fn materialization_is_the_static_depth_three_threshold() {
    assert_eq!(BWD_COEFF_PUBLISH_TARGET_DEPTH, 3);
    for target_depth in 0..=4u8 {
        let expected = target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH;
        let bound = [resolved_window_at(target_depth, target_depth)];
        let setup = lower_one(&bound, target_depth)
            .unwrap_or_else(|error| panic!("depth {target_depth} must lower: {error:?}"));
        assert_eq!(
            setup.desc.source_windows[0].materialize,
            u8::from(expected),
            "target depth {target_depth} publishes iff it is at or past the threshold"
        );
        assert_eq!(
            setup.desc.source_windows[0].publish_base.is_null(),
            !expected,
            "a publish backing exists exactly when the window materializes"
        );

        // The threshold is not negotiable from either side.
        let mut flipped = bound;
        flipped[0].materialize = !expected;
        flipped[0].publish = (!expected).then(|| e4_column(FAKE_PUBLISH_BASE));
        assert_eq!(
            lower_err(
                lower_one(&flipped, target_depth),
                "the depth-three policy is not a per-window choice",
            ),
            BwdCoeffLowerError::MaterializationPolicyMismatch {
                window: 0,
                target_depth,
                materialize: !expected,
            }
        );
    }
}

/// The runtime factor bank holds the depth-one pair and ONE depth-`fold_depth`
/// leaf table, so a window is either already at target depth, exactly one fold
/// behind, or has never caught up. A depth-two catch-up under D3 would be
/// weighted with D3's challenges and produce a silently wrong fold.
#[test]
fn only_bank_backed_catch_up_distances_lower() {
    for round in 0..=4u8 {
        let fold_depth = bwd_coeff_fold_depth(round);
        for delta in 0..=round.min(BWD_COEFF_MAX_FOLD_DEPTH) {
            let bound = [resolved_window_at(round - delta, round)];
            let supported =
                delta <= fold_depth && (delta == 0 || delta == 1 || delta == fold_depth);
            let result = lower_one(&bound, round);
            if supported {
                assert!(
                    result.is_ok(),
                    "round {round} (D{fold_depth}) must accept a depth-{delta} catch-up"
                );
            } else {
                assert_eq!(
                    lower_err(
                        result,
                        "an unweightable catch-up distance must be rejected on the host",
                    ),
                    BwdCoeffLowerError::UnsupportedFoldDelta {
                        window: 0,
                        delta,
                        fold_depth,
                    },
                    "round {round} (D{fold_depth}) must reject a depth-{delta} catch-up"
                );
            }
        }
    }
}

/// The prelude is handed `n_round_challenges` as its target depth while the
/// device resolves from the window's own depths; the two only name the same
/// challenges when the layer's target depth IS the round.
#[test]
fn the_layer_target_depth_must_be_the_round() {
    let bound = [resolved_window_at(1, 2)];
    let runtime = BwdCoeffRoundBinding {
        round: 3,
        n_round_challenges: 3,
        ..round_binding(&bound)
    };
    assert_eq!(
        lower_err(
            lower_bwd_coeff(
                &program(2, None),
                &matrix_binding(1, 2),
                &runtime,
                Vec::new(),
                std::ptr::null(),
                BwdCoeffBank::Constant,
            ),
            "a layer bound for a different depth than the round must be rejected",
        ),
        BwdCoeffLowerError::RoundTargetDepthMismatch {
            round: 3,
            target_depth: 2,
        }
    );
}

/// A procedural binding with `columns` columns of one virtual-setup kind.
fn procedural_binding(columns: usize, target_depth: u8) -> CoeffSourceBinding {
    CoeffSourceBinding {
        target_depth,
        materialize: target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH,
        windows: vec![BoundSourceWindow {
            family: WindowFamily::VirtualSetup { kind: 0 },
            first_column: 0,
            columns: (0..columns)
                .map(|column| BoundColumn {
                    column,
                    source: SourceId(column as u32),
                })
                .collect(),
        }],
        uses: Vec::new(),
    }
}

/// R0 IS round zero.
///
/// `launch_bwd_coeff` matches `(R0, _, bank)` and always launches the
/// `<true, 0>` specialization, so an R0 program lowered for a later round would
/// run a kernel whose BF resolver cannot fold and whose E4 resolver accumulates
/// leaf zero only — the same silent-wrong-answer class the other two depth
/// guards close, and the one the launcher's wildcard hides.
#[test]
fn an_r0_program_must_be_lowered_for_round_zero() {
    let bound = [resolved_window_at(3, 3)];
    assert_eq!(
        lower_err(
            lower_bwd_coeff(
                &program(2, None),
                &matrix_binding(1, 3),
                &round_binding(&bound),
                Vec::new(),
                std::ptr::null(),
                BwdCoeffBank::Constant,
            ),
            "an R0 program at round three must be rejected",
        ),
        BwdCoeffLowerError::R0RoundMismatch { round: 3 }
    );

    // The guard is one-directional: continuation at round three is exactly what
    // the D3 specialization is for, and continuation at round zero is the legal
    // Ext D0 launch.
    for round in [0u8, 3] {
        let bound = [resolved_window_at(round, round)];
        let ext = EncodedProgram {
            regime: BwdRegime::Ext,
            budget: CellBudget::new(2).unwrap(),
            c_init: None,
            words: vec![0, 0],
        };
        assert!(
            lower_bwd_coeff(
                &ext,
                &matrix_binding(1, round),
                &round_binding(&bound),
                Vec::new(),
                std::ptr::null(),
                BwdCoeffBank::Constant,
            )
            .is_ok(),
            "continuation at round {round} must lower"
        );
    }

    // ...and R0 at round zero, which is the only R0 launch there is.
    let bound = [resolved_window_at(0, 0)];
    assert!(lower_one(&bound, 0).is_ok());
}

/// A procedural value is produced from the backing INDEX, so the device resolver
/// ignores the column coordinate. One virtual-setup kind is one column and each
/// kind is its own family, so binding cannot produce a multi-column procedural
/// window — but a silently ignored coordinate is a wrong answer waiting for the
/// first one that does, so the host rejects it.
#[test]
fn a_multi_column_procedural_window_is_rejected() {
    let bound = [ResolvedBwdCoeffSourceWindow {
        read: None,
        publish: None,
        backing_depth: 0,
        target_depth: 0,
        materialize: false,
    }];
    assert!(
        lower_bwd_coeff(
            &program(2, None),
            &procedural_binding(1, 0),
            &round_binding(&bound),
            Vec::new(),
            std::ptr::null(),
            BwdCoeffBank::Constant,
        )
        .is_ok(),
        "a single-column procedural window is the only shape binding produces"
    );
    assert_eq!(
        lower_err(
            lower_bwd_coeff(
                &program(2, None),
                &procedural_binding(2, 0),
                &round_binding(&bound),
                Vec::new(),
                std::ptr::null(),
                BwdCoeffBank::Constant,
            ),
            "a multi-column procedural window must be rejected",
        ),
        BwdCoeffLowerError::MultiColumnProceduralWindow {
            window: 0,
            columns: 2,
        }
    );
}

/// Round zero, pinned by name.
///
/// Most of the lowering tests above run at round zero only because
/// [`resolved_windows`] defaults to depth zero, and [`round_binding`] now derives
/// the round from the windows it is given. This test states the round-zero shape
/// outright so that coverage cannot drift away again as an unnoticed side effect
/// of a helper default.
#[test]
fn round_zero_lowering_is_pinned_explicitly() {
    let bound = resolved_windows(2, 0);
    let runtime = round_binding(&bound);
    assert_eq!(runtime.round, 0);
    assert_eq!(runtime.n_round_challenges, 0);
    assert!(runtime.round_challenges.is_null());

    let setup = lower_bwd_coeff(
        &program(4, None),
        &matrix_binding(2, 0),
        &runtime,
        Vec::new(),
        std::ptr::null(),
        BwdCoeffBank::Constant,
    )
    .expect("round zero must lower");
    assert_eq!(setup.regime, BwdRegime::R0);
    assert_eq!(setup.fold_depth, 0);
    assert_eq!(setup.desc.n_round_challenges, 0);
    assert!(setup.desc.round_challenges.is_null());
    for window in &setup.desc.source_windows[..2] {
        assert_eq!(window.backing_depth, 0);
        assert_eq!(window.target_depth, 0);
        assert_eq!(window.materialize, 0);
        assert!(window.publish_base.is_null());
    }

    // Moving this program off round zero is rejected at the regime guard, which
    // is upstream of the depth guards — `only_bank_backed_catch_up_distances_lower`
    // covers round zero's "delta must be zero" side.
    let behind = [resolved_window_at(0, 1)];
    assert_eq!(
        lower_err(
            lower_bwd_coeff(
                &program(2, None),
                &matrix_binding(1, 1),
                &round_binding(&behind),
                Vec::new(),
                std::ptr::null(),
                BwdCoeffBank::Constant,
            ),
            "an R0 program has only round zero",
        ),
        BwdCoeffLowerError::R0RoundMismatch { round: 1 }
    );
}
