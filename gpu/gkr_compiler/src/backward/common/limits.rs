//! Backward wire-format limits and measured production-corpus maxima.

use gkr_eval_ir::FieldKind;

use super::model::{CoeffTerm, CoefficientRecipeId};

// ── Encoding limits ──────────────────────────────────────────────────────────

/// `bits 0..12` of the u16 header.
pub const HEADER_COEFFICIENT_BITS: u32 = 13;
/// `bits 13..15` of the u16 header.
pub const HEADER_OPCODE_BITS: u32 = 3;

const _: () = assert!(HEADER_COEFFICIENT_BITS + HEADER_OPCODE_BITS == 16);

/// Coefficient encodings thirteen bits admit, INCLUDING the two reserved
/// literals. A layer's banked recipe count plus
/// [`CoefficientRecipeId::RESERVED`] must not exceed it.
pub const MAX_COEFFICIENT_ENCODINGS: usize = 1 << HEADER_COEFFICIENT_BITS;
const _: () = assert!(MAX_COEFFICIENT_ENCODINGS == 8_192);

/// Opcode values three bits admit, per regime.
pub(crate) const MAX_OPCODES_PER_REGIME: usize = 1 << HEADER_OPCODE_BITS;
const _: () = assert!(MAX_OPCODES_PER_REGIME == 8);

/// Continuation group-header control code. R0 uses the same value for a term,
/// so decoding requires the regime.
pub const LEAN_CONT_GROUP_HEADER_CLASS: u16 = 2;

/// Wire-level cap on one coordinate's immediate table. The GPU
/// descriptor capacity `BWD_SEG_MAX_IMMEDIATES` mirror-asserts EQUAL to this —
/// the crates never import each other's constant.
pub const LEAN_MAX_IMMEDIATES: usize = 512;

/// Number of source windows representable by the six-bit window field.
pub const MAX_SOURCE_WINDOWS: usize = 64;
/// Number of columns representable by the seven-bit column field.
pub const SOURCE_WINDOW_COLUMNS: usize = 128;

/// Maximum by-value kernel argument size.
pub const KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;

/// Alignment of the by-value launch descriptor.
pub const DESCRIPTOR_ALIGNMENT_BYTES: usize = 16;
/// First target depth materialized by the coefficient prologue.
pub const PUBLISH_TARGET_DEPTH: u8 = 3;

const _: () = assert!(PUBLISH_TARGET_DEPTH == 3);

// ── Live term categories ─────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TermCategory {
    C0LinearBf,
    C0LinearE4,
    C2ProductBfBf,
    C2ProductBfE4,
    C2ProductE4E4,
    DualProductE4,
}

impl TermCategory {
    pub const fn tag(self) -> u8 {
        match self {
            TermCategory::C0LinearBf => 0,
            TermCategory::C0LinearE4 => 1,
            TermCategory::C2ProductBfBf => 2,
            TermCategory::C2ProductBfE4 => 3,
            TermCategory::C2ProductE4E4 => 4,
            TermCategory::DualProductE4 => 5,
        }
    }
}

pub(crate) fn term_category(term: &CoeffTerm) -> TermCategory {
    match term {
        CoeffTerm::C0Linear {
            field: FieldKind::Base,
            ..
        } => TermCategory::C0LinearBf,
        CoeffTerm::C0Linear {
            field: FieldKind::Ext,
            ..
        } => TermCategory::C0LinearE4,
        CoeffTerm::C2Product {
            lhs_field,
            rhs_field,
            ..
        } => match (lhs_field, rhs_field) {
            (FieldKind::Base, FieldKind::Base) => TermCategory::C2ProductBfBf,
            (FieldKind::Ext, FieldKind::Ext) => TermCategory::C2ProductE4E4,
            _ => TermCategory::C2ProductBfE4,
        },
        CoeffTerm::DualProduct { .. } => TermCategory::DualProductE4,
    }
}

pub const fn category_arity(category: TermCategory) -> usize {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => 1,
        TermCategory::C2ProductBfBf
        | TermCategory::C2ProductBfE4
        | TermCategory::C2ProductE4E4
        | TermCategory::DualProductE4 => 2,
    }
}
pub(crate) const fn program_bytes(words: usize) -> usize {
    words * 2
}

/// Coefficient recipes available after the two reserved literals.
pub(crate) const LEAN_MAX_COEFFICIENT_RECIPES: usize = 1_150;
/// Source records available in the runtime descriptor.
pub(crate) const LEAN_MAX_SOURCES: usize = 1_072;
/// Inline program capacity of the runtime descriptor.
pub const LEAN_DESCRIPTOR_PROGRAM_WORDS: usize = 6_472;
/// [`LEAN_DESCRIPTOR_PROGRAM_WORDS`] in bytes: 16-byte aligned by construction.
pub const LEAN_DESCRIPTOR_PROGRAM_BYTES: usize = 12_944;

const _: () = assert!(
    LEAN_MAX_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
        <= MAX_COEFFICIENT_ENCODINGS
);
const _: () = assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS.is_multiple_of(DESCRIPTOR_ALIGNMENT_BYTES / 2));
const _: () =
    assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES == program_bytes(LEAN_DESCRIPTOR_PROGRAM_WORDS));
const _: () = assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES < KERNEL_ARGUMENT_CEILING_BYTES);
