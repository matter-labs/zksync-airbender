//! IndirectSource gather descriptors (spec §4). Four visible variants; the
//! n/mapping/n_len/predicate fields live off the joint matrix table. The
//! descriptor is what makes gather schedulable instead of opaque-NativeK.
//!
//! # Plain vs. decoder VectorizedLookup (IR gap note)
//!
//! `CacheKind::VectorizedLookup` carries NO explicit decoder field in the IR
//! (`cs/src/gkr_compiler/codegen_ir.rs` :292). The plain/decoder distinction
//! is `lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX` (= `usize::MAX`,
//! `cs::definitions::DECODER_LOOKUP_FORMAL_SET_INDEX`), which is how
//! `cache_relation.rs` (line 383) distinguishes the two paths at runtime.
//! `variant_for` branches on this same field — it is not a plan gap, but an
//! IR convention that the constant encodes.

use crate::isa_v2::IndirectKind;
use cs::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
use cs::gkr_compiler::codegen_ir::CacheKind;

/// Full gather descriptor for one `CacheKind`. `n_slot`, `mapping_slot`,
/// `n_len`, and `decoder` are filled by Task 2.5 (`build_descriptor`); this
/// task only proves the variant classification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GatherDescriptor {
    pub kind: IndirectKind,
    pub field_ext: bool,
    /// Matrix-slot of the value table `n` (None for MappedVirtualBf which reads
    /// virtual_setup). Filled by Task 2.5.
    pub n_slot: Option<u8>,
    /// Matrix-slot of the `mapping` table (None for RowIndexedSetupE4).
    /// Filled by Task 2.5.
    pub mapping_slot: Option<u8>,
    /// Length guard for RowIndexedSetupE4. Filled by Task 2.5.
    pub n_len: Option<u32>,
    /// Decoder predicate + fill scalar for DecoderMappedE4. Filled by Task 2.5.
    pub decoder: Option<DecoderSpec>,
}

/// Decoder-lookup-specific fields: the fill α-power index and the lookup
/// table id. Used only when `kind == IndirectKind::DecoderMappedE4`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecoderSpec {
    pub fill_alpha_power: u16,
    pub table_id: u32,
}

/// Classify a `CacheKind` into the corresponding `(IndirectKind, field_ext)`.
///
/// Mapping:
/// - `SingleColumnLookup`        → `(MappedVirtualBf,  false)` — base field,
///   virtual-setup read via a per-row mapping table (cache_relation.rs:347,
///   lookup_helpers.cuh:51).
/// - `VectorizedLookup` plain    → `(MappedGenericE4,  true)` — ext field,
///   generic lookup table `n` indexed via a mapping (cache_relation.rs:382,
///   lookup_helpers.cuh:58). "Plain" = `lookup_set_index != usize::MAX`.
/// - `VectorizedLookup` decoder  → `(DecoderMappedE4,  true)` — ext field,
///   same load shape but with a predicate mask + fill scalar
///   (cache_relation.rs:394, lookup_helpers.cuh:70). "Decoder" =
///   `lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX` (= `usize::MAX`).
/// - `VectorizedLookupSetup`     → `(RowIndexedSetupE4, true)` — ext field,
///   row-indexed (no mapping), length-guarded (cache_relation.rs:421,
///   gkr_forward_generation.cuh LOOKUP_SETUP).
/// - `MemoryTuple`               → not a gather; call `routine_for_cache`
///   instead. This arm panics.
pub fn variant_for(k: &CacheKind) -> (IndirectKind, bool) {
    match k {
        CacheKind::SingleColumnLookup { .. } => (IndirectKind::MappedVirtualBf, false),
        CacheKind::VectorizedLookup { lookup_set_index, .. } => {
            if *lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
                (IndirectKind::DecoderMappedE4, true)
            } else {
                (IndirectKind::MappedGenericE4, true)
            }
        }
        CacheKind::VectorizedLookupSetup => (IndirectKind::RowIndexedSetupE4, true),
        CacheKind::MemoryTuple { .. } => {
            panic!("MemoryTuple is not a gather variant; use routine_for_cache instead")
        }
    }
}

/// Build a `GatherDescriptor` from a `CacheKind`. Variant and `field_ext` come
/// from `variant_for`. The slot/len/decoder fields are matrix-table /
/// forward-setup specifics that the FORWARD path does not need to bind
/// structurally (a forward inline gather of a CACHED VALUE is identified by its
/// descriptor INDEX in the operand lane — spec §4); they are left `None` here
/// and filled precisely by the Phase-3 interpreter from the forward setup. The
/// `decoder` predicate/fill scalar is the one variant-specific datum the
/// decoder lookup carries; the IR exposes it via the `lookup_set_index ==
/// DECODER_LOOKUP_FORMAL_SET_INDEX` convention only (no fill α-power / table id
/// in the per-layer IR), so it is left `None` for Phase-3 to resolve against
/// the circuit globals.
pub fn build_descriptor(k: &CacheKind) -> GatherDescriptor {
    let (kind, field_ext) = variant_for(k);
    GatherDescriptor {
        kind,
        field_ext,
        // Forward inline gather: the table/mapping pointers live on the forward
        // setup, bound by the Phase-3 interpreter from the descriptor variant.
        n_slot: None,
        mapping_slot: None,
        n_len: None,
        decoder: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa_v2::IndirectKind;
    use cs::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
    use cs::gkr_compiler::codegen_ir::{CacheKind, LinearComb};

    fn single_col() -> CacheKind {
        CacheKind::SingleColumnLookup {
            column: LinearComb { terms: vec![], constant: 0 },
            lookup_set_index: 0,
            range_check_width: 16,
        }
    }

    fn vec_lookup_plain() -> CacheKind {
        CacheKind::VectorizedLookup {
            columns: vec![],
            lookup_set_index: 3, // any value != usize::MAX
        }
    }

    fn vec_lookup_decoder() -> CacheKind {
        CacheKind::VectorizedLookup {
            columns: vec![],
            lookup_set_index: DECODER_LOOKUP_FORMAL_SET_INDEX, // usize::MAX
        }
    }

    fn vec_setup() -> CacheKind {
        CacheKind::VectorizedLookupSetup
    }

    #[test]
    fn cache_kind_to_gather_variant() {
        // SingleColumnLookup → MappedVirtualBf, base (field_ext = false)
        assert_eq!(variant_for(&single_col()).0, IndirectKind::MappedVirtualBf);
        assert!(!variant_for(&single_col()).1, "SingleColumnLookup must be base field");

        // VectorizedLookup plain → MappedGenericE4, ext
        assert_eq!(variant_for(&vec_lookup_plain()).0, IndirectKind::MappedGenericE4);
        assert!(variant_for(&vec_lookup_plain()).1, "VectorizedLookup plain must be ext field");

        // VectorizedLookup decoder → DecoderMappedE4, ext
        assert_eq!(variant_for(&vec_lookup_decoder()).0, IndirectKind::DecoderMappedE4);
        assert!(
            variant_for(&vec_lookup_decoder()).1,
            "VectorizedLookup decoder must be ext field"
        );

        // VectorizedLookupSetup → RowIndexedSetupE4, ext
        assert_eq!(variant_for(&vec_setup()).0, IndirectKind::RowIndexedSetupE4);
        assert!(variant_for(&vec_setup()).1, "VectorizedLookupSetup must be ext field");
    }
}
