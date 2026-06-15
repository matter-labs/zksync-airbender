//! Joint matrix-slot table (spec §5). One entry per distinct logical backing
//! key `(canonical_layer, AddressClass, FieldType, stride-class)` — compiler-
//! visible so the CPU oracle can check it; the launcher fills pointers and
//! asserts each matches the key. Shared by AffineSource reads and Materialize
//! stores. <= 16 backings/layer (GKR_MAX_SLOTS).

use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{CodegenLayer, Domain};
use std::collections::HashMap;
// Finding 6 + F5: do NOT mirror the launcher taxonomy — import it, so the
// compiler's slot assignment cannot drift from the model the launcher fills
// pointers against. gpu_gkr_model is CPU-only (deps cs+field, no CUDA, no
// cycle — verified Step 0). AddressClass is re-exported from `address_audit`,
// NOT `storage_layout` (storage_layout imports it privately).
use gpu_gkr_model::address_audit::{AddressClass, classify};
// Per-address storage layer (RR5-F1): 0 for base/setup/virtual-setup/scratch,
// `addr.layer` for InnerLayer/Cached. The launcher classifies each address at
// ITS storage layer, not a build-wide layer.
use gpu_gkr_model::storage_layout::address_storage_layer;
// Field-aware source∪dst collector (RR4-F1) + per-backing column offset, both
// in test_support (F2) so the R3 gate AND this table call the SAME walk.
use crate::test_support::{collect_v2_address_refs, column_offset};

/// Logical backing key (spec §5). Compiler-visible identity of a matrix slot;
/// the launcher fills a pointer for each key and asserts it matches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BackingKey {
    /// PER-ADDRESS storage layer (RR5-F1) = `address_storage_layer(addr)`, NOT
    /// a build-wide layer index. base/setup/scratch → 0; InnerLayer/Cached →
    /// their own `layer`. Mixing a single build-wide layer keys prev-layer
    /// reads and this-layer writes under the wrong backing.
    pub canonical_layer: u32,
    pub class: AddressClass,
    pub field_ext: bool,
    /// Stride-class disambiguator. The corpus has not been observed to need
    /// stride disambiguation, so this is always 0 (single-stride). TODO: if a
    /// future circuit places multiple strides under the same
    /// (layer, class, field), this must distinguish them — GKRAddress carries no
    /// stride source today, so do NOT invent one here; thread the per-layer
    /// `log2_stride` from the storage layout instead.
    pub stride_class: u8,
}

impl BackingKey {
    pub fn field_is_ext(&self) -> bool {
        self.field_ext
    }
}

pub struct MatrixTable {
    keys: Vec<BackingKey>,
    /// addr -> slot, built from the annotated refs. `slot_for` is a lookup, NOT
    /// a key recompute — `GKRAddress` alone can't supply `field_ext` (RR4-F1).
    addr_slot: HashMap<GKRAddress, u8>,
}

impl MatrixTable {
    pub fn build(layer: &CodegenLayer) -> Self {
        let mut keys: Vec<BackingKey> = Vec::new();
        let mut addr_slot: HashMap<GKRAddress, u8> = HashMap::new();

        for (addr, domain) in collect_v2_address_refs(layer) {
            // PER-ADDRESS storage layer (RR5-F1): derived from the address, not
            // a build-wide layer index. `classify` is then applied AT that layer.
            let sl = address_storage_layer(addr);
            let key = BackingKey {
                canonical_layer: sl as u32,
                class: classify(&addr, sl),
                field_ext: domain == Domain::Ext,
                // Single-stride corpus: 0 for all addresses (see BackingKey doc).
                stride_class: 0,
            };
            // Dedup keys preserving first-seen order.
            let slot = match keys.iter().position(|k| *k == key) {
                Some(i) => i as u8,
                None => {
                    let i = keys.len() as u8;
                    keys.push(key);
                    i
                }
            };
            // An address always resolves to the same logical key, so re-inserting
            // is idempotent (a single addr is read and written under one backing).
            addr_slot.insert(addr, slot);
        }

        assert!(
            keys.len() <= 16,
            "matrix table has {} backings, exceeds the 16-slot (4-bit MatrixSlot) cap",
            keys.len()
        );

        MatrixTable { keys, addr_slot }
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// Map lookup (NOT a key recompute — the field isn't derivable from addr).
    pub fn slot_for(&self, addr: &GKRAddress) -> Option<u8> {
        self.addr_slot.get(addr).copied()
    }

    pub fn key(&self, slot: u8) -> BackingKey {
        self.keys[slot as usize]
    }

    /// Per-slot store field — used by the interpreter (Task 3.1) and the
    /// base-arith dst-domain check (Task 2.4/F7).
    pub fn field_is_ext(&self, slot: u8) -> bool {
        self.keys[slot as usize].field_ext
    }

    pub fn column_of(&self, addr: &GKRAddress) -> u16 {
        column_offset(addr) as u16 // shared with the R3 gate (test_support, F2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{collect_v2_address_refs, fixture_path};
    use cs::gkr_compiler::codegen_ir::Domain;
    use gkr_design_space::import::load_circuit;

    #[test]
    fn add_sub_l0_table_small_and_keyed() {
        let c = load_circuit(&fixture_path("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let layer = &c.circuit.layers[0];
        let table = MatrixTable::build(layer);
        assert!(table.len() <= 16, "more than 16 backings/layer");

        // RR3-F3 + RR4-F1: EVERY source AND destination address (cache out, gate
        // dst, inner-layer output) must resolve to a slot whose field matches
        // its producing node's domain — using the SAME field-annotated walk
        // `MatrixTable::build` consumes. A table that mis-keys (or can't resolve)
        // a materialize-destination field fails here, not just for Place reads.
        for (addr, domain) in collect_v2_address_refs(layer) {
            let slot = table.slot_for(&addr).expect("address has a backing slot");
            assert_eq!(
                table.key(slot).field_is_ext(),
                domain == Domain::Ext,
                "slot field for {addr:?} disagrees with its node domain"
            );
        }
    }

    /// RR5-F1: keys must use the PER-ADDRESS storage layer, matching the
    /// launcher's `address_storage_layer`. Exercise an UPPER layer (prev-layer
    /// reads + this-layer writes coexist), which `add_sub` L0 cannot catch.
    #[test]
    fn upper_layer_keys_use_per_address_storage_layer() {
        // Pick a fixture+layer with an inner (layer >= 1) program that actually
        // references addresses (most multi-layer circuits; blake2 with caches).
        let c = load_circuit(&fixture_path("blake2_g_function_codegen_ir_gkr.json")).unwrap();
        let (li, layer) = c
            .circuit
            .layers
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, l)| !collect_v2_address_refs(l).is_empty())
            .expect("an upper layer with addresses");
        let table = MatrixTable::build(layer);
        for (addr, _domain) in collect_v2_address_refs(layer) {
            let slot = table.slot_for(&addr).expect("address has a backing slot");
            // Key layer == the launcher's per-address storage layer, NOT `li`.
            assert_eq!(
                table.key(slot).canonical_layer as usize,
                address_storage_layer(addr),
                "L{li} key layer for {addr:?} != address_storage_layer (build-wide-layer bug)"
            );
        }
    }
}
