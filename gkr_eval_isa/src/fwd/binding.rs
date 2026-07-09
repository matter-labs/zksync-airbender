//! Backing/source table: ReadPlace ⇄ (slot, col), keyed on storage field (§4,§8,§12).
//!
//! v2 (spec §2): a slot IS one homogeneous device matrix. Production storage keeps
//! separate consolidated base and ext backings per logical layer/cache output
//! (out_base/out_ext, cache_base/cache_ext), so `LayerOutput`/`CacheOutput` keys are
//! FIELD-QUALIFIED — a mixed logical output uses TWO slots, one per matrix.
//! `BaseLayerMemory`/`BaseLayerWitness`/`Setup`/`Scratch` are intrinsically bf
//! (see `cs::gkr_compiler::dag_ir::field_infer`: base-storage places are always
//! `FieldKind::Base`; GPU `ScratchSpace` resolves through `base_field_inputs`).
//!
//! Column indices are DENSE PER SLOT: `slot_col`/`read_slot_col` renumber the
//! original layer-offset to the slot's next dense matrix-column index, so the v2
//! descriptor can address column `c` of slot `s` as `base[s] + c * stride[s]`.
//! The reverse map (`slot_col_to_read_place`, `slot_columns`) is first-class:
//! every reader that needs the ORIGINAL offset (CPU interp resolution, GPU
//! address wiring, disassembly) must go through it — a dense col is meaningless
//! outside its table.

use super::error::BindError;
use super::isa::{OperandField, MAX_COLS, MAX_SLOTS};
use cs::gkr_compiler::dag_ir::ReadPlace;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BackingKey {
    BaseLayerMemory, BaseLayerWitness, Setup, Scratch, // intrinsically bf matrices
    LayerOutput { layer: usize, field: OperandField },
    CacheOutput { layer: usize, field: OperandField },
}

impl BackingKey {
    /// The storage field of the matrix this key names (spec §2: one slot = one
    /// homogeneous matrix). Base-storage keys are intrinsically bf.
    pub fn field(&self) -> OperandField {
        match self {
            BackingKey::BaseLayerMemory
            | BackingKey::BaseLayerWitness
            | BackingKey::Setup
            | BackingKey::Scratch => OperandField::Base,
            BackingKey::LayerOutput { field, .. } | BackingKey::CacheOutput { field, .. } => *field,
        }
    }
}

/// Per-slot dense column renumbering: original layer-offset → dense matrix col,
/// plus the dense-ordered offset list for the reverse direction.
#[derive(Clone, Debug, Default)]
struct SlotCols {
    dense_of: BTreeMap<usize, u16>, // original offset -> dense col
    offsets: Vec<usize>,            // dense col -> original offset (assignment order)
}

#[derive(Clone, Debug, Default)]
pub struct BackingTable {
    slots: Vec<BackingKey>,
    cols: Vec<SlotCols>, // parallel to `slots`
}

impl BackingTable {
    pub fn intern(&mut self, key: BackingKey) -> Result<u8, BindError> {
        if let Some(i) = self.slots.iter().position(|k| *k == key) { return Ok(i as u8); }
        if self.slots.len() as u32 >= MAX_SLOTS { return Err(BindError::SlotOverflow); }
        self.slots.push(key);
        self.cols.push(SlotCols::default());
        Ok((self.slots.len() - 1) as u8)
    }
    pub fn backing(&self, slot: u8) -> Option<&BackingKey> { self.slots.get(slot as usize) }

    /// The storage field of `slot`'s matrix (validation: every `Global`
    /// operand/dst field bit must agree with this).
    pub fn slot_field(&self, slot: u8) -> Option<OperandField> {
        self.slots.get(slot as usize).map(BackingKey::field)
    }

    /// Number of interned slots (≤ `MAX_SLOTS`).
    pub fn n_slots(&self) -> usize { self.slots.len() }

    /// Intern `(key, original offset)` → `(slot, dense col)`. The SINGLE
    /// renumbering authority: reads (`read_slot_col`) and GlobalMaterialize
    /// writes (compile's sink path) both go through here, so a value's read and
    /// write resolve to the same dense column.
    pub fn slot_col(&mut self, key: BackingKey, offset: usize) -> Result<(u8, u16), BindError> {
        let slot = self.intern(key)?;
        let sc = &mut self.cols[slot as usize];
        if let Some(&c) = sc.dense_of.get(&offset) { return Ok((slot, c)); }
        let c = sc.offsets.len();
        if c as u32 >= MAX_COLS { return Err(BindError::ColOverflow(offset)); }
        sc.dense_of.insert(offset, c as u16);
        sc.offsets.push(offset);
        Ok((slot, c as u16))
    }

    /// Resolve a read to `(slot, dense col)`. `field` is the READ's field (the
    /// producing sink's field for cross-layer places — see
    /// `build_cross_layer_field_map`); it selects which homogeneous matrix
    /// (slot) of a mixed logical output the read targets. Intrinsically-bf
    /// places ignore it (their key carries no field).
    pub fn read_slot_col(
        &mut self,
        place: &ReadPlace,
        field: OperandField,
    ) -> Result<(u8, u16), BindError> {
        let (key, offset) = read_place_to_backing(place, field);
        self.slot_col(key, offset)
    }

    /// First-class reverse map: the `ReadPlace` (with ORIGINAL offset) behind a
    /// `(slot, dense col)`. `None` for an unknown slot or an unassigned column.
    pub fn slot_col_to_read_place(&self, slot: u8, col: u16) -> Option<ReadPlace> {
        let key = self.slots.get(slot as usize)?;
        let offset = *self.cols.get(slot as usize)?.offsets.get(col as usize)?;
        Some(match *key {
            BackingKey::BaseLayerMemory => ReadPlace::BaseLayerMemory { column: offset },
            BackingKey::BaseLayerWitness => ReadPlace::BaseLayerWitness { column: offset },
            BackingKey::Setup => ReadPlace::Setup { column: offset },
            BackingKey::Scratch => ReadPlace::Scratch { slot: offset },
            BackingKey::LayerOutput { layer, .. } => ReadPlace::LayerOutput { layer, offset },
            BackingKey::CacheOutput { layer, .. } => ReadPlace::CacheOutput { layer, offset },
        })
    }

    /// The slot's original offsets in dense-column order (`slot_columns(s)[c]`
    /// is the original offset of dense col `c`). Empty for an unknown slot.
    /// The descriptor lowering orders matrix columns with this.
    pub fn slot_columns(&self, slot: u8) -> &[usize] {
        self.cols.get(slot as usize).map(|sc| sc.offsets.as_slice()).unwrap_or(&[])
    }
}

/// The field-qualified backing key + ORIGINAL offset of a read. `field` is the
/// read's storage field; only `LayerOutput`/`CacheOutput` keys carry it.
pub fn read_place_to_backing(place: &ReadPlace, field: OperandField) -> (BackingKey, usize) {
    match *place {
        ReadPlace::BaseLayerMemory { column } => (BackingKey::BaseLayerMemory, column),
        ReadPlace::BaseLayerWitness { column } => (BackingKey::BaseLayerWitness, column),
        ReadPlace::Setup { column } => (BackingKey::Setup, column),
        ReadPlace::Scratch { slot } => (BackingKey::Scratch, slot),
        ReadPlace::LayerOutput { layer, offset } => (BackingKey::LayerOutput { layer, field }, offset),
        ReadPlace::CacheOutput { layer, offset } => (BackingKey::CacheOutput { layer, field }, offset),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_place_maps_and_reuses_slot() {
        let mut t = BackingTable::default();
        let (s, c) = t
            .read_slot_col(&ReadPlace::BaseLayerMemory { column: 5 }, OperandField::Base)
            .unwrap();
        assert_eq!(c, 0, "first column of a slot is dense col 0");
        assert_eq!(t.backing(s), Some(&BackingKey::BaseLayerMemory));
        let (s2, c2) = t
            .read_slot_col(&ReadPlace::BaseLayerMemory { column: 9 }, OperandField::Base)
            .unwrap();
        assert_eq!(s2, s);
        assert_eq!(c2, 1);
        // Re-reading an already-interned offset returns the SAME dense col.
        let (s3, c3) = t
            .read_slot_col(&ReadPlace::BaseLayerMemory { column: 5 }, OperandField::Base)
            .unwrap();
        assert_eq!((s3, c3), (s, 0));
    }

    /// Same logical layer output read as Base and Ext → two DISTINCT slots (one
    /// per homogeneous matrix), each with its own dense column space.
    #[test]
    fn mixed_layer_output_uses_two_slots() {
        let mut t = BackingTable::default();
        let (sb, cb) = t
            .read_slot_col(&ReadPlace::LayerOutput { layer: 3, offset: 7 }, OperandField::Base)
            .unwrap();
        let (se, ce) = t
            .read_slot_col(&ReadPlace::LayerOutput { layer: 3, offset: 8 }, OperandField::Ext)
            .unwrap();
        assert_ne!(sb, se, "base and ext halves of one layer output are separate slots");
        assert_eq!((cb, ce), (0, 0), "each slot's dense column space starts at 0");
        assert_eq!(
            t.backing(sb),
            Some(&BackingKey::LayerOutput { layer: 3, field: OperandField::Base })
        );
        assert_eq!(
            t.backing(se),
            Some(&BackingKey::LayerOutput { layer: 3, field: OperandField::Ext })
        );
        assert_eq!(t.slot_field(sb), Some(OperandField::Base));
        assert_eq!(t.slot_field(se), Some(OperandField::Ext));
        // CacheOutput splits the same way.
        let (scb, _) = t
            .read_slot_col(&ReadPlace::CacheOutput { layer: 3, offset: 0 }, OperandField::Base)
            .unwrap();
        let (sce, _) = t
            .read_slot_col(&ReadPlace::CacheOutput { layer: 3, offset: 0 }, OperandField::Ext)
            .unwrap();
        assert_ne!(scb, sce);
    }

    /// Sparse original offsets 3, 9, 40 renumber to dense cols 0, 1, 2.
    #[test]
    fn cols_are_dense_per_slot() {
        let mut t = BackingTable::default();
        let mut cols = Vec::new();
        for off in [3usize, 9, 40] {
            let (s, c) = t
                .read_slot_col(&ReadPlace::Setup { column: off }, OperandField::Base)
                .unwrap();
            assert_eq!(s, 0);
            cols.push(c);
        }
        assert_eq!(cols, vec![0, 1, 2]);
        assert_eq!(t.slot_columns(0), &[3, 9, 40]);
        // A second slot's columns are independent (dense from 0 again).
        let (s, c) = t
            .read_slot_col(&ReadPlace::Scratch { slot: 40 }, OperandField::Base)
            .unwrap();
        assert_eq!((s, c), (1, 0));
    }

    /// `slot_col_to_read_place(read_slot_col(p)) == p` for every ReadPlace variant.
    #[test]
    fn reverse_map_roundtrips() {
        let places: Vec<(ReadPlace, OperandField)> = vec![
            (ReadPlace::BaseLayerMemory { column: 22 }, OperandField::Base),
            (ReadPlace::BaseLayerWitness { column: 17 }, OperandField::Base),
            (ReadPlace::Setup { column: 1023 }, OperandField::Base),
            (ReadPlace::Scratch { slot: 4 }, OperandField::Base),
            (ReadPlace::LayerOutput { layer: 2, offset: 9 }, OperandField::Base),
            (ReadPlace::LayerOutput { layer: 2, offset: 10 }, OperandField::Ext),
            (ReadPlace::CacheOutput { layer: 5, offset: 0 }, OperandField::Base),
            (ReadPlace::CacheOutput { layer: 5, offset: 3 }, OperandField::Ext),
        ];
        let mut t = BackingTable::default();
        for (place, field) in &places {
            let (s, c) = t.read_slot_col(place, *field).unwrap();
            assert_eq!(
                t.slot_col_to_read_place(s, c).as_ref(),
                Some(place),
                "roundtrip failed for {place:?} ({field:?})"
            );
        }
        // Writes renumber identically to reads: the sink path (`slot_col`) on the
        // same (key, offset) resolves to the same (slot, col).
        let (s, c) = t
            .slot_col(BackingKey::CacheOutput { layer: 5, field: OperandField::Ext }, 3)
            .unwrap();
        assert_eq!(
            t.slot_col_to_read_place(s, c),
            Some(ReadPlace::CacheOutput { layer: 5, offset: 3 })
        );
        // Unknown slot / unassigned col → None.
        assert_eq!(t.slot_col_to_read_place(15, 0), None);
        assert_eq!(t.slot_col_to_read_place(0, 999), None);
    }

    #[test]
    fn col_and_slot_overflow_rejected() {
        let mut t = BackingTable::default();
        // Cols are dense per slot: the 1025th DISTINCT column overflows (the
        // original offset no longer matters — offset 1024 alone is dense col 0).
        for col in 0..MAX_COLS as usize {
            t.read_slot_col(&ReadPlace::Setup { column: col * 7 }, OperandField::Base).unwrap();
        }
        assert_eq!(
            t.read_slot_col(&ReadPlace::Setup { column: 99999 }, OperandField::Base),
            Err(BindError::ColOverflow(99999))
        );
        let mut t = BackingTable::default();
        for l in 0..16 {
            t.intern(BackingKey::LayerOutput { layer: l, field: OperandField::Base }).unwrap();
        }
        assert_eq!(
            t.intern(BackingKey::CacheOutput { layer: 0, field: OperandField::Base }),
            Err(BindError::SlotOverflow)
        );
        // A field-qualified twin of an existing layer counts as a NEW slot.
        assert_eq!(
            t.intern(BackingKey::LayerOutput { layer: 0, field: OperandField::Ext }),
            Err(BindError::SlotOverflow)
        );
    }
}
