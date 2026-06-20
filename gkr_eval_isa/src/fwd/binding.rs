//! Backing/source table: ReadPlace + VirtualSetup ⇄ (slot, col), keyed on storage field (§4,§8,§12).
//! SP1 slot order is CPU-local (deterministic, roundtrippable); NOT GPU-ABI-ready (see TODO(SP3)).

use super::error::BindError;
use super::isa::{MAX_COLS, MAX_SLOTS};
use cs::gkr_compiler::dag_ir::{ReadPlace, VirtualSetupKind};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BackingKey {
    BaseLayerMemory, BaseLayerWitness, Setup, Scratch,
    LayerOutput { layer: usize }, CacheOutput { layer: usize },
    VirtualSetup { kind: VirtualSetupKind },
}

#[derive(Clone, Debug, Default)]
pub struct BackingTable { slots: Vec<BackingKey> }

impl BackingTable {
    // TODO(SP3): reconcile slot order with GpuGKRStorageLayout for GPU-ABI compatibility.
    pub fn intern(&mut self, key: BackingKey) -> Result<u8, BindError> {
        if let Some(i) = self.slots.iter().position(|k| *k == key) { return Ok(i as u8); }
        if self.slots.len() as u32 >= MAX_SLOTS { return Err(BindError::SlotOverflow); }
        self.slots.push(key); Ok((self.slots.len() - 1) as u8)
    }
    pub fn backing(&self, slot: u8) -> Option<&BackingKey> { self.slots.get(slot as usize) }

    pub fn read_slot_col(&mut self, place: &ReadPlace) -> Result<(u8, u16), BindError> {
        let (key, col) = read_place_to_backing(place);
        if col as u32 >= MAX_COLS { return Err(BindError::ColOverflow(col)); }
        Ok((self.intern(key)?, col as u16))
    }
    pub fn virtual_setup_slot(&mut self, kind: &VirtualSetupKind) -> Result<(u8, u16), BindError> {
        Ok((self.intern(BackingKey::VirtualSetup { kind: kind.clone() })?, 0))
    }
}

pub fn read_place_to_backing(place: &ReadPlace) -> (BackingKey, usize) {
    match *place {
        ReadPlace::BaseLayerMemory { column } => (BackingKey::BaseLayerMemory, column),
        ReadPlace::BaseLayerWitness { column } => (BackingKey::BaseLayerWitness, column),
        ReadPlace::Setup { column } => (BackingKey::Setup, column),
        ReadPlace::Scratch { slot } => (BackingKey::Scratch, slot),
        ReadPlace::LayerOutput { layer, offset } => (BackingKey::LayerOutput { layer }, offset),
        ReadPlace::CacheOutput { layer, offset } => (BackingKey::CacheOutput { layer }, offset),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn read_place_maps_and_reuses_slot() {
        let mut t = BackingTable::default();
        let (s, c) = t.read_slot_col(&ReadPlace::BaseLayerMemory { column: 5 }).unwrap();
        assert_eq!(c, 5);
        assert_eq!(t.backing(s), Some(&BackingKey::BaseLayerMemory));
        assert_eq!(t.read_slot_col(&ReadPlace::BaseLayerMemory { column: 9 }).unwrap().0, s);
    }
    #[test]
    fn virtual_setup_gets_a_backing() {
        let mut t = BackingTable::default();
        let (s, c) = t.virtual_setup_slot(&VirtualSetupKind::RangeCheck16Bits).unwrap();
        assert_eq!(c, 0);
        assert!(matches!(t.backing(s), Some(BackingKey::VirtualSetup { .. })));
    }
    #[test]
    fn col_and_slot_overflow_rejected() {
        let mut t = BackingTable::default();
        assert_eq!(t.read_slot_col(&ReadPlace::Setup { column: 1024 }), Err(BindError::ColOverflow(1024)));
        for l in 0..16 { t.intern(BackingKey::LayerOutput { layer: l }).unwrap(); }
        assert_eq!(t.intern(BackingKey::CacheOutput { layer: 0 }), Err(BindError::SlotOverflow));
    }
}
