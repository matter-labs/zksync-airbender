//! Maps logical reads to dense columns in homogeneous storage slots.
//!
//! Layer and cache slots are field-qualified; base memory, witness, setup, and
//! scratch slots are always base-field. Reverse lookup recovers the original
//! logical offset when binding GPU addresses.

use super::error::BindError;
use super::isa::{Instr, OperandField, OperandLine, Program, MAX_COLS, MAX_SLOTS};
use crate::source_bind::{bind_source_sequence, BindFailure, BoundSourceUse, LogicalSourceUse};
use gkr_eval_ir::ReadPlace;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum BackingKey {
    BaseLayerMemory,
    BaseLayerWitness,
    Setup,
    Scratch, // intrinsically bf matrices
    LayerOutput { layer: usize, field: OperandField },
    CacheOutput { layer: usize, field: OperandField },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceWindow {
    pub backing: BackingKey,
    pub first_column: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SourceWindowTable {
    windows: Vec<SourceWindow>,
}

impl SourceWindowTable {
    pub fn len(&self) -> usize {
        self.windows.len()
    }
    pub fn source_field(&self, window: u8) -> Option<OperandField> {
        self.windows
            .get(window as usize)
            .map(|entry| entry.backing.field())
    }

    pub fn resolve_read_place(&self, window: u8, column: u16) -> Option<ReadPlace> {
        let entry = self.windows.get(window as usize)?;
        let absolute = entry.first_column.checked_add(column as usize)?;
        Some(backing_to_read_place(&entry.backing, absolute))
    }
}

impl BackingKey {
    /// Storage field of the matrix this key names.
    pub(crate) fn field(&self) -> OperandField {
        match self {
            BackingKey::BaseLayerMemory
            | BackingKey::BaseLayerWitness
            | BackingKey::Setup
            | BackingKey::Scratch => OperandField::Base,
            BackingKey::LayerOutput { field, .. } | BackingKey::CacheOutput { field, .. } => *field,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct SlotCols {
    offsets: Vec<usize>,
    index: BTreeMap<usize, u16>,
}

#[derive(Clone, Debug, Default)]
pub struct BackingTable {
    slots: Vec<BackingKey>,
    cols: Vec<SlotCols>, // parallel to `slots`
}

impl BackingTable {
    pub(crate) fn intern(&mut self, key: BackingKey) -> Result<u8, BindError> {
        if let Some(i) = self.slots.iter().position(|k| *k == key) {
            return Ok(i as u8);
        }
        if self.slots.len() as u32 >= MAX_SLOTS {
            return Err(BindError::SlotOverflow);
        }
        self.slots.push(key);
        self.cols.push(SlotCols::default());
        Ok((self.slots.len() - 1) as u8)
    }
    pub(crate) fn backing(&self, slot: u8) -> Option<&BackingKey> {
        self.slots.get(slot as usize)
    }

    /// The storage field of `slot`'s matrix (validation: every `Global`
    /// operand/dst field bit must agree with this).
    pub fn slot_field(&self, slot: u8) -> Option<OperandField> {
        self.slots.get(slot as usize).map(BackingKey::field)
    }

    /// Intern `(key, original offset)` → `(slot, dense col)`. The SINGLE
    /// renumbering authority: reads (`read_slot_col`) and GlobalMaterialize
    /// writes (compile's sink path) both go through here, so a value's read and
    /// write resolve to the same dense column.
    pub(crate) fn slot_col(
        &mut self,
        key: BackingKey,
        offset: usize,
    ) -> Result<(u8, u16), BindError> {
        let slot = self.intern(key)?;
        let sc = &mut self.cols[slot as usize];
        if let Some(&column) = sc.index.get(&offset) {
            return Ok((slot, column));
        }
        let c = sc.offsets.len();
        if c as u32 >= MAX_COLS {
            return Err(BindError::ColOverflow(offset));
        }
        sc.offsets.push(offset);
        sc.index.insert(offset, c as u16);
        Ok((slot, c as u16))
    }

    pub(crate) fn strip_indexes(&mut self) {
        for cols in &mut self.cols {
            cols.index = BTreeMap::new();
        }
    }

    /// Resolve a read to `(slot, dense col)`. `field` is the READ's field (the
    /// producing sink's field for cross-layer places — see
    /// `build_cross_layer_field_map`); it selects which homogeneous matrix
    /// (slot) of a mixed logical output the read targets. Intrinsically-bf
    /// places ignore it (their key carries no field).
    pub(crate) fn read_slot_col(
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
    pub(crate) fn slot_columns(&self, slot: u8) -> &[usize] {
        self.cols
            .get(slot as usize)
            .map(|sc| sc.offsets.as_slice())
            .unwrap_or(&[])
    }
}

/// One logical read this program still makes, in operand-visit order.
///
struct LogicalRead {
    backing: BackingKey,
    absolute: usize,
}

/// Rewrite compiler-private logical reads after all source-moving peepholes.
/// Windows are freely based, deterministic, and contain only surviving reads.
///
/// The window partitioning and first-access marking are
/// [`crate::source_bind::bind_source_sequence`]; this is the `Program` adapter
/// around it. Window numbering is unchanged: the core numbers windows by ascending
/// backing index, and this adapter indexes backings in `BackingKey` order.
pub(crate) fn bind_final_sources(
    program: &mut Program,
    backings: &BackingTable,
) -> Result<SourceWindowTable, BindError> {
    let mut reads = Vec::<LogicalRead>::new();
    visit_operands_mut(program, |operand| {
        if let OperandLine::LogicalGlobal { slot, col } = *operand {
            let backing = backings
                .backing(slot)
                .cloned()
                .ok_or(BindError::UnknownLogicalSource { slot, col })?;
            let absolute = backings
                .slot_columns(slot)
                .get(col as usize)
                .copied()
                .ok_or(BindError::UnknownLogicalSource { slot, col })?;
            reads.push(LogicalRead { backing, absolute });
        }
        Ok(())
    })?;

    // Windows are numbered in `BackingKey` order, so that is the order the core's
    // backing indices are assigned in.
    let keys: Vec<BackingKey> = reads
        .iter()
        .map(|read| read.backing.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let index_of: BTreeMap<&BackingKey, u8> = keys
        .iter()
        .enumerate()
        .map(|(index, key)| (key, index as u8))
        .collect();
    let sequence: Vec<LogicalSourceUse> = reads
        .iter()
        .map(|read| LogicalSourceUse {
            slot: index_of[&read.backing],
            column: read.absolute,
        })
        .collect();

    let binding = bind_source_sequence(&sequence).map_err(|failure| match failure {
        BindFailure::WindowOverflow => BindError::SourceWindowOverflow,
    })?;

    let table = SourceWindowTable {
        windows: binding
            .windows
            .iter()
            .map(|window| SourceWindow {
                backing: keys[window.slot as usize].clone(),
                first_column: window.first_column,
            })
            .collect(),
    };

    // Same visit order as the collecting pass, so `binding.uses[i]` is the
    // coordinate of the `i`-th logical operand.
    let mut bound = binding.uses.iter();
    visit_operands_mut(program, |operand| {
        if !matches!(*operand, OperandLine::LogicalGlobal { .. }) {
            return Ok(());
        }
        let &BoundSourceUse { window, column } = bound
            .next()
            .expect("one bound coordinate per logical operand");
        *operand = OperandLine::Source {
            window,
            column: column.into(),
        };
        Ok(())
    })?;
    debug_assert!(
        bound.next().is_none(),
        "every bound coordinate was consumed"
    );
    Ok(table)
}

fn visit_operands_mut(
    program: &mut Program,
    mut visit: impl FnMut(&mut OperandLine) -> Result<(), BindError>,
) -> Result<(), BindError> {
    for instr in &mut program.instrs {
        match instr {
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                for operand in operands {
                    visit(operand)?;
                }
            }
            Instr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    visit(lhs)?;
                    visit(rhs)?;
                }
            }
            Instr::Mov { src, .. } => {
                if let Some(src) = src {
                    visit(src)?;
                }
            }
        }
    }
    Ok(())
}

/// The field-qualified backing key + ORIGINAL offset of a read. `field` is the
/// read's storage field; only `LayerOutput`/`CacheOutput` keys carry it.
fn read_place_to_backing(place: &ReadPlace, field: OperandField) -> (BackingKey, usize) {
    match *place {
        ReadPlace::BaseLayerMemory { column } => (BackingKey::BaseLayerMemory, column),
        ReadPlace::BaseLayerWitness { column } => (BackingKey::BaseLayerWitness, column),
        ReadPlace::Setup { column } => (BackingKey::Setup, column),
        ReadPlace::Scratch { slot } => (BackingKey::Scratch, slot),
        ReadPlace::LayerOutput { layer, offset } => {
            (BackingKey::LayerOutput { layer, field }, offset)
        }
        ReadPlace::CacheOutput { layer, offset } => {
            (BackingKey::CacheOutput { layer, field }, offset)
        }
    }
}

fn backing_to_read_place(backing: &BackingKey, offset: usize) -> ReadPlace {
    match *backing {
        BackingKey::BaseLayerMemory => ReadPlace::BaseLayerMemory { column: offset },
        BackingKey::BaseLayerWitness => ReadPlace::BaseLayerWitness { column: offset },
        BackingKey::Setup => ReadPlace::Setup { column: offset },
        BackingKey::Scratch => ReadPlace::Scratch { slot: offset },
        BackingKey::LayerOutput { layer, .. } => ReadPlace::LayerOutput { layer, offset },
        BackingKey::CacheOutput { layer, .. } => ReadPlace::CacheOutput { layer, offset },
    }
}
