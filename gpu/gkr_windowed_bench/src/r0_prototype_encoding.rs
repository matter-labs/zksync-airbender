use std::array;

use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::backward::{
    CoeffGroupingAnalysis, CoeffLayer, CoeffTerm, NormalizedCoefficientRecipe, SourceId,
    SOURCE_NONE,
};
use serde::{Deserialize, Serialize};

use crate::accumulator_schedule::{
    ScheduleViews, SemanticSourceKey, SourceProjection, SplitSchedule,
};
use crate::r0_artifact::{FrozenR0Challenge, FrozenR0Coordinate, FrozenR0Product, FrozenR0Recipe};
use crate::r0_prototype_manifest::R0ProgramEncoding;

const BABY_BEAR_ORDER: u64 = 2_013_265_921;
const CLASS_SHIFT: u32 = 13;
const COEFFICIENT_MASK: u16 = 0x1fff;
const COMPACT_TAG_BITS: u8 = 3;
const COMPACT_TAG_LINEAR_DIRECT: u32 = 0;
const COMPACT_TAG_PRODUCT_SAME_WINDOW: u32 = 1;
const COMPACT_TAG_PRODUCT_DIRECT: u32 = 2;
const COMPACT_TAG_ESCAPE: u32 = 7;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0Phase {
    Bf,
    E4,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct R0PrototypeOp {
    pub phase: R0Phase,
    pub term_class: u8,
    pub coefficient_id: u32,
    pub source_a: SemanticSourceKey,
    pub source_b: Option<SemanticSourceKey>,
    pub group_id: Option<u32>,
    pub member_index: Option<u32>,
}

impl R0PrototypeOp {
    fn semantic_record(&self) -> (u8, u32, SemanticSourceKey, Option<SemanticSourceKey>) {
        (
            self.term_class,
            self.coefficient_id,
            self.source_a,
            self.source_b,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurrentFixedProgram {
    pub program_words: Vec<u16>,
    pub source_slots: Vec<u16>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixedRecord {
    pub header: u16,
    pub source_a: u16,
    pub source_b: u16,
    pub reserved: u16,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SplitFixedSlotProgram {
    pub bf: Vec<FixedRecord>,
    pub e4: Vec<FixedRecord>,
    pub source_slots: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SplitFixedDirectProgram {
    pub bf: Vec<FixedRecord>,
    pub e4: Vec<FixedRecord>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HomogeneousSlotProgram {
    pub classes: [Vec<FixedRecord>; 5],
    pub order: Vec<u8>,
    pub source_slots: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HomogeneousDirectProgram {
    pub classes: [Vec<FixedRecord>; 5],
    pub order: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StoredSource {
    Slot(u16),
    Direct(u16),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GroupedMember {
    pub term_class: u8,
    pub immediate: u32,
    pub source_a: StoredSource,
    pub source_b: Option<StoredSource>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GroupedAtom {
    Singleton {
        phase: R0Phase,
        coefficient_id: u32,
        term_class: u8,
        source_a: StoredSource,
        source_b: Option<StoredSource>,
    },
    Group {
        phase: R0Phase,
        group_id: u32,
        core: FrozenR0Recipe,
        members: Vec<GroupedMember>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GroupedSlotProgram {
    pub atoms: Vec<GroupedAtom>,
    pub source_slots: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GroupedDirectProgram {
    pub atoms: Vec<GroupedAtom>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactR0Program {
    pub words: Vec<u32>,
    pub source_slots: Vec<u16>,
    pub coefficient_bits: u8,
    pub window_bits: u8,
    pub column_bits: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum R0EncodedProgram {
    CurrentFixedSlot(CurrentFixedProgram),
    CompactR0Port(CompactR0Program),
    SplitFixedSlot(SplitFixedSlotProgram),
    SplitFixedDirect(SplitFixedDirectProgram),
    HomogeneousSlot(HomogeneousSlotProgram),
    HomogeneousDirect(HomogeneousDirectProgram),
    GroupedSlot(GroupedSlotProgram),
    GroupedDirect(GroupedDirectProgram),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeProgramEntry {
    pub encoding: R0ProgramEncoding,
    pub operations: Vec<R0PrototypeOp>,
    pub encoded: R0EncodedProgram,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeProgramSet {
    pub entries: Vec<R0PrototypeProgramEntry>,
}

impl R0PrototypeProgramSet {
    pub fn get(&self, encoding: R0ProgramEncoding) -> Option<&R0PrototypeProgramEntry> {
        self.entries.iter().find(|entry| entry.encoding == encoding)
    }
}

impl R0EncodedProgram {
    pub fn source_slots(&self) -> Option<&[u16]> {
        match self {
            Self::CurrentFixedSlot(program) => Some(&program.source_slots),
            Self::CompactR0Port(program) => Some(&program.source_slots),
            Self::SplitFixedSlot(program) => Some(&program.source_slots),
            Self::HomogeneousSlot(program) => Some(&program.source_slots),
            Self::GroupedSlot(program) => Some(&program.source_slots),
            Self::SplitFixedDirect(_) | Self::HomogeneousDirect(_) | Self::GroupedDirect(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0CompactFieldAudit {
    pub tag_bits: u8,
    pub coefficient_bits: u8,
    pub window_bits: u8,
    pub column_bits: u8,
    pub span_bits: u8,
    pub count_bits: u8,
    pub compact_words: u64,
    pub direct_words: u64,
    pub escape_words: u64,
    pub weighted_escape_source_uses: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0EncodingCapacityFactV1 {
    pub encoding: R0ProgramEncoding,
    pub semantic_records: u32,
    pub represented_records: u32,
    pub bf_records: u32,
    pub e4_records: u32,
    pub group_headers: u32,
    pub logical_program_u16_words: u32,
    pub source_slot_u16_words: u32,
    pub model_json_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0DescriptorCapacityFactV1 {
    pub encoding: R0ProgramEncoding,
    pub tile_capacity: Option<crate::r0_prototype_tile::R0TileCapacity>,
    pub payload_size: usize,
    pub max_dynamic_shared_bytes: u32,
    pub program_sha256: String,
    pub tile_sha256: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeCapacityCoordinateV1 {
    pub circuit: String,
    pub layer: u32,
    pub coordinate_payload_sha256: String,
    pub compact: R0CompactFieldAudit,
    pub encodings: Vec<R0EncodingCapacityFactV1>,
    pub descriptors: Vec<R0DescriptorCapacityFactV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0EncodingCapacityMaximumV1 {
    pub encoding: R0ProgramEncoding,
    pub circuit: String,
    pub layer: u32,
    pub represented_records: u32,
    pub logical_program_u16_words: u32,
    pub source_slot_u16_words: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeCapacityV1 {
    pub schema_version: u32,
    pub coordinates: Vec<R0PrototypeCapacityCoordinateV1>,
    pub maxima: Vec<R0EncodingCapacityMaximumV1>,
    pub descriptor_layouts: Vec<crate::r0_prototype_abi::R0PrototypeDescriptorLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0PrototypeEncodingError {
    InvalidProgramLength { expected: usize, observed: usize },
    InvalidClass(u8),
    InvalidCoefficient(u32),
    InvalidSource(u32),
    InvalidReservedWord(u16),
    InvalidCompactTag(u32),
    TruncatedCompact,
    InvalidCompactWidth,
    InvalidGroupedProgram,
    CoefficientRecipeMismatch,
    CountOverflow,
}

fn bit_width(value: u64) -> u8 {
    (u64::BITS - value.leading_zeros()).max(1) as u8
}

pub(crate) fn packed_source_slots(coordinate: &FrozenR0Coordinate) -> Vec<u16> {
    coordinate
        .binding
        .source_slots
        .iter()
        .map(|slot| (u16::from(slot.window) << 7) | slot.column)
        .collect()
}

fn phase_for_class(class: u8) -> Result<R0Phase, R0PrototypeEncodingError> {
    match class {
        0 | 2 => Ok(R0Phase::Bf),
        1 | 3 | 4 => Ok(R0Phase::E4),
        class => Err(R0PrototypeEncodingError::InvalidClass(class)),
    }
}

fn projection_for_class(class: u8) -> Result<SourceProjection, R0PrototypeEncodingError> {
    match class {
        0 | 1 => Ok(SourceProjection::Endpoint0),
        2..=4 => Ok(SourceProjection::Delta),
        class => Err(R0PrototypeEncodingError::InvalidClass(class)),
    }
}

fn class_for_term(term: &CoeffTerm) -> Result<u8, R0PrototypeEncodingError> {
    let class = match term {
        CoeffTerm::C0Linear { field, .. } => match field {
            FieldKind::Base => 0,
            FieldKind::Ext => 1,
        },
        CoeffTerm::C2Product {
            lhs_field,
            rhs_field,
            ..
        } => match (lhs_field, rhs_field) {
            (FieldKind::Base, FieldKind::Base) => 2,
            (FieldKind::Base, FieldKind::Ext) | (FieldKind::Ext, FieldKind::Base) => 3,
            (FieldKind::Ext, FieldKind::Ext) => 4,
        },
        CoeffTerm::DualProduct { .. } => return Err(R0PrototypeEncodingError::InvalidClass(5)),
    };
    Ok(class)
}

fn sources_for_term(term: &CoeffTerm) -> (SourceId, Option<SourceId>) {
    match term {
        CoeffTerm::C0Linear { value, .. } => (value.source, None),
        CoeffTerm::C2Product {
            lhs,
            rhs,
            lhs_field,
            rhs_field,
            ..
        } => {
            if matches!((lhs_field, rhs_field), (FieldKind::Ext, FieldKind::Base)) {
                (rhs.source, Some(lhs.source))
            } else {
                (lhs.source, Some(rhs.source))
            }
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => (*lhs, Some(*rhs)),
    }
}

fn operations_from_split(
    layer: &CoeffLayer,
    split: &SplitSchedule,
    grouping: &CoeffGroupingAnalysis,
    grouped: bool,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    let terms = layer
        .terms
        .iter()
        .map(|term| (term.id(), term))
        .collect::<std::collections::BTreeMap<_, _>>();
    let mut group_members = std::collections::BTreeMap::new();
    for (group_id, group) in grouping.groups.iter().enumerate() {
        for (member_index, member) in group.members.iter().enumerate() {
            group_members.insert(member.term, (group_id as u32, member_index as u32));
        }
    }
    let mut operations = Vec::with_capacity(layer.terms.len());
    for (phase, atoms) in [(R0Phase::Bf, &split.bf), (R0Phase::E4, &split.e4)] {
        for atom in atoms {
            for term_id in &atom.terms {
                let term = terms
                    .get(term_id)
                    .ok_or(R0PrototypeEncodingError::InvalidGroupedProgram)?;
                let class = class_for_term(term)?;
                let projection = projection_for_class(class)?;
                let (source_a, source_b) = sources_for_term(term);
                let group = grouped
                    .then(|| group_members.get(term_id).copied())
                    .flatten();
                operations.push(R0PrototypeOp {
                    phase,
                    term_class: class,
                    coefficient_id: term.coefficient().0,
                    source_a: SemanticSourceKey {
                        source: source_a.0,
                        projection,
                    },
                    source_b: source_b.map(|source| SemanticSourceKey {
                        source: source.0,
                        projection,
                    }),
                    group_id: group.map(|entry| entry.0),
                    member_index: group.map(|entry| entry.1),
                });
            }
        }
    }
    Ok(operations)
}

pub fn prototype_operations(
    _coordinate: &FrozenR0Coordinate,
    layer: &CoeffLayer,
    schedules: &ScheduleViews,
    grouping: &CoeffGroupingAnalysis,
    grouped: bool,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    operations_from_split(
        layer,
        if grouped {
            &schedules.analysis_split
        } else {
            &schedules.canonical_split
        },
        grouping,
        grouped,
    )
}

fn header(class: u8, coefficient: u32) -> Result<u16, R0PrototypeEncodingError> {
    if class > 4 {
        return Err(R0PrototypeEncodingError::InvalidClass(class));
    }
    if coefficient > u32::from(COEFFICIENT_MASK) {
        return Err(R0PrototypeEncodingError::InvalidCoefficient(coefficient));
    }
    Ok((u16::from(class) << CLASS_SHIFT) | coefficient as u16)
}

fn fixed_record(
    coordinate: &FrozenR0Coordinate,
    op: &R0PrototypeOp,
    direct: bool,
) -> Result<FixedRecord, R0PrototypeEncodingError> {
    let source = |key: SemanticSourceKey| -> Result<u16, R0PrototypeEncodingError> {
        let slot = u16::try_from(key.source)
            .map_err(|_| R0PrototypeEncodingError::InvalidSource(key.source))?;
        if direct {
            packed_source_slots(coordinate)
                .get(slot as usize)
                .copied()
                .ok_or(R0PrototypeEncodingError::InvalidSource(key.source))
        } else if usize::from(slot) < coordinate.binding.source_slots.len() {
            Ok(slot)
        } else {
            Err(R0PrototypeEncodingError::InvalidSource(key.source))
        }
    };
    Ok(FixedRecord {
        header: header(op.term_class, op.coefficient_id)?,
        source_a: source(op.source_a)?,
        source_b: op.source_b.map(source).transpose()?.unwrap_or(SOURCE_NONE),
        reserved: 0,
    })
}

fn split_fixed(
    coordinate: &FrozenR0Coordinate,
    operations: &[R0PrototypeOp],
    direct: bool,
) -> Result<(Vec<FixedRecord>, Vec<FixedRecord>), R0PrototypeEncodingError> {
    let mut bf = Vec::new();
    let mut e4 = Vec::new();
    for op in operations {
        let record = fixed_record(coordinate, op, direct)?;
        match op.phase {
            R0Phase::Bf => bf.push(record),
            R0Phase::E4 => e4.push(record),
        }
    }
    Ok((bf, e4))
}

fn homogeneous(
    coordinate: &FrozenR0Coordinate,
    operations: &[R0PrototypeOp],
    direct: bool,
) -> Result<([Vec<FixedRecord>; 5], Vec<u8>), R0PrototypeEncodingError> {
    let mut classes: [Vec<FixedRecord>; 5] = array::from_fn(|_| Vec::new());
    let mut order = Vec::with_capacity(operations.len());
    for op in operations {
        classes[op.term_class as usize].push(fixed_record(coordinate, op, direct)?);
        order.push(op.term_class);
    }
    Ok((classes, order))
}

fn normalized_to_frozen(recipe: &NormalizedCoefficientRecipe) -> FrozenR0Recipe {
    FrozenR0Recipe {
        products: recipe
            .terms
            .iter()
            .map(|product| FrozenR0Product {
                scalar: product.scalar,
                challenges: product
                    .challenges
                    .iter()
                    .map(|challenge| FrozenR0Challenge {
                        reference: challenge.0.clone(),
                    })
                    .collect(),
                inits_and_teardowns_top_bits: product.inits_and_teardowns_top_bits.clone(),
            })
            .collect(),
    }
}

fn stored_source(
    coordinate: &FrozenR0Coordinate,
    key: SemanticSourceKey,
    direct: bool,
) -> Result<StoredSource, R0PrototypeEncodingError> {
    let source = u16::try_from(key.source)
        .map_err(|_| R0PrototypeEncodingError::InvalidSource(key.source))?;
    if usize::from(source) >= coordinate.binding.source_slots.len() {
        return Err(R0PrototypeEncodingError::InvalidSource(key.source));
    }
    Ok(if direct {
        StoredSource::Direct(packed_source_slots(coordinate)[usize::from(source)])
    } else {
        StoredSource::Slot(source)
    })
}

fn grouped_atoms(
    coordinate: &FrozenR0Coordinate,
    layer: &CoeffLayer,
    schedules: &ScheduleViews,
    grouping: &CoeffGroupingAnalysis,
    direct: bool,
) -> Result<Vec<GroupedAtom>, R0PrototypeEncodingError> {
    let operations = operations_from_split(layer, &schedules.analysis_split, grouping, true)?;
    let by_term = operations
        .iter()
        .map(|op| {
            let key = (op.group_id, op.member_index, op.semantic_record());
            (key, op)
        })
        .collect::<Vec<_>>();
    let mut cursor = 0usize;
    let mut atoms = Vec::new();
    for (phase, phase_atoms) in [
        (R0Phase::Bf, &schedules.analysis_split.bf),
        (R0Phase::E4, &schedules.analysis_split.e4),
    ] {
        for atom in phase_atoms {
            if atom.terms.len() == 1 {
                let op = by_term
                    .get(cursor)
                    .map(|entry| entry.1)
                    .ok_or(R0PrototypeEncodingError::InvalidGroupedProgram)?;
                atoms.push(GroupedAtom::Singleton {
                    phase,
                    coefficient_id: op.coefficient_id,
                    term_class: op.term_class,
                    source_a: stored_source(coordinate, op.source_a, direct)?,
                    source_b: op
                        .source_b
                        .map(|key| stored_source(coordinate, key, direct))
                        .transpose()?,
                });
                cursor += 1;
                continue;
            }
            let group_id = operations
                .get(cursor)
                .and_then(|op| op.group_id)
                .ok_or(R0PrototypeEncodingError::InvalidGroupedProgram)?;
            let group = grouping
                .groups
                .get(group_id as usize)
                .ok_or(R0PrototypeEncodingError::InvalidGroupedProgram)?;
            let mut members = Vec::with_capacity(atom.terms.len());
            for member in &group.members {
                let op = operations
                    .get(cursor)
                    .ok_or(R0PrototypeEncodingError::InvalidGroupedProgram)?;
                if op.group_id != Some(group_id) || op.member_index != Some(members.len() as u32) {
                    return Err(R0PrototypeEncodingError::InvalidGroupedProgram);
                }
                members.push(GroupedMember {
                    term_class: op.term_class,
                    immediate: member.immediate,
                    source_a: stored_source(coordinate, op.source_a, direct)?,
                    source_b: op
                        .source_b
                        .map(|key| stored_source(coordinate, key, direct))
                        .transpose()?,
                });
                cursor += 1;
            }
            atoms.push(GroupedAtom::Group {
                phase,
                group_id,
                core: normalized_to_frozen(&group.core),
                members,
            });
        }
    }
    if cursor != operations.len() {
        return Err(R0PrototypeEncodingError::InvalidGroupedProgram);
    }
    Ok(atoms)
}

fn compact_widths(coordinate: &FrozenR0Coordinate) -> (u8, u8, u8) {
    let coefficient_max = coordinate
        .program_words
        .chunks_exact(4)
        .map(|record| u64::from(record[0] & COEFFICIENT_MASK))
        .max()
        .unwrap_or(0);
    let window_max = coordinate
        .binding
        .source_slots
        .iter()
        .map(|slot| u64::from(slot.window))
        .max()
        .unwrap_or(0);
    let column_max = coordinate
        .binding
        .source_slots
        .iter()
        .map(|slot| u64::from(slot.column))
        .max()
        .unwrap_or(0);
    (
        bit_width(coefficient_max),
        bit_width(window_max),
        bit_width(column_max),
    )
}

fn compact_encode(
    coordinate: &FrozenR0Coordinate,
    operations: &[R0PrototypeOp],
) -> Result<CompactR0Program, R0PrototypeEncodingError> {
    let slots = packed_source_slots(coordinate);
    let (coefficient_bits, window_bits, column_bits) = compact_widths(coordinate);
    let mut words = Vec::new();
    for op in operations {
        if op.coefficient_id > u32::from(COEFFICIENT_MASK) {
            return Err(R0PrototypeEncodingError::InvalidCoefficient(
                op.coefficient_id,
            ));
        }
        let packed_a = *slots
            .get(op.source_a.source as usize)
            .ok_or(R0PrototypeEncodingError::InvalidSource(op.source_a.source))?;
        let common = (u32::from(op.term_class) << 3) | (op.coefficient_id << 6);
        let mut escape = || -> Result<(), R0PrototypeEncodingError> {
            let source_a = u16::try_from(op.source_a.source)
                .map_err(|_| R0PrototypeEncodingError::InvalidSource(op.source_a.source))?;
            let source_b = match op.source_b {
                Some(source) => u16::try_from(source.source)
                    .map_err(|_| R0PrototypeEncodingError::InvalidSource(source.source))?,
                None => SOURCE_NONE,
            };
            let header = (u16::from(op.term_class) << CLASS_SHIFT)
                | u16::try_from(op.coefficient_id)
                    .map_err(|_| R0PrototypeEncodingError::InvalidCoefficient(op.coefficient_id))?;
            words.push(COMPACT_TAG_ESCAPE | (2 << 3));
            words.push(u32::from(header) | (u32::from(source_a) << 16));
            words.push(u32::from(source_b));
            Ok(())
        };
        match op.source_b {
            None => {
                if packed_a <= 0x0fff && op.coefficient_id <= u32::from(COEFFICIENT_MASK) {
                    words.push(COMPACT_TAG_LINEAR_DIRECT | common | (u32::from(packed_a) << 19));
                } else {
                    escape()?;
                }
            }
            Some(source_b) => {
                let packed_b = *slots
                    .get(source_b.source as usize)
                    .ok_or(R0PrototypeEncodingError::InvalidSource(source_b.source))?;
                let window_a = packed_a >> 7;
                let window_b = packed_b >> 7;
                if window_a == window_b
                    && window_a <= 0x1f
                    && packed_a & 0x7f <= 0x7f
                    && packed_b & 0x7f <= 0x7f
                    && op.coefficient_id <= u32::from(COEFFICIENT_MASK)
                {
                    words.push(
                        COMPACT_TAG_PRODUCT_SAME_WINDOW
                            | common
                            | (u32::from(window_a) << 19)
                            | (u32::from(packed_a & 0x7f) << 24),
                    );
                    words.push(u32::from(packed_b & 0x7f));
                } else if packed_a <= 0x0fff
                    && packed_b <= 0x0fff
                    && op.coefficient_id <= u32::from(COEFFICIENT_MASK)
                {
                    words.push(COMPACT_TAG_PRODUCT_DIRECT | common);
                    words.push(u32::from(packed_a) | (u32::from(packed_b) << 12));
                } else {
                    escape()?;
                }
            }
        }
    }
    Ok(CompactR0Program {
        words,
        source_slots: slots,
        coefficient_bits,
        window_bits,
        column_bits,
    })
}

pub fn encode_r0_prototype(
    coordinate: &FrozenR0Coordinate,
    layer: &CoeffLayer,
    schedules: &ScheduleViews,
    grouping: &CoeffGroupingAnalysis,
    encoding: R0ProgramEncoding,
) -> Result<R0EncodedProgram, R0PrototypeEncodingError> {
    let grouped = encoding.grouped();
    let operations = prototype_operations(coordinate, layer, schedules, grouping, grouped)?;
    let source_slots = packed_source_slots(coordinate);
    Ok(match encoding {
        R0ProgramEncoding::CurrentFixedSlot => {
            R0EncodedProgram::CurrentFixedSlot(CurrentFixedProgram {
                program_words: coordinate.program_words.clone(),
                source_slots,
            })
        }
        R0ProgramEncoding::CompactR0Port => {
            R0EncodedProgram::CompactR0Port(compact_encode(coordinate, &operations)?)
        }
        R0ProgramEncoding::SplitFixedSlot => {
            let (bf, e4) = split_fixed(coordinate, &operations, false)?;
            R0EncodedProgram::SplitFixedSlot(SplitFixedSlotProgram {
                bf,
                e4,
                source_slots,
            })
        }
        R0ProgramEncoding::SplitFixedDirect => {
            let (bf, e4) = split_fixed(coordinate, &operations, true)?;
            R0EncodedProgram::SplitFixedDirect(SplitFixedDirectProgram { bf, e4 })
        }
        R0ProgramEncoding::HomogeneousSlot => {
            let (classes, order) = homogeneous(coordinate, &operations, false)?;
            R0EncodedProgram::HomogeneousSlot(HomogeneousSlotProgram {
                classes,
                order,
                source_slots,
            })
        }
        R0ProgramEncoding::HomogeneousDirect => {
            let (classes, order) = homogeneous(coordinate, &operations, true)?;
            R0EncodedProgram::HomogeneousDirect(HomogeneousDirectProgram { classes, order })
        }
        R0ProgramEncoding::GroupedSlot => R0EncodedProgram::GroupedSlot(GroupedSlotProgram {
            atoms: grouped_atoms(coordinate, layer, schedules, grouping, false)?,
            source_slots,
        }),
        R0ProgramEncoding::GroupedDirect => R0EncodedProgram::GroupedDirect(GroupedDirectProgram {
            atoms: grouped_atoms(coordinate, layer, schedules, grouping, true)?,
        }),
    })
}

pub fn build_r0_prototype_program_set(
    coordinate: &FrozenR0Coordinate,
    layer: &CoeffLayer,
    schedules: &ScheduleViews,
    grouping: &CoeffGroupingAnalysis,
) -> Result<R0PrototypeProgramSet, R0PrototypeEncodingError> {
    let mut entries = Vec::with_capacity(R0ProgramEncoding::ALL.len());
    for encoding in R0ProgramEncoding::ALL {
        let operations =
            prototype_operations(coordinate, layer, schedules, grouping, encoding.grouped())?;
        let encoded = encode_r0_prototype(coordinate, layer, schedules, grouping, encoding)?;
        entries.push(R0PrototypeProgramEntry {
            encoding,
            operations,
            encoded,
        });
    }
    Ok(R0PrototypeProgramSet { entries })
}

fn source_key_from_stored(
    coordinate: &FrozenR0Coordinate,
    stored: StoredSource,
    projection: SourceProjection,
) -> Result<SemanticSourceKey, R0PrototypeEncodingError> {
    let source = match stored {
        StoredSource::Slot(slot) => {
            if usize::from(slot) >= coordinate.binding.source_slots.len() {
                return Err(R0PrototypeEncodingError::InvalidSource(u32::from(slot)));
            }
            u32::from(slot)
        }
        StoredSource::Direct(packed) => packed_source_slots(coordinate)
            .iter()
            .position(|candidate| *candidate == packed)
            .ok_or(R0PrototypeEncodingError::InvalidSource(u32::from(packed)))?
            as u32,
    };
    Ok(SemanticSourceKey { source, projection })
}

fn decode_fixed_records(
    coordinate: &FrozenR0Coordinate,
    records: impl IntoIterator<Item = (R0Phase, FixedRecord)>,
    direct: bool,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    let mut operations = Vec::new();
    for (phase, record) in records {
        if record.reserved != 0 {
            return Err(R0PrototypeEncodingError::InvalidReservedWord(
                record.reserved,
            ));
        }
        let class = (record.header >> CLASS_SHIFT) as u8;
        if phase_for_class(class)? != phase {
            return Err(R0PrototypeEncodingError::InvalidClass(class));
        }
        let coefficient_id = u32::from(record.header & COEFFICIENT_MASK);
        recipe_for_coefficient(coordinate, coefficient_id)?;
        let projection = projection_for_class(class)?;
        let stored = |value| {
            if direct {
                StoredSource::Direct(value)
            } else {
                StoredSource::Slot(value)
            }
        };
        operations.push(R0PrototypeOp {
            phase,
            term_class: class,
            coefficient_id,
            source_a: source_key_from_stored(coordinate, stored(record.source_a), projection)?,
            source_b: (record.source_b != SOURCE_NONE)
                .then(|| source_key_from_stored(coordinate, stored(record.source_b), projection))
                .transpose()?,
            group_id: None,
            member_index: None,
        });
    }
    Ok(operations)
}

fn records_from_current(
    program: &CurrentFixedProgram,
) -> Result<Vec<(R0Phase, FixedRecord)>, R0PrototypeEncodingError> {
    if !program.program_words.len().is_multiple_of(4) {
        return Err(R0PrototypeEncodingError::InvalidProgramLength {
            expected: program.program_words.len().next_multiple_of(4),
            observed: program.program_words.len(),
        });
    }
    let mut bf = Vec::new();
    let mut e4 = Vec::new();
    for words in program.program_words.chunks_exact(4) {
        let class = (words[0] >> CLASS_SHIFT) as u8;
        let entry = (
            phase_for_class(class)?,
            FixedRecord {
                header: words[0],
                source_a: words[1],
                source_b: words[2],
                reserved: words[3],
            },
        );
        match entry.0 {
            R0Phase::Bf => bf.push(entry),
            R0Phase::E4 => e4.push(entry),
        }
    }
    bf.extend(e4);
    Ok(bf)
}

fn normalize_canonical_operation_order(operations: &mut [R0PrototypeOp]) {
    operations.sort_by_key(|op| {
        let phase = match op.phase {
            R0Phase::Bf => 0u8,
            R0Phase::E4 => 1,
        };
        let arity = u8::from(op.source_b.is_some());
        let a = op.source_a.source;
        let b = op.source_b.map(|source| source.source).unwrap_or(a);
        (phase, arity, a.min(b), a.max(b))
    });
}

fn decode_homogeneous(
    coordinate: &FrozenR0Coordinate,
    classes: &[Vec<FixedRecord>; 5],
    order: &[u8],
    direct: bool,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    let mut cursors = [0usize; 5];
    let mut records = Vec::with_capacity(order.len());
    for class in order {
        if *class > 4 {
            return Err(R0PrototypeEncodingError::InvalidClass(*class));
        }
        let record = classes[*class as usize]
            .get(cursors[*class as usize])
            .copied()
            .ok_or(R0PrototypeEncodingError::InvalidProgramLength {
                expected: order.len(),
                observed: records.len(),
            })?;
        cursors[*class as usize] += 1;
        records.push((phase_for_class(*class)?, record));
    }
    if classes
        .iter()
        .zip(cursors)
        .any(|(class_records, cursor)| class_records.len() != cursor)
    {
        return Err(R0PrototypeEncodingError::InvalidProgramLength {
            expected: order.len(),
            observed: classes.iter().map(Vec::len).sum(),
        });
    }
    decode_fixed_records(coordinate, records, direct)
}

pub(crate) fn scale_recipe(recipe: &FrozenR0Recipe, scalar: u32) -> FrozenR0Recipe {
    FrozenR0Recipe {
        products: recipe
            .products
            .iter()
            .map(|product| FrozenR0Product {
                scalar: (u64::from(product.scalar) * u64::from(scalar) % BABY_BEAR_ORDER) as u32,
                challenges: product.challenges.clone(),
                inits_and_teardowns_top_bits: product.inits_and_teardowns_top_bits.clone(),
            })
            .collect(),
    }
}

pub(crate) fn recipe_for_coefficient(
    coordinate: &FrozenR0Coordinate,
    coefficient: u32,
) -> Result<FrozenR0Recipe, R0PrototypeEncodingError> {
    match coefficient {
        0 => Ok(FrozenR0Recipe {
            products: vec![FrozenR0Product {
                scalar: 1,
                challenges: Vec::new(),
                inits_and_teardowns_top_bits: Vec::new(),
            }],
        }),
        1 => Ok(FrozenR0Recipe {
            products: vec![FrozenR0Product {
                scalar: (BABY_BEAR_ORDER - 1) as u32,
                challenges: Vec::new(),
                inits_and_teardowns_top_bits: Vec::new(),
            }],
        }),
        id => coordinate
            .recipes
            .get((id - 2) as usize)
            .cloned()
            .ok_or(R0PrototypeEncodingError::InvalidCoefficient(id)),
    }
}

fn coefficient_for_recipe(
    coordinate: &FrozenR0Coordinate,
    recipe: &FrozenR0Recipe,
) -> Result<u32, R0PrototypeEncodingError> {
    for id in 0..coordinate.recipes.len() as u32 + 2 {
        if recipe_for_coefficient(coordinate, id)? == *recipe {
            return Ok(id);
        }
    }
    Err(R0PrototypeEncodingError::CoefficientRecipeMismatch)
}

fn decode_grouped(
    coordinate: &FrozenR0Coordinate,
    atoms: &[GroupedAtom],
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    let mut operations = Vec::new();
    let mut observed_groups = std::collections::BTreeSet::new();
    for atom in atoms {
        match atom {
            GroupedAtom::Singleton {
                phase,
                coefficient_id,
                term_class,
                source_a,
                source_b,
            } => {
                if phase_for_class(*term_class)? != *phase {
                    return Err(R0PrototypeEncodingError::InvalidGroupedProgram);
                }
                recipe_for_coefficient(coordinate, *coefficient_id)?;
                let projection = projection_for_class(*term_class)?;
                operations.push(R0PrototypeOp {
                    phase: *phase,
                    term_class: *term_class,
                    coefficient_id: *coefficient_id,
                    source_a: source_key_from_stored(coordinate, *source_a, projection)?,
                    source_b: source_b
                        .map(|source| source_key_from_stored(coordinate, source, projection))
                        .transpose()?,
                    group_id: None,
                    member_index: None,
                });
            }
            GroupedAtom::Group {
                phase,
                group_id,
                core,
                members,
            } => {
                if members.len() < 2 || !observed_groups.insert(*group_id) {
                    return Err(R0PrototypeEncodingError::InvalidGroupedProgram);
                }
                for (member_index, member) in members.iter().enumerate() {
                    phase_for_class(member.term_class)?;
                    let projection = projection_for_class(member.term_class)?;
                    let recipe = scale_recipe(core, member.immediate);
                    operations.push(R0PrototypeOp {
                        phase: *phase,
                        term_class: member.term_class,
                        coefficient_id: coefficient_for_recipe(coordinate, &recipe)?,
                        source_a: source_key_from_stored(coordinate, member.source_a, projection)?,
                        source_b: member
                            .source_b
                            .map(|source| source_key_from_stored(coordinate, source, projection))
                            .transpose()?,
                        group_id: Some(*group_id),
                        member_index: Some(member_index as u32),
                    });
                }
            }
        }
    }
    Ok(operations)
}

fn source_for_packed(
    coordinate: &FrozenR0Coordinate,
    packed: u16,
    projection: SourceProjection,
) -> Result<SemanticSourceKey, R0PrototypeEncodingError> {
    source_key_from_stored(coordinate, StoredSource::Direct(packed), projection)
}

fn decode_compact(
    coordinate: &FrozenR0Coordinate,
    program: &CompactR0Program,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    if program.source_slots != packed_source_slots(coordinate) {
        return Err(R0PrototypeEncodingError::InvalidSource(u32::MAX));
    }
    if (
        program.coefficient_bits,
        program.window_bits,
        program.column_bits,
    ) != compact_widths(coordinate)
    {
        return Err(R0PrototypeEncodingError::InvalidCompactWidth);
    }
    let mut operations = Vec::new();
    let mut cursor = 0usize;
    while cursor < program.words.len() {
        let word = program.words[cursor];
        let tag = word & 7;
        if tag == COMPACT_TAG_ESCAPE {
            if word != COMPACT_TAG_ESCAPE | (2 << 3) {
                return Err(R0PrototypeEncodingError::InvalidCompactTag(word));
            }
            let first = *program
                .words
                .get(cursor + 1)
                .ok_or(R0PrototypeEncodingError::TruncatedCompact)?;
            let second = *program
                .words
                .get(cursor + 2)
                .ok_or(R0PrototypeEncodingError::TruncatedCompact)?;
            let fixed = FixedRecord {
                header: first as u16,
                source_a: (first >> 16) as u16,
                source_b: second as u16,
                reserved: (second >> 16) as u16,
            };
            let phase = phase_for_class((fixed.header >> CLASS_SHIFT) as u8)?;
            operations.extend(decode_fixed_records(coordinate, [(phase, fixed)], false)?);
            cursor += 3;
            continue;
        }
        let class = ((word >> 3) & 7) as u8;
        let coefficient = (word >> 6) & u32::from(COEFFICIENT_MASK);
        recipe_for_coefficient(coordinate, coefficient)?;
        let phase = phase_for_class(class)?;
        let projection = projection_for_class(class)?;
        let (packed_a, packed_b, consumed) = match tag {
            COMPACT_TAG_LINEAR_DIRECT => (((word >> 19) & 0xfff) as u16, None, 1),
            COMPACT_TAG_PRODUCT_SAME_WINDOW => {
                let tail = *program
                    .words
                    .get(cursor + 1)
                    .ok_or(R0PrototypeEncodingError::TruncatedCompact)?;
                if tail & !0x7f != 0 {
                    return Err(R0PrototypeEncodingError::InvalidCompactTag(tail));
                }
                let window = ((word >> 19) & 0x1f) as u16;
                let a = (window << 7) | ((word >> 24) & 0x7f) as u16;
                let b = (window << 7) | tail as u16;
                (a, Some(b), 2)
            }
            COMPACT_TAG_PRODUCT_DIRECT => {
                let tail = *program
                    .words
                    .get(cursor + 1)
                    .ok_or(R0PrototypeEncodingError::TruncatedCompact)?;
                if tail >> 24 != 0 {
                    return Err(R0PrototypeEncodingError::InvalidCompactTag(tail));
                }
                (
                    (tail & 0xfff) as u16,
                    Some(((tail >> 12) & 0xfff) as u16),
                    2,
                )
            }
            tag => return Err(R0PrototypeEncodingError::InvalidCompactTag(tag)),
        };
        if (class <= 1) != packed_b.is_none() {
            return Err(R0PrototypeEncodingError::InvalidClass(class));
        }
        operations.push(R0PrototypeOp {
            phase,
            term_class: class,
            coefficient_id: coefficient,
            source_a: source_for_packed(coordinate, packed_a, projection)?,
            source_b: packed_b
                .map(|source| source_for_packed(coordinate, source, projection))
                .transpose()?,
            group_id: None,
            member_index: None,
        });
        cursor += consumed;
    }
    Ok(operations)
}

pub fn decode_r0_prototype(
    coordinate: &FrozenR0Coordinate,
    encoded: &R0EncodedProgram,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    let operations = match encoded {
        R0EncodedProgram::CurrentFixedSlot(program) => {
            if program.source_slots != packed_source_slots(coordinate) {
                return Err(R0PrototypeEncodingError::InvalidSource(u32::MAX));
            }
            let mut operations =
                decode_fixed_records(coordinate, records_from_current(program)?, false)?;
            normalize_canonical_operation_order(&mut operations);
            operations
        }
        R0EncodedProgram::CompactR0Port(program) => decode_compact(coordinate, program)?,
        R0EncodedProgram::SplitFixedSlot(program) => {
            if program.source_slots != packed_source_slots(coordinate) {
                return Err(R0PrototypeEncodingError::InvalidSource(u32::MAX));
            }
            decode_fixed_records(
                coordinate,
                program
                    .bf
                    .iter()
                    .copied()
                    .map(|record| (R0Phase::Bf, record))
                    .chain(
                        program
                            .e4
                            .iter()
                            .copied()
                            .map(|record| (R0Phase::E4, record)),
                    ),
                false,
            )?
        }
        R0EncodedProgram::SplitFixedDirect(program) => decode_fixed_records(
            coordinate,
            program
                .bf
                .iter()
                .copied()
                .map(|record| (R0Phase::Bf, record))
                .chain(
                    program
                        .e4
                        .iter()
                        .copied()
                        .map(|record| (R0Phase::E4, record)),
                ),
            true,
        )?,
        R0EncodedProgram::HomogeneousSlot(program) => {
            if program.source_slots != packed_source_slots(coordinate) {
                return Err(R0PrototypeEncodingError::InvalidSource(u32::MAX));
            }
            decode_homogeneous(coordinate, &program.classes, &program.order, false)?
        }
        R0EncodedProgram::HomogeneousDirect(program) => {
            decode_homogeneous(coordinate, &program.classes, &program.order, true)?
        }
        R0EncodedProgram::GroupedSlot(program) => {
            if program.source_slots != packed_source_slots(coordinate) {
                return Err(R0PrototypeEncodingError::InvalidSource(u32::MAX));
            }
            decode_grouped(coordinate, &program.atoms)?
        }
        R0EncodedProgram::GroupedDirect(program) => decode_grouped(coordinate, &program.atoms)?,
    };
    if operations.len() != coordinate.term_count as usize {
        return Err(R0PrototypeEncodingError::InvalidProgramLength {
            expected: coordinate.term_count as usize,
            observed: operations.len(),
        });
    }
    Ok(operations)
}

pub(crate) fn decode_current_fixed_wire_order(
    coordinate: &FrozenR0Coordinate,
    program: &CurrentFixedProgram,
) -> Result<Vec<R0PrototypeOp>, R0PrototypeEncodingError> {
    if program.source_slots != packed_source_slots(coordinate) {
        return Err(R0PrototypeEncodingError::InvalidSource(u32::MAX));
    }
    if !program.program_words.len().is_multiple_of(4) {
        return Err(R0PrototypeEncodingError::InvalidProgramLength {
            expected: program.program_words.len().next_multiple_of(4),
            observed: program.program_words.len(),
        });
    }
    let records = program.program_words.chunks_exact(4).map(|words| {
        let class = (words[0] >> CLASS_SHIFT) as u8;
        Ok((
            phase_for_class(class)?,
            FixedRecord {
                header: words[0],
                source_a: words[1],
                source_b: words[2],
                reserved: words[3],
            },
        ))
    });
    decode_fixed_records(
        coordinate,
        records.collect::<Result<Vec<_>, R0PrototypeEncodingError>>()?,
        false,
    )
}

pub trait R0PrototypeOperationSequence {
    fn semantic_records(&self) -> Vec<(u8, u32, SemanticSourceKey, Option<SemanticSourceKey>)>;
}

impl R0PrototypeOperationSequence for [R0PrototypeOp] {
    fn semantic_records(&self) -> Vec<(u8, u32, SemanticSourceKey, Option<SemanticSourceKey>)> {
        let mut records = self
            .iter()
            .map(R0PrototypeOp::semantic_record)
            .collect::<Vec<_>>();
        records.sort();
        records
    }
}

impl R0PrototypeOperationSequence for Vec<R0PrototypeOp> {
    fn semantic_records(&self) -> Vec<(u8, u32, SemanticSourceKey, Option<SemanticSourceKey>)> {
        self.as_slice().semantic_records()
    }
}

pub fn audit_compact_r0_fields(
    coordinates: &[FrozenR0Coordinate],
) -> Result<Vec<R0CompactFieldAudit>, R0PrototypeEncodingError> {
    let mut audits = Vec::with_capacity(coordinates.len());
    for coordinate in coordinates {
        let expected = coordinate.term_count as usize * 4;
        if coordinate.program_words.len() != expected {
            return Err(R0PrototypeEncodingError::InvalidProgramLength {
                expected,
                observed: coordinate.program_words.len(),
            });
        }
        let (coefficient_bits, window_bits, column_bits) = compact_widths(coordinate);
        let slots = packed_source_slots(coordinate);
        let mut compact_words = 0u64;
        let mut direct_words = 0u64;
        let mut escape_words = 0u64;
        let mut weighted_escape_source_uses = 0u64;
        for record in coordinate.program_words.chunks_exact(4) {
            if record[3] != 0 {
                return Err(R0PrototypeEncodingError::InvalidReservedWord(record[3]));
            }
            let class = (record[0] >> CLASS_SHIFT) as u8;
            phase_for_class(class)?;
            if class <= 1 {
                let a = *slots.get(record[1] as usize).ok_or(
                    R0PrototypeEncodingError::InvalidSource(u32::from(record[1])),
                )?;
                if a <= 0x0fff {
                    compact_words += 1;
                } else {
                    escape_words += 3;
                    weighted_escape_source_uses += 1;
                }
            } else {
                let a = *slots.get(record[1] as usize).ok_or(
                    R0PrototypeEncodingError::InvalidSource(u32::from(record[1])),
                )?;
                let b = *slots.get(record[2] as usize).ok_or(
                    R0PrototypeEncodingError::InvalidSource(u32::from(record[2])),
                )?;
                if a >> 7 == b >> 7 && a >> 7 <= 0x1f {
                    compact_words += 2;
                } else if a <= 0x0fff && b <= 0x0fff {
                    direct_words += 2;
                } else {
                    escape_words += 3;
                    weighted_escape_source_uses += 2;
                }
            }
        }
        audits.push(R0CompactFieldAudit {
            tag_bits: COMPACT_TAG_BITS,
            coefficient_bits,
            window_bits,
            column_bits,
            span_bits: bit_width(u64::from(coordinate.term_count)),
            count_bits: bit_width(u64::from(coordinate.term_count)),
            compact_words,
            direct_words,
            escape_words,
            weighted_escape_source_uses,
        });
    }
    Ok(audits)
}

fn checked_u32(value: usize) -> Result<u32, String> {
    u32::try_from(value).map_err(|_| format!("value {value} does not fit u32"))
}

fn encoded_capacity_fact(
    encoding: R0ProgramEncoding,
    encoded: &R0EncodedProgram,
    operations: &[R0PrototypeOp],
) -> Result<R0EncodingCapacityFactV1, String> {
    let bf_records = operations
        .iter()
        .filter(|operation| operation.phase == R0Phase::Bf)
        .count();
    let e4_records = operations.len() - bf_records;
    let (represented_records, group_headers, logical_program_u16_words) = match encoded {
        R0EncodedProgram::CurrentFixedSlot(program) => (
            program.program_words.len() / 4,
            0,
            program.program_words.len(),
        ),
        R0EncodedProgram::CompactR0Port(program) => {
            (operations.len(), 0, program.words.len().saturating_mul(2))
        }
        R0EncodedProgram::SplitFixedSlot(program) => (
            program.bf.len() + program.e4.len(),
            0,
            (program.bf.len() + program.e4.len()).saturating_mul(4),
        ),
        R0EncodedProgram::SplitFixedDirect(program) => (
            program.bf.len() + program.e4.len(),
            0,
            (program.bf.len() + program.e4.len()).saturating_mul(4),
        ),
        R0EncodedProgram::HomogeneousSlot(program) => {
            let records = program.classes.iter().map(Vec::len).sum::<usize>();
            let words = program
                .classes
                .iter()
                .enumerate()
                .map(|(class, records)| records.len() * if class <= 1 { 2 } else { 3 })
                .sum::<usize>()
                + program.order.len();
            (records, 0, words)
        }
        R0EncodedProgram::HomogeneousDirect(program) => {
            let records = program.classes.iter().map(Vec::len).sum::<usize>();
            let words = program
                .classes
                .iter()
                .enumerate()
                .map(|(class, records)| records.len() * if class <= 1 { 2 } else { 3 })
                .sum::<usize>()
                + program.order.len();
            (records, 0, words)
        }
        R0EncodedProgram::GroupedSlot(program) => grouped_capacity(&program.atoms),
        R0EncodedProgram::GroupedDirect(program) => grouped_capacity(&program.atoms),
    };
    let source_slots = encoded.source_slots().map_or(0, <[u16]>::len);
    Ok(R0EncodingCapacityFactV1 {
        encoding,
        semantic_records: checked_u32(operations.len())?,
        represented_records: checked_u32(represented_records)?,
        bf_records: checked_u32(bf_records)?,
        e4_records: checked_u32(e4_records)?,
        group_headers: checked_u32(group_headers)?,
        logical_program_u16_words: checked_u32(logical_program_u16_words)?,
        source_slot_u16_words: checked_u32(source_slots)?,
        model_json_bytes: serde_json::to_vec(encoded)
            .map_err(|error| format!("serialize encoded model: {error}"))?
            .len() as u64,
    })
}

fn grouped_capacity(atoms: &[GroupedAtom]) -> (usize, usize, usize) {
    let mut represented_records = 0usize;
    let mut group_headers = 0usize;
    let mut words = 0usize;
    for atom in atoms {
        match atom {
            GroupedAtom::Singleton { term_class, .. } => {
                represented_records += 1;
                words += if *term_class <= 1 { 2 } else { 3 };
            }
            GroupedAtom::Group { members, .. } => {
                group_headers += 1;
                represented_records += 1 + members.len();
                words += 4 + members
                    .iter()
                    .map(|member| if member.term_class <= 1 { 3 } else { 4 })
                    .sum::<usize>();
            }
        }
    }
    (represented_records, group_headers, words)
}

pub fn build_r0_prototype_capacity_artifact() -> Result<R0PrototypeCapacityV1, String> {
    use gpu_gkr_compiler::backward::analyze_coeff_grouping;

    use crate::accumulator_schedule::build_schedule_views;
    use crate::census::compile_corpus;
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};

    let bundle = decode_r0_bundle(R0_CORPUS_BYTES)
        .map_err(|error| format!("decode frozen R0 corpus: {error}"))?;
    let audits = audit_compact_r0_fields(&bundle.coordinates)
        .map_err(|error| format!("audit compact R0 fields: {error:?}"))?;
    let frozen = bundle
        .coordinates
        .iter()
        .zip(audits)
        .map(|(coordinate, audit)| {
            (
                (coordinate.circuit.as_str(), coordinate.layer),
                (coordinate, audit),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    let corpus = compile_corpus().map_err(|error| format!("compile R0 corpus: {error}"))?;
    let mut coordinates = Vec::with_capacity(corpus.layers.len());
    for layer in &corpus.layers {
        let (coordinate, compact) = frozen
            .get(&(layer.circuit.as_str(), layer.layer as u32))
            .ok_or_else(|| {
                format!(
                    "missing frozen coordinate {}:{}",
                    layer.circuit, layer.layer
                )
            })?;
        let grouping = analyze_coeff_grouping(&layer.r0.coefficients)
            .map_err(|error| format!("group {}:{}: {error:?}", layer.circuit, layer.layer))?;
        let schedules = build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping)
            .map_err(|error| format!("schedule {}:{}: {error:?}", layer.circuit, layer.layer))?;
        let programs = build_r0_prototype_program_set(
            coordinate,
            &layer.r0.coefficients,
            &schedules,
            &grouping,
        )
        .map_err(|error| {
            format!(
                "build prototype programs {}:{}: {error:?}",
                layer.circuit, layer.layer
            )
        })?;
        let encodings = programs
            .entries
            .iter()
            .map(|entry| encoded_capacity_fact(entry.encoding, &entry.encoded, &entry.operations))
            .collect::<Result<Vec<_>, _>>()?;
        let descriptors =
            crate::r0_prototype_abi::build_prototype_descriptors(coordinate, &programs, 3)
                .map_err(|error| {
                    format!(
                        "build prototype descriptors {}:{}: {error:?}",
                        layer.circuit, layer.layer
                    )
                })?
                .into_iter()
                .map(|descriptor| R0DescriptorCapacityFactV1 {
                    encoding: descriptor.encoding,
                    tile_capacity: descriptor.capacity,
                    payload_size: descriptor.payload_size,
                    max_dynamic_shared_bytes: descriptor.max_dynamic_shared_bytes(),
                    program_sha256: descriptor.program_sha256,
                    tile_sha256: descriptor.tile_sha256,
                })
                .collect();
        coordinates.push(R0PrototypeCapacityCoordinateV1 {
            circuit: layer.circuit.clone(),
            layer: layer.layer as u32,
            coordinate_payload_sha256: coordinate.payload_sha256.clone(),
            compact: compact.clone(),
            encodings,
            descriptors,
        });
    }
    coordinates
        .sort_by(|left, right| (&left.circuit, left.layer).cmp(&(&right.circuit, right.layer)));
    let mut maxima = Vec::with_capacity(R0ProgramEncoding::ALL.len());
    for encoding in R0ProgramEncoding::ALL {
        let (coordinate, fact) = coordinates
            .iter()
            .flat_map(|coordinate| {
                coordinate
                    .encodings
                    .iter()
                    .filter(move |fact| fact.encoding == encoding)
                    .map(move |fact| (coordinate, fact))
            })
            .max_by_key(|(coordinate, fact)| {
                (
                    fact.represented_records,
                    fact.logical_program_u16_words,
                    fact.source_slot_u16_words,
                    std::cmp::Reverse((&coordinate.circuit, coordinate.layer)),
                )
            })
            .ok_or_else(|| format!("no capacity facts for {}", encoding.as_str()))?;
        maxima.push(R0EncodingCapacityMaximumV1 {
            encoding,
            circuit: coordinate.circuit.clone(),
            layer: coordinate.layer,
            represented_records: fact.represented_records,
            logical_program_u16_words: fact.logical_program_u16_words,
            source_slot_u16_words: fact.source_slot_u16_words,
        });
    }
    Ok(R0PrototypeCapacityV1 {
        schema_version: 1,
        coordinates,
        maxima,
        descriptor_layouts: crate::r0_prototype_abi::R0PrototypeAbiLayout::rust().descriptors,
    })
}

pub fn render_r0_prototype_capacity_json() -> Result<Vec<u8>, String> {
    let capacity = build_r0_prototype_capacity_artifact()?;
    let mut bytes = serde_json::to_vec_pretty(&capacity)
        .map_err(|error| format!("serialize R0 prototype capacity: {error}"))?;
    bytes.push(b'\n');
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use gpu_gkr_compiler::backward::analyze_coeff_grouping;

    use crate::accumulator_schedule::build_schedule_views;
    use crate::census::compile_corpus;
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
    use crate::r0_prototype_manifest::R0ProgramEncoding;

    use super::*;

    type SemanticRecord = (u8, u32, SemanticSourceKey, Option<SemanticSourceKey>);

    fn ordered_semantic_records(operations: &[R0PrototypeOp]) -> Vec<SemanticRecord> {
        operations
            .iter()
            .map(R0PrototypeOp::semantic_record)
            .collect()
    }

    fn independent_raw_semantic_records(
        coordinate: &FrozenR0Coordinate,
        encoded: &R0EncodedProgram,
    ) -> Vec<SemanticRecord> {
        let packed = packed_source_slots(coordinate);
        let source = |stored: StoredSource, projection: SourceProjection| -> SemanticSourceKey {
            let source = match stored {
                StoredSource::Slot(slot) => usize::from(slot),
                StoredSource::Direct(value) => packed
                    .iter()
                    .position(|candidate| *candidate == value)
                    .unwrap(),
            };
            SemanticSourceKey {
                source: source as u32,
                projection,
            }
        };
        let record = |header: u16,
                      source_a: StoredSource,
                      source_b: Option<StoredSource>|
         -> SemanticRecord {
            let class = (header >> CLASS_SHIFT) as u8;
            let projection = if class <= 1 {
                SourceProjection::Endpoint0
            } else {
                SourceProjection::Delta
            };
            (
                class,
                u32::from(header & COEFFICIENT_MASK),
                source(source_a, projection),
                source_b.map(|source_b| source(source_b, projection)),
            )
        };
        let mut records = Vec::new();
        match encoded {
            R0EncodedProgram::CurrentFixedSlot(program) => {
                for words in program.program_words.chunks_exact(4) {
                    records.push(record(
                        words[0],
                        StoredSource::Slot(words[1]),
                        (words[2] != SOURCE_NONE).then_some(StoredSource::Slot(words[2])),
                    ));
                }
            }
            R0EncodedProgram::CompactR0Port(program) => {
                let mut cursor = 0usize;
                while cursor < program.words.len() {
                    let word = program.words[cursor];
                    let tag = word & 7;
                    let class = ((word >> 3) & 7) as u8;
                    let coefficient = (word >> 6) & u32::from(COEFFICIENT_MASK);
                    let projection = if class <= 1 {
                        SourceProjection::Endpoint0
                    } else {
                        SourceProjection::Delta
                    };
                    let (a, b, consumed) = match tag {
                        COMPACT_TAG_ESCAPE => {
                            assert_eq!(word, COMPACT_TAG_ESCAPE | (2 << 3));
                            let first = program.words[cursor + 1];
                            let second = program.words[cursor + 2];
                            assert_eq!(second >> 16, 0);
                            let header = first as u16;
                            records.push(record(
                                header,
                                StoredSource::Slot((first >> 16) as u16),
                                ((second as u16) != SOURCE_NONE)
                                    .then_some(StoredSource::Slot(second as u16)),
                            ));
                            cursor += 3;
                            continue;
                        }
                        COMPACT_TAG_LINEAR_DIRECT => (((word >> 19) & 0xfff) as u16, None, 1),
                        COMPACT_TAG_PRODUCT_SAME_WINDOW => {
                            let window = ((word >> 19) & 0x1f) as u16;
                            (
                                (window << 7) | ((word >> 24) & 0x7f) as u16,
                                Some((window << 7) | program.words[cursor + 1] as u16),
                                2,
                            )
                        }
                        COMPACT_TAG_PRODUCT_DIRECT => (
                            (program.words[cursor + 1] & 0xfff) as u16,
                            Some(((program.words[cursor + 1] >> 12) & 0xfff) as u16),
                            2,
                        ),
                        _ => panic!("valid encoder emitted unexpected compact tag {tag}"),
                    };
                    records.push((
                        class,
                        coefficient,
                        source(StoredSource::Direct(a), projection),
                        b.map(|value| source(StoredSource::Direct(value), projection)),
                    ));
                    cursor += consumed;
                }
            }
            R0EncodedProgram::SplitFixedSlot(program) => {
                for fixed in program.bf.iter().chain(&program.e4) {
                    records.push(record(
                        fixed.header,
                        StoredSource::Slot(fixed.source_a),
                        (fixed.source_b != SOURCE_NONE)
                            .then_some(StoredSource::Slot(fixed.source_b)),
                    ));
                }
            }
            R0EncodedProgram::SplitFixedDirect(program) => {
                for fixed in program.bf.iter().chain(&program.e4) {
                    records.push(record(
                        fixed.header,
                        StoredSource::Direct(fixed.source_a),
                        (fixed.source_b != SOURCE_NONE)
                            .then_some(StoredSource::Direct(fixed.source_b)),
                    ));
                }
            }
            R0EncodedProgram::HomogeneousSlot(program) => {
                let mut cursors = [0usize; 5];
                for class in &program.order {
                    let fixed = program.classes[*class as usize][cursors[*class as usize]];
                    cursors[*class as usize] += 1;
                    records.push(record(
                        fixed.header,
                        StoredSource::Slot(fixed.source_a),
                        (fixed.source_b != SOURCE_NONE)
                            .then_some(StoredSource::Slot(fixed.source_b)),
                    ));
                }
            }
            R0EncodedProgram::HomogeneousDirect(program) => {
                let mut cursors = [0usize; 5];
                for class in &program.order {
                    let fixed = program.classes[*class as usize][cursors[*class as usize]];
                    cursors[*class as usize] += 1;
                    records.push(record(
                        fixed.header,
                        StoredSource::Direct(fixed.source_a),
                        (fixed.source_b != SOURCE_NONE)
                            .then_some(StoredSource::Direct(fixed.source_b)),
                    ));
                }
            }
            R0EncodedProgram::GroupedSlot(program) => {
                independent_grouped_records(coordinate, &program.atoms, &source, &mut records)
            }
            R0EncodedProgram::GroupedDirect(program) => {
                independent_grouped_records(coordinate, &program.atoms, &source, &mut records)
            }
        }
        records
    }

    fn independent_grouped_records(
        coordinate: &FrozenR0Coordinate,
        atoms: &[GroupedAtom],
        source: &impl Fn(StoredSource, SourceProjection) -> SemanticSourceKey,
        records: &mut Vec<SemanticRecord>,
    ) {
        for atom in atoms {
            match atom {
                GroupedAtom::Singleton {
                    coefficient_id,
                    term_class,
                    source_a,
                    source_b,
                    ..
                } => {
                    let projection = if *term_class <= 1 {
                        SourceProjection::Endpoint0
                    } else {
                        SourceProjection::Delta
                    };
                    records.push((
                        *term_class,
                        *coefficient_id,
                        source(*source_a, projection),
                        source_b.map(|value| source(value, projection)),
                    ));
                }
                GroupedAtom::Group { core, members, .. } => {
                    for member in members {
                        let projection = if member.term_class <= 1 {
                            SourceProjection::Endpoint0
                        } else {
                            SourceProjection::Delta
                        };
                        let coefficient = coefficient_for_recipe(
                            coordinate,
                            &scale_recipe(core, member.immediate),
                        )
                        .unwrap();
                        records.push((
                            member.term_class,
                            coefficient,
                            source(member.source_a, projection),
                            member.source_b.map(|value| source(value, projection)),
                        ));
                    }
                }
            }
        }
    }

    #[test]
    fn cpu_all_corpus_encodings_roundtrip_the_normalized_r0_operations() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let frozen = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        assert_eq!(corpus.layers.len(), 57);

        for layer in &corpus.layers {
            let coordinate = frozen[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let expected = prototype_operations(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
                false,
            )
            .unwrap();

            for encoding in R0ProgramEncoding::ALL {
                let encoded = encode_r0_prototype(
                    coordinate,
                    &layer.r0.coefficients,
                    &schedules,
                    &grouping,
                    encoding,
                )
                .unwrap_or_else(|error| {
                    panic!(
                        "encode {}:{} {}: {error:?}",
                        coordinate.circuit,
                        coordinate.layer,
                        encoding.as_str()
                    )
                });
                let decoded = decode_r0_prototype(coordinate, &encoded).unwrap_or_else(|error| {
                    panic!(
                        "decode {}:{} {}: {error:?}",
                        coordinate.circuit,
                        coordinate.layer,
                        encoding.as_str()
                    )
                });
                let paired_wire_order = match &encoded {
                    R0EncodedProgram::CurrentFixedSlot(program) => {
                        decode_current_fixed_wire_order(coordinate, program).unwrap()
                    }
                    _ => decoded.clone(),
                };
                assert_eq!(
                    independent_raw_semantic_records(coordinate, &encoded),
                    ordered_semantic_records(&paired_wire_order),
                    "independent ordered wire records {}:{} {}",
                    coordinate.circuit,
                    coordinate.layer,
                    encoding.as_str()
                );
                assert_eq!(
                    decoded.semantic_records(),
                    expected.semantic_records(),
                    "semantic records {}:{} {}",
                    coordinate.circuit,
                    coordinate.layer,
                    encoding.as_str()
                );
                if !encoding.grouped() {
                    assert_eq!(
                        decoded,
                        expected,
                        "operation order {}:{} {}",
                        coordinate.circuit,
                        coordinate.layer,
                        encoding.as_str()
                    );
                } else {
                    let expected_grouped = prototype_operations(
                        coordinate,
                        &layer.r0.coefficients,
                        &schedules,
                        &grouping,
                        true,
                    )
                    .unwrap();
                    assert_eq!(
                        decoded,
                        expected_grouped,
                        "group order {}:{} {}",
                        coordinate.circuit,
                        coordinate.layer,
                        encoding.as_str()
                    );
                }
                assert_eq!(decoded.len(), coordinate.term_count as usize);

                if matches!(
                    encoding,
                    R0ProgramEncoding::SplitFixedDirect
                        | R0ProgramEncoding::HomogeneousDirect
                        | R0ProgramEncoding::GroupedDirect
                ) {
                    assert!(encoded.source_slots().is_none());
                }
                if encoding == R0ProgramEncoding::CurrentFixedSlot {
                    let R0EncodedProgram::CurrentFixedSlot(current) = encoded else {
                        unreachable!();
                    };
                    assert_eq!(current.program_words, coordinate.program_words);
                    assert_eq!(
                        current.source_slots,
                        coordinate
                            .binding
                            .source_slots
                            .iter()
                            .map(|slot| (u16::from(slot.window) << 7) | slot.column)
                            .collect::<Vec<_>>()
                    );
                }
            }
        }
    }

    #[test]
    fn cpu_compact_widths_are_derived_from_r0_not_continuation() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let audit = audit_compact_r0_fields(&bundle.coordinates).unwrap();
        assert_eq!(audit.len(), 57);
        assert!(audit.iter().all(|row| row.tag_bits == 3));
        assert!(audit.iter().any(|row| row.coefficient_bits > 7));
        assert!(audit
            .iter()
            .all(|row| row.compact_words + row.direct_words > 0));
    }

    #[test]
    fn cpu_compact_canonical_escape_has_an_explicit_exact_length() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .next()
            .unwrap();
        let fixed = &coordinate.program_words[..4];
        let (coefficient_bits, window_bits, column_bits) = compact_widths(&coordinate);
        let valid = CompactR0Program {
            words: vec![
                COMPACT_TAG_ESCAPE | (2 << 3),
                u32::from(fixed[0]) | (u32::from(fixed[1]) << 16),
                u32::from(fixed[2]) | (u32::from(fixed[3]) << 16),
            ],
            source_slots: packed_source_slots(&coordinate),
            coefficient_bits,
            window_bits,
            column_bits,
        };
        assert_eq!(decode_compact(&coordinate, &valid).unwrap().len(), 1);
        let mut bad = valid;
        bad.words[0] = COMPACT_TAG_ESCAPE | (1 << 3);
        assert!(decode_compact(&coordinate, &bad).is_err());
    }

    #[test]
    fn cpu_compact_encoder_falls_back_to_escape_for_wide_coordinates() {
        let mut coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .next()
            .unwrap();
        coordinate.binding.source_slots[0].window = 32;
        let current = CurrentFixedProgram {
            program_words: coordinate.program_words.clone(),
            source_slots: packed_source_slots(&coordinate),
        };
        let operations = decode_current_fixed_wire_order(&coordinate, &current).unwrap();
        let compact = compact_encode(&coordinate, &operations).unwrap();
        assert!(compact
            .words
            .iter()
            .any(|word| word & 7 == COMPACT_TAG_ESCAPE));
        assert_eq!(decode_compact(&coordinate, &compact).unwrap(), operations);
        assert_eq!(
            independent_raw_semantic_records(
                &coordinate,
                &R0EncodedProgram::CompactR0Port(compact)
            ),
            ordered_semantic_records(&operations)
        );
    }

    #[test]
    fn cpu_grouped_mixed_field_atom_retains_the_schedule_phase() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|row| row.circuit == "add_sub_lui_auipc_mop" && row.layer == 0)
            .unwrap();
        let layer = compile_corpus()
            .unwrap()
            .layers
            .into_iter()
            .find(|row| row.circuit == coordinate.circuit && row.layer == 0)
            .unwrap();
        let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
        let schedules =
            build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
        assert!(schedules.analysis_split.e4.iter().any(|atom| {
            atom.terms.len() > 1
                && atom.terms.iter().any(|term| {
                    matches!(
                        layer.r0.coefficients.terms[term.0 as usize],
                        gpu_gkr_compiler::backward::CoeffTerm::C0Linear {
                            field: gkr_eval_ir::FieldKind::Base,
                            ..
                        } | gpu_gkr_compiler::backward::CoeffTerm::C2Product {
                            lhs_field: gkr_eval_ir::FieldKind::Base,
                            rhs_field: gkr_eval_ir::FieldKind::Base,
                            ..
                        }
                    )
                })
        }));
        let encoded = encode_r0_prototype(
            &coordinate,
            &layer.r0.coefficients,
            &schedules,
            &grouping,
            R0ProgramEncoding::GroupedSlot,
        )
        .unwrap();
        assert_eq!(
            decode_r0_prototype(&coordinate, &encoded).unwrap().len(),
            coordinate.term_count as usize
        );
    }

    #[test]
    fn cpu_malformed_wire_families_fail_closed() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|row| row.circuit == "add_sub_lui_auipc_mop" && row.layer == 0)
            .unwrap();
        let layer = compile_corpus()
            .unwrap()
            .layers
            .into_iter()
            .find(|row| row.circuit == coordinate.circuit && row.layer == 0)
            .unwrap();
        let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
        let schedules =
            build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
        let encode = |encoding| {
            encode_r0_prototype(
                &coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
                encoding,
            )
            .unwrap()
        };

        let mut current = encode(R0ProgramEncoding::CurrentFixedSlot);
        let R0EncodedProgram::CurrentFixedSlot(program) = &mut current else {
            unreachable!();
        };
        program.program_words[3] = 1;
        assert!(decode_r0_prototype(&coordinate, &current).is_err());
        let mut current_class = encode(R0ProgramEncoding::CurrentFixedSlot);
        let R0EncodedProgram::CurrentFixedSlot(program) = &mut current_class else {
            unreachable!();
        };
        program.program_words[0] =
            (7 << CLASS_SHIFT) | (program.program_words[0] & COEFFICIENT_MASK);
        assert!(decode_r0_prototype(&coordinate, &current_class).is_err());
        let mut current_slot = encode(R0ProgramEncoding::CurrentFixedSlot);
        let R0EncodedProgram::CurrentFixedSlot(program) = &mut current_slot else {
            unreachable!();
        };
        program.program_words[1] = u16::MAX;
        assert!(decode_r0_prototype(&coordinate, &current_slot).is_err());
        let mut current_coefficient = encode(R0ProgramEncoding::CurrentFixedSlot);
        let R0EncodedProgram::CurrentFixedSlot(program) = &mut current_coefficient else {
            unreachable!();
        };
        program.program_words[0] =
            (program.program_words[0] & !COEFFICIENT_MASK) | COEFFICIENT_MASK;
        assert!(decode_r0_prototype(&coordinate, &current_coefficient).is_err());

        let mut compact = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact else {
            unreachable!();
        };
        program.words[0] = (program.words[0] & !7) | 6;
        assert!(decode_r0_prototype(&coordinate, &compact).is_err());
        let mut compact_slots = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact_slots else {
            unreachable!();
        };
        program.source_slots[0] ^= 1;
        assert!(decode_r0_prototype(&coordinate, &compact_slots).is_err());
        let mut compact_width = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact_width else {
            unreachable!();
        };
        program.column_bits ^= 1;
        assert!(decode_r0_prototype(&coordinate, &compact_width).is_err());
        let mut compact_truncated = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact_truncated else {
            unreachable!();
        };
        program.words = vec![COMPACT_TAG_ESCAPE | (2 << 3), 0];
        assert!(decode_r0_prototype(&coordinate, &compact_truncated).is_err());
        let mut compact_escape = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact_escape else {
            unreachable!();
        };
        program.words[0] = COMPACT_TAG_ESCAPE | (1 << 3);
        assert!(decode_r0_prototype(&coordinate, &compact_escape).is_err());
        let mut compact_coefficient = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact_coefficient else {
            unreachable!();
        };
        let word = program
            .words
            .iter_mut()
            .find(|word| **word & 7 != COMPACT_TAG_ESCAPE)
            .unwrap();
        *word = (*word & !(u32::from(COEFFICIENT_MASK) << 6)) | (u32::from(COEFFICIENT_MASK) << 6);
        assert!(decode_r0_prototype(&coordinate, &compact_coefficient).is_err());
        let mut compact_direct = encode(R0ProgramEncoding::CompactR0Port);
        let R0EncodedProgram::CompactR0Port(program) = &mut compact_direct else {
            unreachable!();
        };
        let cursor = program
            .words
            .iter()
            .position(|word| {
                matches!(
                    *word & 7,
                    COMPACT_TAG_LINEAR_DIRECT
                        | COMPACT_TAG_PRODUCT_SAME_WINDOW
                        | COMPACT_TAG_PRODUCT_DIRECT
                )
            })
            .unwrap();
        match program.words[cursor] & 7 {
            COMPACT_TAG_LINEAR_DIRECT => {
                program.words[cursor] = (program.words[cursor] & !(0xfff << 19)) | (0xfff << 19);
            }
            COMPACT_TAG_PRODUCT_SAME_WINDOW => {
                program.words[cursor] = (program.words[cursor] & !(0x1f << 19)) | (0x1f << 19);
                program.words[cursor + 1] = 0x7f;
            }
            COMPACT_TAG_PRODUCT_DIRECT => program.words[cursor + 1] = 0x00ff_ffff,
            _ => unreachable!(),
        }
        assert!(decode_r0_prototype(&coordinate, &compact_direct).is_err());

        let mut split_slot = encode(R0ProgramEncoding::SplitFixedSlot);
        let R0EncodedProgram::SplitFixedSlot(program) = &mut split_slot else {
            unreachable!();
        };
        program.source_slots[0] ^= 1;
        assert!(decode_r0_prototype(&coordinate, &split_slot).is_err());
        let mut split_slot_reserved = encode(R0ProgramEncoding::SplitFixedSlot);
        let R0EncodedProgram::SplitFixedSlot(program) = &mut split_slot_reserved else {
            unreachable!();
        };
        program.bf[0].reserved = 1;
        assert!(decode_r0_prototype(&coordinate, &split_slot_reserved).is_err());
        let mut split_slot_coefficient = encode(R0ProgramEncoding::SplitFixedSlot);
        let R0EncodedProgram::SplitFixedSlot(program) = &mut split_slot_coefficient else {
            unreachable!();
        };
        program.bf[0].header = (program.bf[0].header & !COEFFICIENT_MASK) | COEFFICIENT_MASK;
        assert!(decode_r0_prototype(&coordinate, &split_slot_coefficient).is_err());
        let mut split_slot_count = encode(R0ProgramEncoding::SplitFixedSlot);
        let R0EncodedProgram::SplitFixedSlot(program) = &mut split_slot_count else {
            unreachable!();
        };
        program.bf.pop();
        assert!(decode_r0_prototype(&coordinate, &split_slot_count).is_err());
        let mut split_slot_class = encode(R0ProgramEncoding::SplitFixedSlot);
        let R0EncodedProgram::SplitFixedSlot(program) = &mut split_slot_class else {
            unreachable!();
        };
        program.bf[0].header = (7 << CLASS_SHIFT) | (program.bf[0].header & COEFFICIENT_MASK);
        assert!(decode_r0_prototype(&coordinate, &split_slot_class).is_err());

        let mut split_direct = encode(R0ProgramEncoding::SplitFixedDirect);
        let R0EncodedProgram::SplitFixedDirect(program) = &mut split_direct else {
            unreachable!();
        };
        program.bf[0].source_a = u16::MAX;
        assert!(decode_r0_prototype(&coordinate, &split_direct).is_err());
        let mut split_direct_class = encode(R0ProgramEncoding::SplitFixedDirect);
        let R0EncodedProgram::SplitFixedDirect(program) = &mut split_direct_class else {
            unreachable!();
        };
        program.bf[0].header = (7 << CLASS_SHIFT) | (program.bf[0].header & COEFFICIENT_MASK);
        assert!(decode_r0_prototype(&coordinate, &split_direct_class).is_err());
        let mut split_direct_source_b = encode(R0ProgramEncoding::SplitFixedDirect);
        let R0EncodedProgram::SplitFixedDirect(program) = &mut split_direct_source_b else {
            unreachable!();
        };
        program
            .bf
            .iter_mut()
            .chain(&mut program.e4)
            .find(|record| record.source_b != SOURCE_NONE)
            .unwrap()
            .source_b = u16::MAX - 1;
        assert!(decode_r0_prototype(&coordinate, &split_direct_source_b).is_err());
        let mut split_direct_coefficient = encode(R0ProgramEncoding::SplitFixedDirect);
        let R0EncodedProgram::SplitFixedDirect(program) = &mut split_direct_coefficient else {
            unreachable!();
        };
        program.bf[0].header = (program.bf[0].header & !COEFFICIENT_MASK) | COEFFICIENT_MASK;
        assert!(decode_r0_prototype(&coordinate, &split_direct_coefficient).is_err());
        let mut split_direct_count = encode(R0ProgramEncoding::SplitFixedDirect);
        let R0EncodedProgram::SplitFixedDirect(program) = &mut split_direct_count else {
            unreachable!();
        };
        program.bf.pop();
        assert!(decode_r0_prototype(&coordinate, &split_direct_count).is_err());

        let mut homogeneous = encode(R0ProgramEncoding::HomogeneousSlot);
        let R0EncodedProgram::HomogeneousSlot(program) = &mut homogeneous else {
            unreachable!();
        };
        program.order.pop();
        assert!(decode_r0_prototype(&coordinate, &homogeneous).is_err());
        let mut homogeneous_slots = encode(R0ProgramEncoding::HomogeneousSlot);
        let R0EncodedProgram::HomogeneousSlot(program) = &mut homogeneous_slots else {
            unreachable!();
        };
        program.source_slots[0] ^= 1;
        assert!(decode_r0_prototype(&coordinate, &homogeneous_slots).is_err());
        let mut homogeneous_class = encode(R0ProgramEncoding::HomogeneousSlot);
        let R0EncodedProgram::HomogeneousSlot(program) = &mut homogeneous_class else {
            unreachable!();
        };
        let populated = program
            .classes
            .iter_mut()
            .find(|class| !class.is_empty())
            .unwrap();
        populated[0].header = (7 << CLASS_SHIFT) | (populated[0].header & COEFFICIENT_MASK);
        assert!(decode_r0_prototype(&coordinate, &homogeneous_class).is_err());
        let mut homogeneous_coefficient = encode(R0ProgramEncoding::HomogeneousSlot);
        let R0EncodedProgram::HomogeneousSlot(program) = &mut homogeneous_coefficient else {
            unreachable!();
        };
        let populated = program
            .classes
            .iter_mut()
            .find(|class| !class.is_empty())
            .unwrap();
        populated[0].header = (populated[0].header & !COEFFICIENT_MASK) | COEFFICIENT_MASK;
        assert!(decode_r0_prototype(&coordinate, &homogeneous_coefficient).is_err());
        let mut homogeneous_slot_source = encode(R0ProgramEncoding::HomogeneousSlot);
        let R0EncodedProgram::HomogeneousSlot(program) = &mut homogeneous_slot_source else {
            unreachable!();
        };
        let populated = program
            .classes
            .iter_mut()
            .find(|class| !class.is_empty())
            .unwrap();
        populated[0].source_a = u16::MAX;
        assert!(decode_r0_prototype(&coordinate, &homogeneous_slot_source).is_err());
        let mut homogeneous_direct = encode(R0ProgramEncoding::HomogeneousDirect);
        let R0EncodedProgram::HomogeneousDirect(program) = &mut homogeneous_direct else {
            unreachable!();
        };
        let populated = program
            .classes
            .iter_mut()
            .find(|class| !class.is_empty())
            .unwrap();
        populated[0].source_a = u16::MAX;
        assert!(decode_r0_prototype(&coordinate, &homogeneous_direct).is_err());
        let mut homogeneous_direct_coefficient = encode(R0ProgramEncoding::HomogeneousDirect);
        let R0EncodedProgram::HomogeneousDirect(program) = &mut homogeneous_direct_coefficient
        else {
            unreachable!();
        };
        let populated = program
            .classes
            .iter_mut()
            .find(|class| !class.is_empty())
            .unwrap();
        populated[0].header = (populated[0].header & !COEFFICIENT_MASK) | COEFFICIENT_MASK;
        assert!(decode_r0_prototype(&coordinate, &homogeneous_direct_coefficient).is_err());
        let mut homogeneous_direct_source_b = encode(R0ProgramEncoding::HomogeneousDirect);
        let R0EncodedProgram::HomogeneousDirect(program) = &mut homogeneous_direct_source_b else {
            unreachable!();
        };
        program
            .classes
            .iter_mut()
            .flat_map(|class| class.iter_mut())
            .find(|record| record.source_b != SOURCE_NONE)
            .unwrap()
            .source_b = u16::MAX - 1;
        assert!(decode_r0_prototype(&coordinate, &homogeneous_direct_source_b).is_err());
        let mut homogeneous_direct_class = encode(R0ProgramEncoding::HomogeneousDirect);
        let R0EncodedProgram::HomogeneousDirect(program) = &mut homogeneous_direct_class else {
            unreachable!();
        };
        let populated = program
            .classes
            .iter_mut()
            .find(|class| !class.is_empty())
            .unwrap();
        populated[0].header = (7 << CLASS_SHIFT) | (populated[0].header & COEFFICIENT_MASK);
        assert!(decode_r0_prototype(&coordinate, &homogeneous_direct_class).is_err());

        let mut grouped = encode(R0ProgramEncoding::GroupedSlot);
        let R0EncodedProgram::GroupedSlot(program) = &mut grouped else {
            unreachable!();
        };
        let GroupedAtom::Group { members, .. } = program
            .atoms
            .iter_mut()
            .find(|atom| matches!(atom, GroupedAtom::Group { .. }))
            .unwrap()
        else {
            unreachable!();
        };
        members.truncate(1);
        assert!(decode_r0_prototype(&coordinate, &grouped).is_err());
        let mut grouped_slots = encode(R0ProgramEncoding::GroupedSlot);
        let R0EncodedProgram::GroupedSlot(program) = &mut grouped_slots else {
            unreachable!();
        };
        program.source_slots[0] ^= 1;
        assert!(decode_r0_prototype(&coordinate, &grouped_slots).is_err());
        let mut grouped_slot_source = encode(R0ProgramEncoding::GroupedSlot);
        let R0EncodedProgram::GroupedSlot(program) = &mut grouped_slot_source else {
            unreachable!();
        };
        let member = program
            .atoms
            .iter_mut()
            .find_map(|atom| match atom {
                GroupedAtom::Group { members, .. } => members.first_mut(),
                GroupedAtom::Singleton { .. } => None,
            })
            .unwrap();
        member.source_a = StoredSource::Slot(u16::MAX);
        assert!(decode_r0_prototype(&coordinate, &grouped_slot_source).is_err());
        let mut grouped_slot_coefficient = encode(R0ProgramEncoding::GroupedSlot);
        let R0EncodedProgram::GroupedSlot(program) = &mut grouped_slot_coefficient else {
            unreachable!();
        };
        let GroupedAtom::Singleton { coefficient_id, .. } = program
            .atoms
            .iter_mut()
            .find(|atom| matches!(atom, GroupedAtom::Singleton { .. }))
            .unwrap()
        else {
            unreachable!();
        };
        *coefficient_id = u32::MAX;
        assert!(decode_r0_prototype(&coordinate, &grouped_slot_coefficient).is_err());

        let mut grouped_coefficient = encode(R0ProgramEncoding::GroupedDirect);
        let R0EncodedProgram::GroupedDirect(program) = &mut grouped_coefficient else {
            unreachable!();
        };
        let GroupedAtom::Singleton { coefficient_id, .. } = program
            .atoms
            .iter_mut()
            .find(|atom| matches!(atom, GroupedAtom::Singleton { .. }))
            .unwrap()
        else {
            unreachable!();
        };
        *coefficient_id = u32::MAX;
        assert!(decode_r0_prototype(&coordinate, &grouped_coefficient).is_err());
        let mut grouped_direct_source = encode(R0ProgramEncoding::GroupedDirect);
        let R0EncodedProgram::GroupedDirect(program) = &mut grouped_direct_source else {
            unreachable!();
        };
        let member = program
            .atoms
            .iter_mut()
            .find_map(|atom| match atom {
                GroupedAtom::Group { members, .. } => members.first_mut(),
                GroupedAtom::Singleton { .. } => None,
            })
            .unwrap();
        member.source_a = StoredSource::Direct(u16::MAX);
        assert!(decode_r0_prototype(&coordinate, &grouped_direct_source).is_err());
        let mut grouped_member_class = encode(R0ProgramEncoding::GroupedDirect);
        let R0EncodedProgram::GroupedDirect(program) = &mut grouped_member_class else {
            unreachable!();
        };
        let member = program
            .atoms
            .iter_mut()
            .find_map(|atom| match atom {
                GroupedAtom::Group { members, .. } => members.first_mut(),
                GroupedAtom::Singleton { .. } => None,
            })
            .unwrap();
        member.term_class = 7;
        assert!(decode_r0_prototype(&coordinate, &grouped_member_class).is_err());
        let mut grouped_member_coefficient = encode(R0ProgramEncoding::GroupedDirect);
        let R0EncodedProgram::GroupedDirect(program) = &mut grouped_member_coefficient else {
            unreachable!();
        };
        let member = program
            .atoms
            .iter_mut()
            .find_map(|atom| match atom {
                GroupedAtom::Group { members, .. } => members.first_mut(),
                GroupedAtom::Singleton { .. } => None,
            })
            .unwrap();
        member.immediate = u32::MAX;
        assert!(decode_r0_prototype(&coordinate, &grouped_member_coefficient).is_err());
        let mut grouped_duplicate = encode(R0ProgramEncoding::GroupedDirect);
        let R0EncodedProgram::GroupedDirect(program) = &mut grouped_duplicate else {
            unreachable!();
        };
        let group_ids = program
            .atoms
            .iter()
            .filter_map(|atom| match atom {
                GroupedAtom::Group { group_id, .. } => Some(*group_id),
                _ => None,
            })
            .collect::<Vec<_>>();
        if group_ids.len() >= 2 {
            let duplicate = group_ids[0];
            let GroupedAtom::Group { group_id, .. } = program
                .atoms
                .iter_mut()
                .filter(|atom| matches!(atom, GroupedAtom::Group { .. }))
                .nth(1)
                .unwrap()
            else {
                unreachable!();
            };
            *group_id = duplicate;
            assert!(decode_r0_prototype(&coordinate, &grouped_duplicate).is_err());
        }
    }

    #[test]
    fn cpu_capacity_artifact_pins_all_encodings_and_grouped_maximum() {
        let artifact = build_r0_prototype_capacity_artifact().unwrap();
        assert_eq!(artifact.schema_version, 1);
        assert_eq!(artifact.coordinates.len(), 57);
        assert!(artifact.coordinates.iter().all(
            |coordinate| coordinate.encodings.len() == 8 && coordinate.descriptors.len() == 32
        ));
        assert_eq!(artifact.maxima.len(), 8);
        assert_eq!(artifact.descriptor_layouts.len(), 15);
        for encoding in [
            R0ProgramEncoding::GroupedSlot,
            R0ProgramEncoding::GroupedDirect,
        ] {
            let maximum = artifact
                .maxima
                .iter()
                .find(|row| row.encoding == encoding)
                .unwrap();
            assert_eq!(maximum.represented_records, 1_841);
            assert_eq!(maximum.circuit, "bigint_with_extended_control");
            assert_eq!(maximum.layer, 0);
        }
    }
}
