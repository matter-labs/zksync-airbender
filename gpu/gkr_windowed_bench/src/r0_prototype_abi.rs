use core::mem::{align_of, offset_of, size_of};
use std::collections::BTreeMap;
use std::io::Write;
use std::process::{Command, Stdio};

use field::PrimeField;
use gkr_eval_ir::Bf;
use gpu_gkr_compiler::backward::{
    derive_window_shape, lower_window_sections, window_operands, CoeffChallenge, CoeffProduct,
    NormalizedCoefficientRecipe, WindowCoefficientPlan, WindowGroupedAtom, WindowGroupedMember,
    WindowGroupedProgram, WindowLoweringError, WindowLoweringInputs, WindowPhase,
};
use serde::{Deserialize, Serialize};

use crate::abi::{WindowEqSizes, E4};
use crate::accumulator_schedule::{SemanticSourceKey, SourceProjection};
use crate::r0_abi::{R0VmDesc, R0WindowAddr, KERNEL_ARGUMENT_CEILING_BYTES, R0_WINDOW_CAPACITY};
use crate::r0_artifact::{FrozenR0Coordinate, FrozenR0Recipe};
use crate::r0_prototype_encoding::{
    decode_current_fixed_wire_order, packed_source_slots, recipe_for_coefficient, CompactR0Program,
    FixedRecord, GroupedAtom, GroupedSlotProgram, HomogeneousDirectProgram, HomogeneousSlotProgram,
    R0EncodedProgram, R0Phase, R0PrototypeProgramEntry, R0PrototypeProgramSet,
    SplitFixedDirectProgram, SplitFixedSlotProgram, StoredSource,
};
use crate::r0_prototype_manifest::{R0DedicatedShape, R0ProgramEncoding};
use crate::r0_prototype_tile::{
    plan_r0_source_tiles, R0SourceTilePlan, R0TileCapacity, R0_TILE_SOURCE_NONE,
};

pub const R0_PROTOTYPE_COMMON_SECTION_WORDS: usize = 16;
pub const R0_PROTOTYPE_IMMEDIATE_CAPACITY: usize = 512;
pub const R0_PROTOTYPE_TILE_CAPACITY: usize = 330;
pub const R0_PROTOTYPE_TILE_SOURCE_CAPACITY: usize = 2_618;
pub const R0_PROTOTYPE_TILE_RECORD_CAPACITY: usize = 1_632;

pub const R0_CURRENT_PROGRAM_CAPACITY: usize = 6_528;
pub const R0_COMPACT_PROGRAM_CAPACITY: usize = 6_208;
pub const R0_SPLIT_PROGRAM_CAPACITY: usize = 6_528;
pub const R0_HOMOGENEOUS_PROGRAM_CAPACITY: usize = 6_368;
pub const R0_GROUPED_PROGRAM_CAPACITY: usize = 7_680;
pub const R0_PROTOTYPE_SOURCE_SLOT_CAPACITY: usize = 1_062;

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub struct R0PrototypeCommonDesc {
    pub window_bases: [R0WindowAddr; R0_WINDOW_CAPACITY],
    pub eq_low: *const E4,
    pub partials: *mut E4,
    pub log_rows: u32,
    pub record_count: u32,
    pub bf_record_count: u32,
    pub source_slot_count: u32,
}

impl Default for R0PrototypeCommonDesc {
    fn default() -> Self {
        Self {
            window_bases: [R0WindowAddr::default(); R0_WINDOW_CAPACITY],
            eq_low: core::ptr::null(),
            partials: core::ptr::null_mut(),
            log_rows: 0,
            record_count: 0,
            bf_record_count: 0,
            source_slot_count: 0,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R0PrototypeProgramMeta {
    pub program_words: u32,
    pub immediate_count: u32,
    pub window_count: u32,
    pub banked_coefficient_count: u32,
    pub eq_sizes: WindowEqSizes,
    pub sections: [u32; R0_PROTOTYPE_COMMON_SECTION_WORDS],
    pub program_sha256: [u8; 32],
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct R0PrototypeOrdinaryDesc<
    const PROGRAM: usize,
    const SOURCES: usize,
    const IMMEDIATES: usize,
> {
    pub common: R0PrototypeCommonDesc,
    pub meta: R0PrototypeProgramMeta,
    pub program: [u16; PROGRAM],
    pub source_slots: [u16; SOURCES],
    pub immediates: [u32; IMMEDIATES],
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R0PrototypeTileHeader {
    pub first_record: u16,
    pub record_count: u16,
    pub source_offset: u16,
    pub source_counts: u16,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R0PrototypeTileMeta {
    pub tile_count: u32,
    pub tile_source_count: u32,
    pub tile_record_count: u32,
    pub capacity: u32,
    pub max_dynamic_shared_bytes: u32,
    pub reserved: [u32; 3],
    pub tile_sha256: [u8; 32],
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct R0PrototypeMaterializedDesc<
    const PROGRAM: usize,
    const SOURCES: usize,
    const IMMEDIATES: usize,
> {
    pub ordinary: R0PrototypeOrdinaryDesc<PROGRAM, SOURCES, IMMEDIATES>,
    pub tile_meta: R0PrototypeTileMeta,
    pub tiles: [R0PrototypeTileHeader; R0_PROTOTYPE_TILE_CAPACITY],
    pub tile_sources: [u16; R0_PROTOTYPE_TILE_SOURCE_CAPACITY],
    pub record_local_sources: [[u8; 2]; R0_PROTOTYPE_TILE_RECORD_CAPACITY],
}

pub type R0CompactOrdinaryDesc =
    R0PrototypeOrdinaryDesc<R0_COMPACT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>;
pub type R0SplitSlotOrdinaryDesc =
    R0PrototypeOrdinaryDesc<R0_SPLIT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>;
pub type R0SplitDirectOrdinaryDesc = R0PrototypeOrdinaryDesc<R0_SPLIT_PROGRAM_CAPACITY, 0, 0>;
pub type R0HomogeneousSlotOrdinaryDesc =
    R0PrototypeOrdinaryDesc<R0_HOMOGENEOUS_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>;
pub type R0HomogeneousDirectOrdinaryDesc =
    R0PrototypeOrdinaryDesc<R0_HOMOGENEOUS_PROGRAM_CAPACITY, 0, 0>;
pub type R0GroupedSlotOrdinaryDesc = R0PrototypeOrdinaryDesc<
    R0_GROUPED_PROGRAM_CAPACITY,
    R0_PROTOTYPE_SOURCE_SLOT_CAPACITY,
    R0_PROTOTYPE_IMMEDIATE_CAPACITY,
>;
pub type R0GroupedDirectOrdinaryDesc =
    R0PrototypeOrdinaryDesc<R0_GROUPED_PROGRAM_CAPACITY, 0, R0_PROTOTYPE_IMMEDIATE_CAPACITY>;

pub type R0CurrentMaterializedDesc =
    R0PrototypeMaterializedDesc<R0_CURRENT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>;
pub type R0CompactMaterializedDesc =
    R0PrototypeMaterializedDesc<R0_COMPACT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>;
pub type R0SplitSlotMaterializedDesc =
    R0PrototypeMaterializedDesc<R0_SPLIT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>;
pub type R0SplitDirectMaterializedDesc =
    R0PrototypeMaterializedDesc<R0_SPLIT_PROGRAM_CAPACITY, 0, 0>;
pub type R0HomogeneousSlotMaterializedDesc = R0PrototypeMaterializedDesc<
    R0_HOMOGENEOUS_PROGRAM_CAPACITY,
    R0_PROTOTYPE_SOURCE_SLOT_CAPACITY,
    0,
>;
pub type R0HomogeneousDirectMaterializedDesc =
    R0PrototypeMaterializedDesc<R0_HOMOGENEOUS_PROGRAM_CAPACITY, 0, 0>;
pub type R0GroupedSlotMaterializedDesc = R0PrototypeMaterializedDesc<
    R0_GROUPED_PROGRAM_CAPACITY,
    R0_PROTOTYPE_SOURCE_SLOT_CAPACITY,
    R0_PROTOTYPE_IMMEDIATE_CAPACITY,
>;
pub type R0GroupedDirectMaterializedDesc =
    R0PrototypeMaterializedDesc<R0_GROUPED_PROGRAM_CAPACITY, 0, R0_PROTOTYPE_IMMEDIATE_CAPACITY>;

pub enum R0PrototypePayload {
    CurrentOrdinary(R0VmDesc),
    CompactOrdinary(R0CompactOrdinaryDesc),
    SplitSlotOrdinary(R0SplitSlotOrdinaryDesc),
    SplitDirectOrdinary(R0SplitDirectOrdinaryDesc),
    HomogeneousSlotOrdinary(R0HomogeneousSlotOrdinaryDesc),
    HomogeneousDirectOrdinary(R0HomogeneousDirectOrdinaryDesc),
    GroupedSlotOrdinary(R0GroupedSlotOrdinaryDesc),
    GroupedDirectOrdinary(R0GroupedDirectOrdinaryDesc),
    CurrentMaterialized(R0CurrentMaterializedDesc),
    CompactMaterialized(R0CompactMaterializedDesc),
    SplitSlotMaterialized(R0SplitSlotMaterializedDesc),
    SplitDirectMaterialized(R0SplitDirectMaterializedDesc),
    HomogeneousSlotMaterialized(R0HomogeneousSlotMaterializedDesc),
    HomogeneousDirectMaterialized(R0HomogeneousDirectMaterializedDesc),
    GroupedSlotMaterialized(R0GroupedSlotMaterializedDesc),
    GroupedDirectMaterialized(R0GroupedDirectMaterializedDesc),
}

pub struct PreparedPrototypeDescriptor {
    pub encoding: R0ProgramEncoding,
    pub capacity: Option<R0TileCapacity>,
    pub payload: R0PrototypePayload,
    pub payload_size: usize,
    pub program_sha256: String,
    pub tile_sha256: Option<String>,
    pub coefficient_recipes: Vec<FrozenR0Recipe>,
    pub dedicated_coefficient_plans: Vec<DedicatedCoefficientPlan>,
}

impl PreparedPrototypeDescriptor {
    pub(crate) fn runtime_common(&self) -> R0PrototypeCommonDesc {
        match &self.payload {
            R0PrototypePayload::CurrentOrdinary(desc) => R0PrototypeCommonDesc {
                window_bases: desc.window_bases,
                eq_low: desc.eq_low,
                partials: desc.partials,
                log_rows: desc.log_rows,
                record_count: desc.record_count,
                bf_record_count: desc.record_count,
                source_slot_count: desc.source_count,
            },
            R0PrototypePayload::CompactOrdinary(desc) => desc.common,
            R0PrototypePayload::SplitSlotOrdinary(desc) => desc.common,
            R0PrototypePayload::SplitDirectOrdinary(desc) => desc.common,
            R0PrototypePayload::HomogeneousSlotOrdinary(desc) => desc.common,
            R0PrototypePayload::HomogeneousDirectOrdinary(desc) => desc.common,
            R0PrototypePayload::GroupedSlotOrdinary(desc) => desc.common,
            R0PrototypePayload::GroupedDirectOrdinary(desc) => desc.common,
            R0PrototypePayload::CurrentMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::CompactMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::SplitSlotMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::SplitDirectMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::HomogeneousSlotMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::HomogeneousDirectMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::GroupedSlotMaterialized(desc) => desc.ordinary.common,
            R0PrototypePayload::GroupedDirectMaterialized(desc) => desc.ordinary.common,
        }
    }

    pub(crate) fn bind_runtime(&mut self, seed: R0VmDesc) -> Result<(), R0PrototypeAbiError> {
        fn bind(common: &mut R0PrototypeCommonDesc, seed: R0VmDesc) {
            common.window_bases = seed.window_bases;
            common.eq_low = seed.eq_low;
            common.partials = seed.partials;
            common.log_rows = seed.log_rows;
        }

        let expected_log_rows = self.runtime_common().log_rows;
        if seed.log_rows != expected_log_rows {
            return Err(R0PrototypeAbiError::InvalidLogTrace(seed.log_rows + 3));
        }
        match &mut self.payload {
            R0PrototypePayload::CurrentOrdinary(desc) => {
                desc.window_bases = seed.window_bases;
                desc.eq_low = seed.eq_low;
                desc.partials = seed.partials;
                desc.log_rows = seed.log_rows;
            }
            R0PrototypePayload::CompactOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::SplitSlotOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::SplitDirectOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::HomogeneousSlotOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::HomogeneousDirectOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::GroupedSlotOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::GroupedDirectOrdinary(desc) => bind(&mut desc.common, seed),
            R0PrototypePayload::CurrentMaterialized(desc) => bind(&mut desc.ordinary.common, seed),
            R0PrototypePayload::CompactMaterialized(desc) => bind(&mut desc.ordinary.common, seed),
            R0PrototypePayload::SplitSlotMaterialized(desc) => {
                bind(&mut desc.ordinary.common, seed)
            }
            R0PrototypePayload::SplitDirectMaterialized(desc) => {
                bind(&mut desc.ordinary.common, seed)
            }
            R0PrototypePayload::HomogeneousSlotMaterialized(desc) => {
                bind(&mut desc.ordinary.common, seed)
            }
            R0PrototypePayload::HomogeneousDirectMaterialized(desc) => {
                bind(&mut desc.ordinary.common, seed)
            }
            R0PrototypePayload::GroupedSlotMaterialized(desc) => {
                bind(&mut desc.ordinary.common, seed)
            }
            R0PrototypePayload::GroupedDirectMaterialized(desc) => {
                bind(&mut desc.ordinary.common, seed)
            }
        }
        Ok(())
    }

    pub fn max_dynamic_shared_bytes(&self) -> u32 {
        match &self.payload {
            R0PrototypePayload::CurrentMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::CompactMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::SplitSlotMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::SplitDirectMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::HomogeneousSlotMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::HomogeneousDirectMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::GroupedSlotMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            R0PrototypePayload::GroupedDirectMaterialized(desc) => {
                desc.tile_meta.max_dynamic_shared_bytes
            }
            _ => 0,
        }
    }

    pub fn tails_are_zero(&self) -> bool {
        match &self.payload {
            R0PrototypePayload::CurrentOrdinary(desc) => {
                desc.program[desc.record_count as usize * 4..]
                    .iter()
                    .all(|word| *word == 0)
                    && desc.source_slots[desc.source_count as usize..]
                        .iter()
                        .all(|word| *word == 0)
            }
            R0PrototypePayload::CompactOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::SplitSlotOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::SplitDirectOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::HomogeneousSlotOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::HomogeneousDirectOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::GroupedSlotOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::GroupedDirectOrdinary(desc) => ordinary_tails_zero(desc),
            R0PrototypePayload::CurrentMaterialized(desc) => materialized_tails_zero(desc),
            R0PrototypePayload::CompactMaterialized(desc) => materialized_tails_zero(desc),
            R0PrototypePayload::SplitSlotMaterialized(desc) => materialized_tails_zero(desc),
            R0PrototypePayload::SplitDirectMaterialized(desc) => materialized_tails_zero(desc),
            R0PrototypePayload::HomogeneousSlotMaterialized(desc) => materialized_tails_zero(desc),
            R0PrototypePayload::HomogeneousDirectMaterialized(desc) => {
                materialized_tails_zero(desc)
            }
            R0PrototypePayload::GroupedSlotMaterialized(desc) => materialized_tails_zero(desc),
            R0PrototypePayload::GroupedDirectMaterialized(desc) => materialized_tails_zero(desc),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0PrototypeAbiError {
    MissingEncoding(R0ProgramEncoding),
    DuplicateEncoding(R0ProgramEncoding),
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    InvalidLogTrace(u32),
    Encoding(String),
    Tile(String),
    Hash(String),
    NativeProbe(i32),
}

struct FlatProgram {
    words: Vec<u16>,
    source_slots: Vec<u16>,
    immediates: Vec<u32>,
    sections: [u32; R0_PROTOTYPE_COMMON_SECTION_WORDS],
    coefficient_recipes: Vec<FrozenR0Recipe>,
    banked_coefficient_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DedicatedCoefficientPlan {
    Direct(FrozenR0Recipe),
    Scaled { recipe: FrozenR0Recipe, scalar: u32 },
    LinearBasis { recipe: FrozenR0Recipe, limb: u8 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DedicatedSectionedProgram {
    pub words: Vec<u16>,
    pub source_slots: Vec<u16>,
    pub immediates: Vec<u32>,
    pub sections: [u32; R0_PROTOTYPE_COMMON_SECTION_WORDS],
    pub coefficient_plans: Vec<DedicatedCoefficientPlan>,
    pub shape: R0DedicatedShape,
}

fn checked_u16(value: usize, resource: &'static str) -> Result<u16, R0PrototypeAbiError> {
    u16::try_from(value).map_err(|_| R0PrototypeAbiError::Capacity {
        resource,
        required: value,
        capacity: u16::MAX as usize,
    })
}

fn stored_word(source: StoredSource) -> u16 {
    match source {
        StoredSource::Slot(value) | StoredSource::Direct(value) => value,
    }
}

fn push_fixed(words: &mut Vec<u16>, record: &FixedRecord) {
    words.extend([
        record.header,
        record.source_a,
        record.source_b,
        record.reserved,
    ]);
}

fn flatten_split(slot: &SplitFixedSlotProgram) -> FlatProgram {
    let mut words = Vec::with_capacity((slot.bf.len() + slot.e4.len()) * 4);
    for record in slot.bf.iter().chain(&slot.e4) {
        push_fixed(&mut words, record);
    }
    let mut sections = [0u32; R0_PROTOTYPE_COMMON_SECTION_WORDS];
    sections[0] = slot.bf.len() as u32;
    sections[1] = slot.e4.len() as u32;
    FlatProgram {
        words,
        source_slots: slot.source_slots.clone(),
        immediates: Vec::new(),
        sections,
        coefficient_recipes: Vec::new(),
        banked_coefficient_count: 0,
    }
}

fn flatten_split_direct(program: &SplitFixedDirectProgram) -> FlatProgram {
    let mut words = Vec::with_capacity((program.bf.len() + program.e4.len()) * 4);
    for record in program.bf.iter().chain(&program.e4) {
        push_fixed(&mut words, record);
    }
    let mut sections = [0u32; R0_PROTOTYPE_COMMON_SECTION_WORDS];
    sections[0] = program.bf.len() as u32;
    sections[1] = program.e4.len() as u32;
    FlatProgram {
        words,
        source_slots: Vec::new(),
        immediates: Vec::new(),
        sections,
        coefficient_recipes: Vec::new(),
        banked_coefficient_count: 0,
    }
}

fn flatten_homogeneous(
    classes: &[Vec<FixedRecord>; 5],
    order: &[u8],
    source_slots: Vec<u16>,
) -> FlatProgram {
    let mut words = order
        .iter()
        .map(|class| u16::from(*class))
        .collect::<Vec<_>>();
    let mut sections = [0u32; R0_PROTOTYPE_COMMON_SECTION_WORDS];
    sections[0] = 0;
    sections[1] = order.len() as u32;
    for (class, records) in classes.iter().enumerate() {
        sections[2 + 2 * class] = words.len() as u32;
        sections[3 + 2 * class] = records.len() as u32;
        for record in records {
            words.push(record.header);
            words.push(record.source_a);
            if class >= 2 {
                words.push(record.source_b);
            }
        }
    }
    FlatProgram {
        words,
        source_slots,
        immediates: Vec::new(),
        sections,
        coefficient_recipes: Vec::new(),
        banked_coefficient_count: 0,
    }
}

fn recipe_key(recipe: &FrozenR0Recipe) -> Result<Vec<u8>, R0PrototypeAbiError> {
    serde_json::to_vec(recipe).map_err(|error| R0PrototypeAbiError::Encoding(error.to_string()))
}

fn flatten_grouped(
    coordinate: &FrozenR0Coordinate,
    atoms: &[GroupedAtom],
    source_slots: Vec<u16>,
) -> Result<FlatProgram, R0PrototypeAbiError> {
    let one = recipe_for_coefficient(coordinate, 0)
        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
    let neg_one = recipe_for_coefficient(coordinate, 1)
        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
    let mut bank = BTreeMap::<Vec<u8>, FrozenR0Recipe>::new();
    let mut immediate_values = BTreeMap::<u32, ()>::new();
    for atom in atoms {
        match atom {
            GroupedAtom::Singleton { coefficient_id, .. } => {
                let recipe = recipe_for_coefficient(coordinate, *coefficient_id)
                    .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
                if recipe != one && recipe != neg_one {
                    bank.insert(recipe_key(&recipe)?, recipe);
                }
            }
            GroupedAtom::Group { core, members, .. } => {
                bank.insert(recipe_key(core)?, core.clone());
                for member in members {
                    if member.immediate != 1 && u64::from(member.immediate) != 2_013_265_920 {
                        immediate_values.insert(member.immediate, ());
                    }
                }
            }
        }
    }
    let coefficient_recipes = bank.into_values().collect::<Vec<_>>();
    let coefficient_ids = coefficient_recipes
        .iter()
        .enumerate()
        .map(|(index, recipe)| Ok((recipe_key(recipe)?, 2 + index as u16)))
        .collect::<Result<BTreeMap<_, _>, R0PrototypeAbiError>>()?;
    let immediates = immediate_values.into_keys().collect::<Vec<_>>();
    let immediate_ids = immediates
        .iter()
        .enumerate()
        .map(|(index, immediate)| (*immediate, 2 + index as u16))
        .collect::<BTreeMap<_, _>>();
    let coefficient_id = |recipe: &FrozenR0Recipe| -> Result<u16, R0PrototypeAbiError> {
        if *recipe == one {
            Ok(0)
        } else if *recipe == neg_one {
            Ok(1)
        } else {
            coefficient_ids
                .get(&recipe_key(recipe)?)
                .copied()
                .ok_or_else(|| R0PrototypeAbiError::Encoding("grouped coefficient absent".into()))
        }
    };
    let immediate_id = |value: u32| -> Result<u16, R0PrototypeAbiError> {
        if value == 1 {
            Ok(0)
        } else if u64::from(value) == 2_013_265_920 {
            Ok(1)
        } else {
            immediate_ids
                .get(&value)
                .copied()
                .ok_or_else(|| R0PrototypeAbiError::Encoding("grouped immediate absent".into()))
        }
    };
    let mut words = Vec::new();
    let mut group_headers = 0u32;
    for atom in atoms {
        match atom {
            GroupedAtom::Singleton {
                coefficient_id: original,
                term_class,
                source_a,
                source_b,
                ..
            } => {
                let recipe = recipe_for_coefficient(coordinate, *original)
                    .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
                words.push((u16::from(*term_class) << 13) | coefficient_id(&recipe)?);
                words.push(stored_word(*source_a));
                if let Some(source_b) = source_b {
                    words.push(stored_word(*source_b));
                }
            }
            GroupedAtom::Group {
                phase,
                group_id,
                core,
                members,
            } => {
                group_headers += 1;
                words.extend([
                    0xffff,
                    coefficient_id(core)?,
                    checked_u16(members.len(), "group members")?,
                    checked_u16(*group_id as usize, "group id")?
                        | if matches!(phase, crate::r0_prototype_encoding::R0Phase::E4) {
                            0x8000
                        } else {
                            0
                        },
                ]);
                for member in members {
                    words.extend([
                        u16::from(member.term_class),
                        immediate_id(member.immediate)?,
                        stored_word(member.source_a),
                    ]);
                    if let Some(source_b) = member.source_b {
                        words.push(stored_word(source_b));
                    }
                }
            }
        }
    }
    let mut sections = [0u32; R0_PROTOTYPE_COMMON_SECTION_WORDS];
    sections[0] = atoms.len() as u32;
    sections[1] = group_headers;
    let banked_coefficient_count = coefficient_recipes.len();
    Ok(FlatProgram {
        words,
        source_slots,
        immediates,
        sections,
        coefficient_recipes,
        banked_coefficient_count,
    })
}

pub(crate) const R0_DEDICATED_GROUP_BF: u16 = 6;
pub(crate) const R0_DEDICATED_GROUP_E4: u16 = 7;
pub(crate) const R0_DEDICATED_LINEAR_BF_PROCEDURAL: u16 = 4;
pub(crate) const R0_DEDICATED_PRODUCT_E4_E4: u16 = 5;
pub(crate) const R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B: u16 = 8;
pub(crate) const R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB: u16 = 9;
pub(crate) const R0_DEDICATED_LINEAR_E4_WIDE: u16 = 10;
pub(crate) const R0_DEDICATED_HAS_PRODUCT: u16 = 1 << 15;
pub(crate) const R0_DEDICATED_REDUCE_AFTER: u16 = 1 << 15;
pub(crate) const R0_DEDICATED_NEGATE_COEFFICIENT: u16 = 1 << 15;

fn push_dedicated_instruction(
    words: &mut Vec<u16>,
    term_class: u16,
    factor: u16,
    source_a: u16,
    source_b: u16,
) {
    words.extend([term_class, factor, source_a, source_b]);
}

fn legacy_dedicated_slot_source(
    coordinate: &FrozenR0Coordinate,
    source: StoredSource,
) -> Result<(u16, Option<u16>), R0PrototypeAbiError> {
    let slot = match source {
        StoredSource::Slot(slot) => slot,
        StoredSource::Direct(_) => {
            return Err(R0PrototypeAbiError::Encoding(
                "dedicated grouped stream requires a slot source".to_owned(),
            ));
        }
    };
    let binding = coordinate
        .binding
        .source_slots
        .get(usize::from(slot))
        .ok_or_else(|| R0PrototypeAbiError::Encoding("dedicated source slot absent".into()))?;
    let window = coordinate
        .binding
        .windows
        .get(usize::from(binding.window))
        .ok_or_else(|| R0PrototypeAbiError::Encoding("dedicated source window absent".into()))?;
    Ok((
        (u16::from(binding.window) << 7) | binding.column,
        window.procedural_kind().map(u16::from),
    ))
}

fn dedicated_operands(
    coordinate: &FrozenR0Coordinate,
    term_class: u8,
    source_a: StoredSource,
    source_b: Option<StoredSource>,
) -> Result<(u16, u16, u16), R0PrototypeAbiError> {
    window_operands(&coordinate.binding, term_class, source_a, source_b)
        .map_err(abi_error_from_window)
}

#[doc(hidden)]
pub fn legacy_dedicated_operands(
    coordinate: &FrozenR0Coordinate,
    term_class: u8,
    source_a: StoredSource,
    source_b: Option<StoredSource>,
) -> Result<(u16, u16, u16), R0PrototypeAbiError> {
    let (slot_a, procedural_a) = legacy_dedicated_slot_source(coordinate, source_a)?;
    let (slot_b, procedural_b) = source_b
        .map(|source| legacy_dedicated_slot_source(coordinate, source))
        .transpose()?
        .unwrap_or((0, None));
    match (term_class, procedural_a, procedural_b) {
        (0, Some(kind), None) => Ok((R0_DEDICATED_LINEAR_BF_PROCEDURAL, kind, 0)),
        (2, Some(kind), None) => Ok((R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B, slot_b, kind)),
        (2, None, Some(kind)) => Ok((R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B, slot_a, kind)),
        (4, None, None) => Ok((R0_DEDICATED_PRODUCT_E4_E4, slot_a, slot_b)),
        (_, None, None) => Ok((u16::from(term_class), slot_a, slot_b)),
        (2, Some(kind_a), Some(kind_b)) => {
            Ok((R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB, kind_a, kind_b))
        }
        _ => Err(R0PrototypeAbiError::Encoding(
            "dedicated procedural source appears in an unsupported term class".to_owned(),
        )),
    }
}

pub fn derive_dedicated_shape(
    coordinate: &FrozenR0Coordinate,
    program: &GroupedSlotProgram,
) -> Result<R0DedicatedShape, R0PrototypeAbiError> {
    let grouped = window_grouped_program(program);
    derive_window_shape(&coordinate.binding, &grouped)
        .map(|shape| R0DedicatedShape::from_bits(shape.bits()))
        .map_err(abi_error_from_window)
}

/// Derive only those compile-time features that remove work from an active
/// sectioned hot loop.  This is deliberately checked independently from the
/// legacy dedicated flattener so future lowering cannot silently reinterpret
/// a new grouped-program shape.
///
/// Retained as the differential oracle for the compiler-owned lowering; it is
/// never reached through [`derive_dedicated_shape`].
#[doc(hidden)]
pub fn legacy_derive_dedicated_shape(
    coordinate: &FrozenR0Coordinate,
    program: &GroupedSlotProgram,
) -> Result<R0DedicatedShape, R0PrototypeAbiError> {
    let mut shape = R0DedicatedShape::EMPTY;

    for atom in &program.atoms {
        match atom {
            GroupedAtom::Singleton {
                phase: R0Phase::Bf,
                term_class,
                source_a,
                source_b,
                ..
            } => {
                let (class, _, _) =
                    legacy_dedicated_operands(coordinate, *term_class, *source_a, *source_b)?;
                if matches!(
                    class,
                    R0_DEDICATED_LINEAR_BF_PROCEDURAL
                        | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B
                        | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB
                ) {
                    shape.insert(R0DedicatedShape::BF_PROCEDURAL);
                }
                if !matches!(
                    class,
                    0 | 2
                        | R0_DEDICATED_LINEAR_BF_PROCEDURAL
                        | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B
                        | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB
                ) {
                    return Err(R0PrototypeAbiError::Encoding(format!(
                        "unsupported BF singleton class {class}"
                    )));
                }
            }
            GroupedAtom::Singleton {
                phase: R0Phase::E4,
                term_class,
                source_a,
                source_b,
                ..
            } => {
                let (class, _, _) =
                    legacy_dedicated_operands(coordinate, *term_class, *source_a, *source_b)?;
                match class {
                    1 => {}
                    3 => shape.insert(R0DedicatedShape::E4_SINGLETON_CLASS_3),
                    R0_DEDICATED_PRODUCT_E4_E4 => {
                        shape.insert(R0DedicatedShape::E4_SINGLETON_CLASS_5)
                    }
                    _ => {
                        return Err(R0PrototypeAbiError::Encoding(format!(
                            "unsupported E4 singleton class {class}"
                        )));
                    }
                }
            }
            GroupedAtom::Group {
                phase: R0Phase::Bf,
                members,
                ..
            } => {
                let mut ordered = members.iter().collect::<Vec<_>>();
                ordered.sort_by_key(|member| member.term_class != 2);
                let product_prefix = ordered
                    .iter()
                    .take_while(|member| member.term_class == 2)
                    .count();
                let linear_tail = ordered.len() - product_prefix;
                if product_prefix == 0 || linear_tail > 1 {
                    return Err(R0PrototypeAbiError::Encoding(format!(
                        "dedicated BF group requires one or more products and at most one linear tail; products={product_prefix} tail={linear_tail}"
                    )));
                }
                if product_prefix > 4 {
                    shape.insert(R0DedicatedShape::BF_INNER_REDUCTION);
                }
                if product_prefix == 1 {
                    shape.insert(R0DedicatedShape::BF_SINGLE_PRODUCT_PREFIX);
                }
                if linear_tail == 1 {
                    shape.insert(R0DedicatedShape::BF_LINEAR_TAIL);
                }
                for member in ordered {
                    if member.immediate != 1 && member.immediate != 2_013_265_920 {
                        shape.insert(R0DedicatedShape::BF_BANKED_IMMEDIATE);
                    }
                    if member.immediate == 2_013_265_920 {
                        shape.insert(R0DedicatedShape::BF_NEGATIVE_FACTOR);
                    }
                    let (class, _, _) = legacy_dedicated_operands(
                        coordinate,
                        member.term_class,
                        member.source_a,
                        member.source_b,
                    )?;
                    if matches!(
                        class,
                        R0_DEDICATED_LINEAR_BF_PROCEDURAL
                            | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B
                            | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB
                    ) {
                        shape.insert(R0DedicatedShape::BF_PROCEDURAL);
                    }
                    if !matches!(
                        class,
                        0 | 2
                            | R0_DEDICATED_LINEAR_BF_PROCEDURAL
                            | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B
                            | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB
                    ) {
                        return Err(R0PrototypeAbiError::Encoding(format!(
                            "unsupported BF group member class {class}"
                        )));
                    }
                }
            }
            GroupedAtom::Group {
                phase: R0Phase::E4,
                members,
                ..
            } => {
                if !matches!(members.len(), 2 | 3) {
                    return Err(R0PrototypeAbiError::Encoding(format!(
                        "dedicated E4 group has {} members; expected linear plus one or two products",
                        members.len()
                    )));
                }
                let linear = &members[0];
                if linear.term_class != 1 || linear.immediate != 1 || linear.source_b.is_some() {
                    return Err(R0PrototypeAbiError::Encoding(
                        "dedicated E4 group requires exactly one first-position +1 linear member"
                            .to_owned(),
                    ));
                }
                let products = &members[1..];
                let mut e4_products = 0usize;
                let mut bf_products = 0usize;
                let mut e4_product_classes = Vec::with_capacity(products.len());
                for product in products {
                    if !matches!(product.immediate, 1 | 2_013_265_920) {
                        return Err(R0PrototypeAbiError::Encoding(format!(
                            "unsupported E4 product factor {}",
                            product.immediate
                        )));
                    }
                    let (class, _, _) = legacy_dedicated_operands(
                        coordinate,
                        product.term_class,
                        product.source_a,
                        product.source_b,
                    )?;
                    match class {
                        2
                        | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B
                        | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB => {
                            bf_products += 1;
                            if product.immediate == 2_013_265_920 {
                                shape.insert(R0DedicatedShape::BF_NEGATIVE_FACTOR);
                            }
                            if class != 2 {
                                shape.insert(R0DedicatedShape::BF_PROCEDURAL);
                            }
                        }
                        3 => {
                            e4_products += 1;
                            e4_product_classes.push(class);
                            if product.immediate == 2_013_265_920 {
                                shape.insert(R0DedicatedShape::E4_NEGATIVE_FACTOR);
                            }
                            shape.insert(R0DedicatedShape::E4_SINGLETON_CLASS_3);
                        }
                        R0_DEDICATED_PRODUCT_E4_E4 => {
                            e4_products += 1;
                            e4_product_classes.push(class);
                            if product.immediate == 2_013_265_920 {
                                shape.insert(R0DedicatedShape::E4_NEGATIVE_FACTOR);
                            }
                            shape.insert(R0DedicatedShape::E4_SINGLETON_CLASS_5);
                        }
                        _ => {
                            return Err(R0PrototypeAbiError::Encoding(format!(
                                "unsupported E4 product class {class}"
                            )));
                        }
                    }
                }
                if products.len() == 2 {
                    if bf_products != 0 || e4_products != 2 {
                        return Err(R0PrototypeAbiError::Encoding(
                            "dedicated E4 pair requires exactly two E4-valued products".to_owned(),
                        ));
                    }
                    if e4_product_classes[0] != e4_product_classes[1] {
                        return Err(R0PrototypeAbiError::Encoding(format!(
                            "heterogeneous E4 pair classes {} and {}",
                            e4_product_classes[0], e4_product_classes[1]
                        )));
                    }
                    shape.insert(R0DedicatedShape::E4_FIXED_PAIR);
                    shape.insert(if e4_product_classes[0] == 3 {
                        R0DedicatedShape::E4_PAIR_CLASS_3
                    } else {
                        R0DedicatedShape::E4_PAIR_CLASS_5
                    });
                } else if bf_products + e4_products != 1 {
                    return Err(R0PrototypeAbiError::Encoding(
                        "dedicated E4 singleton extraction produced no product".to_owned(),
                    ));
                }
            }
        }
    }

    Ok(shape)
}

fn dedicated_plan_key(plan: &DedicatedCoefficientPlan) -> Result<Vec<u8>, R0PrototypeAbiError> {
    serde_json::to_vec(plan).map_err(|error| R0PrototypeAbiError::Encoding(error.to_string()))
}

fn intern_dedicated_plan(
    plans: &mut Vec<DedicatedCoefficientPlan>,
    ids: &mut BTreeMap<Vec<u8>, u16>,
    plan: DedicatedCoefficientPlan,
) -> Result<u16, R0PrototypeAbiError> {
    let key = dedicated_plan_key(&plan)?;
    if let Some(id) = ids.get(&key) {
        return Ok(*id);
    }
    let id = checked_u16(2 + plans.len(), "dedicated coefficient plans")?;
    plans.push(plan);
    ids.insert(key, id);
    Ok(id)
}

fn push_linear_basis_plans(
    plans: &mut Vec<DedicatedCoefficientPlan>,
    ids: &mut BTreeMap<Vec<u8>, u16>,
    recipe: &FrozenR0Recipe,
) -> Result<u16, R0PrototypeAbiError> {
    let first = checked_u16(2 + plans.len(), "dedicated linear basis plans")?;
    for limb in 0..4u8 {
        let plan = DedicatedCoefficientPlan::LinearBasis {
            recipe: recipe.clone(),
            limb,
        };
        let id = checked_u16(2 + plans.len(), "dedicated linear basis plans")?;
        if id != first + u16::from(limb) {
            return Err(R0PrototypeAbiError::Encoding(
                "dedicated linear basis IDs are not consecutive".to_owned(),
            ));
        }
        let key = dedicated_plan_key(&plan)?;
        if ids.contains_key(&key) {
            return Err(R0PrototypeAbiError::Encoding(
                "dedicated linear basis plan is duplicated".to_owned(),
            ));
        }
        plans.push(plan);
        ids.insert(key, id);
    }
    Ok(first)
}

fn u32_section_end(value: usize, resource: &'static str) -> Result<u32, R0PrototypeAbiError> {
    u32::try_from(value).map_err(|_| R0PrototypeAbiError::Capacity {
        resource,
        required: value,
        capacity: u32::MAX as usize,
    })
}

fn validate_sectioned_coefficient_id(
    encoded: u16,
    banked_count: usize,
    span: usize,
    resource: &'static str,
) -> Result<(), R0PrototypeAbiError> {
    let id = usize::from(encoded & R0_DEDICATED_HAS_PRODUCT.wrapping_sub(1));
    let bank_bias = crate::r0_abi::R0_COEFFICIENT_BANK_BIAS as usize;
    if span == 1 && id < bank_bias {
        return Ok(());
    }
    let first = id.checked_sub(bank_bias).ok_or_else(|| {
        R0PrototypeAbiError::Encoding(format!(
            "sectioned {resource} starts at reserved coefficient id {id}"
        ))
    })?;
    let end = first.checked_add(span).ok_or_else(|| {
        R0PrototypeAbiError::Encoding(format!("sectioned {resource} coefficient span overflow"))
    })?;
    if end > banked_count {
        return Err(R0PrototypeAbiError::Encoding(format!(
            "sectioned {resource} coefficient span [{first},{end}) exceeds banked count {banked_count}"
        )));
    }
    Ok(())
}

pub(crate) fn validate_sectioned_coefficient_ids(
    sectioned: &DedicatedSectionedProgram,
) -> Result<(), R0PrototypeAbiError> {
    let banked_count = sectioned.coefficient_plans.len();
    if banked_count > crate::r0_abi::R0_COEFFICIENT_CAPACITY {
        return Err(R0PrototypeAbiError::Capacity {
            resource: "dedicated sectioned coefficient bank",
            required: banked_count,
            capacity: crate::r0_abi::R0_COEFFICIENT_CAPACITY,
        });
    }
    let ends = sectioned.sections.map(|end| end as usize);
    if !ends[..4].windows(2).all(|pair| pair[0] <= pair[1])
        || ends[3].checked_mul(4) != Some(sectioned.words.len())
    {
        return Err(R0PrototypeAbiError::Encoding(
            "sectioned coefficient validation observed malformed endpoints".to_owned(),
        ));
    }

    let instruction = |pc: usize| -> Result<&[u16], R0PrototypeAbiError> {
        sectioned
            .words
            .get(4 * pc..4 * pc + 4)
            .ok_or_else(|| R0PrototypeAbiError::Encoding("sectioned instruction absent".into()))
    };
    let mut pc = 0usize;
    while pc < ends[0] {
        let head = instruction(pc)?;
        validate_sectioned_coefficient_id(head[1], banked_count, 1, "BF core")?;
        pc += 1;
        if head[0] == R0_DEDICATED_GROUP_BF {
            pc = pc.checked_add(usize::from(head[2])).ok_or_else(|| {
                R0PrototypeAbiError::Encoding("sectioned BF group arity overflow".into())
            })?;
            if pc > ends[0] {
                return Err(R0PrototypeAbiError::Encoding(
                    "sectioned BF group crosses its endpoint".into(),
                ));
            }
        }
    }
    while pc < ends[1] {
        let linear = instruction(pc)?;
        validate_sectioned_coefficient_id(linear[1], banked_count, 4, "linear coefficient span")?;
        pc += 1;
    }
    while pc < ends[2] {
        let singleton = instruction(pc)?;
        validate_sectioned_coefficient_id(singleton[1], banked_count, 1, "E4 singleton")?;
        pc += 1;
    }
    while pc < ends[3] {
        let head = instruction(pc)?;
        if head[0] != R0_DEDICATED_GROUP_E4 {
            return Err(R0PrototypeAbiError::Encoding(
                "sectioned pair section contains a non-pair head".into(),
            ));
        }
        validate_sectioned_coefficient_id(head[1], banked_count, 1, "E4 pair core")?;
        pc += 3;
        if pc > ends[3] {
            return Err(R0PrototypeAbiError::Encoding(
                "sectioned E4 pair crosses its endpoint".into(),
            ));
        }
    }
    Ok(())
}

fn window_phase(phase: R0Phase) -> WindowPhase {
    match phase {
        R0Phase::Bf => WindowPhase::Bf,
        R0Phase::E4 => WindowPhase::E4,
    }
}

pub(crate) fn normalized_from_frozen(recipe: &FrozenR0Recipe) -> NormalizedCoefficientRecipe {
    NormalizedCoefficientRecipe {
        terms: recipe
            .products
            .iter()
            .map(|product| CoeffProduct {
                scalar: product.scalar,
                challenges: product
                    .challenges
                    .iter()
                    .map(|challenge| CoeffChallenge(challenge.reference.clone()))
                    .collect(),
                inits_and_teardowns_top_bits: product.inits_and_teardowns_top_bits.clone(),
            })
            .collect(),
    }
}

pub(crate) fn frozen_from_normalized(recipe: &NormalizedCoefficientRecipe) -> FrozenR0Recipe {
    FrozenR0Recipe {
        products: recipe
            .terms
            .iter()
            .map(|product| crate::r0_artifact::FrozenR0Product {
                scalar: product.scalar,
                challenges: product
                    .challenges
                    .iter()
                    .map(|challenge| crate::r0_artifact::FrozenR0Challenge {
                        reference: challenge.0.clone(),
                    })
                    .collect(),
                inits_and_teardowns_top_bits: product.inits_and_teardowns_top_bits.clone(),
            })
            .collect(),
    }
}

fn window_grouped_program(program: &GroupedSlotProgram) -> WindowGroupedProgram {
    WindowGroupedProgram {
        atoms: program
            .atoms
            .iter()
            .map(|atom| match atom {
                GroupedAtom::Singleton {
                    phase,
                    coefficient_id,
                    term_class,
                    source_a,
                    source_b,
                } => WindowGroupedAtom::Singleton {
                    phase: window_phase(*phase),
                    coefficient_id: *coefficient_id,
                    term_class: *term_class,
                    source_a: *source_a,
                    source_b: *source_b,
                },
                GroupedAtom::Group {
                    phase,
                    group_id,
                    core,
                    members,
                } => WindowGroupedAtom::Group {
                    phase: window_phase(*phase),
                    group_id: *group_id,
                    core: normalized_from_frozen(core),
                    members: members
                        .iter()
                        .map(|member| WindowGroupedMember {
                            term_class: member.term_class,
                            immediate: member.immediate,
                            source_a: member.source_a,
                            source_b: member.source_b,
                        })
                        .collect(),
                },
            })
            .collect(),
        source_slots: program.source_slots.clone(),
    }
}

pub(crate) fn abi_error_from_window(error: WindowLoweringError) -> R0PrototypeAbiError {
    match error {
        WindowLoweringError::Capacity {
            resource,
            required,
            capacity,
        } => R0PrototypeAbiError::Capacity {
            resource,
            required,
            capacity,
        },
        WindowLoweringError::Encoding(message) => R0PrototypeAbiError::Encoding(message),
        other => R0PrototypeAbiError::Encoding(format!("{other:?}")),
    }
}

pub(crate) fn dedicated_plan_from_window(plan: &WindowCoefficientPlan) -> DedicatedCoefficientPlan {
    match plan {
        WindowCoefficientPlan::Direct(recipe) => {
            DedicatedCoefficientPlan::Direct(frozen_from_normalized(recipe))
        }
        WindowCoefficientPlan::Scaled { recipe, scalar } => DedicatedCoefficientPlan::Scaled {
            recipe: frozen_from_normalized(recipe),
            scalar: *scalar,
        },
        WindowCoefficientPlan::LinearBasis { recipe, limb } => {
            DedicatedCoefficientPlan::LinearBasis {
                recipe: frozen_from_normalized(recipe),
                limb: *limb,
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn window_plan_from_dedicated(plan: &DedicatedCoefficientPlan) -> WindowCoefficientPlan {
    match plan {
        DedicatedCoefficientPlan::Direct(recipe) => {
            WindowCoefficientPlan::Direct(normalized_from_frozen(recipe))
        }
        DedicatedCoefficientPlan::Scaled { recipe, scalar } => WindowCoefficientPlan::Scaled {
            recipe: normalized_from_frozen(recipe),
            scalar: *scalar,
        },
        DedicatedCoefficientPlan::LinearBasis { recipe, limb } => {
            WindowCoefficientPlan::LinearBasis {
                recipe: normalized_from_frozen(recipe),
                limb: *limb,
            }
        }
    }
}

pub(crate) fn lower_dedicated_sections(
    coordinate: &FrozenR0Coordinate,
    program: &GroupedSlotProgram,
) -> Result<DedicatedSectionedProgram, R0PrototypeAbiError> {
    let recipes = coordinate
        .recipes
        .iter()
        .map(normalized_from_frozen)
        .collect::<Vec<_>>();
    let lowered = lower_window_sections(
        &WindowLoweringInputs {
            layer: coordinate.layer as usize,
            binding: &coordinate.binding,
            coefficient_recipes: &recipes,
        },
        &window_grouped_program(program),
    )
    .map_err(abi_error_from_window)?;
    Ok(DedicatedSectionedProgram {
        words: lowered.words,
        source_slots: lowered.source_slots,
        immediates: lowered.immediates,
        sections: lowered.sections,
        coefficient_plans: lowered
            .coefficient_plans
            .iter()
            .map(dedicated_plan_from_window)
            .collect(),
        shape: R0DedicatedShape::from_bits(lowered.shape.bits()),
    })
}

/// Retained as the differential oracle for the compiler-owned lowering; it is
/// never reached through [`lower_dedicated_sections`].
#[doc(hidden)]
pub fn legacy_lower_dedicated_sections(
    coordinate: &FrozenR0Coordinate,
    program: &GroupedSlotProgram,
) -> Result<DedicatedSectionedProgram, R0PrototypeAbiError> {
    let grouped = flatten_grouped(coordinate, &program.atoms, program.source_slots.clone())?;
    let one = recipe_for_coefficient(coordinate, 0)
        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
    let neg_one = recipe_for_coefficient(coordinate, 1)
        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
    let mut plans = Vec::new();
    let mut plan_ids = BTreeMap::<Vec<u8>, u16>::new();
    let direct_id = |recipe: &FrozenR0Recipe,
                     plans: &mut Vec<DedicatedCoefficientPlan>,
                     plan_ids: &mut BTreeMap<Vec<u8>, u16>|
     -> Result<u16, R0PrototypeAbiError> {
        if *recipe == one {
            Ok(0)
        } else if *recipe == neg_one {
            Ok(1)
        } else {
            intern_dedicated_plan(
                plans,
                plan_ids,
                DedicatedCoefficientPlan::Direct(recipe.clone()),
            )
        }
    };
    let immediate_ids = grouped
        .immediates
        .iter()
        .enumerate()
        .map(|(index, immediate)| (*immediate, 2 + index as u16))
        .collect::<BTreeMap<_, _>>();
    let immediate_id = |value: u32| -> Result<u16, R0PrototypeAbiError> {
        if value == 1 {
            Ok(0)
        } else if value == 2_013_265_920 {
            Ok(1)
        } else {
            immediate_ids
                .get(&value)
                .copied()
                .ok_or_else(|| R0PrototypeAbiError::Encoding("dedicated immediate absent".into()))
        }
    };

    let mut bf = Vec::<u16>::new();
    let mut linear_e4 = Vec::<u16>::new();
    let mut e4_single = Vec::<u16>::new();
    let mut e4_pair = Vec::<u16>::new();

    for atom in &program.atoms {
        match atom {
            GroupedAtom::Singleton {
                phase: R0Phase::Bf,
                coefficient_id,
                term_class,
                source_a,
                source_b,
            } => {
                let recipe = recipe_for_coefficient(coordinate, *coefficient_id)
                    .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
                let (class, source_a, source_b) =
                    legacy_dedicated_operands(coordinate, *term_class, *source_a, *source_b)?;
                push_dedicated_instruction(
                    &mut bf,
                    class,
                    direct_id(&recipe, &mut plans, &mut plan_ids)?,
                    source_a,
                    source_b,
                );
            }
            GroupedAtom::Singleton {
                phase: R0Phase::E4,
                coefficient_id,
                term_class,
                source_a,
                source_b,
            } => {
                let recipe = recipe_for_coefficient(coordinate, *coefficient_id)
                    .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
                let (class, source_a, source_b) =
                    legacy_dedicated_operands(coordinate, *term_class, *source_a, *source_b)?;
                if class == 1 {
                    let basis = push_linear_basis_plans(&mut plans, &mut plan_ids, &recipe)?;
                    push_dedicated_instruction(
                        &mut linear_e4,
                        R0_DEDICATED_LINEAR_E4_WIDE,
                        basis,
                        source_a,
                        0,
                    );
                } else if matches!(class, 3 | R0_DEDICATED_PRODUCT_E4_E4) {
                    push_dedicated_instruction(
                        &mut e4_single,
                        class,
                        direct_id(&recipe, &mut plans, &mut plan_ids)?,
                        source_a,
                        source_b,
                    );
                } else {
                    return Err(R0PrototypeAbiError::Encoding(format!(
                        "unsupported sectioned E4 singleton class {class}"
                    )));
                }
            }
            GroupedAtom::Group {
                phase: R0Phase::Bf,
                core,
                members,
                ..
            } => {
                let mut ordered = members.iter().collect::<Vec<_>>();
                ordered.sort_by_key(|member| member.term_class != 2);
                let product_prefix = ordered
                    .iter()
                    .take_while(|member| member.term_class == 2)
                    .count();
                let linear_tail = ordered.len() - product_prefix;
                if product_prefix == 0 || linear_tail > 1 {
                    return Err(R0PrototypeAbiError::Encoding(format!(
                        "dedicated BF group requires one or more products and at most one linear tail; products={product_prefix} tail={linear_tail}"
                    )));
                }
                push_dedicated_instruction(
                    &mut bf,
                    R0_DEDICATED_GROUP_BF,
                    direct_id(core, &mut plans, &mut plan_ids)?,
                    checked_u16(ordered.len(), "dedicated BF group members")?,
                    checked_u16(product_prefix, "dedicated BF product prefix")?
                        | R0_DEDICATED_HAS_PRODUCT,
                );
                for (index, member) in ordered.iter().enumerate() {
                    let mut factor = immediate_id(member.immediate)?;
                    if index < product_prefix && (index + 1) % 4 == 0 && index + 1 < product_prefix
                    {
                        factor |= R0_DEDICATED_REDUCE_AFTER;
                    }
                    let (class, source_a, source_b) = legacy_dedicated_operands(
                        coordinate,
                        member.term_class,
                        member.source_a,
                        member.source_b,
                    )?;
                    push_dedicated_instruction(&mut bf, class, factor, source_a, source_b);
                }
            }
            GroupedAtom::Group {
                phase: R0Phase::E4,
                core,
                members,
                ..
            } => {
                if !matches!(members.len(), 2 | 3) {
                    return Err(R0PrototypeAbiError::Encoding(format!(
                        "dedicated E4 group has {} members; expected linear plus one or two products",
                        members.len()
                    )));
                }
                let linear = &members[0];
                if linear.term_class != 1 || linear.immediate != 1 || linear.source_b.is_some() {
                    return Err(R0PrototypeAbiError::Encoding(
                        "dedicated E4 group requires exactly one first-position +1 linear member"
                            .to_owned(),
                    ));
                }
                let (linear_class, linear_source, linear_source_b) = legacy_dedicated_operands(
                    coordinate,
                    linear.term_class,
                    linear.source_a,
                    linear.source_b,
                )?;
                if linear_class != 1 || linear_source_b != 0 {
                    return Err(R0PrototypeAbiError::Encoding(
                        "dedicated E4 linear member has an invalid source shape".to_owned(),
                    ));
                }
                let basis = push_linear_basis_plans(&mut plans, &mut plan_ids, core)?;
                push_dedicated_instruction(
                    &mut linear_e4,
                    R0_DEDICATED_LINEAR_E4_WIDE,
                    basis,
                    linear_source,
                    0,
                );

                let products = &members[1..];
                if products.len() == 1 {
                    let product = &products[0];
                    let (class, source_a, source_b) = legacy_dedicated_operands(
                        coordinate,
                        product.term_class,
                        product.source_a,
                        product.source_b,
                    )?;
                    if !matches!(product.immediate, 1 | 2_013_265_920) {
                        return Err(R0PrototypeAbiError::Encoding(format!(
                            "unsupported sectioned singleton factor {}",
                            product.immediate
                        )));
                    }
                    let coefficient = basis
                        | if product.immediate == 2_013_265_920 {
                            R0_DEDICATED_NEGATE_COEFFICIENT
                        } else {
                            0
                        };
                    if matches!(
                        class,
                        2 | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B
                            | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB
                    ) {
                        push_dedicated_instruction(&mut bf, class, coefficient, source_a, source_b);
                    } else if matches!(class, 3 | R0_DEDICATED_PRODUCT_E4_E4) {
                        push_dedicated_instruction(
                            &mut e4_single,
                            class,
                            coefficient,
                            source_a,
                            source_b,
                        );
                    } else {
                        return Err(R0PrototypeAbiError::Encoding(format!(
                            "unsupported sectioned E4 product class {class}"
                        )));
                    }
                } else {
                    push_dedicated_instruction(&mut e4_pair, R0_DEDICATED_GROUP_E4, basis, 0, 0);
                    let mut pair_class = None;
                    for product in products {
                        let (class, source_a, source_b) = legacy_dedicated_operands(
                            coordinate,
                            product.term_class,
                            product.source_a,
                            product.source_b,
                        )?;
                        if !matches!(class, 3 | R0_DEDICATED_PRODUCT_E4_E4) {
                            return Err(R0PrototypeAbiError::Encoding(format!(
                                "unsupported sectioned E4 pair class {class}"
                            )));
                        }
                        if let Some(expected) = pair_class {
                            if class != expected {
                                return Err(R0PrototypeAbiError::Encoding(format!(
                                    "heterogeneous E4 pair classes {expected} and {class}"
                                )));
                            }
                        } else {
                            pair_class = Some(class);
                        }
                        push_dedicated_instruction(
                            &mut e4_pair,
                            class,
                            immediate_id(product.immediate)?,
                            source_a,
                            source_b,
                        );
                    }
                }
            }
        }
    }

    let bf_end = bf.len() / 4;
    let linear_end = bf_end + linear_e4.len() / 4;
    let singleton_end = linear_end + e4_single.len() / 4;
    let pair_end = singleton_end + e4_pair.len() / 4;
    let mut words = bf;
    words.extend(linear_e4);
    words.extend(e4_single);
    words.extend(e4_pair);
    let mut sections = [0u32; R0_PROTOTYPE_COMMON_SECTION_WORDS];
    sections[0] = u32_section_end(bf_end, "dedicated BF section")?;
    sections[1] = u32_section_end(linear_end, "dedicated linear E4 section")?;
    sections[2] = u32_section_end(singleton_end, "dedicated singleton E4 section")?;
    sections[3] = u32_section_end(pair_end, "dedicated pair E4 section")?;
    let shape = legacy_derive_dedicated_shape(coordinate, program)?;
    sections[4] = u32::from(shape.bits());
    let immediates = grouped
        .immediates
        .iter()
        .map(|value| Bf::from_u32_unchecked(*value).as_u32_raw_repr_reduced())
        .collect();
    let sectioned = DedicatedSectionedProgram {
        words,
        source_slots: grouped.source_slots,
        immediates,
        sections,
        coefficient_plans: plans,
        shape,
    };
    validate_sectioned_coefficient_ids(&sectioned)?;
    Ok(sectioned)
}

fn flatten_dedicated_grouped(
    coordinate: &FrozenR0Coordinate,
    program: &GroupedSlotProgram,
) -> Result<FlatProgram, R0PrototypeAbiError> {
    let grouped = flatten_grouped(coordinate, &program.atoms, program.source_slots.clone())?;
    let one = recipe_for_coefficient(coordinate, 0)
        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
    let neg_one = recipe_for_coefficient(coordinate, 1)
        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
    let coefficient_ids = grouped
        .coefficient_recipes
        .iter()
        .enumerate()
        .map(|(index, recipe)| Ok((recipe_key(recipe)?, 2 + index as u16)))
        .collect::<Result<BTreeMap<_, _>, R0PrototypeAbiError>>()?;
    let coefficient_id = |recipe: &FrozenR0Recipe| -> Result<u16, R0PrototypeAbiError> {
        if *recipe == one {
            Ok(0)
        } else if *recipe == neg_one {
            Ok(1)
        } else {
            coefficient_ids
                .get(&recipe_key(recipe)?)
                .copied()
                .ok_or_else(|| R0PrototypeAbiError::Encoding("dedicated coefficient absent".into()))
        }
    };
    let immediate_ids = grouped
        .immediates
        .iter()
        .enumerate()
        .map(|(index, immediate)| (*immediate, 2 + index as u16))
        .collect::<BTreeMap<_, _>>();
    let immediate_id = |value: u32| -> Result<u16, R0PrototypeAbiError> {
        if value == 1 {
            Ok(0)
        } else if u64::from(value) == 2_013_265_920 {
            Ok(1)
        } else {
            immediate_ids
                .get(&value)
                .copied()
                .ok_or_else(|| R0PrototypeAbiError::Encoding("dedicated immediate absent".into()))
        }
    };
    let mut words = Vec::new();
    let mut bf_instructions = 0usize;
    for target_phase in [R0Phase::Bf, R0Phase::E4] {
        for atom in &program.atoms {
            match atom {
                GroupedAtom::Singleton {
                    phase,
                    coefficient_id: original,
                    term_class,
                    source_a,
                    source_b,
                } => {
                    if *phase != target_phase {
                        continue;
                    }
                    let recipe = recipe_for_coefficient(coordinate, *original)
                        .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
                    let (term_class, source_a, source_b) =
                        dedicated_operands(coordinate, *term_class, *source_a, *source_b)?;
                    push_dedicated_instruction(
                        &mut words,
                        term_class,
                        coefficient_id(&recipe)?,
                        source_a,
                        source_b,
                    );
                }
                GroupedAtom::Group {
                    phase,
                    core,
                    members,
                    ..
                } => {
                    if *phase != target_phase {
                        continue;
                    }
                    let mut ordered = members.iter().collect::<Vec<_>>();
                    if target_phase == R0Phase::Bf {
                        ordered.sort_by_key(|member| member.term_class != 2);
                    } else {
                        if ordered.len() == 3 {
                            let singleton = ordered.remove(0);
                            if singleton.term_class != 1
                                || singleton.immediate != 1
                                || singleton.source_b.is_some()
                            {
                                return Err(R0PrototypeAbiError::Encoding(
                                    "dedicated E4 arity-three group is not a linear +1 prefix followed by a pair"
                                        .to_owned(),
                                ));
                            }
                            let (term_class, source_a, source_b) = dedicated_operands(
                                coordinate,
                                singleton.term_class,
                                singleton.source_a,
                                singleton.source_b,
                            )?;
                            push_dedicated_instruction(
                                &mut words,
                                term_class,
                                coefficient_id(core)?,
                                source_a,
                                source_b,
                            );
                        }
                        if ordered.len() != 2 {
                            return Err(R0PrototypeAbiError::Encoding(format!(
                                "dedicated E4 group has {} members after singleton extraction; expected exactly two",
                                ordered.len()
                            )));
                        }
                    }
                    let chunk_size = ordered.len();
                    for chunk in ordered.chunks(chunk_size) {
                        let product_prefix = if target_phase == R0Phase::Bf {
                            chunk
                                .iter()
                                .take_while(|member| member.term_class == 2)
                                .count()
                        } else {
                            0
                        };
                        let linear_tail = chunk.len() - product_prefix;
                        if target_phase == R0Phase::Bf && (product_prefix == 0 || linear_tail > 1) {
                            return Err(R0PrototypeAbiError::Encoding(format!(
                                "dedicated BF group requires one or more products and at most one linear tail; products={product_prefix} tail={linear_tail}"
                            )));
                        }
                        let has_product = chunk.iter().any(|member| member.term_class >= 2);
                        push_dedicated_instruction(
                            &mut words,
                            if target_phase == R0Phase::Bf {
                                R0_DEDICATED_GROUP_BF
                            } else {
                                R0_DEDICATED_GROUP_E4
                            },
                            coefficient_id(core)?,
                            if target_phase == R0Phase::Bf {
                                checked_u16(chunk.len(), "dedicated group members")?
                            } else {
                                0
                            },
                            checked_u16(product_prefix, "dedicated product prefix")?
                                | if has_product {
                                    R0_DEDICATED_HAS_PRODUCT
                                } else {
                                    0
                                },
                        );
                        for (index, member) in chunk.iter().enumerate() {
                            let mut factor = immediate_id(member.immediate)?;
                            if target_phase == R0Phase::Bf
                                && index < product_prefix
                                && (index + 1) % 4 == 0
                                && index + 1 < product_prefix
                            {
                                factor |= R0_DEDICATED_REDUCE_AFTER;
                            }
                            let (term_class, source_a, source_b) = dedicated_operands(
                                coordinate,
                                member.term_class,
                                member.source_a,
                                member.source_b,
                            )?;
                            push_dedicated_instruction(
                                &mut words, term_class, factor, source_a, source_b,
                            );
                        }
                    }
                }
            }
        }
        if target_phase == R0Phase::Bf {
            bf_instructions = words.len() / 4;
        }
    }
    let instruction_count = words.len() / 4;
    let mut sections = [0u32; R0_PROTOTYPE_COMMON_SECTION_WORDS];
    sections[0] = u32::try_from(bf_instructions).map_err(|_| R0PrototypeAbiError::Capacity {
        resource: "dedicated BF instructions",
        required: bf_instructions,
        capacity: u32::MAX as usize,
    })?;
    sections[1] = u32::try_from(instruction_count).map_err(|_| R0PrototypeAbiError::Capacity {
        resource: "dedicated instructions",
        required: instruction_count,
        capacity: u32::MAX as usize,
    })?;
    // The dedicated decoder consumes the bank as already-reduced Montgomery
    // limbs.  Pay the canonical -> Montgomery conversion once while building
    // the by-value descriptor, never once per decoded group member on device.
    let immediates = grouped
        .immediates
        .iter()
        .map(|value| Bf::from_u32_unchecked(*value).as_u32_raw_repr_reduced())
        .collect();
    let banked_coefficient_count = grouped.coefficient_recipes.len();
    Ok(FlatProgram {
        words,
        source_slots: grouped.source_slots,
        immediates,
        sections,
        coefficient_recipes: grouped.coefficient_recipes,
        banked_coefficient_count,
    })
}

fn flatten_program(
    coordinate: &FrozenR0Coordinate,
    entry: &R0PrototypeProgramEntry,
) -> Result<FlatProgram, R0PrototypeAbiError> {
    let original_recipes = || coordinate.recipes.clone();
    Ok(match &entry.encoded {
        R0EncodedProgram::CurrentFixedSlot(program) => FlatProgram {
            words: program.program_words.clone(),
            source_slots: program.source_slots.clone(),
            immediates: Vec::new(),
            sections: [0; R0_PROTOTYPE_COMMON_SECTION_WORDS],
            coefficient_recipes: original_recipes(),
            banked_coefficient_count: coordinate.recipes.len(),
        },
        R0EncodedProgram::CompactR0Port(CompactR0Program {
            words,
            source_slots,
            ..
        }) => FlatProgram {
            words: words
                .iter()
                .flat_map(|word| [*word as u16, (*word >> 16) as u16])
                .collect(),
            source_slots: source_slots.clone(),
            immediates: Vec::new(),
            sections: [0; R0_PROTOTYPE_COMMON_SECTION_WORDS],
            coefficient_recipes: original_recipes(),
            banked_coefficient_count: coordinate.recipes.len(),
        },
        R0EncodedProgram::SplitFixedSlot(program) => {
            let mut flat = flatten_split(program);
            flat.coefficient_recipes = original_recipes();
            flat.banked_coefficient_count = flat.coefficient_recipes.len();
            flat
        }
        R0EncodedProgram::SplitFixedDirect(program) => {
            let mut flat = flatten_split_direct(program);
            flat.coefficient_recipes = original_recipes();
            flat.banked_coefficient_count = flat.coefficient_recipes.len();
            flat
        }
        R0EncodedProgram::HomogeneousSlot(HomogeneousSlotProgram {
            classes,
            order,
            source_slots,
        }) => {
            let mut flat = flatten_homogeneous(classes, order, source_slots.clone());
            flat.coefficient_recipes = original_recipes();
            flat.banked_coefficient_count = flat.coefficient_recipes.len();
            flat
        }
        R0EncodedProgram::HomogeneousDirect(HomogeneousDirectProgram { classes, order }) => {
            let mut flat = flatten_homogeneous(classes, order, Vec::new());
            flat.coefficient_recipes = original_recipes();
            flat.banked_coefficient_count = flat.coefficient_recipes.len();
            flat
        }
        R0EncodedProgram::GroupedSlot(program) => {
            flatten_grouped(coordinate, &program.atoms, program.source_slots.clone())?
        }
        R0EncodedProgram::GroupedDirect(program) => {
            flatten_grouped(coordinate, &program.atoms, Vec::new())?
        }
    })
}

fn sha256_bytes(bytes: &[u8]) -> Result<String, R0PrototypeAbiError> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| R0PrototypeAbiError::Hash(error.to_string()))?;
    child
        .stdin
        .take()
        .ok_or_else(|| R0PrototypeAbiError::Hash("sha256sum stdin absent".into()))?
        .write_all(bytes)
        .map_err(|error| R0PrototypeAbiError::Hash(error.to_string()))?;
    let output = child
        .wait_with_output()
        .map_err(|error| R0PrototypeAbiError::Hash(error.to_string()))?;
    if !output.status.success() {
        return Err(R0PrototypeAbiError::Hash(format!(
            "sha256sum exited {}",
            output.status
        )));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|error| R0PrototypeAbiError::Hash(error.to_string()))?;
    let hash = stdout
        .split_ascii_whitespace()
        .next()
        .ok_or_else(|| R0PrototypeAbiError::Hash("sha256sum output absent".into()))?;
    if hash.len() != 64 {
        return Err(R0PrototypeAbiError::Hash(
            "sha256sum output malformed".into(),
        ));
    }
    Ok(hash.to_owned())
}

fn hash_array(hash: &str) -> Result<[u8; 32], R0PrototypeAbiError> {
    let mut bytes = [0u8; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hash[index * 2..index * 2 + 2], 16)
            .map_err(|error| R0PrototypeAbiError::Hash(error.to_string()))?;
    }
    Ok(bytes)
}

fn common_desc(
    entry: &R0PrototypeProgramEntry,
    log_trace: u32,
) -> Result<R0PrototypeCommonDesc, R0PrototypeAbiError> {
    if !(3..=27).contains(&log_trace) {
        return Err(R0PrototypeAbiError::InvalidLogTrace(log_trace));
    }
    Ok(R0PrototypeCommonDesc {
        log_rows: log_trace - 3,
        record_count: entry.operations.len() as u32,
        bf_record_count: entry
            .operations
            .iter()
            .filter(|operation| operation.phase == crate::r0_prototype_encoding::R0Phase::Bf)
            .count() as u32,
        source_slot_count: entry.encoded.source_slots().map_or(0, <[u16]>::len) as u32,
        ..R0PrototypeCommonDesc::default()
    })
}

fn ordinary_desc<const P: usize, const S: usize, const I: usize>(
    common: R0PrototypeCommonDesc,
    coordinate: &FrozenR0Coordinate,
    flat: &FlatProgram,
    program_hash: &str,
    log_trace: u32,
) -> Result<R0PrototypeOrdinaryDesc<P, S, I>, R0PrototypeAbiError> {
    for (resource, required, capacity) in [
        ("prototype program", flat.words.len(), P),
        ("prototype source slots", flat.source_slots.len(), S),
        ("prototype immediates", flat.immediates.len(), I),
    ] {
        if required > capacity {
            return Err(R0PrototypeAbiError::Capacity {
                resource,
                required,
                capacity,
            });
        }
    }
    let mut program = [0u16; P];
    program[..flat.words.len()].copy_from_slice(&flat.words);
    let mut source_slots = [0u16; S];
    source_slots[..flat.source_slots.len()].copy_from_slice(&flat.source_slots);
    let mut immediates = [0u32; I];
    immediates[..flat.immediates.len()].copy_from_slice(&flat.immediates);
    let eq_sizes = crate::geometry::make_eq_sizes(log_trace)
        .map_err(|_| R0PrototypeAbiError::InvalidLogTrace(log_trace))?;
    Ok(R0PrototypeOrdinaryDesc {
        common,
        meta: R0PrototypeProgramMeta {
            program_words: flat.words.len() as u32,
            immediate_count: flat.immediates.len() as u32,
            window_count: coordinate.binding.windows.len() as u32,
            banked_coefficient_count: flat.banked_coefficient_count as u32,
            eq_sizes,
            sections: flat.sections,
            program_sha256: hash_array(program_hash)?,
        },
        program,
        source_slots,
        immediates,
    })
}

fn ordinary_tails_zero<const P: usize, const S: usize, const I: usize>(
    desc: &R0PrototypeOrdinaryDesc<P, S, I>,
) -> bool {
    desc.program[desc.meta.program_words as usize..]
        .iter()
        .all(|word| *word == 0)
        && desc.source_slots[desc.common.source_slot_count as usize..]
            .iter()
            .all(|word| *word == 0)
        && desc.immediates[desc.meta.immediate_count as usize..]
            .iter()
            .all(|word| *word == 0)
}

fn packed_tile_source(
    coordinate: &FrozenR0Coordinate,
    source: SemanticSourceKey,
) -> Result<u16, R0PrototypeAbiError> {
    let packed = *packed_source_slots(coordinate)
        .get(source.source as usize)
        .ok_or_else(|| R0PrototypeAbiError::Encoding("tile source is absent".into()))?;
    Ok(packed
        | if source.projection == SourceProjection::Delta {
            0x8000
        } else {
            0
        })
}

fn materialized_desc<const P: usize, const S: usize, const I: usize>(
    ordinary: R0PrototypeOrdinaryDesc<P, S, I>,
    coordinate: &FrozenR0Coordinate,
    plan: &R0SourceTilePlan,
    tile_hash: &str,
) -> Result<R0PrototypeMaterializedDesc<P, S, I>, R0PrototypeAbiError> {
    let tile_source_count = plan
        .tiles
        .iter()
        .map(|tile| tile.bf_sources.len() + tile.e4_sources.len())
        .sum::<usize>();
    let tile_record_count = plan
        .tiles
        .iter()
        .map(|tile| tile.record_count as usize)
        .sum::<usize>();
    for (resource, required, capacity) in [
        (
            "prototype tiles",
            plan.tiles.len(),
            R0_PROTOTYPE_TILE_CAPACITY,
        ),
        (
            "prototype tile sources",
            tile_source_count,
            R0_PROTOTYPE_TILE_SOURCE_CAPACITY,
        ),
        (
            "prototype tile records",
            tile_record_count,
            R0_PROTOTYPE_TILE_RECORD_CAPACITY,
        ),
    ] {
        if required > capacity {
            return Err(R0PrototypeAbiError::Capacity {
                resource,
                required,
                capacity,
            });
        }
    }
    let mut tiles = [R0PrototypeTileHeader::default(); R0_PROTOTYPE_TILE_CAPACITY];
    let mut tile_sources = [0u16; R0_PROTOTYPE_TILE_SOURCE_CAPACITY];
    let mut record_local_sources = [[0u8; 2]; R0_PROTOTYPE_TILE_RECORD_CAPACITY];
    let mut source_cursor = 0usize;
    let mut record_cursor = 0usize;
    for (tile_index, tile) in plan.tiles.iter().enumerate() {
        let bf = tile.bf_sources.len();
        let e4 = tile.e4_sources.len();
        if bf > u8::MAX as usize || e4 > u8::MAX as usize {
            return Err(R0PrototypeAbiError::Capacity {
                resource: "prototype tile typed sources",
                required: bf.max(e4),
                capacity: u8::MAX as usize,
            });
        }
        tiles[tile_index] = R0PrototypeTileHeader {
            first_record: checked_u16(tile.first_record as usize, "tile first record")?,
            record_count: checked_u16(tile.record_count as usize, "tile record count")?,
            source_offset: checked_u16(source_cursor, "tile source offset")?,
            source_counts: (bf as u16) | ((e4 as u16) << 8),
        };
        for source in tile.bf_sources.iter().chain(&tile.e4_sources) {
            tile_sources[source_cursor] = packed_tile_source(coordinate, *source)?;
            source_cursor += 1;
        }
        for local in &tile.record_local_sources {
            record_local_sources[record_cursor] = [
                if local[0] == R0_TILE_SOURCE_NONE {
                    u8::MAX
                } else {
                    u8::try_from(local[0]).map_err(|_| R0PrototypeAbiError::Capacity {
                        resource: "tile local source",
                        required: local[0] as usize,
                        capacity: u8::MAX as usize,
                    })?
                },
                if local[1] == R0_TILE_SOURCE_NONE {
                    u8::MAX
                } else {
                    u8::try_from(local[1]).map_err(|_| R0PrototypeAbiError::Capacity {
                        resource: "tile local source",
                        required: local[1] as usize,
                        capacity: u8::MAX as usize,
                    })?
                },
            ];
            record_cursor += 1;
        }
    }
    Ok(R0PrototypeMaterializedDesc {
        ordinary,
        tile_meta: R0PrototypeTileMeta {
            tile_count: plan.tiles.len() as u32,
            tile_source_count: tile_source_count as u32,
            tile_record_count: tile_record_count as u32,
            capacity: plan.capacity.identities() as u32,
            max_dynamic_shared_bytes: plan.max_dynamic_shared_bytes,
            reserved: [0; 3],
            tile_sha256: hash_array(tile_hash)?,
        },
        tiles,
        tile_sources,
        record_local_sources,
    })
}

fn materialized_tails_zero<const P: usize, const S: usize, const I: usize>(
    desc: &R0PrototypeMaterializedDesc<P, S, I>,
) -> bool {
    ordinary_tails_zero(&desc.ordinary)
        && desc.tiles[desc.tile_meta.tile_count as usize..]
            .iter()
            .all(|tile| *tile == R0PrototypeTileHeader::default())
        && desc.tile_sources[desc.tile_meta.tile_source_count as usize..]
            .iter()
            .all(|source| *source == 0)
        && desc.record_local_sources[desc.tile_meta.tile_record_count as usize..]
            .iter()
            .all(|local| *local == [0, 0])
}

fn ordinary_payload(
    encoding: R0ProgramEncoding,
    common: R0PrototypeCommonDesc,
    coordinate: &FrozenR0Coordinate,
    flat: &FlatProgram,
    program_hash: &str,
    log_trace: u32,
) -> Result<R0PrototypePayload, R0PrototypeAbiError> {
    Ok(match encoding {
        R0ProgramEncoding::CurrentFixedSlot => {
            let windows = vec![R0WindowAddr::default(); coordinate.binding.windows.len()];
            let desc = R0VmDesc::from_coordinate(
                coordinate,
                &windows,
                log_trace,
                core::ptr::null(),
                core::ptr::null_mut(),
                crate::geometry::make_eq_sizes(log_trace)
                    .map_err(|_| R0PrototypeAbiError::InvalidLogTrace(log_trace))?,
                coordinate.recipes.len(),
            )
            .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
            R0PrototypePayload::CurrentOrdinary(desc)
        }
        R0ProgramEncoding::CompactR0Port => R0PrototypePayload::CompactOrdinary(ordinary_desc(
            common,
            coordinate,
            flat,
            program_hash,
            log_trace,
        )?),
        R0ProgramEncoding::SplitFixedSlot => R0PrototypePayload::SplitSlotOrdinary(ordinary_desc(
            common,
            coordinate,
            flat,
            program_hash,
            log_trace,
        )?),
        R0ProgramEncoding::SplitFixedDirect => R0PrototypePayload::SplitDirectOrdinary(
            ordinary_desc(common, coordinate, flat, program_hash, log_trace)?,
        ),
        R0ProgramEncoding::HomogeneousSlot => R0PrototypePayload::HomogeneousSlotOrdinary(
            ordinary_desc(common, coordinate, flat, program_hash, log_trace)?,
        ),
        R0ProgramEncoding::HomogeneousDirect => R0PrototypePayload::HomogeneousDirectOrdinary(
            ordinary_desc(common, coordinate, flat, program_hash, log_trace)?,
        ),
        R0ProgramEncoding::GroupedSlot => R0PrototypePayload::GroupedSlotOrdinary(ordinary_desc(
            common,
            coordinate,
            flat,
            program_hash,
            log_trace,
        )?),
        R0ProgramEncoding::GroupedDirect => R0PrototypePayload::GroupedDirectOrdinary(
            ordinary_desc(common, coordinate, flat, program_hash, log_trace)?,
        ),
    })
}

fn materialized_payload(
    encoding: R0ProgramEncoding,
    common: R0PrototypeCommonDesc,
    coordinate: &FrozenR0Coordinate,
    flat: &FlatProgram,
    plan: &R0SourceTilePlan,
    program_hash: &str,
    tile_hash: &str,
    log_trace: u32,
) -> Result<R0PrototypePayload, R0PrototypeAbiError> {
    macro_rules! materialized {
        ($variant:ident) => {{
            let ordinary = ordinary_desc(common, coordinate, flat, program_hash, log_trace)?;
            R0PrototypePayload::$variant(materialized_desc(ordinary, coordinate, plan, tile_hash)?)
        }};
    }
    Ok(match encoding {
        R0ProgramEncoding::CurrentFixedSlot => materialized!(CurrentMaterialized),
        R0ProgramEncoding::CompactR0Port => materialized!(CompactMaterialized),
        R0ProgramEncoding::SplitFixedSlot => materialized!(SplitSlotMaterialized),
        R0ProgramEncoding::SplitFixedDirect => materialized!(SplitDirectMaterialized),
        R0ProgramEncoding::HomogeneousSlot => materialized!(HomogeneousSlotMaterialized),
        R0ProgramEncoding::HomogeneousDirect => materialized!(HomogeneousDirectMaterialized),
        R0ProgramEncoding::GroupedSlot => materialized!(GroupedSlotMaterialized),
        R0ProgramEncoding::GroupedDirect => materialized!(GroupedDirectMaterialized),
    })
}

fn payload_size(payload: &R0PrototypePayload) -> usize {
    match payload {
        R0PrototypePayload::CurrentOrdinary(_) => size_of::<R0VmDesc>(),
        R0PrototypePayload::CompactOrdinary(_) => size_of::<R0CompactOrdinaryDesc>(),
        R0PrototypePayload::SplitSlotOrdinary(_) => size_of::<R0SplitSlotOrdinaryDesc>(),
        R0PrototypePayload::SplitDirectOrdinary(_) => size_of::<R0SplitDirectOrdinaryDesc>(),
        R0PrototypePayload::HomogeneousSlotOrdinary(_) => {
            size_of::<R0HomogeneousSlotOrdinaryDesc>()
        }
        R0PrototypePayload::HomogeneousDirectOrdinary(_) => {
            size_of::<R0HomogeneousDirectOrdinaryDesc>()
        }
        R0PrototypePayload::GroupedSlotOrdinary(_) => size_of::<R0GroupedSlotOrdinaryDesc>(),
        R0PrototypePayload::GroupedDirectOrdinary(_) => size_of::<R0GroupedDirectOrdinaryDesc>(),
        R0PrototypePayload::CurrentMaterialized(_) => size_of::<R0CurrentMaterializedDesc>(),
        R0PrototypePayload::CompactMaterialized(_) => size_of::<R0CompactMaterializedDesc>(),
        R0PrototypePayload::SplitSlotMaterialized(_) => size_of::<R0SplitSlotMaterializedDesc>(),
        R0PrototypePayload::SplitDirectMaterialized(_) => {
            size_of::<R0SplitDirectMaterializedDesc>()
        }
        R0PrototypePayload::HomogeneousSlotMaterialized(_) => {
            size_of::<R0HomogeneousSlotMaterializedDesc>()
        }
        R0PrototypePayload::HomogeneousDirectMaterialized(_) => {
            size_of::<R0HomogeneousDirectMaterializedDesc>()
        }
        R0PrototypePayload::GroupedSlotMaterialized(_) => {
            size_of::<R0GroupedSlotMaterializedDesc>()
        }
        R0PrototypePayload::GroupedDirectMaterialized(_) => {
            size_of::<R0GroupedDirectMaterializedDesc>()
        }
    }
}

pub fn build_dedicated_grouped_descriptor(
    coordinate: &FrozenR0Coordinate,
    programs: &R0PrototypeProgramSet,
    log_trace: u32,
) -> Result<PreparedPrototypeDescriptor, R0PrototypeAbiError> {
    let entry = programs.get(R0ProgramEncoding::GroupedSlot).ok_or(
        R0PrototypeAbiError::MissingEncoding(R0ProgramEncoding::GroupedSlot),
    )?;
    let R0EncodedProgram::GroupedSlot(program) = &entry.encoded else {
        return Err(R0PrototypeAbiError::Encoding(
            "grouped-slot entry has the wrong representation".into(),
        ));
    };
    let flat = flatten_dedicated_grouped(coordinate, program)?;
    let program_bytes = serde_json::to_vec(&(
        "dedicated_grouped_u64_u96_v1",
        &flat.words,
        &flat.source_slots,
        &flat.immediates,
        &flat.coefficient_recipes,
        &flat.sections,
    ))
    .map_err(|error| R0PrototypeAbiError::Encoding(error.to_string()))?;
    let program_sha256 = sha256_bytes(&program_bytes)?;
    let common = common_desc(entry, log_trace)?;
    let payload = ordinary_payload(
        R0ProgramEncoding::GroupedSlot,
        common,
        coordinate,
        &flat,
        &program_sha256,
        log_trace,
    )?;
    let size = payload_size(&payload);
    if size > KERNEL_ARGUMENT_CEILING_BYTES {
        return Err(R0PrototypeAbiError::Capacity {
            resource: "dedicated grouped descriptor bytes",
            required: size,
            capacity: KERNEL_ARGUMENT_CEILING_BYTES,
        });
    }
    Ok(PreparedPrototypeDescriptor {
        encoding: R0ProgramEncoding::GroupedSlot,
        capacity: None,
        payload,
        payload_size: size,
        program_sha256,
        tile_sha256: None,
        coefficient_recipes: flat.coefficient_recipes,
        dedicated_coefficient_plans: Vec::new(),
    })
}

pub fn build_dedicated_sectioned_descriptor(
    coordinate: &FrozenR0Coordinate,
    programs: &R0PrototypeProgramSet,
    log_trace: u32,
) -> Result<PreparedPrototypeDescriptor, R0PrototypeAbiError> {
    let entry = programs.get(R0ProgramEncoding::GroupedSlot).ok_or(
        R0PrototypeAbiError::MissingEncoding(R0ProgramEncoding::GroupedSlot),
    )?;
    let R0EncodedProgram::GroupedSlot(program) = &entry.encoded else {
        return Err(R0PrototypeAbiError::Encoding(
            "grouped-slot entry has the wrong representation".into(),
        ));
    };
    let sectioned = lower_dedicated_sections(coordinate, program)?;
    let program_bytes = serde_json::to_vec(&(
        "dedicated_sectioned_u64_u96_v1",
        &sectioned.words,
        &sectioned.source_slots,
        &sectioned.immediates,
        &sectioned.coefficient_plans,
        &sectioned.sections,
        sectioned.shape,
    ))
    .map_err(|error| R0PrototypeAbiError::Encoding(error.to_string()))?;
    let program_sha256 = sha256_bytes(&program_bytes)?;
    let flat = FlatProgram {
        words: sectioned.words,
        source_slots: sectioned.source_slots,
        immediates: sectioned.immediates,
        sections: sectioned.sections,
        coefficient_recipes: Vec::new(),
        banked_coefficient_count: sectioned.coefficient_plans.len(),
    };
    let common = common_desc(entry, log_trace)?;
    let payload = ordinary_payload(
        R0ProgramEncoding::GroupedSlot,
        common,
        coordinate,
        &flat,
        &program_sha256,
        log_trace,
    )?;
    let size = payload_size(&payload);
    if size > KERNEL_ARGUMENT_CEILING_BYTES {
        return Err(R0PrototypeAbiError::Capacity {
            resource: "dedicated sectioned descriptor bytes",
            required: size,
            capacity: KERNEL_ARGUMENT_CEILING_BYTES,
        });
    }
    Ok(PreparedPrototypeDescriptor {
        encoding: R0ProgramEncoding::GroupedSlot,
        capacity: None,
        payload,
        payload_size: size,
        program_sha256,
        tile_sha256: None,
        coefficient_recipes: Vec::new(),
        dedicated_coefficient_plans: sectioned.coefficient_plans,
    })
}

pub fn build_prototype_descriptors(
    coordinate: &FrozenR0Coordinate,
    programs: &R0PrototypeProgramSet,
    log_trace: u32,
) -> Result<Vec<PreparedPrototypeDescriptor>, R0PrototypeAbiError> {
    if programs.entries.len() != R0ProgramEncoding::ALL.len() {
        return Err(R0PrototypeAbiError::Capacity {
            resource: "prototype program entries",
            required: programs.entries.len(),
            capacity: R0ProgramEncoding::ALL.len(),
        });
    }
    let mut seen = BTreeMap::new();
    let mut prepared = Vec::with_capacity(32);
    let mut inputs = Vec::with_capacity(8);
    for encoding in R0ProgramEncoding::ALL {
        let entry = programs
            .get(encoding)
            .ok_or(R0PrototypeAbiError::MissingEncoding(encoding))?;
        if seen.insert(encoding, ()).is_some() {
            return Err(R0PrototypeAbiError::DuplicateEncoding(encoding));
        }
        let flat = flatten_program(coordinate, entry)?;
        let program_bytes = serde_json::to_vec(&entry.encoded)
            .map_err(|error| R0PrototypeAbiError::Encoding(error.to_string()))?;
        let program_sha256 = sha256_bytes(&program_bytes)?;
        let common = common_desc(entry, log_trace)?;
        let payload = ordinary_payload(
            encoding,
            common,
            coordinate,
            &flat,
            &program_sha256,
            log_trace,
        )?;
        let size = payload_size(&payload);
        if size > KERNEL_ARGUMENT_CEILING_BYTES {
            return Err(R0PrototypeAbiError::Capacity {
                resource: "ordinary descriptor bytes",
                required: size,
                capacity: KERNEL_ARGUMENT_CEILING_BYTES,
            });
        }
        prepared.push(PreparedPrototypeDescriptor {
            encoding,
            capacity: None,
            payload,
            payload_size: size,
            program_sha256: program_sha256.clone(),
            tile_sha256: None,
            coefficient_recipes: flat.coefficient_recipes.clone(),
            dedicated_coefficient_plans: Vec::new(),
        });
        inputs.push((encoding, entry, flat, common, program_sha256));
    }
    for (encoding, entry, flat, common, program_sha256) in inputs {
        let current_wire_operations;
        let materialized_operations =
            if let R0EncodedProgram::CurrentFixedSlot(program) = &entry.encoded {
                current_wire_operations = decode_current_fixed_wire_order(coordinate, program)
                    .map_err(|error| R0PrototypeAbiError::Encoding(format!("{error:?}")))?;
                current_wire_operations.as_slice()
            } else {
                entry.operations.as_slice()
            };
        for capacity in R0TileCapacity::ALL {
            let plan = plan_r0_source_tiles(materialized_operations, capacity)
                .map_err(|error| R0PrototypeAbiError::Tile(format!("{error:?}")))?;
            let tile_bytes = serde_json::to_vec(&plan)
                .map_err(|error| R0PrototypeAbiError::Tile(error.to_string()))?;
            let tile_sha256 = sha256_bytes(&tile_bytes)?;
            let payload = materialized_payload(
                encoding,
                common,
                coordinate,
                &flat,
                &plan,
                &program_sha256,
                &tile_sha256,
                log_trace,
            )?;
            let size = payload_size(&payload);
            if size > KERNEL_ARGUMENT_CEILING_BYTES {
                return Err(R0PrototypeAbiError::Capacity {
                    resource: "materialized descriptor bytes",
                    required: size,
                    capacity: KERNEL_ARGUMENT_CEILING_BYTES,
                });
            }
            prepared.push(PreparedPrototypeDescriptor {
                encoding,
                capacity: Some(capacity),
                payload,
                payload_size: size,
                program_sha256: program_sha256.clone(),
                tile_sha256: Some(tile_sha256),
                coefficient_recipes: flat.coefficient_recipes.clone(),
                dedicated_coefficient_plans: Vec::new(),
            });
        }
    }
    Ok(prepared)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeDescriptorLayout {
    pub name: String,
    pub size: usize,
    pub align: usize,
    pub common_offset: usize,
    pub program_offset: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeAbiLayout {
    pub common_size: usize,
    pub common_align: usize,
    pub common_window_bases: usize,
    pub common_eq_low: usize,
    pub common_partials: usize,
    pub common_log_rows: usize,
    pub common_record_count: usize,
    pub common_bf_record_count: usize,
    pub common_source_slot_count: usize,
    pub descriptors: Vec<R0PrototypeDescriptorLayout>,
}

fn ordinary_layout<const P: usize, const S: usize, const I: usize>(
    name: &str,
) -> R0PrototypeDescriptorLayout {
    R0PrototypeDescriptorLayout {
        name: name.to_owned(),
        size: size_of::<R0PrototypeOrdinaryDesc<P, S, I>>(),
        align: align_of::<R0PrototypeOrdinaryDesc<P, S, I>>(),
        common_offset: offset_of!(R0PrototypeOrdinaryDesc<P, S, I>, common),
        program_offset: offset_of!(R0PrototypeOrdinaryDesc<P, S, I>, program),
    }
}

fn materialized_layout<const P: usize, const S: usize, const I: usize>(
    name: &str,
) -> R0PrototypeDescriptorLayout {
    R0PrototypeDescriptorLayout {
        name: name.to_owned(),
        size: size_of::<R0PrototypeMaterializedDesc<P, S, I>>(),
        align: align_of::<R0PrototypeMaterializedDesc<P, S, I>>(),
        common_offset: offset_of!(R0PrototypeMaterializedDesc<P, S, I>, ordinary),
        program_offset: offset_of!(R0PrototypeMaterializedDesc<P, S, I>, ordinary)
            + offset_of!(R0PrototypeOrdinaryDesc<P, S, I>, program),
    }
}

impl R0PrototypeAbiLayout {
    pub fn rust() -> Self {
        let descriptors = vec![
            ordinary_layout::<R0_COMPACT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>(
                "compact_ordinary",
            ),
            ordinary_layout::<R0_SPLIT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>(
                "split_slot_ordinary",
            ),
            ordinary_layout::<R0_SPLIT_PROGRAM_CAPACITY, 0, 0>("split_direct_ordinary"),
            ordinary_layout::<R0_HOMOGENEOUS_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>(
                "homogeneous_slot_ordinary",
            ),
            ordinary_layout::<R0_HOMOGENEOUS_PROGRAM_CAPACITY, 0, 0>("homogeneous_direct_ordinary"),
            ordinary_layout::<
                R0_GROUPED_PROGRAM_CAPACITY,
                R0_PROTOTYPE_SOURCE_SLOT_CAPACITY,
                R0_PROTOTYPE_IMMEDIATE_CAPACITY,
            >("grouped_slot_ordinary"),
            ordinary_layout::<R0_GROUPED_PROGRAM_CAPACITY, 0, R0_PROTOTYPE_IMMEDIATE_CAPACITY>(
                "grouped_direct_ordinary",
            ),
            materialized_layout::<R0_CURRENT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>(
                "current_materialized",
            ),
            materialized_layout::<R0_COMPACT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>(
                "compact_materialized",
            ),
            materialized_layout::<R0_SPLIT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY, 0>(
                "split_slot_materialized",
            ),
            materialized_layout::<R0_SPLIT_PROGRAM_CAPACITY, 0, 0>("split_direct_materialized"),
            materialized_layout::<
                R0_HOMOGENEOUS_PROGRAM_CAPACITY,
                R0_PROTOTYPE_SOURCE_SLOT_CAPACITY,
                0,
            >("homogeneous_slot_materialized"),
            materialized_layout::<R0_HOMOGENEOUS_PROGRAM_CAPACITY, 0, 0>(
                "homogeneous_direct_materialized",
            ),
            materialized_layout::<
                R0_GROUPED_PROGRAM_CAPACITY,
                R0_PROTOTYPE_SOURCE_SLOT_CAPACITY,
                R0_PROTOTYPE_IMMEDIATE_CAPACITY,
            >("grouped_slot_materialized"),
            materialized_layout::<R0_GROUPED_PROGRAM_CAPACITY, 0, R0_PROTOTYPE_IMMEDIATE_CAPACITY>(
                "grouped_direct_materialized",
            ),
        ];
        Self {
            common_size: size_of::<R0PrototypeCommonDesc>(),
            common_align: align_of::<R0PrototypeCommonDesc>(),
            common_window_bases: offset_of!(R0PrototypeCommonDesc, window_bases),
            common_eq_low: offset_of!(R0PrototypeCommonDesc, eq_low),
            common_partials: offset_of!(R0PrototypeCommonDesc, partials),
            common_log_rows: offset_of!(R0PrototypeCommonDesc, log_rows),
            common_record_count: offset_of!(R0PrototypeCommonDesc, record_count),
            common_bf_record_count: offset_of!(R0PrototypeCommonDesc, bf_record_count),
            common_source_slot_count: offset_of!(R0PrototypeCommonDesc, source_slot_count),
            descriptors,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
struct R0PrototypeDescriptorLayoutRaw {
    size: u64,
    align: u64,
    common_offset: u64,
    program_offset: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
struct R0PrototypeAbiLayoutRaw {
    common_size: u64,
    common_align: u64,
    common_window_bases: u64,
    common_eq_low: u64,
    common_partials: u64,
    common_log_rows: u64,
    common_record_count: u64,
    common_bf_record_count: u64,
    common_source_slot_count: u64,
    descriptor_count: u64,
    descriptors: [R0PrototypeDescriptorLayoutRaw; 15],
}

#[cfg(not(no_cuda))]
unsafe extern "C" {
    fn ab_gkr_windowed_r0_prototype_abi_probe(layout: *mut R0PrototypeAbiLayoutRaw);
}

pub fn native_r0_prototype_abi_layout() -> Result<R0PrototypeAbiLayout, R0PrototypeAbiError> {
    #[cfg(not(no_cuda))]
    {
        let mut raw = R0PrototypeAbiLayoutRaw::default();
        unsafe { ab_gkr_windowed_r0_prototype_abi_probe(&mut raw) };
        let names = R0PrototypeAbiLayout::rust()
            .descriptors
            .into_iter()
            .map(|row| row.name)
            .collect::<Vec<_>>();
        if raw.descriptor_count as usize != names.len() {
            return Err(R0PrototypeAbiError::NativeProbe(
                raw.descriptor_count as i32,
            ));
        }
        Ok(R0PrototypeAbiLayout {
            common_size: raw.common_size as usize,
            common_align: raw.common_align as usize,
            common_window_bases: raw.common_window_bases as usize,
            common_eq_low: raw.common_eq_low as usize,
            common_partials: raw.common_partials as usize,
            common_log_rows: raw.common_log_rows as usize,
            common_record_count: raw.common_record_count as usize,
            common_bf_record_count: raw.common_bf_record_count as usize,
            common_source_slot_count: raw.common_source_slot_count as usize,
            descriptors: names
                .into_iter()
                .zip(raw.descriptors)
                .map(|(name, row)| R0PrototypeDescriptorLayout {
                    name,
                    size: row.size as usize,
                    align: row.align as usize,
                    common_offset: row.common_offset as usize,
                    program_offset: row.program_offset as usize,
                })
                .collect(),
        })
    }
    #[cfg(no_cuda)]
    {
        Err(R0PrototypeAbiError::NativeProbe(-1))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use field::Field;
    use field::PrimeField;
    use gkr_eval_ir::Bf;
    use gpu_gkr_compiler::backward::analyze_coeff_grouping;

    use crate::accumulator_schedule::build_schedule_views;
    use crate::census::compile_corpus;
    use crate::r0_artifact::{decode_r0_bundle, FrozenR0Product, FrozenR0Recipe, R0_CORPUS_BYTES};
    use crate::r0_prototype_encoding::{
        build_r0_prototype_program_set, GroupedAtom, GroupedMember, GroupedSlotProgram,
        R0EncodedProgram, R0Phase, StoredSource,
    };
    use crate::r0_prototype_manifest::{R0DedicatedShape, R0ProgramEncoding};

    use super::{
        build_dedicated_grouped_descriptor, build_prototype_descriptors, dedicated_operands,
        native_r0_prototype_abi_layout, R0PrototypeAbiLayout, R0PrototypeCommonDesc,
        R0PrototypePayload,
    };

    #[test]
    fn cpu_dedicated_grouped_stream_rejects_direct_source_words() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = &bundle.coordinates[0];
        let error = dedicated_operands(coordinate, 0, StoredSource::Direct(7), None).unwrap_err();
        assert!(format!("{error:?}").contains("slot source"));
    }

    #[test]
    fn cpu_dedicated_grouped_wire_specializes_uncached_procedural_sources() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let (coordinate, procedural_slot, procedural_kind, ordinary_slot) = bundle
            .coordinates
            .iter()
            .find_map(|coordinate| {
                let procedural = coordinate
                    .binding
                    .source_slots
                    .iter()
                    .enumerate()
                    .find_map(|(slot, source)| {
                        coordinate.binding.windows[usize::from(source.window)]
                            .procedural_kind()
                            .map(|kind| (slot as u16, u16::from(kind)))
                    })?;
                let ordinary = coordinate
                    .binding
                    .source_slots
                    .iter()
                    .enumerate()
                    .find(|(slot, source)| {
                        coordinate.binding.windows[usize::from(source.window)]
                            .procedural_kind()
                            .is_none()
                            && ((u16::from(source.window) << 7) | source.column) != *slot as u16
                    })?
                    .0 as u16;
                Some((coordinate, procedural.0, procedural.1, ordinary))
            })
            .expect("R0 corpus has both procedural and ordinary BF sources");
        let ordinary_source = &coordinate.binding.source_slots[usize::from(ordinary_slot)];
        let ordinary_packed = (u16::from(ordinary_source.window) << 7) | ordinary_source.column;

        assert_eq!(
            dedicated_operands(coordinate, 0, StoredSource::Slot(procedural_slot), None).unwrap(),
            (4, procedural_kind, 0)
        );
        assert_eq!(
            dedicated_operands(
                coordinate,
                2,
                StoredSource::Slot(procedural_slot),
                Some(StoredSource::Slot(ordinary_slot)),
            )
            .unwrap(),
            (8, ordinary_packed, procedural_kind)
        );
        assert_eq!(
            dedicated_operands(
                coordinate,
                2,
                StoredSource::Slot(ordinary_slot),
                Some(StoredSource::Slot(procedural_slot)),
            )
            .unwrap(),
            (8, ordinary_packed, procedural_kind)
        );
    }

    #[test]
    fn cpu_all_r0_coordinates_have_checked_sectioned_shapes() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let frozen = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut coordinates = 0usize;
        let mut linear_group_members = 0usize;
        let mut linear_singletons = 0usize;
        let mut migrated_bf_products = 0usize;
        let mut e4_single_products = 0usize;
        let mut e4_product_pairs = 0usize;
        let mut maximum_coefficient_plans = 0usize;
        let mut maximum_coefficient_plan_row = None;
        let mut maximum_descriptor_coefficient_count = 0usize;
        let mut distinct_shapes = std::collections::BTreeSet::new();
        let mut malformed_linear_prefix = None;
        let mut unsupported_product_class = None;
        let mut heterogeneous_pair = None;
        let mut invalid_linear_bank_span = None;

        for layer in &corpus.layers {
            let coordinate = frozen[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let programs = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .unwrap();
            let R0EncodedProgram::GroupedSlot(grouped) = &programs
                .get(R0ProgramEncoding::GroupedSlot)
                .expect("grouped-slot program")
                .encoded
            else {
                unreachable!()
            };

            let shape = super::derive_dedicated_shape(coordinate, grouped).unwrap();
            assert_ne!(shape, R0DedicatedShape::EMPTY);
            distinct_shapes.insert(shape.bits());
            let sectioned = super::lower_dedicated_sections(coordinate, grouped).unwrap();
            assert!(sectioned.sections[..4]
                .windows(2)
                .all(|pair| pair[0] <= pair[1]));
            assert_eq!(sectioned.sections[3] as usize * 4, sectioned.words.len());
            let descriptor =
                super::build_dedicated_sectioned_descriptor(coordinate, &programs, 3).unwrap();
            let R0PrototypePayload::GroupedSlotOrdinary(descriptor) = descriptor.payload else {
                panic!("sectioned descriptor used the wrong payload")
            };
            assert_eq!(
                descriptor.meta.banked_coefficient_count as usize,
                sectioned.coefficient_plans.len(),
                "sectioned descriptor coefficient-bank count drifted"
            );
            maximum_descriptor_coefficient_count = maximum_descriptor_coefficient_count
                .max(descriptor.meta.banked_coefficient_count as usize);
            if invalid_linear_bank_span.is_none() && sectioned.sections[0] < sectioned.sections[1] {
                let mut malformed = sectioned.clone();
                let first_linear_factor = 4 * malformed.sections[0] as usize + 1;
                malformed.words[first_linear_factor] =
                    u16::try_from(malformed.coefficient_plans.len()).unwrap();
                invalid_linear_bank_span = Some(malformed);
            }
            if sectioned.coefficient_plans.len() > maximum_coefficient_plans {
                maximum_coefficient_plans = sectioned.coefficient_plans.len();
                maximum_coefficient_plan_row = Some((
                    coordinate.circuit.clone(),
                    coordinate.layer,
                    sectioned
                        .coefficient_plans
                        .iter()
                        .filter(|plan| matches!(plan, super::DedicatedCoefficientPlan::Direct(_)))
                        .count(),
                    sectioned
                        .coefficient_plans
                        .iter()
                        .filter(|plan| {
                            matches!(plan, super::DedicatedCoefficientPlan::Scaled { .. })
                        })
                        .count(),
                    sectioned
                        .coefficient_plans
                        .iter()
                        .filter(|plan| {
                            matches!(plan, super::DedicatedCoefficientPlan::LinearBasis { .. })
                        })
                        .count(),
                    {
                        let basis_zero = sectioned
                            .coefficient_plans
                            .iter()
                            .filter_map(|plan| match plan {
                                super::DedicatedCoefficientPlan::LinearBasis {
                                    recipe,
                                    limb: 0,
                                } => Some(super::recipe_key(recipe).unwrap()),
                                _ => None,
                            })
                            .collect::<std::collections::BTreeSet<_>>();
                        sectioned
                            .coefficient_plans
                            .iter()
                            .filter(|plan| match plan {
                                super::DedicatedCoefficientPlan::Direct(recipe) => {
                                    basis_zero.contains(&super::recipe_key(recipe).unwrap())
                                }
                                _ => false,
                            })
                            .count()
                    },
                ));
            }
            coordinates += 1;

            let mut coordinate_pair_classes = std::collections::BTreeSet::new();
            for atom in &grouped.atoms {
                match atom {
                    GroupedAtom::Singleton {
                        phase: R0Phase::E4,
                        term_class: 1,
                        source_b: None,
                        ..
                    } => linear_singletons += 1,
                    GroupedAtom::Group {
                        phase: R0Phase::E4,
                        members,
                        ..
                    } => {
                        assert!(matches!(members.len(), 2 | 3));
                        let linear = &members[0];
                        assert_eq!(linear.term_class, 1);
                        assert_eq!(linear.immediate, 1);
                        assert!(linear.source_b.is_none());
                        linear_group_members += 1;
                        let products = &members[1..];
                        match products.len() {
                            1 => {
                                let (class, _, _) = super::dedicated_operands(
                                    coordinate,
                                    products[0].term_class,
                                    products[0].source_a,
                                    products[0].source_b,
                                )
                                .unwrap();
                                if matches!(class, 2 | 8 | 9) {
                                    migrated_bf_products += 1;
                                } else {
                                    assert!(matches!(class, 3 | 5));
                                    e4_single_products += 1;
                                }
                            }
                            2 => {
                                let mut pair_classes = Vec::with_capacity(2);
                                for product in products {
                                    let (class, _, _) = super::dedicated_operands(
                                        coordinate,
                                        product.term_class,
                                        product.source_a,
                                        product.source_b,
                                    )
                                    .unwrap();
                                    assert!(matches!(class, 3 | 5));
                                    pair_classes.push(class);
                                }
                                assert_eq!(
                                    pair_classes[0], pair_classes[1],
                                    "corpus fixed pair must be class-homogeneous"
                                );
                                coordinate_pair_classes.insert(pair_classes[0]);
                                if heterogeneous_pair.is_none() {
                                    let mut malformed = grouped.clone();
                                    let GroupedAtom::Group { members, .. } = malformed
                                        .atoms
                                        .iter_mut()
                                        .find(|atom| {
                                            matches!(
                                                atom,
                                                GroupedAtom::Group {
                                                    phase: R0Phase::E4,
                                                    members,
                                                    ..
                                                } if members.len() == 3
                                            )
                                        })
                                        .unwrap()
                                    else {
                                        unreachable!()
                                    };
                                    members[2].term_class =
                                        if pair_classes[0] == 3 { 4 } else { 3 };
                                    heterogeneous_pair = Some((coordinate, malformed));
                                }
                                e4_product_pairs += 1;
                            }
                            count => panic!("unexpected extracted E4 product count {count}"),
                        }

                        if malformed_linear_prefix.is_none() {
                            let mut malformed = grouped.clone();
                            let GroupedAtom::Group { members, .. } = malformed
                                .atoms
                                .iter_mut()
                                .find(|atom| {
                                    matches!(
                                        atom,
                                        GroupedAtom::Group {
                                            phase: R0Phase::E4,
                                            ..
                                        }
                                    )
                                })
                                .unwrap()
                            else {
                                unreachable!()
                            };
                            members[0].immediate = 2_013_265_920;
                            malformed_linear_prefix = Some((coordinate, malformed));
                        }
                        if unsupported_product_class.is_none() {
                            let mut malformed = grouped.clone();
                            let GroupedAtom::Group { members, .. } = malformed
                                .atoms
                                .iter_mut()
                                .find(|atom| {
                                    matches!(
                                        atom,
                                        GroupedAtom::Group {
                                            phase: R0Phase::E4,
                                            ..
                                        }
                                    )
                                })
                                .unwrap()
                            else {
                                unreachable!()
                            };
                            members[1].term_class = 0;
                            unsupported_product_class = Some((coordinate, malformed));
                        }
                    }
                    _ => {}
                }
            }
            assert!(
                coordinate_pair_classes.len() <= 1,
                "one compiled coordinate must not mix fixed-pair classes: {}:{} {coordinate_pair_classes:?}",
                coordinate.circuit,
                coordinate.layer
            );
        }

        assert_eq!(linear_group_members, 1_255);
        assert_eq!(linear_singletons, 500);
        assert_eq!(migrated_bf_products, 172);
        assert_eq!(e4_single_products, 779);
        assert_eq!(e4_product_pairs, 304);
        assert_eq!(coordinates, 57);
        assert_eq!(
            distinct_shapes,
            [
                1, 32, 433, 439, 1_015, 1_019, 1_120, 1_136, 1_270, 2_495, 3_067, 3_071, 3_192,
                3_194,
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(
            maximum_coefficient_plan_row,
            Some((
                "blake2_with_extended_control".to_owned(),
                0,
                301,
                0,
                1_364,
                0,
            ))
        );
        assert_eq!(maximum_coefficient_plans, 1_665);
        assert_eq!(maximum_descriptor_coefficient_count, 1_665);
        assert!(maximum_coefficient_plans <= crate::r0_abi::R0_COEFFICIENT_CAPACITY);

        let (coordinate, malformed) = malformed_linear_prefix.unwrap();
        let error = super::derive_dedicated_shape(coordinate, &malformed).unwrap_err();
        assert!(format!("{error:?}").contains("first-position +1 linear"));

        let (coordinate, malformed) = unsupported_product_class.unwrap();
        let error = super::derive_dedicated_shape(coordinate, &malformed).unwrap_err();
        assert!(format!("{error:?}").contains("unsupported E4 product class"));

        let (coordinate, malformed) = heterogeneous_pair.unwrap();
        let error = super::derive_dedicated_shape(coordinate, &malformed).unwrap_err();
        assert!(format!("{error:?}").contains("heterogeneous E4 pair"));
        let error = super::lower_dedicated_sections(coordinate, &malformed).unwrap_err();
        assert!(format!("{error:?}").contains("heterogeneous E4 pair"));

        let error = super::validate_sectioned_coefficient_ids(&invalid_linear_bank_span.unwrap())
            .unwrap_err();
        assert!(format!("{error:?}").contains("linear coefficient span"));
    }

    #[test]
    fn cpu_window_program_port_matches_legacy_sectioned_lowering() {
        use gpu_gkr_compiler::backward::{
            lower_window_program, walk_window_source_lanes, WindowCapacities, WindowProgram,
            WindowShape,
        };

        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let frozen = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut coordinates = 0usize;
        let mut lane_words = 0usize;

        for layer in &corpus.layers {
            let coordinate = frozen[&(layer.circuit.as_str(), layer.layer as u32)];
            let label = format!("{}:{}", layer.circuit, layer.layer);
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let programs = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .unwrap();
            let R0EncodedProgram::GroupedSlot(grouped) = &programs
                .get(R0ProgramEncoding::GroupedSlot)
                .expect("grouped-slot program")
                .encoded
            else {
                unreachable!()
            };
            let legacy = super::legacy_lower_dedicated_sections(coordinate, grouped).unwrap();
            assert_eq!(
                super::lower_dedicated_sections(coordinate, grouped).unwrap(),
                legacy,
                "{label} delegating sectioned wrapper"
            );
            let expected = WindowProgram {
                layer: layer.layer,
                words: legacy.words.clone(),
                source_slots: legacy.source_slots.clone(),
                // The legacy oracle predates the lane side table, so it defines
                // no expectation for it; the guards below stand in.
                source_lanes: Vec::new(),
                windows: coordinate.binding.windows.clone(),
                immediates: legacy.immediates.clone(),
                sections: legacy.sections,
                coefficient_plans: legacy
                    .coefficient_plans
                    .iter()
                    .map(super::window_plan_from_dedicated)
                    .collect(),
                shape: WindowShape::from_bits(legacy.shape.bits()).unwrap(),
                capacities: WindowCapacities {
                    records: legacy.words.len() / 4,
                    program_words: legacy.words.len(),
                    source_slots: legacy.source_slots.len(),
                    windows: coordinate.binding.windows.len(),
                    immediates: legacy.immediates.len(),
                    coefficient_plans: legacy.coefficient_plans.len(),
                },
            };
            let ported = lower_window_program(&layer.r0).unwrap();

            assert_eq!(ported.layer, expected.layer, "{label} layer");
            assert_eq!(ported.words, expected.words, "{label} wire words");
            assert_eq!(
                ported.source_slots, expected.source_slots,
                "{label} source slots"
            );
            assert_eq!(
                ported.windows, expected.windows,
                "{label} window identities"
            );
            assert_eq!(ported.immediates, expected.immediates, "{label} immediates");
            assert_eq!(ported.sections, expected.sections, "{label} sections");
            assert_eq!(
                ported.coefficient_plans, expected.coefficient_plans,
                "{label} coefficient plans"
            );
            assert_eq!(ported.shape, expected.shape, "{label} shape mask");
            assert_eq!(ported.capacities, expected.capacities, "{label} capacities");
            let mut legacy_defined = ported.clone();
            let lanes = std::mem::take(&mut legacy_defined.source_lanes);
            assert_eq!(
                legacy_defined, expected,
                "{label} lowered window program (fields the legacy oracle defines)"
            );

            // Side-table self-consistency: every listed word holds the lane its
            // named source lowered to, and the list covers EVERY lane-bearing
            // word of the wire (the walker decodes the instruction stream the
            // way the kernels do).
            for lane in &lanes {
                assert_eq!(
                    ported.words[lane.word as usize],
                    ported.source_slots[usize::from(lane.source)],
                    "{label} lane word {}",
                    lane.word
                );
            }
            let recorded: Vec<u32> = lanes.iter().map(|lane| lane.word).collect();
            assert_eq!(
                walk_window_source_lanes(&ported).unwrap(),
                recorded,
                "{label} lane coverage"
            );
            assert!(!lanes.is_empty(), "{label} has no addressed source");
            lane_words += lanes.len();
            coordinates += 1;
        }

        assert_eq!(coordinates, 57);
        assert_eq!(lane_words, 13_509, "corpus lane-word total");
    }

    #[test]
    fn cpu_sectioned_wire_has_four_exact_sections_and_linear_basis_ids() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|coordinate| {
                coordinate
                    .binding
                    .source_slots
                    .iter()
                    .filter(|source| {
                        coordinate.binding.windows[usize::from(source.window)]
                            .procedural_kind()
                            .is_none()
                    })
                    .count()
                    >= 2
            })
            .expect("fixture coordinate with two ordinary sources");
        let ordinary_slots = coordinate
            .binding
            .source_slots
            .iter()
            .enumerate()
            .filter(|(_, source)| {
                coordinate.binding.windows[usize::from(source.window)]
                    .procedural_kind()
                    .is_none()
            })
            .map(|(slot, _)| StoredSource::Slot(slot as u16))
            .take(2)
            .collect::<Vec<_>>();
        let a = ordinary_slots[0];
        let b = ordinary_slots[1];
        let core = FrozenR0Recipe {
            products: vec![FrozenR0Product {
                scalar: 7,
                challenges: Vec::new(),
                inits_and_teardowns_top_bits: Vec::new(),
            }],
        };
        let program = GroupedSlotProgram {
            atoms: vec![
                GroupedAtom::Singleton {
                    phase: R0Phase::Bf,
                    coefficient_id: 0,
                    term_class: 2,
                    source_a: a,
                    source_b: Some(b),
                },
                GroupedAtom::Singleton {
                    phase: R0Phase::E4,
                    coefficient_id: 0,
                    term_class: 3,
                    source_a: a,
                    source_b: Some(b),
                },
                GroupedAtom::Group {
                    phase: R0Phase::E4,
                    group_id: 0,
                    core: core.clone(),
                    members: vec![
                        GroupedMember {
                            term_class: 1,
                            immediate: 1,
                            source_a: a,
                            source_b: None,
                        },
                        GroupedMember {
                            term_class: 4,
                            immediate: 1,
                            source_a: a,
                            source_b: Some(b),
                        },
                        GroupedMember {
                            term_class: 4,
                            immediate: 2_013_265_920,
                            source_a: b,
                            source_b: Some(a),
                        },
                    ],
                },
            ],
            source_slots: crate::r0_prototype_encoding::packed_source_slots(coordinate),
        };

        let flat = super::lower_dedicated_sections(coordinate, &program).unwrap();
        assert_eq!(&flat.sections[..4], &[1, 2, 3, 6]);
        assert_eq!(flat.words.len(), 6 * 4);
        assert_eq!(flat.words[4], super::R0_DEDICATED_LINEAR_E4_WIDE);
        let basis_first = flat.words[5];
        assert_eq!(basis_first, 2);
        assert!(matches!(
            &flat.coefficient_plans[..4],
            [
                super::DedicatedCoefficientPlan::LinearBasis { limb: 0, .. },
                super::DedicatedCoefficientPlan::LinearBasis { limb: 1, .. },
                super::DedicatedCoefficientPlan::LinearBasis { limb: 2, .. },
                super::DedicatedCoefficientPlan::LinearBasis { limb: 3, .. },
            ]
        ));
        assert_eq!(flat.words[12], super::R0_DEDICATED_GROUP_E4);
        assert_eq!(flat.words[13], basis_first, "pair reuses basis-0 core");
        assert_eq!(flat.words[14], 0, "fixed pair arity is section-implied");

        let resolved = crate::r0_prototype_harness::resolve_dedicated_coefficient_plans(
            &flat.coefficient_plans,
            &[],
        )
        .unwrap();
        assert_eq!(resolved.len(), 4, "pair core reuses linear basis zero");
        let resolved_core = crate::abi::E4::from_array_of_base([
            Bf::from_u32_with_reduction(7),
            Bf::ZERO,
            Bf::ZERO,
            Bf::ZERO,
        ]);
        for limb in 0..4 {
            let mut basis = [Bf::ZERO; 4];
            basis[limb] = Bf::ONE;
            let basis = crate::abi::E4::from_array_of_base(basis);
            let mut expected = resolved_core;
            expected.mul_assign(&basis);
            assert_eq!(resolved[limb], expected);
        }

        let direct_and_scaled = crate::r0_prototype_harness::resolve_dedicated_coefficient_plans(
            &[
                super::DedicatedCoefficientPlan::Direct(core.clone()),
                super::DedicatedCoefficientPlan::Scaled {
                    recipe: core,
                    scalar: 3,
                },
            ],
            &[],
        )
        .unwrap();
        assert_eq!(direct_and_scaled[0], resolved_core);
        let mut scaled = resolved_core;
        scaled.mul_assign(&crate::abi::E4::from_array_of_base([
            Bf::from_u32_with_reduction(3),
            Bf::ZERO,
            Bf::ZERO,
            Bf::ZERO,
        ]));
        assert_eq!(direct_and_scaled[1], scaled);
    }

    #[test]
    fn cpu_all_r0_coordinates_build_fixed_width_dedicated_grouped_streams() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let frozen = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut maximum_instructions = 0usize;
        let mut minimum_e4_group = usize::MAX;
        let mut maximum_e4_group = 0usize;
        let mut e4_pair_classes = BTreeMap::<(u16, u16), usize>::new();
        let mut e4_pair_factors = BTreeMap::<(u32, u32), usize>::new();
        let mut bf_group_shapes = BTreeMap::<(u16, u16), usize>::new();
        for layer in &corpus.layers {
            let coordinate = frozen[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let programs = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .unwrap();
            let grouped_program = match &programs
                .get(crate::r0_prototype_manifest::R0ProgramEncoding::GroupedSlot)
                .unwrap()
                .encoded
            {
                crate::r0_prototype_encoding::R0EncodedProgram::GroupedSlot(program) => program,
                _ => unreachable!(),
            };
            let dedicated_flat =
                super::flatten_dedicated_grouped(coordinate, grouped_program).unwrap();
            let generic_flat = super::flatten_grouped(
                coordinate,
                &grouped_program.atoms,
                grouped_program.source_slots.clone(),
            )
            .unwrap();
            let immediate = |table: &[u32], id: u16| match id {
                0 => 1,
                1 => 2_013_265_920,
                _ => table[usize::from(id - 2)],
            };
            let mut generic_ops = Vec::new();
            let mut word = 0usize;
            while word < generic_flat.words.len() {
                if generic_flat.words[word] == 0xffff {
                    let coefficient = generic_flat.words[word + 1];
                    let count = usize::from(generic_flat.words[word + 2]);
                    let phase = u8::from(generic_flat.words[word + 3] & 0x8000 != 0);
                    word += 4;
                    for _ in 0..count {
                        let class = generic_flat.words[word] as u8;
                        let factor =
                            immediate(&generic_flat.immediates, generic_flat.words[word + 1]);
                        let source_a = generic_flat.words[word + 2];
                        let source_b = if class <= 1 {
                            0
                        } else {
                            generic_flat.words[word + 3]
                        };
                        word += if class <= 1 { 3 } else { 4 };
                        generic_ops.push((phase, class, coefficient, factor, source_a, source_b));
                    }
                } else {
                    let header = generic_flat.words[word];
                    let class = (header >> 13) as u8;
                    let coefficient = header & 0x1fff;
                    let source_a = generic_flat.words[word + 1];
                    let source_b = if class <= 1 {
                        0
                    } else {
                        generic_flat.words[word + 2]
                    };
                    word += if class <= 1 { 2 } else { 3 };
                    generic_ops.push((
                        u8::from(!matches!(class, 0 | 2)),
                        class,
                        coefficient,
                        1,
                        source_a,
                        source_b,
                    ));
                }
            }
            let mut dedicated_ops = Vec::new();
            let procedural_slot = |kind: u16| {
                coordinate
                    .binding
                    .source_slots
                    .iter()
                    .enumerate()
                    .find_map(|(slot, source)| {
                        (coordinate.binding.windows[usize::from(source.window)].procedural_kind()
                            == Some(kind as u8))
                        .then_some(slot as u16)
                    })
                    .expect("dedicated procedural kind is bound")
            };
            let direct_slot = |packed: u16| {
                let window = packed >> 7;
                let column = packed & 0x7f;
                coordinate
                    .binding
                    .source_slots
                    .iter()
                    .position(|source| {
                        u16::from(source.window) == window && source.column == column
                    })
                    .map(|slot| slot as u16)
                    .expect("dedicated direct coordinate is bound")
            };
            let normalize_dedicated = |class: u8, source_a: u16, source_b: u16| match class {
                4 => (0, procedural_slot(source_a), 0),
                5 => (4, direct_slot(source_a), direct_slot(source_b)),
                8 => (2, direct_slot(source_a), procedural_slot(source_b)),
                9 => (2, procedural_slot(source_a), procedural_slot(source_b)),
                0 | 1 => (class, direct_slot(source_a), 0),
                2 | 3 => (class, direct_slot(source_a), direct_slot(source_b)),
                _ => panic!("unexpected dedicated term class {class}"),
            };
            let mut pc = 0usize;
            while pc < dedicated_flat.sections[1] as usize {
                let base = 4 * pc;
                let head = &dedicated_flat.words[base..base + 4];
                let phase = u8::from(pc >= dedicated_flat.sections[0] as usize);
                pc += 1;
                if matches!(
                    head[0],
                    super::R0_DEDICATED_GROUP_BF | super::R0_DEDICATED_GROUP_E4
                ) {
                    if head[0] == super::R0_DEDICATED_GROUP_BF {
                        let product_prefix =
                            head[3] & super::R0_DEDICATED_HAS_PRODUCT.wrapping_sub(1);
                        assert_ne!(
                            product_prefix, 0,
                            "dedicated BF group must contain products"
                        );
                        assert!(
                            head[2] - product_prefix <= 1,
                            "dedicated BF group has at most one linear tail"
                        );
                        *bf_group_shapes
                            .entry((product_prefix, head[2] - product_prefix))
                            .or_default() += 1;
                    }
                    let members = if head[0] == super::R0_DEDICATED_GROUP_E4 {
                        assert_eq!(head[2], 0, "E4 pair arity must be implicit");
                        2
                    } else {
                        head[2]
                    };
                    for _ in 0..members {
                        let base = 4 * pc;
                        let member = &dedicated_flat.words[base..base + 4];
                        let raw = immediate(
                            &dedicated_flat.immediates,
                            member[1] & super::R0_DEDICATED_HAS_PRODUCT.wrapping_sub(1),
                        );
                        let factor =
                            if member[1] & super::R0_DEDICATED_HAS_PRODUCT.wrapping_sub(1) <= 1 {
                                raw
                            } else {
                                Bf::from_reduced_raw_repr(raw).as_u32_reduced()
                            };
                        let (class, source_a, source_b) =
                            normalize_dedicated(member[0] as u8, member[2], member[3]);
                        dedicated_ops.push((phase, class, head[1], factor, source_a, source_b));
                        pc += 1;
                    }
                } else {
                    let (class, source_a, source_b) =
                        normalize_dedicated(head[0] as u8, head[2], head[3]);
                    dedicated_ops.push((phase, class, head[1], 1, source_a, source_b));
                }
            }
            generic_ops.sort_unstable();
            dedicated_ops.sort_unstable();
            assert_eq!(dedicated_ops, generic_ops, "fixed semantic wire mismatch");
            let descriptor = build_dedicated_grouped_descriptor(coordinate, &programs, 3).unwrap();
            let R0PrototypePayload::GroupedSlotOrdinary(desc) = &descriptor.payload else {
                panic!("dedicated grouped descriptor used the wrong payload");
            };
            let bf_instructions = desc.meta.sections[0] as usize;
            let total_instructions = desc.meta.sections[1] as usize;
            assert!(bf_instructions <= total_instructions);
            assert_eq!(desc.meta.program_words as usize, 4 * total_instructions);
            assert_eq!(
                desc.common.record_count as usize,
                coordinate.shape.records as usize
            );
            assert_eq!(
                desc.common.bf_record_count as usize,
                programs
                    .get(crate::r0_prototype_manifest::R0ProgramEncoding::GroupedSlot)
                    .unwrap()
                    .operations
                    .iter()
                    .take_while(|operation| {
                        operation.phase == crate::r0_prototype_encoding::R0Phase::Bf
                    })
                    .count()
            );
            assert!(descriptor.payload_size <= crate::r0_abi::KERNEL_ARGUMENT_CEILING_BYTES);
            assert!(descriptor.tails_are_zero());
            let grouped_entry = programs
                .get(crate::r0_prototype_manifest::R0ProgramEncoding::GroupedSlot)
                .unwrap();
            let crate::r0_prototype_encoding::R0EncodedProgram::GroupedSlot(grouped) =
                &grouped_entry.encoded
            else {
                unreachable!()
            };
            let canonical_immediates = grouped
                .atoms
                .iter()
                .filter_map(|atom| match atom {
                    crate::r0_prototype_encoding::GroupedAtom::Group { members, .. } => {
                        Some(members.as_slice())
                    }
                    _ => None,
                })
                .flatten()
                .map(|member| member.immediate)
                .filter(|value| *value != 1 && *value != 2_013_265_920)
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                desc.meta.immediate_count as usize,
                canonical_immediates.len()
            );
            for (raw, canonical) in desc
                .immediates
                .iter()
                .zip(canonical_immediates.iter())
                .take(desc.meta.immediate_count as usize)
            {
                assert_eq!(Bf::from_reduced_raw_repr(*raw).as_u32_reduced(), *canonical);
            }
            let mut semantic_records = 0usize;
            let mut scan_pc = 0usize;
            while scan_pc < total_instructions {
                let head = &desc.program[4 * scan_pc..4 * scan_pc + 4];
                scan_pc += 1;
                if matches!(
                    head[0],
                    super::R0_DEDICATED_GROUP_BF | super::R0_DEDICATED_GROUP_E4
                ) {
                    let members = if head[0] == super::R0_DEDICATED_GROUP_E4 {
                        assert_eq!(head[2], 0, "E4 pair arity must be implicit");
                        2
                    } else {
                        usize::from(head[2])
                    };
                    semantic_records += members;
                    scan_pc += members;
                } else {
                    semantic_records += 1;
                }
            }
            assert_eq!(scan_pc, total_instructions);
            assert_eq!(semantic_records, desc.common.record_count as usize);
            let mut pc = bf_instructions;
            while pc < total_instructions {
                let head = &desc.program[4 * pc..4 * pc + 4];
                pc += 1;
                if head[0] == super::R0_DEDICATED_GROUP_E4 {
                    assert_eq!(head[2], 0, "E4 pair arity must be implicit");
                    minimum_e4_group = minimum_e4_group.min(2);
                    maximum_e4_group = maximum_e4_group.max(2);
                    let members = (0..2)
                        .map(|offset| {
                            let base = 4 * (pc + offset);
                            &desc.program[base..base + 4]
                        })
                        .collect::<Vec<_>>();
                    let factor = |member: &[u16]| {
                        immediate(
                            &dedicated_flat.immediates,
                            member[1] & super::R0_DEDICATED_HAS_PRODUCT.wrapping_sub(1),
                        )
                    };
                    *e4_pair_classes
                        .entry((members[0][0], members[1][0]))
                        .or_default() += 1;
                    *e4_pair_factors
                        .entry((factor(members[0]), factor(members[1])))
                        .or_default() += 1;
                    if matches!((members[0][0], members[1][0]), (3, 3) | (5, 5)) {
                        let direct = |packed: u16| {
                            let window = &coordinate.binding.windows[usize::from(packed >> 7)];
                            (
                                &window.family,
                                window.first_column + usize::from(packed & 0x7f),
                            )
                        };
                        let (a0_family, a0_column) = direct(members[0][2]);
                        let (a1_family, a1_column) = direct(members[1][2]);
                        let (b0_family, b0_column) = direct(members[0][3]);
                        let (b1_family, b1_column) = direct(members[1][3]);
                        assert_eq!(b0_family, b1_family);
                        assert_eq!(
                            i64::try_from(b1_column).unwrap() - i64::try_from(b0_column).unwrap(),
                            -1
                        );
                        if members[0][0] == 5 {
                            assert_eq!(a0_family, a1_family);
                            assert_eq!(
                                i64::try_from(a1_column).unwrap()
                                    - i64::try_from(a0_column).unwrap(),
                                1
                            );
                        } else {
                            assert_ne!(a0_family, a1_family);
                        }
                    }
                    pc += 2;
                }
            }
            maximum_instructions = maximum_instructions.max(total_instructions);
        }
        assert!(maximum_instructions > 1_600);
        assert_eq!((minimum_e4_group, maximum_e4_group), (2, 2));
        assert_eq!(
            e4_pair_classes,
            BTreeMap::from([
                ((1, 2), 153),
                ((1, 3), 55),
                ((1, 5), 724),
                ((1, 8), 19),
                ((3, 3), 7),
                ((5, 5), 297),
            ])
        );
        assert_eq!(
            e4_pair_factors,
            BTreeMap::from([((1, 1), 1_225), ((1, 2_013_265_920), 30)])
        );
        assert_eq!(bf_group_shapes.values().sum::<usize>(), 668);
        assert_eq!(bf_group_shapes.get(&(1, 1)), Some(&34));
        assert_eq!(
            bf_group_shapes
                .iter()
                .filter(|((_, linear_tail), _)| *linear_tail == 1)
                .map(|(_, count)| count)
                .sum::<usize>(),
            59
        );
        assert_eq!(
            bf_group_shapes.keys().map(|(products, _)| *products).max(),
            Some(48)
        );
    }

    #[test]
    fn cpu_all_coordinates_build_exactly_32_checked_descriptor_forms() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let frozen = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut forms = 0usize;
        for layer in &corpus.layers {
            let coordinate = frozen[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let programs = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .unwrap();
            let descriptors = build_prototype_descriptors(coordinate, &programs, 3).unwrap();
            assert_eq!(descriptors.len(), 32);
            assert_eq!(
                descriptors
                    .iter()
                    .filter(|row| row.capacity.is_none())
                    .count(),
                8
            );
            assert_eq!(
                descriptors
                    .iter()
                    .filter(|row| row.capacity.is_some())
                    .count(),
                24
            );
            assert!(descriptors
                .iter()
                .all(|row| row.payload_size <= crate::r0_abi::KERNEL_ARGUMENT_CEILING_BYTES));
            assert!(descriptors.iter().all(|row| row.tails_are_zero()));
            assert!(descriptors.iter().all(|row| row.program_sha256.len() == 64));
            assert!(descriptors
                .iter()
                .all(|row| row.tile_sha256.as_ref().is_none_or(|hash| hash.len() == 64)));
            forms += descriptors.len();
        }
        assert_eq!(forms, 57 * 32);
    }

    #[test]
    fn cpu_rust_descriptor_layouts_fit_the_kernel_argument_ceiling() {
        let layout = R0PrototypeAbiLayout::rust();
        assert_eq!(
            layout.common_size,
            core::mem::size_of::<R0PrototypeCommonDesc>()
        );
        assert_eq!(
            layout.common_align,
            core::mem::align_of::<R0PrototypeCommonDesc>()
        );
        assert_eq!(layout.descriptors.len(), 15);
        assert!(layout
            .descriptors
            .iter()
            .all(|row| row.size <= crate::r0_abi::KERNEL_ARGUMENT_CEILING_BYTES));
    }

    #[test]
    fn cpu_native_and_rust_prototype_layouts_match_field_for_field() {
        assert_eq!(
            native_r0_prototype_abi_layout().unwrap(),
            R0PrototypeAbiLayout::rust()
        );
    }
}
