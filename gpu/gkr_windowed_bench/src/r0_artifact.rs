use std::collections::BTreeSet;
use std::io::Write;
use std::process::{Command, Stdio};

use bincode::Options;
use gkr_eval_ir::{ChallengeRef, InitsAndTeardownsTopBitsRef};
use gpu_gkr_compiler::backward::{
    CoeffChallenge, LeanSourceBinding, LEAN_MAX_IMMEDIATES, SOURCE_NONE,
};
use serde::{Deserialize, Serialize};

pub const R0_BUNDLE_MAGIC: [u8; 8] = *b"WGKRR0\0\0";
pub const R0_BUNDLE_VERSION: u32 = 1;
pub const R0_RECORD_WORDS: usize = 4;
pub const R0_DECLARED_RECORDS: usize = 1_791;
pub const R0_DECLARED_PROGRAM_WORDS: usize = 7_164;
pub const R0_DECLARED_PROJECTIONS: usize = 1_731;
pub const R0_DECLARED_COEFFICIENTS: usize = 1_138;
pub const R0_DECLARED_SOURCES: usize = 1_062;
pub const R0_DECLARED_WINDOWS: usize = 64;
pub const R0_CLASS_NAMES: [&str; 5] = [
    "C0LinearBf",
    "C0LinearE4",
    "C2ProductBfBf",
    "C2ProductBfE4",
    "C2ProductE4E4",
];
pub const R0_COEFFICIENT_ONE: u32 = 0;
pub const R0_COEFFICIENT_NEG_ONE: u32 = 1;
pub const R0_COEFFICIENT_RESERVED: u32 = 2;
pub static R0_CORPUS_BYTES: &[u8] = include_bytes!("../artifacts/windowed_r0_corpus_v1.bin");

const R0_CLASS_SHIFT: u16 = 13;
const R0_COEFFICIENT_MASK: u16 = (1 << R0_CLASS_SHIFT) - 1;
const R0_SOURCE_WINDOW_BITS: u8 = 6;
const R0_SOURCE_COLUMN_BITS: u8 = 7;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenR0BundleV1 {
    pub magic: [u8; 8],
    pub version: u32,
    pub layout_hashes: Vec<R0LayoutHash>,
    pub coordinates: Vec<FrozenR0Coordinate>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0LayoutHash {
    pub path: String,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0CoordinateOffsets {
    pub circuit: String,
    pub layer: u32,
    pub coordinate_offset: u64,
    pub coordinate_len: u64,
    pub program_offset: u64,
    pub program_len: u64,
    pub binding_offset: u64,
    pub binding_len: u64,
    pub recipes_offset: u64,
    pub recipes_len: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InspectedR0Bundle {
    pub bundle: FrozenR0BundleV1,
    pub offsets: Vec<R0CoordinateOffsets>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenR0Shape {
    pub records: u32,
    pub projections: u32,
    pub bf_atoms: u32,
    pub e4_atoms: u32,
    pub source_uses: u32,
    pub unique_sources: u32,
    pub windows: u16,
    pub max_relative_column: u16,
    pub coefficient_recipes: u32,
    pub immediates: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenR0Coordinate {
    pub circuit: String,
    pub layer: u32,
    pub trace_len: u64,
    pub passes_per_invocation: u32,
    pub program_words: Vec<u16>,
    pub term_count: u32,
    pub binding: LeanSourceBinding,
    pub recipes: Vec<FrozenR0Recipe>,
    pub immediates: Vec<u32>,
    pub c_init: Option<u32>,
    pub shape: FrozenR0Shape,
    pub payload_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenR0Recipe {
    pub products: Vec<FrozenR0Product>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenR0Product {
    pub scalar: u32,
    pub challenges: Vec<FrozenR0Challenge>,
    pub inits_and_teardowns_top_bits: Vec<InitsAndTeardownsTopBitsRef>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenR0Challenge {
    pub reference: ChallengeRef,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0ArtifactError {
    BadMagic,
    BadVersion(u32),
    DuplicateCoordinate(String),
    UnsortedCoordinate(String),
    InvalidUtf8,
    NoncanonicalSha256,
    ProgramMisaligned,
    InvalidClass(u16),
    InvalidSourceCoordinate(u16),
    InvalidSourceBinding,
    InvalidCoefficient(u32),
    NonCanonicalChallenge,
    CInitPresent,
    CapacityOverflow,
    OffsetOverflow,
    LengthOverflow,
    Truncated,
    TrailingBytes,
    Codec(String),
    PayloadHashMismatch,
    ShapeMismatch,
}

impl core::fmt::Display for R0ArtifactError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0ArtifactError {}

pub fn pack_r0_source(window: u8, column: u16) -> Result<u16, R0ArtifactError> {
    if window >= 1 << R0_SOURCE_WINDOW_BITS || column >= 1 << R0_SOURCE_COLUMN_BITS {
        return Err(R0ArtifactError::InvalidSourceCoordinate(
            (u16::from(window) << R0_SOURCE_COLUMN_BITS) | column,
        ));
    }
    Ok((u16::from(window) << R0_SOURCE_COLUMN_BITS) | column)
}

pub fn unpack_r0_source(source: u16) -> Result<(u8, u16), R0ArtifactError> {
    let mask = (1u16 << (R0_SOURCE_WINDOW_BITS + R0_SOURCE_COLUMN_BITS)) - 1;
    if source & !mask != 0 {
        return Err(R0ArtifactError::InvalidSourceCoordinate(source));
    }
    Ok((
        (source >> R0_SOURCE_COLUMN_BITS) as u8,
        source & ((1 << R0_SOURCE_COLUMN_BITS) - 1),
    ))
}

pub fn r0_banked_coefficient_index(
    coefficient: u32,
    recipe_count: usize,
) -> Result<usize, R0ArtifactError> {
    let index = coefficient
        .checked_sub(R0_COEFFICIENT_RESERVED)
        .ok_or(R0ArtifactError::InvalidCoefficient(coefficient))?;
    let index = usize::try_from(index).map_err(|_| R0ArtifactError::CapacityOverflow)?;
    if index >= recipe_count {
        return Err(R0ArtifactError::InvalidCoefficient(coefficient));
    }
    Ok(index)
}

pub fn encode_r0_bundle(value: &FrozenR0BundleV1) -> Result<Vec<u8>, R0ArtifactError> {
    validate_r0_bundle(value)?;
    let mut output = Vec::new();
    output.extend_from_slice(&value.magic);
    push_u32(&mut output, value.version);
    push_u32(&mut output, u32_len(value.layout_hashes.len())?);
    push_u32(&mut output, u32_len(value.coordinates.len())?);
    for hash in &value.layout_hashes {
        push_string(&mut output, &hash.path)?;
        output.extend_from_slice(&decode_sha256(&hash.sha256)?);
    }
    for coordinate in &value.coordinates {
        let frame = encode_coordinate_frame(coordinate)?;
        push_u32(&mut output, u32_len(frame.len())?);
        output.extend_from_slice(&frame);
    }
    Ok(output)
}

pub fn decode_r0_bundle(bytes: &[u8]) -> Result<FrozenR0BundleV1, R0ArtifactError> {
    Ok(inspect_r0_bundle(bytes)?.bundle)
}

pub fn inspect_r0_bundle(bytes: &[u8]) -> Result<InspectedR0Bundle, R0ArtifactError> {
    let mut cursor = Cursor::new(bytes);
    let magic = cursor.take_array::<8>()?;
    let version = cursor.u32()?;
    let layout_count = usize_from_u32(cursor.u32()?)?;
    let coordinate_count = usize_from_u32(cursor.u32()?)?;
    if layout_count > cursor.remaining() / 36 || coordinate_count > cursor.remaining() / 4 {
        return Err(R0ArtifactError::Truncated);
    }
    let mut layout_hashes = Vec::with_capacity(layout_count);
    for _ in 0..layout_count {
        let path = cursor.string()?;
        let sha256 = encode_sha256(&cursor.take_array::<32>()?);
        layout_hashes.push(R0LayoutHash { path, sha256 });
    }

    let mut coordinates = Vec::with_capacity(coordinate_count);
    let mut offsets = Vec::with_capacity(coordinate_count);
    for _ in 0..coordinate_count {
        let frame_len = usize_from_u32(cursor.u32()?)?;
        let coordinate_offset = cursor.position;
        let frame = cursor.take(frame_len)?;
        let (coordinate, relative_offsets) = decode_coordinate_frame(frame)?;
        let coordinate_len = u64_from_usize(frame_len)?;
        offsets.push(R0CoordinateOffsets {
            circuit: coordinate.circuit.clone(),
            layer: coordinate.layer,
            coordinate_offset: u64_from_usize(coordinate_offset)?,
            coordinate_len,
            program_offset: offset_add(coordinate_offset, relative_offsets.program_offset)?,
            program_len: u64_from_usize(relative_offsets.program_len)?,
            binding_offset: offset_add(coordinate_offset, relative_offsets.binding_offset)?,
            binding_len: u64_from_usize(relative_offsets.binding_len)?,
            recipes_offset: offset_add(coordinate_offset, relative_offsets.recipes_offset)?,
            recipes_len: u64_from_usize(relative_offsets.recipes_len)?,
        });
        coordinates.push(coordinate);
    }
    if !cursor.is_empty() {
        return Err(R0ArtifactError::TrailingBytes);
    }
    let bundle = FrozenR0BundleV1 {
        magic,
        version,
        layout_hashes,
        coordinates,
    };
    validate_r0_bundle(&bundle)?;
    Ok(InspectedR0Bundle { bundle, offsets })
}

pub fn validate_r0_bundle(value: &FrozenR0BundleV1) -> Result<(), R0ArtifactError> {
    if value.magic != R0_BUNDLE_MAGIC {
        return Err(R0ArtifactError::BadMagic);
    }
    if value.version != R0_BUNDLE_VERSION {
        return Err(R0ArtifactError::BadVersion(value.version));
    }
    u32_len(value.layout_hashes.len())?;
    u32_len(value.coordinates.len())?;
    let mut previous = None;
    for layout in &value.layout_hashes {
        let _ = decode_sha256(&layout.sha256)?;
    }
    for coordinate in &value.coordinates {
        let key = (coordinate.circuit.as_str(), coordinate.layer);
        if let Some(previous) = previous {
            if key == previous {
                return Err(R0ArtifactError::DuplicateCoordinate(format!(
                    "{}:{}",
                    coordinate.circuit, coordinate.layer
                )));
            }
            if key < previous {
                return Err(R0ArtifactError::UnsortedCoordinate(format!(
                    "{}:{}",
                    coordinate.circuit, coordinate.layer
                )));
            }
        }
        validate_r0_coordinate(coordinate)?;
        previous = Some(key);
    }
    Ok(())
}

pub fn validate_r0_coordinate(coordinate: &FrozenR0Coordinate) -> Result<(), R0ArtifactError> {
    if coordinate.c_init.is_some() {
        return Err(R0ArtifactError::CInitPresent);
    }
    let record_count = coordinate
        .program_words
        .len()
        .checked_div(R0_RECORD_WORDS)
        .ok_or(R0ArtifactError::ProgramMisaligned)?;
    if coordinate.program_words.len() % R0_RECORD_WORDS != 0 {
        return Err(R0ArtifactError::ProgramMisaligned);
    }
    if record_count > R0_DECLARED_RECORDS
        || coordinate.program_words.len() > R0_DECLARED_PROGRAM_WORDS
        || coordinate.recipes.len() > R0_DECLARED_COEFFICIENTS
        || coordinate.immediates.len() > LEAN_MAX_IMMEDIATES
        || coordinate.binding.source_slots.len() > R0_DECLARED_SOURCES
        || coordinate.binding.windows.len() > R0_DECLARED_WINDOWS
        || usize::try_from(coordinate.shape.projections)
            .map_err(|_| R0ArtifactError::CapacityOverflow)?
            > R0_DECLARED_PROJECTIONS
    {
        return Err(R0ArtifactError::CapacityOverflow);
    }
    if coordinate.term_count != u32_len(record_count)?
        || coordinate.shape.records != u32_len(record_count)?
        || coordinate.shape.coefficient_recipes != u32_len(coordinate.recipes.len())?
        || coordinate.shape.immediates != u32_len(coordinate.immediates.len())?
        || coordinate.shape.unique_sources != u32_len(coordinate.binding.source_slots.len())?
        || coordinate.shape.windows != u16_len(coordinate.binding.windows.len())?
    {
        return Err(R0ArtifactError::ShapeMismatch);
    }
    if coordinate.shape.max_relative_column >= 1 << R0_SOURCE_COLUMN_BITS {
        return Err(R0ArtifactError::CapacityOverflow);
    }
    validate_binding(&coordinate.binding)?;

    let mut source_uses = 0usize;
    let mut bf_atoms = 0usize;
    let mut e4_atoms = 0usize;
    let mut projections = BTreeSet::new();
    for (record, words) in coordinate
        .program_words
        .chunks_exact(R0_RECORD_WORDS)
        .enumerate()
    {
        let class = words[0] >> R0_CLASS_SHIFT;
        if class > 4 {
            return Err(R0ArtifactError::InvalidClass(class));
        }
        match class {
            0 => {
                bf_atoms = bf_atoms
                    .checked_add(1)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
            }
            1 => {
                e4_atoms = e4_atoms
                    .checked_add(1)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
            }
            2 => {
                bf_atoms = bf_atoms
                    .checked_add(2)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
            }
            3 => {
                bf_atoms = bf_atoms
                    .checked_add(1)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
                e4_atoms = e4_atoms
                    .checked_add(1)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
            }
            4 => {
                e4_atoms = e4_atoms
                    .checked_add(2)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
            }
            _ => unreachable!("classes above four are rejected"),
        }
        let coefficient = u32::from(words[0] & R0_COEFFICIENT_MASK);
        if coefficient >= R0_COEFFICIENT_RESERVED {
            r0_banked_coefficient_index(coefficient, coordinate.recipes.len())?;
        }
        if words[3] != 0 {
            return Err(R0ArtifactError::ProgramMisaligned);
        }
        validate_program_source(words[1], &coordinate.binding)?;
        let projection_role = if class <= 1 { 0 } else { 1 };
        projections.insert((words[1], projection_role));
        source_uses = source_uses
            .checked_add(1)
            .ok_or(R0ArtifactError::CapacityOverflow)?;
        match class {
            0 | 1 => {
                if words[2] != SOURCE_NONE {
                    return Err(R0ArtifactError::InvalidSourceBinding);
                }
            }
            2..=4 => {
                if words[2] == SOURCE_NONE {
                    return Err(R0ArtifactError::InvalidSourceBinding);
                }
                validate_program_source(words[2], &coordinate.binding)?;
                projections.insert((words[2], projection_role));
                source_uses = source_uses
                    .checked_add(1)
                    .ok_or(R0ArtifactError::CapacityOverflow)?;
            }
            _ => unreachable!("classes above four are rejected"),
        }
        let _ = record;
    }
    if projections.len() > R0_DECLARED_PROJECTIONS {
        return Err(R0ArtifactError::CapacityOverflow);
    }
    if coordinate.shape.projections != u32_len(projections.len())?
        || coordinate.shape.source_uses != u32_len(source_uses)?
        || coordinate.shape.bf_atoms != u32_len(bf_atoms)?
        || coordinate.shape.e4_atoms != u32_len(e4_atoms)?
        || coordinate.shape.max_relative_column != binding_max_relative_column(&coordinate.binding)?
    {
        return Err(R0ArtifactError::ShapeMismatch);
    }
    for recipe in &coordinate.recipes {
        for product in &recipe.products {
            for challenge in &product.challenges {
                if CoeffChallenge::new(challenge.reference.clone()).0 != challenge.reference {
                    return Err(R0ArtifactError::NonCanonicalChallenge);
                }
            }
        }
    }
    let expected_payload = payload_hash_for_coordinate(coordinate)?;
    if coordinate.payload_sha256 != expected_payload {
        return Err(R0ArtifactError::PayloadHashMismatch);
    }
    Ok(())
}

fn validate_program_source(
    source: u16,
    binding: &LeanSourceBinding,
) -> Result<(), R0ArtifactError> {
    if source == SOURCE_NONE || usize::from(source) >= binding.source_slots.len() {
        return Err(R0ArtifactError::InvalidSourceBinding);
    }
    Ok(())
}

fn validate_binding(binding: &LeanSourceBinding) -> Result<(), R0ArtifactError> {
    if binding.windows.len() > R0_DECLARED_WINDOWS
        || binding.source_slots.len() > R0_DECLARED_SOURCES
    {
        return Err(R0ArtifactError::CapacityOverflow);
    }
    let mut occurrences = vec![0u8; binding.source_slots.len()];
    let mut previous = None;
    for (index, window) in binding.windows.iter().enumerate() {
        let key = (window.family, window.first_column);
        if previous.is_some_and(|previous| key <= previous) {
            return Err(R0ArtifactError::InvalidSourceBinding);
        }
        let end = window
            .first_column
            .checked_add(1usize << R0_SOURCE_COLUMN_BITS)
            .ok_or(R0ArtifactError::CapacityOverflow)?;
        let mut previous_column = None;
        for column in &window.columns {
            if column.column < window.first_column
                || column.column >= end
                || previous_column.is_some_and(|previous| column.column <= previous)
            {
                return Err(R0ArtifactError::InvalidSourceBinding);
            }
            let occurrence = occurrences
                .get_mut(
                    usize::try_from(column.source)
                        .map_err(|_| R0ArtifactError::CapacityOverflow)?,
                )
                .ok_or(R0ArtifactError::InvalidSourceBinding)?;
            *occurrence = occurrence
                .checked_add(1)
                .ok_or(R0ArtifactError::InvalidSourceBinding)?;
            previous_column = Some(column.column);
        }
        let _ = index;
        previous = Some(key);
    }
    for (source, slot) in binding.source_slots.iter().enumerate() {
        let window = binding
            .windows
            .get(usize::from(slot.window))
            .ok_or(R0ArtifactError::InvalidSourceBinding)?;
        let _ = pack_r0_source(slot.window, slot.column)?;
        let absolute = window
            .first_column
            .checked_add(usize::from(slot.column))
            .ok_or(R0ArtifactError::CapacityOverflow)?;
        let resolved = window
            .columns
            .binary_search_by_key(&absolute, |column| column.column)
            .ok()
            .and_then(|index| window.columns.get(index))
            .map(|column| {
                usize::try_from(column.source).map_err(|_| R0ArtifactError::CapacityOverflow)
            })
            .transpose()?;
        if resolved != Some(source) || occurrences[source] != 1 {
            return Err(R0ArtifactError::InvalidSourceBinding);
        }
    }
    Ok(())
}

fn binding_max_relative_column(binding: &LeanSourceBinding) -> Result<u16, R0ArtifactError> {
    binding
        .source_slots
        .iter()
        .map(|slot| slot.column)
        .max()
        .map_or(Ok(0), |column| {
            (column < 1 << R0_SOURCE_COLUMN_BITS)
                .then_some(column)
                .ok_or(R0ArtifactError::InvalidSourceCoordinate(column))
        })
}

fn bincode_options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
}

fn encode_coordinate_frame(coordinate: &FrozenR0Coordinate) -> Result<Vec<u8>, R0ArtifactError> {
    let mut frame = Vec::new();
    push_string(&mut frame, &coordinate.circuit)?;
    push_u32(&mut frame, coordinate.layer);
    push_u64(&mut frame, coordinate.trace_len);
    push_u32(&mut frame, coordinate.passes_per_invocation);
    push_u32(&mut frame, u32_len(coordinate.program_words.len())?);
    for word in &coordinate.program_words {
        push_u16(&mut frame, *word);
    }
    push_u32(&mut frame, coordinate.term_count);
    push_blob(
        &mut frame,
        &bincode_options()
            .serialize(&coordinate.binding)
            .map_err(codec_error)?,
    )?;
    push_blob(
        &mut frame,
        &bincode_options()
            .serialize(&coordinate.recipes)
            .map_err(codec_error)?,
    )?;
    push_u32(&mut frame, u32_len(coordinate.immediates.len())?);
    for immediate in &coordinate.immediates {
        push_u32(&mut frame, *immediate);
    }
    match coordinate.c_init {
        None => frame.push(0),
        Some(value) => {
            frame.push(1);
            push_u32(&mut frame, value);
        }
    }
    push_u32(&mut frame, coordinate.shape.records);
    push_u32(&mut frame, coordinate.shape.projections);
    push_u32(&mut frame, coordinate.shape.bf_atoms);
    push_u32(&mut frame, coordinate.shape.e4_atoms);
    push_u32(&mut frame, coordinate.shape.source_uses);
    push_u32(&mut frame, coordinate.shape.unique_sources);
    push_u16(&mut frame, coordinate.shape.windows);
    push_u16(&mut frame, coordinate.shape.max_relative_column);
    push_u32(&mut frame, coordinate.shape.coefficient_recipes);
    push_u32(&mut frame, coordinate.shape.immediates);
    frame.extend_from_slice(&decode_sha256(&coordinate.payload_sha256)?);
    Ok(frame)
}

struct RelativeOffsets {
    program_offset: usize,
    program_len: usize,
    binding_offset: usize,
    binding_len: usize,
    recipes_offset: usize,
    recipes_len: usize,
}

fn decode_coordinate_frame(
    frame: &[u8],
) -> Result<(FrozenR0Coordinate, RelativeOffsets), R0ArtifactError> {
    let mut cursor = Cursor::new(frame);
    let circuit = cursor.string()?;
    let layer = cursor.u32()?;
    let trace_len = cursor.u64()?;
    let passes_per_invocation = cursor.u32()?;
    let program_words = usize_from_u32(cursor.u32()?)?;
    if program_words > cursor.remaining() / 2 {
        return Err(R0ArtifactError::Truncated);
    }
    let program_offset = cursor.position;
    let program_len = program_words
        .checked_mul(2)
        .ok_or(R0ArtifactError::LengthOverflow)?;
    let mut words = Vec::with_capacity(program_words);
    for _ in 0..program_words {
        words.push(cursor.u16()?);
    }
    let term_count = cursor.u32()?;
    let (binding_offset, binding_bytes) = cursor.blob_with_offset()?;
    let binding_len = binding_bytes.len();
    let binding = bincode_options()
        .deserialize(binding_bytes)
        .map_err(codec_error)?;
    let (recipes_offset, recipes_bytes) = cursor.blob_with_offset()?;
    let recipes_len = recipes_bytes.len();
    let recipes = bincode_options()
        .deserialize(recipes_bytes)
        .map_err(codec_error)?;
    let immediate_count = usize_from_u32(cursor.u32()?)?;
    if immediate_count > cursor.remaining() / 4 {
        return Err(R0ArtifactError::Truncated);
    }
    let mut immediates = Vec::with_capacity(immediate_count);
    for _ in 0..immediate_count {
        immediates.push(cursor.u32()?);
    }
    let c_init = match cursor.u8()? {
        0 => None,
        1 => Some(cursor.u32()?),
        _ => return Err(R0ArtifactError::Codec("invalid c_init tag".to_owned())),
    };
    let shape = FrozenR0Shape {
        records: cursor.u32()?,
        projections: cursor.u32()?,
        bf_atoms: cursor.u32()?,
        e4_atoms: cursor.u32()?,
        source_uses: cursor.u32()?,
        unique_sources: cursor.u32()?,
        windows: cursor.u16()?,
        max_relative_column: cursor.u16()?,
        coefficient_recipes: cursor.u32()?,
        immediates: cursor.u32()?,
    };
    let payload_sha256 = encode_sha256(&cursor.take_array::<32>()?);
    if !cursor.is_empty() {
        return Err(R0ArtifactError::TrailingBytes);
    }
    Ok((
        FrozenR0Coordinate {
            circuit,
            layer,
            trace_len,
            passes_per_invocation,
            program_words: words,
            term_count,
            binding,
            recipes,
            immediates,
            c_init,
            shape,
            payload_sha256,
        },
        RelativeOffsets {
            program_offset,
            program_len,
            binding_offset,
            binding_len,
            recipes_offset,
            recipes_len,
        },
    ))
}

pub fn r0_coordinate_payload_sha256(
    coordinate: &FrozenR0Coordinate,
) -> Result<String, R0ArtifactError> {
    payload_hash_for_coordinate(coordinate)
}

fn payload_hash_for_coordinate(coordinate: &FrozenR0Coordinate) -> Result<String, R0ArtifactError> {
    let mut frame = encode_coordinate_frame(coordinate)?;
    let payload_start = frame
        .len()
        .checked_sub(32)
        .ok_or(R0ArtifactError::LengthOverflow)?;
    frame[payload_start..].fill(0);
    sha256(&frame)
}

fn sha256(bytes: &[u8]) -> Result<String, R0ArtifactError> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| R0ArtifactError::Codec(format!("run sha256sum: {error}")))?;
    child
        .stdin
        .as_mut()
        .ok_or_else(|| R0ArtifactError::Codec("open sha256sum stdin".to_owned()))?
        .write_all(bytes)
        .map_err(|error| R0ArtifactError::Codec(format!("write sha256sum stdin: {error}")))?;
    let output = child
        .wait_with_output()
        .map_err(|error| R0ArtifactError::Codec(format!("wait for sha256sum: {error}")))?;
    if !output.status.success() {
        return Err(R0ArtifactError::Codec("sha256sum failed".to_owned()));
    }
    let text = String::from_utf8(output.stdout).map_err(|_| R0ArtifactError::InvalidUtf8)?;
    let hash = text.split_whitespace().next().unwrap_or_default();
    let _ = decode_sha256(hash)?;
    Ok(hash.to_owned())
}

fn decode_sha256(value: &str) -> Result<[u8; 32], R0ArtifactError> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(R0ArtifactError::NoncanonicalSha256);
    }
    let mut bytes = [0; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        bytes[index] = (hex_digit(pair[0])? << 4) | hex_digit(pair[1])?;
    }
    Ok(bytes)
}

fn encode_sha256(value: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for byte in value {
        output.push(HEX[usize::from(byte >> 4)] as char);
        output.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    output
}

fn hex_digit(byte: u8) -> Result<u8, R0ArtifactError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(R0ArtifactError::NoncanonicalSha256),
    }
}

fn push_string(output: &mut Vec<u8>, value: &str) -> Result<(), R0ArtifactError> {
    push_u32(output, u32_len(value.len())?);
    output.extend_from_slice(value.as_bytes());
    Ok(())
}

fn push_blob(output: &mut Vec<u8>, value: &[u8]) -> Result<(), R0ArtifactError> {
    push_u32(output, u32_len(value.len())?);
    output.extend_from_slice(value);
    Ok(())
}

fn push_u16(output: &mut Vec<u8>, value: u16) {
    output.extend_from_slice(&value.to_le_bytes());
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend_from_slice(&value.to_le_bytes());
}

fn push_u64(output: &mut Vec<u8>, value: u64) {
    output.extend_from_slice(&value.to_le_bytes());
}

fn u32_len(value: usize) -> Result<u32, R0ArtifactError> {
    u32::try_from(value).map_err(|_| R0ArtifactError::CapacityOverflow)
}

fn u16_len(value: usize) -> Result<u16, R0ArtifactError> {
    u16::try_from(value).map_err(|_| R0ArtifactError::CapacityOverflow)
}

fn usize_from_u32(value: u32) -> Result<usize, R0ArtifactError> {
    usize::try_from(value).map_err(|_| R0ArtifactError::LengthOverflow)
}

fn u64_from_usize(value: usize) -> Result<u64, R0ArtifactError> {
    u64::try_from(value).map_err(|_| R0ArtifactError::OffsetOverflow)
}

fn offset_add(base: usize, relative: usize) -> Result<u64, R0ArtifactError> {
    u64_from_usize(
        base.checked_add(relative)
            .ok_or(R0ArtifactError::OffsetOverflow)?,
    )
}

fn codec_error(error: impl core::fmt::Display) -> R0ArtifactError {
    R0ArtifactError::Codec(error.to_string())
}

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn is_empty(&self) -> bool {
        self.position == self.bytes.len()
    }

    fn remaining(&self) -> usize {
        self.bytes.len() - self.position
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], R0ArtifactError> {
        let end = self
            .position
            .checked_add(len)
            .ok_or(R0ArtifactError::LengthOverflow)?;
        let bytes = self
            .bytes
            .get(self.position..end)
            .ok_or(R0ArtifactError::Truncated)?;
        self.position = end;
        Ok(bytes)
    }

    fn take_array<const N: usize>(&mut self) -> Result<[u8; N], R0ArtifactError> {
        self.take(N)?
            .try_into()
            .map_err(|_| R0ArtifactError::Truncated)
    }

    fn u8(&mut self) -> Result<u8, R0ArtifactError> {
        Ok(self.take_array::<1>()?[0])
    }

    fn u16(&mut self) -> Result<u16, R0ArtifactError> {
        Ok(u16::from_le_bytes(self.take_array()?))
    }

    fn u32(&mut self) -> Result<u32, R0ArtifactError> {
        Ok(u32::from_le_bytes(self.take_array()?))
    }

    fn u64(&mut self) -> Result<u64, R0ArtifactError> {
        Ok(u64::from_le_bytes(self.take_array()?))
    }

    fn string(&mut self) -> Result<String, R0ArtifactError> {
        let len = usize_from_u32(self.u32()?)?;
        String::from_utf8(self.take(len)?.to_vec()).map_err(|_| R0ArtifactError::InvalidUtf8)
    }

    fn blob_with_offset(&mut self) -> Result<(usize, &'a [u8]), R0ArtifactError> {
        let len = usize_from_u32(self.u32()?)?;
        let offset = self.position;
        Ok((offset, self.take(len)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gkr_eval_ir::{ChallengeKey, ChallengePower};
    use gpu_gkr_compiler::backward::{
        LeanBoundColumn, LeanBoundWindow, LeanSourceSlot, WindowFamily,
    };

    fn fixture_bundle() -> FrozenR0BundleV1 {
        let mut coordinate = FrozenR0Coordinate {
            circuit: "fixture".to_owned(),
            layer: 0,
            trace_len: 1,
            passes_per_invocation: 1,
            program_words: vec![0, 0, SOURCE_NONE, 0],
            term_count: 1,
            binding: LeanSourceBinding {
                windows: vec![LeanBoundWindow {
                    family: WindowFamily::BaseLayerMemory,
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 0,
                    }],
                }],
                source_slots: vec![LeanSourceSlot {
                    window: 0,
                    column: 0,
                }],
            },
            recipes: vec![FrozenR0Recipe {
                products: vec![FrozenR0Product {
                    scalar: 1,
                    challenges: Vec::new(),
                    inits_and_teardowns_top_bits: Vec::new(),
                }],
            }],
            immediates: Vec::new(),
            c_init: None,
            shape: FrozenR0Shape {
                records: 1,
                projections: 1,
                bf_atoms: 1,
                e4_atoms: 0,
                source_uses: 1,
                unique_sources: 1,
                windows: 1,
                max_relative_column: 0,
                coefficient_recipes: 1,
                immediates: 0,
            },
            payload_sha256: "0".repeat(64),
        };
        coordinate.payload_sha256 = payload_hash_for_coordinate(&coordinate).unwrap();
        FrozenR0BundleV1 {
            magic: R0_BUNDLE_MAGIC,
            version: R0_BUNDLE_VERSION,
            layout_hashes: vec![R0LayoutHash {
                path: "fixture.json".to_owned(),
                sha256: "0".repeat(64),
            }],
            coordinates: vec![coordinate],
        }
    }

    fn product_class_bundle() -> FrozenR0BundleV1 {
        let mut bundle = fixture_bundle();
        let coordinate = &mut bundle.coordinates[0];
        coordinate.program_words = vec![
            0 << R0_CLASS_SHIFT,
            0,
            SOURCE_NONE,
            0,
            1 << R0_CLASS_SHIFT,
            0,
            SOURCE_NONE,
            0,
            2 << R0_CLASS_SHIFT,
            0,
            1,
            0,
            3 << R0_CLASS_SHIFT,
            0,
            1,
            0,
            4 << R0_CLASS_SHIFT,
            0,
            1,
            0,
        ];
        coordinate.term_count = 5;
        coordinate.binding.windows[0].columns.push(LeanBoundColumn {
            column: 1,
            source: 1,
        });
        coordinate.binding.source_slots.push(LeanSourceSlot {
            window: 0,
            column: 1,
        });
        coordinate.shape = FrozenR0Shape {
            records: 5,
            projections: 3,
            bf_atoms: 4,
            e4_atoms: 4,
            source_uses: 8,
            unique_sources: 2,
            windows: 1,
            max_relative_column: 1,
            coefficient_recipes: 1,
            immediates: 0,
        };
        coordinate.payload_sha256 = payload_hash_for_coordinate(coordinate).unwrap();
        bundle
    }

    fn rehash(coordinate: &mut FrozenR0Coordinate) {
        coordinate.payload_sha256 = payload_hash_for_coordinate(coordinate).unwrap();
    }

    fn add_to_u32_le(bytes: &mut [u8], offset: usize, amount: u32) {
        let old = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap());
        bytes[offset..offset + 4].copy_from_slice(&old.checked_add(amount).unwrap().to_le_bytes());
    }

    fn append_trailing_blob_byte(
        bytes: &mut Vec<u8>,
        coordinate_offset: usize,
        payload_offset: usize,
        payload_len: usize,
    ) {
        add_to_u32_le(bytes, payload_offset - 4, 1);
        add_to_u32_le(bytes, coordinate_offset - 4, 1);
        bytes.insert(payload_offset + payload_len, 0);
    }

    fn independent_sha256(bytes: &[u8]) -> String {
        let mut child = Command::new("sha256sum")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.as_mut().unwrap().write_all(bytes).unwrap();
        let output = child.wait_with_output().unwrap();
        String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    }

    #[test]
    fn cpu_r0_bundle_rejects_bad_magic_version_and_duplicate_coordinates() {
        let mut bundle = fixture_bundle();
        bundle.magic = *b"BADR0\0\0\0";
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::BadMagic)
        ));
        let mut bundle = fixture_bundle();
        bundle.version = R0_BUNDLE_VERSION + 1;
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::BadVersion(_))
        ));
        let mut bundle = fixture_bundle();
        bundle.coordinates.push(bundle.coordinates[0].clone());
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::DuplicateCoordinate(_))
        ));
    }

    #[test]
    fn cpu_r0_bundle_pins_wire_classes_and_source_coordinates() {
        assert_eq!(
            R0_CLASS_NAMES,
            [
                "C0LinearBf",
                "C0LinearE4",
                "C2ProductBfBf",
                "C2ProductBfE4",
                "C2ProductE4E4",
            ]
        );
        assert_eq!(pack_r0_source(63, 127).unwrap(), 0x1fff);
        assert_eq!(unpack_r0_source(0x1fff).unwrap(), (63, 127));
        assert!(pack_r0_source(64, 0).is_err());
        assert!(pack_r0_source(0, 128).is_err());
    }

    #[test]
    fn cpu_r0_bundle_pins_literal_and_banked_coefficient_ids() {
        assert_eq!(R0_COEFFICIENT_ONE, 0);
        assert_eq!(R0_COEFFICIENT_NEG_ONE, 1);
        assert_eq!(R0_COEFFICIENT_RESERVED, 2);
        assert_eq!(r0_banked_coefficient_index(2, 1).unwrap(), 0);
        assert!(r0_banked_coefficient_index(1, 1).is_err());
        assert!(r0_banked_coefficient_index(3, 1).is_err());
        assert!(fixture_bundle()
            .coordinates
            .iter()
            .all(|row| row.c_init.is_none()));
    }

    #[test]
    fn cpu_r0_archive_round_trips_and_reports_literal_offsets() {
        let expected = fixture_bundle();
        let bytes = encode_r0_bundle(&expected).unwrap();
        let inspected = inspect_r0_bundle(&bytes).unwrap();
        assert_eq!(inspected.bundle, expected);
        assert_eq!(inspected.offsets.len(), 1);
        let offsets = &inspected.offsets[0];
        let expected_program: Vec<u8> = expected.coordinates[0]
            .program_words
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect();
        assert_eq!(
            &bytes[offsets.program_offset as usize..][..offsets.program_len as usize],
            expected_program.as_slice(),
        );
        assert_eq!(encode_r0_bundle(&inspected.bundle).unwrap(), bytes);
        let mut with_trailer = bytes;
        with_trailer.push(0);
        assert!(matches!(
            decode_r0_bundle(&with_trailer),
            Err(R0ArtifactError::TrailingBytes)
        ));
    }

    #[test]
    fn cpu_r0_bundle_counts_all_product_class_atoms() {
        let bundle = product_class_bundle();
        assert_eq!(bundle.coordinates[0].shape.bf_atoms, 4);
        assert_eq!(bundle.coordinates[0].shape.e4_atoms, 4);
        validate_r0_bundle(&bundle).unwrap();
    }

    #[test]
    fn cpu_r0_coordinate_recomputes_distinct_source_role_projections() {
        let mut bundle = product_class_bundle();
        assert_eq!(bundle.coordinates[0].shape.projections, 3);
        bundle.coordinates[0].shape.projections = 4;
        rehash(&mut bundle.coordinates[0]);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::ShapeMismatch)
        ));
    }

    #[test]
    fn cpu_r0_bundle_offsets_slice_literal_bincode_payloads() {
        let bundle = fixture_bundle();
        let bytes = encode_r0_bundle(&bundle).unwrap();
        let offsets = &inspect_r0_bundle(&bytes).unwrap().offsets[0];
        let expected_binding = bincode_options()
            .serialize(&bundle.coordinates[0].binding)
            .unwrap();
        let expected_recipes = bincode_options()
            .serialize(&bundle.coordinates[0].recipes)
            .unwrap();
        assert_eq!(
            &bytes[offsets.binding_offset as usize..][..offsets.binding_len as usize],
            expected_binding.as_slice(),
        );
        assert_eq!(
            &bytes[offsets.recipes_offset as usize..][..offsets.recipes_len as usize],
            expected_recipes.as_slice(),
        );
    }

    #[test]
    fn cpu_r0_bundle_rejects_unsorted_and_malformed_coordinates() {
        let mut bundle = fixture_bundle();
        let mut later = bundle.coordinates[0].clone();
        later.layer = 1;
        rehash(&mut later);
        bundle.coordinates = vec![later, bundle.coordinates[0].clone()];
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::UnsortedCoordinate(_))
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].program_words.push(0);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::ProgramMisaligned)
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].program_words[0] = 5 << R0_CLASS_SHIFT;
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::InvalidClass(5))
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].program_words[1] = 1;
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::InvalidSourceBinding)
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].binding.source_slots[0].column = 128;
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::InvalidSourceCoordinate(_))
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].program_words[3] = 7;
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::ProgramMisaligned)
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].c_init = Some(0);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::CInitPresent)
        ));
    }

    #[test]
    fn cpu_r0_bundle_rejects_noncanonical_hash_capacity_and_payload_mutations() {
        let mut bundle = fixture_bundle();
        bundle.layout_hashes[0].sha256 = "A".repeat(64);
        assert!(matches!(
            encode_r0_bundle(&bundle),
            Err(R0ArtifactError::NoncanonicalSha256)
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0].shape.projections = (R0_DECLARED_PROJECTIONS + 1) as u32;
        rehash(&mut bundle.coordinates[0]);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::CapacityOverflow)
        ));

        let mut bundle = fixture_bundle();
        bundle.coordinates[0]
            .immediates
            .resize(gpu_gkr_compiler::backward::LEAN_MAX_IMMEDIATES + 1, 0);
        bundle.coordinates[0].shape.immediates = bundle.coordinates[0].immediates.len() as u32;
        rehash(&mut bundle.coordinates[0]);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::CapacityOverflow)
        ));

        let mut bundle = fixture_bundle();
        let replacement = if bundle.coordinates[0].payload_sha256.starts_with('f') {
            "e"
        } else {
            "f"
        };
        bundle.coordinates[0]
            .payload_sha256
            .replace_range(0..1, replacement);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::PayloadHashMismatch)
        ));
    }

    #[test]
    fn cpu_r0_bundle_rejects_invalid_utf8_and_trailing_bincode_sub_blobs() {
        let bundle = fixture_bundle();
        let bytes = encode_r0_bundle(&bundle).unwrap();

        let mut invalid_utf8 = bytes.clone();
        invalid_utf8[24] = 0xff;
        assert!(matches!(
            decode_r0_bundle(&invalid_utf8),
            Err(R0ArtifactError::InvalidUtf8)
        ));

        let offsets = &inspect_r0_bundle(&bytes).unwrap().offsets[0];
        let mut binding_trailer = bytes.clone();
        append_trailing_blob_byte(
            &mut binding_trailer,
            offsets.coordinate_offset as usize,
            offsets.binding_offset as usize,
            offsets.binding_len as usize,
        );
        assert!(matches!(
            decode_r0_bundle(&binding_trailer),
            Err(R0ArtifactError::Codec(_))
        ));

        let mut recipes_trailer = bytes;
        append_trailing_blob_byte(
            &mut recipes_trailer,
            offsets.coordinate_offset as usize,
            offsets.recipes_offset as usize,
            offsets.recipes_len as usize,
        );
        assert!(matches!(
            decode_r0_bundle(&recipes_trailer),
            Err(R0ArtifactError::Codec(_))
        ));
    }

    #[test]
    fn cpu_r0_bundle_canonical_challenges_and_hash_preimage_are_literal() {
        let mut bundle = fixture_bundle();
        bundle.coordinates[0].recipes[0].products[0].challenges = vec![FrozenR0Challenge {
            reference: ChallengeRef {
                key: ChallengeKey::LookupAdditive,
                power: ChallengePower::Static(1),
            },
        }];
        rehash(&mut bundle.coordinates[0]);
        assert!(matches!(
            validate_r0_bundle(&bundle),
            Err(R0ArtifactError::NonCanonicalChallenge)
        ));

        let mut bundle = fixture_bundle();
        let repeated = ChallengeRef {
            key: ChallengeKey::LookupMultiplicative,
            power: ChallengePower::Static(2),
        };
        let second = ChallengeRef {
            key: ChallengeKey::ClaimBatching,
            power: ChallengePower::One,
        };
        bundle.coordinates[0].recipes[0].products[0].challenges = vec![
            FrozenR0Challenge {
                reference: repeated.clone(),
            },
            FrozenR0Challenge {
                reference: second.clone(),
            },
            FrozenR0Challenge {
                reference: repeated.clone(),
            },
        ];
        rehash(&mut bundle.coordinates[0]);
        let decoded = decode_r0_bundle(&encode_r0_bundle(&bundle).unwrap()).unwrap();
        let actual = &decoded.coordinates[0].recipes[0].products[0].challenges;
        assert_eq!(actual.len(), 3);
        assert_eq!(actual[0].reference, repeated);
        assert_eq!(actual[1].reference, second);
        assert_eq!(actual[2].reference, actual[0].reference);

        let encoded = encode_r0_bundle(&bundle).unwrap();
        let offsets = &inspect_r0_bundle(&encoded).unwrap().offsets[0];
        let mut preimage = encoded[offsets.coordinate_offset as usize..]
            [..offsets.coordinate_len as usize]
            .to_vec();
        let payload_start = preimage.len() - 32;
        preimage[payload_start..].fill(0);
        assert_eq!(
            independent_sha256(&preimage),
            bundle.coordinates[0].payload_sha256
        );
    }
}
