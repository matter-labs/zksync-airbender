use bincode::Options;
use serde::{Deserialize, Serialize};

use crate::abi::WindowInstruction;

pub const ARTIFACT_MAGIC: [u8; 8] = *b"WGKRW3\0\0";
pub const ARTIFACT_VERSION: u32 = 1;
pub const SOURCE_NONE: u16 = u16::MAX;
pub const SOURCE_WINDOW_COLUMNS: u16 = 128;
pub static ADD_SUB_LAYER0_BYTES: &[u8] = include_bytes!("../artifacts/add_sub_layer0.bin");

const MAX_COEFFICIENTS: u32 = u16::MAX as u32 + 1;
const MAX_WINDOWS: usize = 64;
const IMMEDIATE_RESERVED: u16 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum WindowClass {
    LinearBf = 0,
    LinearE4 = 1,
    ProductBfBf = 2,
    ProductBfE4 = 3,
    ProductE4E4 = 5,
    GroupBf = 6,
    GroupE4 = 7,
}

impl TryFrom<u8> for WindowClass {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::LinearBf),
            1 => Ok(Self::LinearE4),
            2 => Ok(Self::ProductBfBf),
            3 => Ok(Self::ProductBfE4),
            5 => Ok(Self::ProductE4E4),
            6 => Ok(Self::GroupBf),
            7 => Ok(Self::GroupE4),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FrozenField {
    Base,
    Ext,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FrozenWindowFamily {
    BaseLayerMemory,
    BaseLayerWitness,
    Setup,
    Scratch,
    LayerOutput { layer: u32, ext: bool },
    CacheOutput { layer: u32, ext: bool },
    VirtualSetup { kind: u8 },
}

impl FrozenWindowFamily {
    pub fn is_procedural(self) -> bool {
        matches!(self, Self::VirtualSetup { .. })
    }

    fn expected_field(self) -> FrozenField {
        match self {
            Self::LayerOutput { ext: true, .. } | Self::CacheOutput { ext: true, .. } => {
                FrozenField::Ext
            }
            _ => FrozenField::Base,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenBoundColumn {
    pub column: u32,
    pub source: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenWindow {
    pub family: FrozenWindowFamily,
    pub first_column: u32,
    pub field: FrozenField,
    pub columns: Vec<FrozenBoundColumn>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenSourceSlot {
    pub window: u8,
    pub column: u16,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenArtifact {
    pub magic: [u8; 8],
    pub version: u32,
    pub layer: u32,
    pub term_count: u32,
    pub record_count: u32,
    pub coefficient_count: u32,
    pub c_init_coeff: Option<u32>,
    pub program: Vec<WindowInstruction>,
    pub immediates: Vec<u32>,
    pub windows: Vec<FrozenWindow>,
    pub source_slots: Vec<FrozenSourceSlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WindowTerm {
    pub class: WindowClass,
    pub coefficient: u16,
    pub source_a: u16,
    pub source_b: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WindowAtom {
    Term(WindowTerm),
    GroupBf { core: u16, members: Vec<WindowTerm> },
    GroupE4 { core: u16, members: Vec<WindowTerm> },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProgramStats {
    pub terms: u32,
    pub records: u32,
    pub groups: u32,
    pub bf_groups: u32,
    pub e4_groups: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArtifactError {
    BadMagic,
    UnsupportedVersion { version: u32 },
    WrongLayer { layer: u32 },
    InvalidCoefficientCount { count: u32 },
    CInitOutOfRange { coefficient: u32 },
    RecordCount { declared: u32, decoded: u32 },
    TermCount { declared: u32, decoded: u32 },
    InvalidClass { record: u32, class: u8 },
    CoefficientOutOfRange { record: u32, coefficient: u16 },
    ImmediateOutOfRange { record: u32, immediate: u16 },
    SourceOutOfRange { record: u32, source: u16 },
    SourceBMustBeNone { record: u32 },
    SourceBMissing { record: u32 },
    MalformedGroup { record: u32 },
    GroupHeaderPayloadNonZero { record: u32 },
    GroupMemberClassMismatch { header: u32, record: u32 },
    E4GroupImmediateOutOfRange { record: u32, immediate: u16 },
    FieldClassMismatch { record: u32 },
    TooManyWindows { count: usize },
    NonCanonicalWindow { window: usize },
    InvalidWindowField { window: usize },
    InvalidProceduralKind { window: usize, kind: u8 },
    BoundSourceOutOfRange { window: usize, source: u32 },
    InvalidSourceBinding { source: usize },
    Decode(String),
}

impl core::fmt::Display for ArtifactError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ArtifactError {}

fn bincode_options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
}

pub fn encode_artifact(value: &FrozenArtifact) -> Result<Vec<u8>, ArtifactError> {
    validate_artifact(value)?;
    bincode_options()
        .serialize(value)
        .map_err(|error| ArtifactError::Decode(error.to_string()))
}

pub fn decode_artifact(bytes: &[u8]) -> Result<FrozenArtifact, ArtifactError> {
    let value: FrozenArtifact = bincode_options()
        .deserialize(bytes)
        .map_err(|error| ArtifactError::Decode(error.to_string()))?;
    validate_artifact(&value)?;
    Ok(value)
}

pub fn validate_artifact(value: &FrozenArtifact) -> Result<ProgramStats, ArtifactError> {
    if value.magic != ARTIFACT_MAGIC {
        return Err(ArtifactError::BadMagic);
    }
    if value.version != ARTIFACT_VERSION {
        return Err(ArtifactError::UnsupportedVersion {
            version: value.version,
        });
    }
    if value.layer != 0 {
        return Err(ArtifactError::WrongLayer { layer: value.layer });
    }
    if !(2..=MAX_COEFFICIENTS).contains(&value.coefficient_count) {
        return Err(ArtifactError::InvalidCoefficientCount {
            count: value.coefficient_count,
        });
    }
    if let Some(coefficient) = value.c_init_coeff {
        if coefficient >= value.coefficient_count {
            return Err(ArtifactError::CInitOutOfRange { coefficient });
        }
    }
    validate_windows(value)?;
    let (_, stats) = decode_program(value)?;
    Ok(stats)
}

pub fn decode_program(
    artifact: &FrozenArtifact,
) -> Result<(Vec<WindowAtom>, ProgramStats), ArtifactError> {
    let decoded_records = artifact.program.len() as u32;
    if decoded_records != artifact.record_count {
        return Err(ArtifactError::RecordCount {
            declared: artifact.record_count,
            decoded: decoded_records,
        });
    }

    let mut atoms = Vec::new();
    let mut stats = ProgramStats {
        records: decoded_records,
        ..ProgramStats::default()
    };
    let mut record = 0usize;
    while record < decoded_records as usize {
        let instruction = artifact.program[record];
        let class = decode_class(instruction.term_class, record as u32)?;
        let coefficient = instruction.factor;
        if !matches!(class, WindowClass::GroupBf | WindowClass::GroupE4) {
            let term = decode_term(
                artifact,
                class,
                coefficient,
                instruction,
                record as u32,
                false,
            )?;
            atoms.push(WindowAtom::Term(term));
            stats.terms += 1;
            record += 1;
            continue;
        }

        if coefficient < 2 || u32::from(coefficient) >= artifact.coefficient_count {
            return Err(ArtifactError::CoefficientOutOfRange {
                record: record as u32,
                coefficient,
            });
        }
        let member_count = match class {
            WindowClass::GroupBf => {
                if instruction.source_b != 0 {
                    return Err(ArtifactError::GroupHeaderPayloadNonZero {
                        record: record as u32,
                    });
                }
                usize::from(instruction.source_a)
            }
            WindowClass::GroupE4 => {
                if instruction.source_a != 0 || instruction.source_b != 0 {
                    return Err(ArtifactError::GroupHeaderPayloadNonZero {
                        record: record as u32,
                    });
                }
                2
            }
            _ => unreachable!("non-group records are handled above"),
        };
        if member_count < 2 || record + member_count >= decoded_records as usize {
            return Err(ArtifactError::MalformedGroup {
                record: record as u32,
            });
        }
        let mut members = Vec::with_capacity(member_count);
        for member_offset in 1..=member_count {
            let member_record = record + member_offset;
            let member_instruction = artifact.program[member_record];
            let member_class = decode_class(member_instruction.term_class, member_record as u32)?;
            let immediate = member_instruction.factor;
            if matches!(member_class, WindowClass::GroupBf | WindowClass::GroupE4) {
                return Err(ArtifactError::MalformedGroup {
                    record: record as u32,
                });
            }
            let member_matches_group = match class {
                WindowClass::GroupBf => matches!(
                    member_class,
                    WindowClass::LinearBf | WindowClass::ProductBfBf
                ),
                WindowClass::GroupE4 => matches!(
                    member_class,
                    WindowClass::LinearE4 | WindowClass::ProductBfE4 | WindowClass::ProductE4E4
                ),
                _ => unreachable!("class is a group header"),
            };
            if !member_matches_group {
                return Err(ArtifactError::GroupMemberClassMismatch {
                    header: record as u32,
                    record: member_record as u32,
                });
            }
            match class {
                WindowClass::GroupBf => {
                    validate_immediate(artifact, immediate, member_record as u32)?;
                }
                WindowClass::GroupE4 if immediate >= IMMEDIATE_RESERVED => {
                    return Err(ArtifactError::E4GroupImmediateOutOfRange {
                        record: member_record as u32,
                        immediate,
                    });
                }
                WindowClass::GroupE4 => {}
                _ => unreachable!("class is a group header"),
            }
            members.push(decode_term(
                artifact,
                member_class,
                immediate,
                member_instruction,
                member_record as u32,
                true,
            )?);
        }
        stats.groups += 1;
        stats.terms += member_count as u32;
        match class {
            WindowClass::GroupBf => {
                stats.bf_groups += 1;
                atoms.push(WindowAtom::GroupBf {
                    core: coefficient,
                    members,
                });
            }
            WindowClass::GroupE4 => {
                stats.e4_groups += 1;
                atoms.push(WindowAtom::GroupE4 {
                    core: coefficient,
                    members,
                });
            }
            _ => unreachable!("class is a group header"),
        }
        record += member_count + 1;
    }

    if stats.terms != artifact.term_count {
        return Err(ArtifactError::TermCount {
            declared: artifact.term_count,
            decoded: stats.terms,
        });
    }
    Ok((atoms, stats))
}

fn validate_windows(artifact: &FrozenArtifact) -> Result<(), ArtifactError> {
    if artifact.windows.len() > MAX_WINDOWS {
        return Err(ArtifactError::TooManyWindows {
            count: artifact.windows.len(),
        });
    }
    let mut source_occurrences = vec![0u8; artifact.source_slots.len()];
    for (window_index, window) in artifact.windows.iter().enumerate() {
        if window.field != window.family.expected_field() {
            return Err(ArtifactError::InvalidWindowField {
                window: window_index,
            });
        }
        if let FrozenWindowFamily::VirtualSetup { kind } = window.family {
            if kind >= 4 {
                return Err(ArtifactError::InvalidProceduralKind {
                    window: window_index,
                    kind,
                });
            }
        }
        if window_index > 0 {
            let previous = &artifact.windows[window_index - 1];
            if (window.family, window.first_column) <= (previous.family, previous.first_column)
                || (window.family == previous.family
                    && window.first_column
                        < previous.first_column + u32::from(SOURCE_WINDOW_COLUMNS))
            {
                return Err(ArtifactError::NonCanonicalWindow {
                    window: window_index,
                });
            }
        }
        let mut previous_column = None;
        for column in &window.columns {
            let in_window = column.column >= window.first_column
                && column.column < window.first_column + u32::from(SOURCE_WINDOW_COLUMNS);
            if !in_window || previous_column.is_some_and(|previous| column.column <= previous) {
                return Err(ArtifactError::NonCanonicalWindow {
                    window: window_index,
                });
            }
            let source = column.source as usize;
            let Some(occurrences) = source_occurrences.get_mut(source) else {
                return Err(ArtifactError::BoundSourceOutOfRange {
                    window: window_index,
                    source: column.source,
                });
            };
            *occurrences = occurrences.saturating_add(1);
            previous_column = Some(column.column);
        }
    }

    for (source, slot) in artifact.source_slots.iter().enumerate() {
        let Some(window) = artifact.windows.get(usize::from(slot.window)) else {
            return Err(ArtifactError::InvalidSourceBinding { source });
        };
        if slot.column >= SOURCE_WINDOW_COLUMNS {
            return Err(ArtifactError::InvalidSourceBinding { source });
        }
        let absolute = window.first_column + u32::from(slot.column);
        let resolved = window
            .columns
            .binary_search_by_key(&absolute, |column| column.column)
            .ok()
            .and_then(|index| window.columns.get(index))
            .map(|column| column.source as usize);
        if resolved != Some(source) || source_occurrences[source] != 1 {
            return Err(ArtifactError::InvalidSourceBinding { source });
        }
    }
    Ok(())
}

fn decode_term(
    artifact: &FrozenArtifact,
    class: WindowClass,
    coefficient: u16,
    instruction: WindowInstruction,
    record: u32,
    grouped: bool,
) -> Result<WindowTerm, ArtifactError> {
    if !grouped && u32::from(coefficient) >= artifact.coefficient_count {
        return Err(ArtifactError::CoefficientOutOfRange {
            record,
            coefficient,
        });
    }
    validate_source(artifact, instruction.source_a, record)?;
    match class {
        WindowClass::LinearBf | WindowClass::LinearE4 => {
            if instruction.source_b != SOURCE_NONE {
                return Err(ArtifactError::SourceBMustBeNone { record });
            }
        }
        WindowClass::ProductBfBf | WindowClass::ProductBfE4 | WindowClass::ProductE4E4 => {
            if instruction.source_b == SOURCE_NONE {
                return Err(ArtifactError::SourceBMissing { record });
            }
            validate_source(artifact, instruction.source_b, record)?;
        }
        WindowClass::GroupBf | WindowClass::GroupE4 => {
            unreachable!("group headers are handled by decode_program")
        }
    }
    validate_term_fields(
        artifact,
        class,
        instruction.source_a,
        instruction.source_b,
        record,
    )?;
    Ok(WindowTerm {
        class,
        coefficient,
        source_a: instruction.source_a,
        source_b: instruction.source_b,
    })
}

fn validate_source(
    artifact: &FrozenArtifact,
    source: u16,
    record: u32,
) -> Result<(), ArtifactError> {
    if usize::from(source) >= artifact.source_slots.len() {
        return Err(ArtifactError::SourceOutOfRange { record, source });
    }
    Ok(())
}

fn source_field(artifact: &FrozenArtifact, source: u16) -> FrozenField {
    let slot = artifact.source_slots[usize::from(source)];
    artifact.windows[usize::from(slot.window)].field
}

fn validate_term_fields(
    artifact: &FrozenArtifact,
    class: WindowClass,
    source_a: u16,
    source_b: u16,
    record: u32,
) -> Result<(), ArtifactError> {
    let field_a = source_field(artifact, source_a);
    let fields_match = match class {
        WindowClass::LinearBf => field_a == FrozenField::Base,
        WindowClass::LinearE4 => field_a == FrozenField::Ext,
        WindowClass::ProductBfBf => {
            field_a == FrozenField::Base && source_field(artifact, source_b) == FrozenField::Base
        }
        WindowClass::ProductBfE4 => {
            field_a == FrozenField::Base && source_field(artifact, source_b) == FrozenField::Ext
        }
        WindowClass::ProductE4E4 => {
            field_a == FrozenField::Ext && source_field(artifact, source_b) == FrozenField::Ext
        }
        WindowClass::GroupBf | WindowClass::GroupE4 => false,
    };
    if !fields_match {
        return Err(ArtifactError::FieldClassMismatch { record });
    }
    Ok(())
}

fn validate_immediate(
    artifact: &FrozenArtifact,
    immediate: u16,
    record: u32,
) -> Result<(), ArtifactError> {
    if immediate >= IMMEDIATE_RESERVED
        && usize::from(immediate - IMMEDIATE_RESERVED) >= artifact.immediates.len()
    {
        return Err(ArtifactError::ImmediateOutOfRange { record, immediate });
    }
    Ok(())
}

fn decode_class(value: u16, record: u32) -> Result<WindowClass, ArtifactError> {
    let class = u8::try_from(value)
        .ok()
        .and_then(|class| WindowClass::try_from(class).ok())
        .ok_or(ArtifactError::InvalidClass {
            record,
            class: value as u8,
        })?;
    Ok(class)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_low_bit_selects_the_result_field() {
        assert_eq!(WindowClass::LinearBf as u16, 0);
        assert_eq!(WindowClass::LinearE4 as u16, 1);
        assert_eq!(WindowClass::ProductBfBf as u16, 2);
        assert_eq!(WindowClass::ProductBfE4 as u16, 3);
        assert_eq!(WindowClass::ProductE4E4 as u16, 5);
        assert_eq!(WindowClass::GroupBf as u16, 6);
        assert_eq!(WindowClass::GroupE4 as u16, 7);
        for class in [
            WindowClass::LinearBf,
            WindowClass::ProductBfBf,
            WindowClass::GroupBf,
        ] {
            assert_eq!((class as u16) & 1, 0);
        }
        for class in [
            WindowClass::LinearE4,
            WindowClass::ProductBfE4,
            WindowClass::ProductE4E4,
            WindowClass::GroupE4,
        ] {
            assert_eq!((class as u16) & 1, 1);
        }
    }

    fn instruction(
        class: WindowClass,
        factor: u16,
        source_a: u16,
        source_b: u16,
    ) -> WindowInstruction {
        WindowInstruction {
            term_class: class as u16,
            factor,
            source_a,
            source_b,
        }
    }

    fn valid_artifact() -> FrozenArtifact {
        FrozenArtifact {
            magic: ARTIFACT_MAGIC,
            version: ARTIFACT_VERSION,
            layer: 0,
            term_count: 1,
            record_count: 1,
            coefficient_count: 2,
            c_init_coeff: None,
            program: vec![instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE)],
            immediates: Vec::new(),
            windows: vec![FrozenWindow {
                family: FrozenWindowFamily::BaseLayerMemory,
                first_column: 0,
                field: FrozenField::Base,
                columns: vec![FrozenBoundColumn {
                    column: 0,
                    source: 0,
                }],
            }],
            source_slots: vec![FrozenSourceSlot {
                window: 0,
                column: 0,
            }],
        }
    }

    fn add_ext_source(artifact: &mut FrozenArtifact) {
        artifact.windows.push(FrozenWindow {
            family: FrozenWindowFamily::LayerOutput {
                layer: 0,
                ext: true,
            },
            first_column: 0,
            field: FrozenField::Ext,
            columns: vec![FrozenBoundColumn {
                column: 0,
                source: 1,
            }],
        });
        artifact.source_slots.push(FrozenSourceSlot {
            window: 1,
            column: 0,
        });
    }

    #[test]
    fn singleton_artifact_round_trips() {
        let artifact = valid_artifact();
        let bytes = encode_artifact(&artifact).unwrap();
        assert_eq!(decode_artifact(&bytes).unwrap(), artifact);
    }

    #[test]
    fn bf_group_uses_immediate_ids_for_members() {
        let mut artifact = valid_artifact();
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.program = vec![
            instruction(WindowClass::GroupBf, 2, 2, 0),
            instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
            instruction(WindowClass::ProductBfBf, 1, 0, 0),
        ];
        let stats = validate_artifact(&artifact).unwrap();
        assert_eq!(stats.terms, 2);
        assert_eq!(stats.bf_groups, 1);
        assert_eq!(stats.e4_groups, 0);
    }

    #[test]
    fn e4_group_is_an_implicit_pair_with_sign_immediates() {
        let mut artifact = valid_artifact();
        add_ext_source(&mut artifact);
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.program = vec![
            instruction(WindowClass::GroupE4, 2, 0, 0),
            instruction(WindowClass::LinearE4, 0, 1, SOURCE_NONE),
            instruction(WindowClass::ProductBfE4, 1, 0, 1),
        ];
        let stats = validate_artifact(&artifact).unwrap();
        assert_eq!(stats.terms, 2);
        assert_eq!(stats.bf_groups, 0);
        assert_eq!(stats.e4_groups, 1);
    }

    #[test]
    fn product_bf_e4_must_be_encoded_bf_first() {
        let mut artifact = valid_artifact();
        add_ext_source(&mut artifact);
        artifact.program = vec![instruction(WindowClass::ProductBfE4, 0, 1, 0)];
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::FieldClassMismatch { .. })
        ));
    }

    #[test]
    fn bf_group_rejects_e4_members() {
        let mut artifact = valid_artifact();
        add_ext_source(&mut artifact);
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.program = vec![
            instruction(WindowClass::GroupBf, 2, 2, 0),
            instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
            instruction(WindowClass::LinearE4, 0, 1, SOURCE_NONE),
        ];
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::GroupMemberClassMismatch { .. })
        ));
    }

    #[test]
    fn e4_group_rejects_banked_immediates() {
        let mut artifact = valid_artifact();
        add_ext_source(&mut artifact);
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.immediates.push(7);
        artifact.program = vec![
            instruction(WindowClass::GroupE4, 2, 0, 0),
            instruction(WindowClass::LinearE4, 2, 1, SOURCE_NONE),
            instruction(WindowClass::LinearE4, 0, 1, SOURCE_NONE),
        ];
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::E4GroupImmediateOutOfRange { .. })
        ));
    }

    #[test]
    fn e4_group_header_has_no_payload() {
        let mut artifact = valid_artifact();
        artifact.record_count = 1;
        artifact.coefficient_count = 3;
        artifact.program = vec![instruction(WindowClass::GroupE4, 2, 2, 0)];
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::GroupHeaderPayloadNonZero { .. })
        ));
    }

    #[test]
    fn bad_magic_is_rejected() {
        let mut artifact = valid_artifact();
        artifact.magic[0] ^= 1;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::BadMagic)
        ));
    }

    #[test]
    fn bad_version_is_rejected() {
        let mut artifact = valid_artifact();
        artifact.version += 1;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::UnsupportedVersion { .. })
        ));
    }

    #[test]
    fn declared_record_count_must_match_stream() {
        let mut artifact = valid_artifact();
        artifact.record_count = 2;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::RecordCount { .. })
        ));
    }

    #[test]
    fn source_index_must_exist() {
        let mut artifact = valid_artifact();
        artifact.program[0].source_a = 1;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::SourceOutOfRange { .. })
        ));
    }

    #[test]
    fn singleton_coefficient_must_exist() {
        let mut artifact = valid_artifact();
        artifact.program[0].factor = 2;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::CoefficientOutOfRange { .. })
        ));
    }

    #[test]
    fn group_member_immediate_must_exist() {
        let mut artifact = valid_artifact();
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.program = vec![
            instruction(WindowClass::GroupBf, 2, 2, 0),
            instruction(WindowClass::LinearBf, 2, 0, SOURCE_NONE),
            instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
        ];
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::ImmediateOutOfRange { .. })
        ));
    }

    #[test]
    fn unknown_class_is_rejected() {
        let mut artifact = valid_artifact();
        artifact.program[0].term_class = 4;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::InvalidClass { .. })
        ));
    }

    #[test]
    fn linear_record_requires_source_none() {
        let mut artifact = valid_artifact();
        artifact.program[0].source_b = 0;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::SourceBMustBeNone { .. })
        ));
    }

    #[test]
    fn truncated_group_is_rejected() {
        let mut artifact = valid_artifact();
        artifact.record_count = 1;
        artifact.program = vec![instruction(WindowClass::GroupBf, 2, 2, 0)];
        artifact.coefficient_count = 3;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::MalformedGroup { .. })
        ));
    }

    #[test]
    fn window_columns_must_be_strictly_sorted() {
        let mut artifact = valid_artifact();
        artifact.windows[0].columns.push(FrozenBoundColumn {
            column: 0,
            source: 0,
        });
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::NonCanonicalWindow { .. })
        ));
    }

    #[test]
    fn trailing_encoded_bytes_are_rejected() {
        let mut bytes = encode_artifact(&valid_artifact()).unwrap();
        bytes.push(0);
        assert!(matches!(
            decode_artifact(&bytes),
            Err(ArtifactError::Decode(_))
        ));
    }

    #[test]
    fn embedded_add_sub_layer_zero_is_valid_on_the_default_path() {
        let artifact = decode_artifact(ADD_SUB_LAYER0_BYTES).unwrap();
        assert_eq!(artifact.layer, 0);
        assert_eq!(artifact.term_count, 150);
        assert_eq!(artifact.record_count, 175);
    }
}
