use bincode::Options;
use serde::{Deserialize, Serialize};

use crate::abi::WindowInstruction;

pub const ARTIFACT_MAGIC: [u8; 8] = *b"WGKRW3\0\0";
pub const ARTIFACT_VERSION: u32 = 1;
pub const SOURCE_NONE: u16 = u16::MAX;
pub const SOURCE_WINDOW_COLUMNS: u16 = 128;
pub const SOURCE_COLUMN_BITS: u32 = 7;
pub const SOURCE_COLUMN_MASK: u16 = (1 << SOURCE_COLUMN_BITS) - 1;
pub const SOURCE_WINDOW_BITS: u32 = 6;
pub const SOURCE_COORDINATE_MASK: u16 =
    (((1 << SOURCE_WINDOW_BITS) - 1) << SOURCE_COLUMN_BITS) | SOURCE_COLUMN_MASK;
pub const REDUCE_AFTER: u16 = 1 << 15;
pub const IMMEDIATE_ID_MASK: u16 = REDUCE_AFTER - 1;
pub const MAX_LAZY_PRODUCTS_PER_REDUCTION: u16 = 4;
pub const GROUP_HAS_PRODUCT: u16 = 1 << 15;
pub const GROUP_PRODUCT_PREFIX_COUNT_MASK: u16 = GROUP_HAS_PRODUCT - 1;
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
    LinearBfProceduralA = 4,
    ProductE4E4 = 5,
    GroupBf = 6,
    GroupE4 = 7,
    ProductBfBfProceduralB = 8,
}

impl TryFrom<u8> for WindowClass {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::LinearBf),
            1 => Ok(Self::LinearE4),
            2 => Ok(Self::ProductBfBf),
            3 => Ok(Self::ProductBfE4),
            4 => Ok(Self::LinearBfProceduralA),
            5 => Ok(Self::ProductE4E4),
            6 => Ok(Self::GroupBf),
            7 => Ok(Self::GroupE4),
            8 => Ok(Self::ProductBfBfProceduralB),
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
    GroupBf {
        core: u16,
        lazy_product_count: u16,
        members: Vec<WindowTerm>,
    },
    GroupE4 {
        core: u16,
        members: Vec<WindowTerm>,
    },
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
    UnsupportedVersion {
        version: u32,
    },
    WrongLayer {
        layer: u32,
    },
    InvalidCoefficientCount {
        count: u32,
    },
    CInitOutOfRange {
        coefficient: u32,
    },
    RecordCount {
        declared: u32,
        decoded: u32,
    },
    TermCount {
        declared: u32,
        decoded: u32,
    },
    InvalidClass {
        record: u32,
        class: u8,
    },
    CoefficientOutOfRange {
        record: u32,
        coefficient: u16,
    },
    ImmediateOutOfRange {
        record: u32,
        immediate: u16,
    },
    SourceOutOfRange {
        record: u32,
        source: u16,
    },
    DirectProceduralSource {
        record: u32,
        source: u16,
    },
    ProceduralKindUnavailable {
        record: u32,
        kind: u16,
    },
    SourceBMustBeNone {
        record: u32,
    },
    SourceBMissing {
        record: u32,
    },
    MalformedGroup {
        record: u32,
    },
    GroupHeaderPayloadNonZero {
        record: u32,
    },
    InvalidLazyProductCount {
        record: u32,
        count: u16,
        arity: u16,
    },
    LazyProductFlagMissing {
        record: u32,
        count: u16,
    },
    GroupProductFlagMismatch {
        header: u32,
        encoded: bool,
        products: u16,
    },
    InvalidEagerProductLayout {
        header: u32,
    },
    LazyProductPrefixClass {
        header: u32,
        record: u32,
    },
    LazyProductTailClass {
        header: u32,
        record: u32,
    },
    LazyReductionFlagOutsidePrefix {
        header: u32,
        record: u32,
    },
    LazyReductionWindowTooLong {
        header: u32,
        record: u32,
    },
    GroupMemberClassMismatch {
        header: u32,
        record: u32,
    },
    E4GroupImmediateOutOfRange {
        record: u32,
        immediate: u16,
    },
    FieldClassMismatch {
        record: u32,
    },
    TooManyWindows {
        count: usize,
    },
    NonCanonicalWindow {
        window: usize,
    },
    InvalidWindowField {
        window: usize,
    },
    InvalidProceduralKind {
        window: usize,
        kind: u8,
    },
    BoundSourceOutOfRange {
        window: usize,
        source: u32,
    },
    InvalidSourceBinding {
        source: usize,
    },
    SourceCoordinateOutOfRange {
        window: u8,
        column: u16,
    },
    InvalidSourceCoordinate {
        source: u16,
    },
    Decode(String),
}

impl core::fmt::Display for ArtifactError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ArtifactError {}

pub fn encode_source_coordinate(window: u8, column: u16) -> Result<u16, ArtifactError> {
    if u32::from(window) >= 1 << SOURCE_WINDOW_BITS || column >= SOURCE_WINDOW_COLUMNS {
        return Err(ArtifactError::SourceCoordinateOutOfRange { window, column });
    }
    Ok((u16::from(window) << SOURCE_COLUMN_BITS) | column)
}

pub fn decode_source_coordinate(source: u16) -> Result<(u8, u16), ArtifactError> {
    if source == SOURCE_NONE || source & !SOURCE_COORDINATE_MASK != 0 {
        return Err(ArtifactError::InvalidSourceCoordinate { source });
    }
    Ok((
        (source >> SOURCE_COLUMN_BITS) as u8,
        source & SOURCE_COLUMN_MASK,
    ))
}

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
        let (member_count, lazy_product_count, has_product) = match class {
            WindowClass::GroupBf => (
                usize::from(instruction.source_a),
                instruction.source_b & GROUP_PRODUCT_PREFIX_COUNT_MASK,
                instruction.source_b & GROUP_HAS_PRODUCT != 0,
            ),
            WindowClass::GroupE4 => {
                if instruction.source_a != 0
                    || instruction.source_b & GROUP_PRODUCT_PREFIX_COUNT_MASK != 0
                {
                    return Err(ArtifactError::GroupHeaderPayloadNonZero {
                        record: record as u32,
                    });
                }
                (2, 0, instruction.source_b & GROUP_HAS_PRODUCT != 0)
            }
            _ => unreachable!("non-group records are handled above"),
        };
        if member_count < 2 || record + member_count >= decoded_records as usize {
            return Err(ArtifactError::MalformedGroup {
                record: record as u32,
            });
        }
        if usize::from(lazy_product_count) > member_count {
            return Err(ArtifactError::InvalidLazyProductCount {
                record: record as u32,
                count: lazy_product_count,
                arity: member_count as u16,
            });
        }
        if class == WindowClass::GroupBf && !has_product && lazy_product_count != 0 {
            return Err(ArtifactError::LazyProductFlagMissing {
                record: record as u32,
                count: lazy_product_count,
            });
        }
        let mut members = Vec::with_capacity(member_count);
        let mut products_since_reduction = 0u16;
        for member_offset in 1..=member_count {
            let member_record = record + member_offset;
            let member_instruction = artifact.program[member_record];
            let member_class = decode_class(member_instruction.term_class, member_record as u32)?;
            let reduction_boundary = member_instruction.factor & REDUCE_AFTER != 0;
            let in_lazy_prefix = class == WindowClass::GroupBf
                && lazy_product_count >= 2
                && member_offset <= usize::from(lazy_product_count);
            let immediate = if class == WindowClass::GroupBf {
                member_instruction.factor & IMMEDIATE_ID_MASK
            } else {
                member_instruction.factor
            };
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
            if in_lazy_prefix {
                if member_class != WindowClass::ProductBfBf {
                    return Err(ArtifactError::LazyProductPrefixClass {
                        header: record as u32,
                        record: member_record as u32,
                    });
                }
                products_since_reduction += 1;
                if products_since_reduction > MAX_LAZY_PRODUCTS_PER_REDUCTION {
                    return Err(ArtifactError::LazyReductionWindowTooLong {
                        header: record as u32,
                        record: member_record as u32,
                    });
                }
                if member_offset == usize::from(lazy_product_count) && reduction_boundary {
                    return Err(ArtifactError::LazyReductionFlagOutsidePrefix {
                        header: record as u32,
                        record: member_record as u32,
                    });
                }
                if reduction_boundary {
                    products_since_reduction = 0;
                }
            } else if class == WindowClass::GroupBf
                && lazy_product_count >= 2
                && member_class != WindowClass::LinearBf
            {
                return Err(ArtifactError::LazyProductTailClass {
                    header: record as u32,
                    record: member_record as u32,
                });
            } else if reduction_boundary {
                return Err(ArtifactError::LazyReductionFlagOutsidePrefix {
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
        let product_count = members
            .iter()
            .filter(|member| match class {
                WindowClass::GroupBf => member.class == WindowClass::ProductBfBf,
                WindowClass::GroupE4 => matches!(
                    member.class,
                    WindowClass::ProductBfE4 | WindowClass::ProductE4E4
                ),
                _ => unreachable!("class is a group header"),
            })
            .count() as u16;
        if has_product != (product_count != 0) {
            return Err(ArtifactError::GroupProductFlagMismatch {
                header: record as u32,
                encoded: has_product,
                products: product_count,
            });
        }
        if class == WindowClass::GroupBf {
            if lazy_product_count == 1
                && (product_count != 1 || members[0].class != WindowClass::ProductBfBf)
            {
                return Err(ArtifactError::InvalidEagerProductLayout {
                    header: record as u32,
                });
            }
        }
        stats.groups += 1;
        stats.terms += member_count as u32;
        match class {
            WindowClass::GroupBf => {
                stats.bf_groups += 1;
                atoms.push(WindowAtom::GroupBf {
                    core: coefficient,
                    lazy_product_count: if lazy_product_count >= 2 {
                        lazy_product_count
                    } else {
                        0
                    },
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
    match class {
        WindowClass::LinearBf | WindowClass::LinearE4 => {
            validate_direct_source(artifact, instruction.source_a, record)?;
            if instruction.source_b != SOURCE_NONE {
                return Err(ArtifactError::SourceBMustBeNone { record });
            }
        }
        WindowClass::LinearBfProceduralA => {
            validate_procedural_kind(artifact, instruction.source_a, record)?;
            if instruction.source_b != SOURCE_NONE {
                return Err(ArtifactError::SourceBMustBeNone { record });
            }
        }
        WindowClass::ProductBfBf | WindowClass::ProductBfE4 | WindowClass::ProductE4E4 => {
            validate_direct_source(artifact, instruction.source_a, record)?;
            if instruction.source_b == SOURCE_NONE {
                return Err(ArtifactError::SourceBMissing { record });
            }
            validate_direct_source(artifact, instruction.source_b, record)?;
        }
        WindowClass::ProductBfBfProceduralB => {
            validate_direct_source(artifact, instruction.source_a, record)?;
            if instruction.source_b == SOURCE_NONE {
                return Err(ArtifactError::SourceBMissing { record });
            }
            validate_procedural_kind(artifact, instruction.source_b, record)?;
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

fn validate_direct_source(
    artifact: &FrozenArtifact,
    source: u16,
    record: u32,
) -> Result<(), ArtifactError> {
    let (window, column) = decode_source_coordinate(source)
        .map_err(|_| ArtifactError::SourceOutOfRange { record, source })?;
    if !artifact
        .source_slots
        .iter()
        .any(|slot| slot.window == window && slot.column == column)
    {
        return Err(ArtifactError::SourceOutOfRange { record, source });
    }
    if artifact.windows[usize::from(window)].family.is_procedural() {
        return Err(ArtifactError::DirectProceduralSource { record, source });
    }
    Ok(())
}

fn validate_procedural_kind(
    artifact: &FrozenArtifact,
    kind: u16,
    record: u32,
) -> Result<(), ArtifactError> {
    let available = u8::try_from(kind).ok().is_some_and(|kind| {
        kind < 4
            && artifact
                .windows
                .iter()
                .any(|window| window.family == FrozenWindowFamily::VirtualSetup { kind })
    });
    if !available {
        return Err(ArtifactError::ProceduralKindUnavailable { record, kind });
    }
    Ok(())
}

fn source_field(artifact: &FrozenArtifact, source: u16) -> FrozenField {
    let (window, _) = decode_source_coordinate(source)
        .expect("validated term source must contain a direct coordinate");
    artifact.windows[usize::from(window)].field
}

fn validate_term_fields(
    artifact: &FrozenArtifact,
    class: WindowClass,
    source_a: u16,
    source_b: u16,
    record: u32,
) -> Result<(), ArtifactError> {
    if class == WindowClass::LinearBfProceduralA {
        return Ok(());
    }
    let field_a = source_field(artifact, source_a);
    let fields_match = match class {
        WindowClass::LinearBf => field_a == FrozenField::Base,
        WindowClass::LinearBfProceduralA => unreachable!("handled above"),
        WindowClass::LinearE4 => field_a == FrozenField::Ext,
        WindowClass::ProductBfBf => {
            field_a == FrozenField::Base && source_field(artifact, source_b) == FrozenField::Base
        }
        WindowClass::ProductBfBfProceduralB => field_a == FrozenField::Base,
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
    fn source_coordinate_uses_six_window_and_seven_column_bits() {
        let encoded = encode_source_coordinate(63, 127).unwrap();
        assert_eq!(encoded, 0x1fff);
        assert_eq!(decode_source_coordinate(encoded).unwrap(), (63, 127));
        assert!(encode_source_coordinate(64, 0).is_err());
        assert!(encode_source_coordinate(0, 128).is_err());
        assert!(decode_source_coordinate(0x2000).is_err());
        assert!(decode_source_coordinate(SOURCE_NONE).is_err());
    }

    #[test]
    fn class_low_bit_selects_the_result_field() {
        assert_eq!(WindowClass::LinearBf as u16, 0);
        assert_eq!(WindowClass::LinearE4 as u16, 1);
        assert_eq!(WindowClass::ProductBfBf as u16, 2);
        assert_eq!(WindowClass::ProductBfE4 as u16, 3);
        assert_eq!(WindowClass::LinearBfProceduralA as u16, 4);
        assert_eq!(WindowClass::ProductE4E4 as u16, 5);
        assert_eq!(WindowClass::GroupBf as u16, 6);
        assert_eq!(WindowClass::GroupE4 as u16, 7);
        assert_eq!(WindowClass::ProductBfBfProceduralB as u16, 8);
        for class in [
            WindowClass::LinearBf,
            WindowClass::ProductBfBf,
            WindowClass::GroupBf,
            WindowClass::LinearBfProceduralA,
            WindowClass::ProductBfBfProceduralB,
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

    fn add_virtual_source(artifact: &mut FrozenArtifact, kind: u8) -> u16 {
        let window = artifact.windows.len() as u8;
        let source = artifact.source_slots.len() as u32;
        artifact.windows.push(FrozenWindow {
            family: FrozenWindowFamily::VirtualSetup { kind },
            first_column: 0,
            field: FrozenField::Base,
            columns: vec![FrozenBoundColumn { column: 0, source }],
        });
        artifact
            .source_slots
            .push(FrozenSourceSlot { window, column: 0 });
        encode_source_coordinate(window, 0).unwrap()
    }

    fn lazy_bf_group_artifact(
        lazy_product_count: u16,
        members: Vec<WindowInstruction>,
    ) -> FrozenArtifact {
        let mut artifact = valid_artifact();
        artifact.term_count = members.len() as u32;
        artifact.record_count = members.len() as u32 + 1;
        artifact.coefficient_count = 3;
        artifact.program = vec![instruction(
            WindowClass::GroupBf,
            2,
            members.len() as u16,
            lazy_product_count,
        )];
        artifact.program.extend(members);
        artifact
    }

    #[test]
    fn bf_group_product_flag_must_match_members() {
        let missing = lazy_bf_group_artifact(
            0,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
            ],
        );
        assert!(matches!(
            decode_program(&missing),
            Err(ArtifactError::GroupProductFlagMismatch { .. })
        ));

        let spurious = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT,
            vec![
                instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
                instruction(WindowClass::LinearBf, 1, 0, SOURCE_NONE),
            ],
        );
        assert!(matches!(
            decode_program(&spurious),
            Err(ArtifactError::GroupProductFlagMismatch { .. })
        ));
    }

    #[test]
    fn lazy_count_requires_the_product_flag() {
        let artifact = lazy_bf_group_artifact(
            2,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, REDUCE_AFTER, 0, 0),
            ],
        );
        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::LazyProductFlagMissing { count: 2, .. })
        ));
    }

    #[test]
    fn eager_product_prefix_requires_one_product_at_member_zero() {
        for members in [
            vec![
                instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
            ],
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
            ],
        ] {
            let artifact = lazy_bf_group_artifact(GROUP_HAS_PRODUCT | 1, members);
            assert!(matches!(
                decode_program(&artifact),
                Err(ArtifactError::InvalidEagerProductLayout { .. })
            ));
        }
    }

    #[test]
    fn lazy_bf_group_masks_boundary_bits_from_immediate_ids() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 3,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, REDUCE_AFTER | 1, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
            ],
        );

        let (atoms, stats) = decode_program(&artifact).unwrap();
        assert_eq!(stats.terms, 3);
        assert!(matches!(
            atoms.as_slice(),
            [WindowAtom::GroupBf {
                lazy_product_count: 3,
                members,
                ..
            }] if members.iter().map(|member| member.coefficient).collect::<Vec<_>>() == vec![0, 1, 0]
        ));
    }

    #[test]
    fn one_product_prefix_is_eager() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 1,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
            ],
        );

        let (atoms, _) = decode_program(&artifact).unwrap();
        assert!(matches!(
            atoms.as_slice(),
            [WindowAtom::GroupBf {
                lazy_product_count: 0,
                ..
            }]
        ));
    }

    #[test]
    fn lazy_bf_group_rejects_a_count_above_group_arity() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 3,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, REDUCE_AFTER, 0, 0),
            ],
        );

        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::InvalidLazyProductCount {
                count: 3,
                arity: 2,
                ..
            })
        ));
    }

    #[test]
    fn lazy_bf_group_rejects_a_non_product_in_the_prefix() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 2,
            vec![
                instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
                instruction(WindowClass::ProductBfBf, REDUCE_AFTER, 0, 0),
            ],
        );

        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::LazyProductPrefixClass { record: 1, .. })
        ));
    }

    #[test]
    fn lazy_bf_group_rejects_a_product_after_the_prefix() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 2,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
            ],
        );

        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::LazyProductTailClass { record: 3, .. })
        ));
    }

    #[test]
    fn lazy_bf_group_rejects_a_boundary_flag_after_the_prefix() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 2,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::LinearBf, REDUCE_AFTER, 0, SOURCE_NONE),
            ],
        );

        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::LazyReductionFlagOutsidePrefix { record: 3, .. })
        ));
    }

    #[test]
    fn lazy_bf_group_rejects_a_rebase_on_the_final_product() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 2,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, REDUCE_AFTER | 1, 0, 0),
            ],
        );

        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::LazyReductionFlagOutsidePrefix { record: 2, .. })
        ));
    }

    #[test]
    fn lazy_bf_group_rejects_more_than_four_products_per_window() {
        let artifact = lazy_bf_group_artifact(
            GROUP_HAS_PRODUCT | 5,
            vec![
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
                instruction(WindowClass::ProductBfBf, 0, 0, 0),
            ],
        );

        assert!(matches!(
            decode_program(&artifact),
            Err(ArtifactError::LazyReductionWindowTooLong { record: 5, .. })
        ));
    }

    #[test]
    fn procedural_classes_store_the_kind_in_the_procedural_operand() {
        let mut artifact = valid_artifact();
        add_virtual_source(&mut artifact, 1);
        artifact.program = vec![instruction(
            WindowClass::LinearBfProceduralA,
            0,
            1,
            SOURCE_NONE,
        )];
        let (atoms, _) = decode_program(&artifact).unwrap();
        assert!(matches!(
            atoms.as_slice(),
            [WindowAtom::Term(WindowTerm {
                class: WindowClass::LinearBfProceduralA,
                source_a: 1,
                source_b: SOURCE_NONE,
                ..
            })]
        ));

        artifact.program = vec![instruction(WindowClass::ProductBfBfProceduralB, 0, 0, 1)];
        validate_artifact(&artifact).unwrap();
    }

    #[test]
    fn ordinary_bf_class_rejects_a_procedural_coordinate() {
        let mut artifact = valid_artifact();
        let procedural = add_virtual_source(&mut artifact, 0);
        artifact.program[0].source_a = procedural;
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::DirectProceduralSource { .. })
        ));
    }

    #[test]
    fn procedural_kind_must_be_available() {
        let mut artifact = valid_artifact();
        add_virtual_source(&mut artifact, 0);
        artifact.program[0] = instruction(WindowClass::LinearBfProceduralA, 0, 4, SOURCE_NONE);
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::ProceduralKindUnavailable { kind: 4, .. })
        ));
    }

    #[test]
    fn procedural_term_cannot_be_a_group_member() {
        let mut artifact = valid_artifact();
        add_virtual_source(&mut artifact, 0);
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        for procedural in [
            instruction(WindowClass::LinearBfProceduralA, 0, 0, SOURCE_NONE),
            instruction(WindowClass::ProductBfBfProceduralB, 0, 0, 0),
        ] {
            artifact.program = vec![
                instruction(WindowClass::GroupBf, 2, 2, 0),
                instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
                procedural,
            ];
            assert!(matches!(
                validate_artifact(&artifact),
                Err(ArtifactError::GroupMemberClassMismatch { .. })
            ));
        }
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
            instruction(WindowClass::GroupBf, 2, 2, GROUP_HAS_PRODUCT),
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
        let ext_source = encode_source_coordinate(1, 0).unwrap();
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.program = vec![
            instruction(WindowClass::GroupE4, 2, 0, GROUP_HAS_PRODUCT),
            instruction(WindowClass::LinearE4, 0, ext_source, SOURCE_NONE),
            instruction(WindowClass::ProductBfE4, 1, 0, ext_source),
        ];
        let stats = validate_artifact(&artifact).unwrap();
        assert_eq!(stats.terms, 2);
        assert_eq!(stats.bf_groups, 0);
        assert_eq!(stats.e4_groups, 1);
    }

    #[test]
    fn e4_group_product_flag_must_match_members() {
        let mut missing = valid_artifact();
        add_ext_source(&mut missing);
        let ext_source = encode_source_coordinate(1, 0).unwrap();
        missing.term_count = 2;
        missing.record_count = 3;
        missing.coefficient_count = 3;
        missing.program = vec![
            instruction(WindowClass::GroupE4, 2, 0, 0),
            instruction(WindowClass::LinearE4, 0, ext_source, SOURCE_NONE),
            instruction(WindowClass::ProductBfE4, 1, 0, ext_source),
        ];
        assert!(matches!(
            decode_program(&missing),
            Err(ArtifactError::GroupProductFlagMismatch { .. })
        ));

        let mut spurious = missing;
        spurious.program = vec![
            instruction(WindowClass::GroupE4, 2, 0, GROUP_HAS_PRODUCT),
            instruction(WindowClass::LinearE4, 0, ext_source, SOURCE_NONE),
            instruction(WindowClass::LinearE4, 1, ext_source, SOURCE_NONE),
        ];
        assert!(matches!(
            decode_program(&spurious),
            Err(ArtifactError::GroupProductFlagMismatch { .. })
        ));
    }

    #[test]
    fn product_bf_e4_must_be_encoded_bf_first() {
        let mut artifact = valid_artifact();
        add_ext_source(&mut artifact);
        let ext_source = encode_source_coordinate(1, 0).unwrap();
        artifact.program = vec![instruction(WindowClass::ProductBfE4, 0, ext_source, 0)];
        assert!(matches!(
            validate_artifact(&artifact),
            Err(ArtifactError::FieldClassMismatch { .. })
        ));
    }

    #[test]
    fn bf_group_rejects_e4_members() {
        let mut artifact = valid_artifact();
        add_ext_source(&mut artifact);
        let ext_source = encode_source_coordinate(1, 0).unwrap();
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.program = vec![
            instruction(WindowClass::GroupBf, 2, 2, 0),
            instruction(WindowClass::LinearBf, 0, 0, SOURCE_NONE),
            instruction(WindowClass::LinearE4, 0, ext_source, SOURCE_NONE),
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
        let ext_source = encode_source_coordinate(1, 0).unwrap();
        artifact.term_count = 2;
        artifact.record_count = 3;
        artifact.coefficient_count = 3;
        artifact.immediates.push(7);
        artifact.program = vec![
            instruction(WindowClass::GroupE4, 2, 0, 0),
            instruction(WindowClass::LinearE4, 2, ext_source, SOURCE_NONE),
            instruction(WindowClass::LinearE4, 0, ext_source, SOURCE_NONE),
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
        artifact.program[0].term_class = 9;
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
