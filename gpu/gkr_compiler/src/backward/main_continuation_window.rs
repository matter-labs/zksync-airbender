//! Checked lowering of continuation programs for the width-three main-layer
//! window executor.
//!
//! The product is pointer-free. Source publication is dense by semantic
//! [`SourceId`], while the raw origin retained for binding is independent of the
//! artifact traversal that happened to discover it.

use super::common::interp::{interpret_lean_program, CoeffResolver, LeanInterpError};
use super::common::lean::{
    decode_atoms, validate_program, LeanAtom, LeanCodecError, LeanProgram, LeanTerm,
};
use super::common::lean_bind::LeanSourceBinding;
use super::common::limits::{
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES, LEAN_MAX_SOURCES, MAX_SOURCE_WINDOWS,
};
use super::common::model::{
    CoeffLayer, CoeffSource, CoefficientRecipeId, ImmediateId, NormalizedCoefficientRecipe,
    SourceId,
};
use super::common::source_layout::WindowFamily;
use super::continuation::ContinuationLayerProgram;

/// Shape bits understood by the continuation-window kernel bank.
pub const MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS: u16 = 0x1f;
/// By-value descriptor program capacity, mirrored by the native ABI.
pub const MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY: usize = LEAN_DESCRIPTOR_PROGRAM_WORDS;
/// Source and publication-column capacity, mirrored by the native ABI.
pub const MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY: usize = LEAN_MAX_SOURCES;
/// Raw address-window capacity, mirrored by the native ABI.
pub const MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY: usize = MAX_SOURCE_WINDOWS;
/// Immediate-table capacity, mirrored by the native ABI.
pub const MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY: usize = LEAN_MAX_IMMEDIATES;
/// Existing shared extension coefficient-bank capacity. The two reserved
/// literal coefficient ids occupy its first two slots.
pub const MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY: usize = 1_792;

/// Compile-time paths selected by the generated continuation-window bank.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct MainContinuationWindowShape(u16);

impl MainContinuationWindowShape {
    pub const EMPTY: Self = Self(0);
    pub const PLAIN_LINEAR: Self = Self(1 << 0);
    pub const GROUPED: Self = Self(1 << 1);
    pub const C_INIT: Self = Self(1 << 2);
    /// At least one grouped member has an [`ImmediateId`] greater than or equal
    /// to [`ImmediateId::RESERVED`]. This is an ID predicate: unlike landed R0,
    /// it does not inspect the resolved field value or encode a negate flag.
    pub const BANKED_GROUP_IMMEDIATE: Self = Self(1 << 3);
    /// At least one grouped member has exactly [`ImmediateId::NEG_ONE`]. This
    /// is an ID predicate, distinct from landed R0's value-based
    /// `WINDOW_NEG_ONE_IMMEDIATE` / `WINDOW_FLAG_NEGATE_COEFFICIENT` encoding.
    pub const NEGATIVE_GROUP_IMMEDIATE: Self = Self(1 << 4);
    pub const UNIVERSAL: Self = Self(MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS);

    pub fn from_bits(bits: u16) -> Result<Self, MainContinuationWindowLoweringError> {
        if bits & !MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS != 0 {
            return Err(MainContinuationWindowLoweringError::UndefinedShapeBits { bits });
        }
        Ok(Self(bits))
    }

    pub const fn bits(self) -> u16 {
        self.0
    }

    pub const fn contains(self, feature: Self) -> bool {
        self.0 & feature.0 == feature.0
    }

    fn insert(&mut self, feature: Self) {
        self.0 |= feature.0;
    }
}

/// One half-open record range in the canonical decoded section view.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MainContinuationWindowSection {
    pub start: u32,
    pub end: u32,
}

impl MainContinuationWindowSection {
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// The three semantic, record-granular sections. The original lean words remain in
/// [`MainContinuationWindowProgram::program`]; these endpoints index the
/// canonical view `dual_products || plain_linear || grouped_records`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MainContinuationWindowSections {
    pub dual_products: MainContinuationWindowSection,
    pub plain_linear: MainContinuationWindowSection,
    pub grouped_records: MainContinuationWindowSection,
}

/// One self-delimiting group retained from the continuation lean stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationWindowGroupRecord {
    pub core: u16,
    pub has_c0: bool,
    pub has_c2: bool,
    pub members: Vec<LeanTerm>,
}

/// Canonical source record. `publish_column` is always exactly `id.0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationWindowSource {
    pub id: SourceId,
    pub origin: CoeffSource,
    pub raw_family: WindowFamily,
    pub raw_column: usize,
    pub publish_column: u16,
}

/// Resource footprint checked before a runtime descriptor can be built.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MainContinuationWindowCapacities {
    pub program_words: usize,
    pub sources: usize,
    pub source_windows: usize,
    pub immediates: usize,
    pub coefficient_bank_slots: usize,
}

/// Pointer-free compiler product consumed by the runtime binder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationWindowProgram {
    pub layer: usize,
    /// The committed continuation lean words, byte-for-byte and in their
    /// original atom order.
    pub program: LeanProgram,
    pub plain_linear: Vec<LeanTerm>,
    pub dual_products: Vec<LeanTerm>,
    pub grouped_records: Vec<MainContinuationWindowGroupRecord>,
    pub sections: MainContinuationWindowSections,
    pub coefficient_recipes: Vec<NormalizedCoefficientRecipe>,
    pub c_init: Option<CoefficientRecipeId>,
    pub immediates: Vec<u32>,
    /// Dense by semantic source id, never by traversal position.
    pub sources: Vec<MainContinuationWindowSource>,
    pub shape: MainContinuationWindowShape,
    pub capacities: MainContinuationWindowCapacities,
    /// Retained semantic metadata for CPU checking and later binding.
    pub coefficients: CoeffLayer,
}

impl MainContinuationWindowProgram {
    /// Canonical SourceId-ordered read identities for runtime final repointing.
    /// Virtual sources intentionally return None and are never address targets.
    pub fn canonical_read_places(&self) -> Vec<Option<gkr_eval_ir::ReadPlace>> {
        self.sources
            .iter()
            .map(|source| match &source.origin.origin {
                super::common::source::OriginLeaf::Read(place) => Some(place.clone()),
                super::common::source::OriginLeaf::VirtualSetup { .. } => None,
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MainContinuationWindowLoweringError {
    Codec(LeanCodecError),
    UndefinedShapeBits {
        bits: u16,
    },
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    SourceOutOfRange {
        source: u32,
        source_count: usize,
    },
    DuplicateSemanticSource {
        source: SourceId,
    },
    MissingSemanticSource {
        source: SourceId,
    },
    InvalidCoefficientId {
        id: u32,
        bank_slots: usize,
    },
    InvalidImmediateId {
        id: u16,
        bank_entries: usize,
    },
    MetadataMismatch {
        resource: &'static str,
    },
    UnsupportedPlainClass {
        class: u8,
    },
    RecordCountOverflow,
    RecordCountMismatch {
        expected: usize,
        actual: usize,
    },
}

impl core::fmt::Display for MainContinuationWindowLoweringError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for MainContinuationWindowLoweringError {}

fn require_capacity(
    resource: &'static str,
    required: usize,
    capacity: usize,
) -> Result<(), MainContinuationWindowLoweringError> {
    if required > capacity {
        return Err(MainContinuationWindowLoweringError::Capacity {
            resource,
            required,
            capacity,
        });
    }
    Ok(())
}

fn validate_capacities(
    program: &ContinuationLayerProgram,
) -> Result<MainContinuationWindowCapacities, MainContinuationWindowLoweringError> {
    let coefficient_bank_slots = program
        .coefficient_recipes
        .len()
        .checked_add(CoefficientRecipeId::RESERVED as usize)
        .ok_or(MainContinuationWindowLoweringError::Capacity {
            resource: "coefficient_bank_slots",
            required: usize::MAX,
            capacity: MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
        })?;
    let capacities = MainContinuationWindowCapacities {
        program_words: program.program.words.len(),
        sources: program.coefficients.sources.len(),
        source_windows: program.binding.windows.len(),
        immediates: program.immediates.len(),
        coefficient_bank_slots,
    };
    for (resource, required, capacity) in [
        (
            "program_words",
            capacities.program_words,
            MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
        ),
        (
            "sources",
            capacities.sources,
            MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
        ),
        (
            "source_windows",
            capacities.source_windows,
            MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY,
        ),
        (
            "immediates",
            capacities.immediates,
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
        ),
        (
            "coefficient_bank_slots",
            capacities.coefficient_bank_slots,
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
        ),
    ] {
        require_capacity(resource, required, capacity)?;
    }
    Ok(capacities)
}

fn validate_coefficient_id(
    id: u32,
    bank_slots: usize,
) -> Result<(), MainContinuationWindowLoweringError> {
    if usize::try_from(id).map_or(true, |id| id >= bank_slots) {
        return Err(MainContinuationWindowLoweringError::InvalidCoefficientId { id, bank_slots });
    }
    Ok(())
}

fn validate_immediate_id(
    id: u16,
    bank_entries: usize,
) -> Result<(), MainContinuationWindowLoweringError> {
    if let Some(index) = ImmediateId(id).bank_index() {
        if index >= bank_entries {
            return Err(MainContinuationWindowLoweringError::InvalidImmediateId {
                id,
                bank_entries,
            });
        }
    }
    Ok(())
}

fn canonical_sources(
    binding: &LeanSourceBinding,
    coefficients: &CoeffLayer,
) -> Result<Vec<MainContinuationWindowSource>, MainContinuationWindowLoweringError> {
    let source_count = coefficients.sources.len();
    let mut seen = vec![false; source_count];
    let mut canonical = vec![None; source_count];

    // This traversal and `seen` table are deliberately independent of the
    // destination vector. A duplicate cannot hide a missing semantic source by
    // overwriting its destination slot.
    for window in &binding.windows {
        for column in &window.columns {
            let index = usize::try_from(column.source).map_err(|_| {
                MainContinuationWindowLoweringError::SourceOutOfRange {
                    source: column.source,
                    source_count,
                }
            })?;
            if index >= source_count {
                return Err(MainContinuationWindowLoweringError::SourceOutOfRange {
                    source: column.source,
                    source_count,
                });
            }
            let id = SourceId(column.source);
            if seen[index] {
                return Err(
                    MainContinuationWindowLoweringError::DuplicateSemanticSource { source: id },
                );
            }
            seen[index] = true;
            canonical[index] = Some(MainContinuationWindowSource {
                id,
                origin: coefficients.sources[index].clone(),
                raw_family: window.family,
                raw_column: column.column,
                publish_column: u16::try_from(index).map_err(|_| {
                    MainContinuationWindowLoweringError::SourceOutOfRange {
                        source: column.source,
                        source_count,
                    }
                })?,
            });
        }
    }

    for (index, was_seen) in seen.into_iter().enumerate() {
        if !was_seen {
            return Err(MainContinuationWindowLoweringError::MissingSemanticSource {
                source: SourceId(index as u32),
            });
        }
    }
    Ok(canonical
        .into_iter()
        .map(|entry| entry.expect("the independent seen pass proved every source present"))
        .collect())
}

fn require_record_count(
    expected: usize,
    actual: usize,
) -> Result<(), MainContinuationWindowLoweringError> {
    if expected != actual {
        return Err(MainContinuationWindowLoweringError::RecordCountMismatch { expected, actual });
    }
    Ok(())
}

/// Lower one continuation coordinate into the canonical main-window form.
pub fn lower_main_continuation_window_program(
    program: &ContinuationLayerProgram,
) -> Result<MainContinuationWindowProgram, MainContinuationWindowLoweringError> {
    let capacities = validate_capacities(program)?;
    for (resource, matches) in [
        (
            "coefficient_recipes",
            program.coefficient_recipes == program.coefficients.coefficients,
        ),
        (
            "immediates",
            program.immediates == program.coefficients.immediates,
        ),
        ("c_init", program.c_init == program.coefficients.c_init),
    ] {
        if !matches {
            return Err(MainContinuationWindowLoweringError::MetadataMismatch { resource });
        }
    }
    validate_program(&program.program, &program.coefficients)
        .map_err(MainContinuationWindowLoweringError::Codec)?;
    let atoms = decode_atoms(&program.program, crate::BwdRegime::Ext)
        .map_err(MainContinuationWindowLoweringError::Codec)?;
    let mut plain_linear = Vec::new();
    let mut dual_products = Vec::new();
    let mut grouped_records = Vec::new();
    let mut shape = MainContinuationWindowShape::EMPTY;

    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                validate_coefficient_id(u32::from(term.coeff), capacities.coefficient_bank_slots)?;
                match term.class {
                    0 => {
                        shape.insert(MainContinuationWindowShape::PLAIN_LINEAR);
                        plain_linear.push(term);
                    }
                    1 => dual_products.push(term),
                    class => {
                        return Err(MainContinuationWindowLoweringError::UnsupportedPlainClass {
                            class,
                        });
                    }
                }
            }
            LeanAtom::Group {
                core,
                has_c0,
                has_c2,
                members,
            } => {
                validate_coefficient_id(u32::from(core), capacities.coefficient_bank_slots)?;
                shape.insert(MainContinuationWindowShape::GROUPED);
                for member in &members {
                    validate_immediate_id(member.coeff, program.immediates.len())?;
                    let immediate = ImmediateId(member.coeff);
                    if immediate.bank_index().is_some() {
                        shape.insert(MainContinuationWindowShape::BANKED_GROUP_IMMEDIATE);
                    }
                    if immediate == ImmediateId::NEG_ONE {
                        shape.insert(MainContinuationWindowShape::NEGATIVE_GROUP_IMMEDIATE);
                    }
                }
                grouped_records.push(MainContinuationWindowGroupRecord {
                    core,
                    has_c0,
                    has_c2,
                    members,
                });
            }
        }
    }
    if program.c_init.is_some() {
        shape.insert(MainContinuationWindowShape::C_INIT);
    }
    if let Some(c_init) = program.c_init {
        validate_coefficient_id(c_init.0, capacities.coefficient_bank_slots)?;
    }
    let dual_end = u32::try_from(dual_products.len())
        .map_err(|_| MainContinuationWindowLoweringError::RecordCountOverflow)?;
    let plain_end = dual_end
        .checked_add(
            u32::try_from(plain_linear.len())
                .map_err(|_| MainContinuationWindowLoweringError::RecordCountOverflow)?,
        )
        .ok_or(MainContinuationWindowLoweringError::RecordCountOverflow)?;
    let grouped_record_count = grouped_records.iter().try_fold(0u32, |total, group| {
        let records = u32::try_from(group.members.len()).ok()?.checked_add(1)?;
        total.checked_add(records)
    });
    let grouped_end = plain_end
        .checked_add(
            grouped_record_count.ok_or(MainContinuationWindowLoweringError::RecordCountOverflow)?,
        )
        .ok_or(MainContinuationWindowLoweringError::RecordCountOverflow)?;
    let sections = MainContinuationWindowSections {
        dual_products: MainContinuationWindowSection {
            start: 0,
            end: dual_end,
        },
        plain_linear: MainContinuationWindowSection {
            start: dual_end,
            end: plain_end,
        },
        grouped_records: MainContinuationWindowSection {
            start: plain_end,
            end: grouped_end,
        },
    };
    let actual_records = usize::try_from(grouped_end)
        .map_err(|_| MainContinuationWindowLoweringError::RecordCountOverflow)?;
    require_record_count(program.program.words.len() / 3, actual_records)?;

    let sources = canonical_sources(&program.binding, &program.coefficients)?;
    Ok(MainContinuationWindowProgram {
        layer: program.layer,
        program: program.program.clone(),
        plain_linear,
        dual_products,
        grouped_records,
        sections,
        coefficient_recipes: program.coefficient_recipes.clone(),
        c_init: program.c_init,
        immediates: program.immediates.clone(),
        sources,
        shape,
        capacities,
        coefficients: program.coefficients.clone(),
    })
}

/// A requested executor shape omitted one or more features required by the
/// lowered program, or the shared lean interpreter rejected the program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MainContinuationWindowShapeEvaluationError {
    MissingRequiredFeatures {
        required: u16,
        compiled: u16,
        missing: u16,
    },
    Interpreter(LeanInterpError),
}

impl From<LeanInterpError> for MainContinuationWindowShapeEvaluationError {
    fn from(error: LeanInterpError) -> Self {
        Self::Interpreter(error)
    }
}

/// CPU compatibility and semantics oracle shared with runtime binding tests.
/// Exact and superset shapes evaluate identically; a shape missing any required
/// bit is rejected with a typed payload before interpretation.
#[doc(hidden)]
pub fn interpret_main_continuation_window_shape(
    program: &MainContinuationWindowProgram,
    compiled_shape: MainContinuationWindowShape,
    row: usize,
    resolver: &impl CoeffResolver,
    k: usize,
) -> Result<
    (
        field::baby_bear::ext4::BabyBearExt4,
        field::baby_bear::ext4::BabyBearExt4,
    ),
    MainContinuationWindowShapeEvaluationError,
> {
    let required = program.shape.bits();
    let compiled = compiled_shape.bits();
    let missing = required & !compiled;
    if missing != 0 {
        return Err(
            MainContinuationWindowShapeEvaluationError::MissingRequiredFeatures {
                required,
                compiled,
                missing,
            },
        );
    }
    interpret_lean_program(&program.program, &program.coefficients, row, resolver, k)
        .map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::path::PathBuf;
    use std::sync::OnceLock;

    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::{baby_bear::base::BabyBearField, FieldExtension, PrimeField};
    use gkr_eval_ir::{lower_dag, FieldKind};

    use super::*;
    use crate::backward::common::source::OriginLeaf;
    use crate::backward::common::{Bf, Ext};
    use crate::backward::compile_continuations;

    const CORPUS: &[&str] = &[
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "blake2_g_function_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "inits_and_teardowns_layout_gkr.json",
        "jump_branch_slt_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
        "mem_subword_only_layout_gkr.json",
        "mem_word_only_layout_gkr.json",
        "shift_binop_layout_gkr.json",
        "unified_reduced_machine_layout_gkr.json",
        "unsigned_mul_div_layout_gkr.json",
    ];

    static COMPILED_CORPUS: OnceLock<Vec<(String, ContinuationLayerProgram)>> = OnceLock::new();

    fn compiled_corpus() -> &'static [(String, ContinuationLayerProgram)] {
        COMPILED_CORPUS.get_or_init(|| {
            let directory =
                PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
            let mut coordinates = Vec::new();
            for layout_name in CORPUS {
                let artifact: GKRCircuitArtifact<BabyBearField> =
                    serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap())
                        .unwrap();
                let dag =
                    lower_dag(&artifact).unwrap_or_else(|error| panic!("{layout_name}: {error}"));
                let bundle = compile_continuations(&dag)
                    .unwrap_or_else(|error| panic!("{layout_name}: {error:?}"));
                coordinates.extend(bundle.layers.into_iter().map(|program| {
                    (
                        format!(
                            "{}:{}",
                            layout_name.trim_end_matches("_layout_gkr.json"),
                            program.layer
                        ),
                        program,
                    )
                }));
            }
            coordinates
        })
    }

    struct Resolver;

    fn lift(value: u32) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
    }

    impl CoeffResolver for Resolver {
        fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
            lift(17 + id.0 * 13)
        }

        fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
            let base = 31 + id.0 * 19 + row as u32 * 7;
            (lift(base), lift(base + 5))
        }
    }

    fn first_program_with_sources(count: usize) -> ContinuationLayerProgram {
        compiled_corpus()
            .iter()
            .find(|(_, program)| program.coefficients.sources.len() >= count)
            .unwrap()
            .1
            .clone()
    }

    fn source_positions(binding: &LeanSourceBinding) -> Vec<(usize, usize)> {
        binding
            .windows
            .iter()
            .enumerate()
            .flat_map(|(window, bound)| {
                (0..bound.columns.len()).map(move |column| (window, column))
            })
            .collect()
    }

    fn legacy_publication_displaced(program: &ContinuationLayerProgram) -> usize {
        // This census models the first continuation window: round 3 over raw
        // depth-0 inputs, hence delta 3. The reviewed corpus establishes that
        // every semantic source materializes there. Production therefore
        // assigns its dense global column with `destinations.len()` in this
        // exact windows/columns traversal order.
        let source_count = program.coefficients.sources.len();
        let mut seen = vec![false; source_count];
        let mut published = 0usize;
        let mut displaced = 0usize;
        for column in program
            .binding
            .windows
            .iter()
            .flat_map(|window| &window.columns)
        {
            let source = column.source as usize;
            assert!(
                source < source_count,
                "census source {source} is out of range"
            );
            assert!(!seen[source], "census source {source} is duplicated");
            seen[source] = true;
            displaced += usize::from(published != source);
            published += 1;
        }
        assert_eq!(published, source_count, "not every source materialized");
        assert!(seen.into_iter().all(|source| source));
        displaced
    }

    #[test]
    fn cpu_main_continuation_window_corpus_census_and_superset_inertness() {
        let mut masks = BTreeMap::<u16, usize>::new();
        let mut maxima = [0usize; 13];
        let mut non_identity_coordinates = 0usize;
        let mut max_displaced = 0usize;

        for (coordinate, source) in compiled_corpus() {
            let lowered = lower_main_continuation_window_program(source)
                .unwrap_or_else(|error| panic!("{coordinate}: {error:?}"));
            *masks.entry(lowered.shape.bits()).or_default() += 1;

            let record_count = source.program.words.len() / 3;
            let group_count = source.coefficients.groups.len();
            let max_group_members = source
                .coefficients
                .groups
                .iter()
                .map(|group| group.members.len())
                .max()
                .unwrap_or(0);
            let (mut raw_bf, mut raw_e4, mut procedural) = (0, 0, 0);
            for window in &source.binding.windows {
                for column in &window.columns {
                    let semantic_source = &source.coefficients.sources[column.source as usize];
                    match semantic_source.origin {
                        OriginLeaf::VirtualSetup { .. } => procedural += 1,
                        OriginLeaf::Read(_) if window.backing_field() == FieldKind::Ext => {
                            raw_e4 += 1;
                        }
                        OriginLeaf::Read(_) => raw_bf += 1,
                    }
                }
            }
            maxima[0] = maxima[0].max(source.program.words.len());
            maxima[1] = maxima[1].max(record_count);
            maxima[2] = maxima[2].max(source.program.term_count);
            maxima[3] = maxima[3].max(group_count);
            maxima[4] = maxima[4].max(max_group_members);
            maxima[5] = maxima[5].max(source.coefficient_recipes.len() + 2);
            maxima[6] = maxima[6].max(source.immediates.len());
            maxima[7] = maxima[7].max(source.coefficients.sources.len());
            maxima[8] = maxima[8].max(raw_bf);
            maxima[9] = maxima[9].max(raw_e4);
            maxima[10] = maxima[10].max(procedural);
            maxima[11] = maxima[11].max(source.binding.windows.len());
            maxima[12] = maxima[12].max(source.coefficients.sources.len().div_ceil(128));

            let displaced = legacy_publication_displaced(source);
            if displaced != 0 {
                non_identity_coordinates += 1;
            }
            max_displaced = max_displaced.max(displaced);

            assert_eq!(lowered.sources.len(), source.coefficients.sources.len());
            assert!(lowered.sources.iter().enumerate().all(|(index, record)| {
                record.id == SourceId(index as u32) && usize::from(record.publish_column) == index
            }));
            assert_eq!(
                lowered.sections.plain_linear.is_empty(),
                !lowered
                    .shape
                    .contains(MainContinuationWindowShape::PLAIN_LINEAR)
            );
            assert_eq!(
                lowered.sections.grouped_records.is_empty(),
                !lowered.shape.contains(MainContinuationWindowShape::GROUPED)
            );
            assert_eq!(
                lowered.c_init.is_some(),
                lowered.shape.contains(MainContinuationWindowShape::C_INIT)
            );
            if !lowered
                .shape
                .contains(MainContinuationWindowShape::BANKED_GROUP_IMMEDIATE)
            {
                assert!(lowered.grouped_records.iter().all(|group| group
                    .members
                    .iter()
                    .all(|member| member.coeff < ImmediateId::RESERVED)));
            }
            if !lowered
                .shape
                .contains(MainContinuationWindowShape::NEGATIVE_GROUP_IMMEDIATE)
            {
                assert!(lowered.grouped_records.iter().all(|group| group
                    .members
                    .iter()
                    .all(|member| member.coeff != ImmediateId::NEG_ONE.0)));
            }
            assert!(source.coefficients.sources.len().div_ceil(128) <= 8);

            for bit in 0..5 {
                let feature = 1u16 << bit;
                if lowered.shape.bits() & feature == 0 {
                    continue;
                }
                let compiled = lowered.shape.bits() & !feature;
                let missing_shape = MainContinuationWindowShape::from_bits(compiled).unwrap();
                assert_eq!(
                    interpret_main_continuation_window_shape(
                        &lowered,
                        missing_shape,
                        0,
                        &Resolver,
                        1,
                    ),
                    Err(
                        MainContinuationWindowShapeEvaluationError::MissingRequiredFeatures {
                            required: lowered.shape.bits(),
                            compiled,
                            missing: feature,
                        }
                    ),
                    "{coordinate} accepted shape bit {feature:#04x} being removed"
                );
            }

            for (row, k) in [(0, 1), (3, 7)] {
                let exact = interpret_main_continuation_window_shape(
                    &lowered,
                    lowered.shape,
                    row,
                    &Resolver,
                    k,
                )
                .unwrap();
                let universal = interpret_main_continuation_window_shape(
                    &lowered,
                    MainContinuationWindowShape::UNIVERSAL,
                    row,
                    &Resolver,
                    k,
                )
                .unwrap();
                assert_eq!(exact, universal, "{coordinate} row {row} K {k}");
            }
        }

        assert_eq!(compiled_corpus().len(), 57);
        assert_eq!(
            masks,
            BTreeMap::from([
                (0x00, 3),
                (0x01, 6),
                (0x03, 19),
                (0x07, 15),
                (0x13, 1),
                (0x17, 1),
                (0x1f, 12),
            ])
        );
        assert_eq!(
            maxima,
            [6_468, 2_156, 1_791, 365, 49, 913, 9, 1_012, 715, 341, 4, 13, 8,]
        );
        assert_eq!(non_identity_coordinates, 23);
        assert_eq!(max_displaced, 174);
    }

    #[test]
    fn cpu_main_continuation_window_canonical_publication_mutation_gates() {
        let source = first_program_with_sources(2);
        let canonical = lower_main_continuation_window_program(&source).unwrap();
        let positions = source_positions(&source.binding);

        let mut duplicate = source.clone();
        let first_id = duplicate.binding.windows[positions[0].0].columns[positions[0].1].source;
        let deleted_id = duplicate.binding.windows[positions[1].0].columns[positions[1].1].source;
        duplicate.binding.windows[positions[1].0].columns[positions[1].1].source = first_id;
        assert!(matches!(
            lower_main_continuation_window_program(&duplicate),
            Err(MainContinuationWindowLoweringError::DuplicateSemanticSource {
                source: SourceId(id)
            }) if id == first_id
        ));

        let mut missing = source.clone();
        missing.binding.windows[positions[1].0]
            .columns
            .remove(positions[1].1);
        assert!(matches!(
            lower_main_continuation_window_program(&missing),
            Err(MainContinuationWindowLoweringError::MissingSemanticSource {
                source: SourceId(id)
            }) if id == deleted_id
        ));

        let mut permuted = source.clone();
        let window_count = permuted.binding.windows.len();
        permuted.binding.windows.reverse();
        for slot in &mut permuted.binding.source_slots {
            slot.window = u8::try_from(window_count - 1 - usize::from(slot.window)).unwrap();
        }
        assert_eq!(
            lower_main_continuation_window_program(&permuted).unwrap(),
            canonical
        );

        let mut corrupt = source;
        corrupt.binding.windows[positions[0].0].columns[positions[0].1].source = u32::MAX;
        assert!(matches!(
            lower_main_continuation_window_program(&corrupt),
            Err(MainContinuationWindowLoweringError::SourceOutOfRange {
                source: u32::MAX,
                ..
            })
        ));
    }

    fn expect_capacity(
        program: &ContinuationLayerProgram,
        resource: &'static str,
        required: usize,
        capacity: usize,
    ) {
        assert_eq!(
            lower_main_continuation_window_program(program),
            Err(MainContinuationWindowLoweringError::Capacity {
                resource,
                required,
                capacity,
            })
        );
    }

    #[test]
    fn cpu_main_continuation_window_capacity_and_shape_mutation_gates() {
        let source = first_program_with_sources(1);

        let mut words = source.clone();
        words
            .program
            .words
            .resize(MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY + 1, 0);
        expect_capacity(
            &words,
            "program_words",
            MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY + 1,
            MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
        );

        let mut sources = source.clone();
        sources.coefficients.sources.resize(
            MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY + 1,
            sources.coefficients.sources[0].clone(),
        );
        expect_capacity(
            &sources,
            "sources",
            MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY + 1,
            MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
        );

        let mut windows = source.clone();
        windows.binding.windows.resize(
            MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY + 1,
            windows.binding.windows[0].clone(),
        );
        expect_capacity(
            &windows,
            "source_windows",
            MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY + 1,
            MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY,
        );

        let mut immediates = source.clone();
        immediates
            .immediates
            .resize(MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY + 1, 0);
        expect_capacity(
            &immediates,
            "immediates",
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY + 1,
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
        );

        let mut coefficients = source;
        coefficients.coefficient_recipes.resize(
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
            coefficients.coefficient_recipes[0].clone(),
        );
        expect_capacity(
            &coefficients,
            "coefficient_bank_slots",
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY
                + CoefficientRecipeId::RESERVED as usize,
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
        );

        assert_eq!(
            MainContinuationWindowShape::from_bits(0x20),
            Err(MainContinuationWindowLoweringError::UndefinedShapeBits { bits: 0x20 })
        );
        assert_eq!(
            require_record_count(7, 6),
            Err(MainContinuationWindowLoweringError::RecordCountMismatch {
                expected: 7,
                actual: 6,
            })
        );
    }
}
