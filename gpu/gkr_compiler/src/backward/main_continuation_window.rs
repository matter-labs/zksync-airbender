//! Checked lowering of continuation programs for the width-three main-layer
//! window executor.
//!
//! The product is pointer-free. Source publication is dense by semantic
//! [`SourceId`], while the raw origin retained for binding is independent of the
//! artifact traversal that happened to discover it.

use super::common::lean::{validate_program, LeanAtom, LeanCodecError, LeanProgram};
use super::common::lean_bind::LeanSourceBinding;
use super::common::limits::{
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES, LEAN_MAX_SOURCES, MAX_SOURCE_WINDOWS,
};
use super::common::model::{CoeffLayer, CoeffSource, CoefficientRecipeId, ImmediateId, SourceId};
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
    /// to [`ImmediateId::RESERVED`]. This is an ID predicate;
    /// it does not inspect the resolved field value or encode a negate flag.
    pub const BANKED_GROUP_IMMEDIATE: Self = Self(1 << 3);
    /// At least one grouped member has exactly [`ImmediateId::NEG_ONE`]. This
    /// is an ID predicate, distinct from R0's value-based
    /// `WINDOW_NEG_ONE_IMMEDIATE` / `WINDOW_FLAG_NEGATE_COEFFICIENT` encoding.
    pub const NEGATIVE_GROUP_IMMEDIATE: Self = Self(1 << 4);

    pub const fn bits(self) -> u16 {
        self.0
    }

    fn insert(&mut self, feature: Self) {
        self.0 |= feature.0;
    }
}

/// Source origins in dense semantic source-ID order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationWindowSource {
    pub origin: CoeffSource,
    pub raw_family: WindowFamily,
    pub raw_column: usize,
}

/// Pointer-free compiler product consumed by the runtime binder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationWindowProgram {
    /// The committed continuation lean words, byte-for-byte and in their
    /// original atom order.
    pub program: LeanProgram,
    /// Candidates constructed from this program; selection uses runtime geometry/device.
    pub partitions: Vec<super::main_continuation_partitions::MainContinuationPartitionPlan>,
    pub c_init: Option<CoefficientRecipeId>,
    pub immediates: Vec<u32>,
    /// Dense by semantic source id, never by traversal position.
    pub sources: Vec<MainContinuationWindowSource>,
    pub shape: MainContinuationWindowShape,
}

/// Canonical SourceId-ordered runtime identity of one continuation source: a
/// storage read, or the procedural virtual-setup column at that SourceId.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalSourceIdentity {
    Read(gkr_eval_ir::ReadPlace),
    VirtualSetup { kind: gkr_eval_ir::VirtualSetupKind },
}

impl MainContinuationWindowProgram {
    /// Canonical SourceId-ordered identities for runtime final repointing.
    /// Every source, virtual included, owns its dense publication column.
    pub fn canonical_source_identities(&self) -> Vec<CanonicalSourceIdentity> {
        self.sources
            .iter()
            .map(|source| match &source.origin.origin {
                super::common::source::OriginLeaf::Read(place) => {
                    CanonicalSourceIdentity::Read(*place)
                }
                super::common::source::OriginLeaf::VirtualSetup { kind } => {
                    CanonicalSourceIdentity::VirtualSetup { kind: *kind }
                }
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MainContinuationWindowLoweringError {
    Codec(LeanCodecError),
    Partition(&'static str),
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
) -> Result<usize, MainContinuationWindowLoweringError> {
    let coefficient_bank_slots = program
        .coefficients
        .coefficients
        .len()
        .checked_add(CoefficientRecipeId::RESERVED as usize)
        .ok_or(MainContinuationWindowLoweringError::Capacity {
            resource: "coefficient_bank_slots",
            required: usize::MAX,
            capacity: MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
        })?;
    for (resource, required, capacity) in [
        (
            "program_words",
            program.program.words.len(),
            MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
        ),
        (
            "sources",
            program.coefficients.sources.len(),
            MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
        ),
        (
            "source_windows",
            program.binding.windows.len(),
            MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY,
        ),
        (
            "immediates",
            program.coefficients.immediates.len(),
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
        ),
        (
            "coefficient_bank_slots",
            coefficient_bank_slots,
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
        ),
    ] {
        require_capacity(resource, required, capacity)?;
    }
    Ok(coefficient_bank_slots)
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

fn canonical_sources(
    binding: &LeanSourceBinding,
    coefficients: &CoeffLayer,
) -> Result<Vec<MainContinuationWindowSource>, MainContinuationWindowLoweringError> {
    let source_count = coefficients.sources.len();
    let mut canonical = vec![None; source_count];

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
            if canonical[index].is_some() {
                return Err(
                    MainContinuationWindowLoweringError::DuplicateSemanticSource { source: id },
                );
            }
            canonical[index] = Some(MainContinuationWindowSource {
                origin: coefficients.sources[index].clone(),
                raw_family: window.family,
                raw_column: column.column,
            });
        }
    }

    canonical
        .into_iter()
        .enumerate()
        .map(|(index, entry)| {
            entry.ok_or(MainContinuationWindowLoweringError::MissingSemanticSource {
                source: SourceId(index as u32),
            })
        })
        .collect()
}

/// Lower one continuation coordinate into the canonical main-window form.
pub fn lower_main_continuation_window_program(
    program: &ContinuationLayerProgram,
) -> Result<MainContinuationWindowProgram, MainContinuationWindowLoweringError> {
    let coefficient_bank_slots = validate_capacities(program)?;
    let atoms = validate_program(&program.program, &program.coefficients)
        .map_err(MainContinuationWindowLoweringError::Codec)?;
    let mut shape = MainContinuationWindowShape::EMPTY;

    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                if term.class == 0 {
                    shape.insert(MainContinuationWindowShape::PLAIN_LINEAR);
                }
            }
            LeanAtom::Group { members, .. } => {
                shape.insert(MainContinuationWindowShape::GROUPED);
                for member in &members {
                    let immediate = ImmediateId(member.coeff);
                    if immediate.bank_index().is_some() {
                        shape.insert(MainContinuationWindowShape::BANKED_GROUP_IMMEDIATE);
                    }
                    if immediate == ImmediateId::NEG_ONE {
                        shape.insert(MainContinuationWindowShape::NEGATIVE_GROUP_IMMEDIATE);
                    }
                }
            }
        }
    }
    if program.coefficients.c_init.is_some() {
        shape.insert(MainContinuationWindowShape::C_INIT);
    }
    if let Some(c_init) = program.coefficients.c_init {
        validate_coefficient_id(c_init.0, coefficient_bank_slots)?;
    }
    let sources = canonical_sources(&program.binding, &program.coefficients)?;
    Ok(MainContinuationWindowProgram {
        partitions: super::main_continuation_partitions::compile_main_continuation_partitions(
            &program.program.words,
            sources.len(),
        )
        .map_err(MainContinuationWindowLoweringError::Partition)?,
        program: program.program.clone(),
        c_init: program.coefficients.c_init,
        immediates: program.coefficients.immediates.clone(),
        sources,
        shape,
    })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::OnceLock;

    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::base::BabyBearField;
    use gkr_eval_ir::lower_dag;

    use super::*;
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
    fn cpu_main_continuation_window_capacity_mutation_gates() {
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
            .coefficients
            .immediates
            .resize(MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY + 1, 0);
        expect_capacity(
            &immediates,
            "immediates",
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY + 1,
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
        );

        let mut coefficients = source;
        coefficients.coefficients.coefficients.resize(
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
            coefficients.coefficients.coefficients[0].clone(),
        );
        expect_capacity(
            &coefficients,
            "coefficient_bank_slots",
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY
                + CoefficientRecipeId::RESERVED as usize,
            MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
        );
    }
}
