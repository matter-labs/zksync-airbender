//! Static lowering of a compiled R0 layer program into the window-3 sectioned
//! wire program consumed by the windowed backward executor.
//!
//! The product is per layer and carries no device pointers and no trace shape:
//! sections, wire words, source/window identities, interned coefficient plans,
//! and the native shape mask.

use std::collections::{BTreeMap, BTreeSet};

use field::PrimeField;
use gkr_eval_ir::FieldKind;

use super::common::group::CoeffGroupingAnalysis;
use super::common::lean_bind::{LeanBoundWindow, LeanSourceBinding};
use super::common::model::{
    CoeffError, CoeffLayer, CoeffTerm, CoefficientRecipeId, NormalizedCoefficientRecipe, SourceId,
    TermId,
};
use super::common::Bf;
use super::r0::R0LayerProgram;

pub const WINDOW_SECTION_WORDS: usize = 16;
pub const WINDOW_MAX_COEFFICIENT_PLANS: usize = 1_728;
pub const WINDOW_COEFFICIENT_BANK_BIAS: u16 = 2;
pub const WINDOW_SHAPE_DEFINED_BITS: u16 = 0x0fff;

const WINDOW_NEG_ONE_IMMEDIATE: u32 = 2_013_265_920;
const WINDOW_SOURCE_COLUMN_BITS: u16 = 7;
const WINDOW_SOURCE_COLUMNS: u16 = 1 << WINDOW_SOURCE_COLUMN_BITS;

const WINDOW_OPCODE_GROUP_BF: u16 = 6;
const WINDOW_OPCODE_GROUP_E4: u16 = 7;
const WINDOW_OPCODE_LINEAR_BF_PROCEDURAL: u16 = 4;
const WINDOW_OPCODE_PRODUCT_E4_E4: u16 = 5;
const WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B: u16 = 8;
const WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB: u16 = 9;
const WINDOW_OPCODE_LINEAR_E4_WIDE: u16 = 10;
const WINDOW_FLAG_HAS_PRODUCT: u16 = 1 << 15;
const WINDOW_FLAG_REDUCE_AFTER: u16 = 1 << 15;
const WINDOW_FLAG_NEGATE_COEFFICIENT: u16 = 1 << 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum WindowPhase {
    Bf,
    E4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WindowGroupedMember {
    term_class: u8,
    immediate: u32,
    source_a: u16,
    source_b: Option<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum WindowGroupedAtom {
    Singleton {
        phase: WindowPhase,
        coefficient_id: u32,
        term_class: u8,
        source_a: u16,
        source_b: Option<u16>,
    },
    Group {
        phase: WindowPhase,
        group_id: u32,
        core: NormalizedCoefficientRecipe,
        members: Vec<WindowGroupedMember>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WindowGroupedProgram {
    atoms: Vec<WindowGroupedAtom>,
    source_slots: Vec<u16>,
}

/// Compile-time hot-loop features of the sectioned wire program. Section
/// presence is descriptor metadata rather than a shape bit: an empty section is
/// skipped by its uniform endpoint comparison.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct WindowShape(u16);

impl WindowShape {
    pub const EMPTY: Self = Self(0);
    pub const BF_PROCEDURAL: Self = Self(1 << 0);
    pub const BF_BANKED_IMMEDIATE: Self = Self(1 << 1);
    pub const BF_INNER_REDUCTION: Self = Self(1 << 2);
    pub const BF_LINEAR_TAIL: Self = Self(1 << 3);
    pub const E4_SINGLETON_CLASS_3: Self = Self(1 << 4);
    pub const E4_SINGLETON_CLASS_5: Self = Self(1 << 5);
    pub const E4_FIXED_PAIR: Self = Self(1 << 6);
    pub const BF_NEGATIVE_FACTOR: Self = Self(1 << 7);
    pub const E4_NEGATIVE_FACTOR: Self = Self(1 << 8);
    pub const E4_PAIR_CLASS_3: Self = Self(1 << 9);
    pub const E4_PAIR_CLASS_5: Self = Self(1 << 10);
    pub const BF_SINGLE_PRODUCT_PREFIX: Self = Self(1 << 11);

    pub fn from_bits(bits: u16) -> Result<Self, WindowLoweringError> {
        if bits & !WINDOW_SHAPE_DEFINED_BITS != 0 {
            return Err(WindowLoweringError::UndefinedShapeBits { bits });
        }
        Ok(Self(bits))
    }

    pub const fn bits(self) -> u16 {
        self.0
    }

    pub const fn contains(self, feature: Self) -> bool {
        self.0 & feature.0 == feature.0
    }

    pub fn insert(&mut self, feature: Self) {
        self.0 |= feature.0;
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum WindowCoefficientPlan {
    Direct(NormalizedCoefficientRecipe),
    Scaled {
        recipe: NormalizedCoefficientRecipe,
        scalar: u32,
    },
    LinearBasis {
        recipe: NormalizedCoefficientRecipe,
        limb: u8,
    },
}

/// One operand word that carries a source addressing lane.
///
/// The lowered lane is `(window << 7) | relative column`, which is the artifact's
/// geometry, not storage's: production storage partitions a layer's columns into
/// per-class backings, so one artifact window's columns can land in different
/// matrices. The runtime binder therefore re-addresses each source and rewrites
/// exactly these words. This table is what lets it do so without decoding the
/// wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WindowSourceLane {
    /// Index into [`WindowProgram::words`].
    pub word: u32,
    /// The source slot this operand reads, indexing [`WindowProgram::source_slots`].
    pub source: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowProgram {
    pub layer: usize,
    pub words: Vec<u16>,
    pub source_slots: Vec<u16>,
    /// Every lane-bearing operand word of `words`, in ascending word order.
    pub source_lanes: Vec<WindowSourceLane>,
    pub windows: Vec<LeanBoundWindow>,
    pub immediates: Vec<u32>,
    pub sections: [u32; WINDOW_SECTION_WORDS],
    pub coefficient_plans: Vec<WindowCoefficientPlan>,
    pub shape: WindowShape,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WindowLoweringError {
    Grouping(CoeffError),
    UnknownSource {
        term: u32,
        source: u32,
    },
    UnknownWindow {
        source: u32,
        window: u8,
    },
    InvalidRelativeColumn {
        source: u32,
        column: u16,
    },
    IncompleteTermPartition {
        expected: usize,
        observed: usize,
    },
    UnsupportedTermClass(u8),
    InvalidCoefficient(u32),
    UndefinedShapeBits {
        bits: u16,
    },
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    Encoding(String),
}

impl core::fmt::Display for WindowLoweringError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for WindowLoweringError {}

/// The layer-scoped inputs the sectioned lowering reads. Kept separate from
/// [`R0LayerProgram`] so a frozen corpus coordinate can drive the same lowering.
#[derive(Clone, Copy, Debug)]
pub struct WindowLoweringInputs<'a> {
    pub layer: usize,
    pub binding: &'a LeanSourceBinding,
    pub coefficient_recipes: &'a [NormalizedCoefficientRecipe],
}

pub fn lower_window_program(
    program: &R0LayerProgram,
) -> Result<WindowProgram, WindowLoweringError> {
    let analysis = super::common::group::analyze_coeff_grouping(&program.coefficients)
        .map_err(WindowLoweringError::Grouping)?;
    let grouped = build_window_grouped_program(program, &analysis)?;
    lower_window_sections(
        &WindowLoweringInputs {
            layer: program.layer,
            binding: &program.binding,
            coefficient_recipes: &program.coefficient_recipes,
        },
        &grouped,
    )
}

// ── Schedule split ───────────────────────────────────────────────────────────

struct ScheduleAtom {
    terms: Vec<TermId>,
    phase: WindowPhase,
}

fn source_backing_field(
    binding: &LeanSourceBinding,
    term: TermId,
    source: u32,
) -> Result<FieldKind, WindowLoweringError> {
    let slot =
        binding
            .source_slots
            .get(source as usize)
            .ok_or(WindowLoweringError::UnknownSource {
                term: term.0,
                source,
            })?;
    binding
        .windows
        .get(usize::from(slot.window))
        .map(|window| window.backing_field())
        .ok_or(WindowLoweringError::UnknownWindow {
            source,
            window: slot.window,
        })
}

fn term_value_phase(
    binding: &LeanSourceBinding,
    term: &CoeffTerm,
) -> Result<WindowPhase, WindowLoweringError> {
    let phase = match term {
        CoeffTerm::C0Linear { value, .. } => {
            match source_backing_field(binding, term.id(), value.source.0)? {
                FieldKind::Base => WindowPhase::Bf,
                FieldKind::Ext => WindowPhase::E4,
            }
        }
        CoeffTerm::C2Product { lhs, rhs, .. } => {
            let lhs_field = source_backing_field(binding, term.id(), lhs.source.0)?;
            let rhs_field = source_backing_field(binding, term.id(), rhs.source.0)?;
            match (lhs_field, rhs_field) {
                (FieldKind::Base, FieldKind::Base) => WindowPhase::Bf,
                _ => WindowPhase::E4,
            }
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => {
            let lhs_field = source_backing_field(binding, term.id(), lhs.0)?;
            let rhs_field = source_backing_field(binding, term.id(), rhs.0)?;
            match (lhs_field, rhs_field) {
                (FieldKind::Base, FieldKind::Base) => WindowPhase::Bf,
                _ => WindowPhase::E4,
            }
        }
    };
    Ok(phase)
}

fn validate_projection_uses(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    term: &CoeffTerm,
) -> Result<(), WindowLoweringError> {
    let mut projections = Vec::new();
    term.for_each_projection_use(|projection| projections.push(projection));
    for projection in projections {
        let source = projection.source.0;
        layer
            .source(projection.source)
            .ok_or(WindowLoweringError::UnknownSource {
                term: term.id().0,
                source,
            })?;
        let slot = binding.source_slots.get(source as usize).ok_or(
            WindowLoweringError::UnknownSource {
                term: term.id().0,
                source,
            },
        )?;
        if slot.column >= WINDOW_SOURCE_COLUMNS {
            return Err(WindowLoweringError::InvalidRelativeColumn {
                source,
                column: slot.column,
            });
        }
        binding.windows.get(usize::from(slot.window)).ok_or(
            WindowLoweringError::UnknownWindow {
                source,
                window: slot.window,
            },
        )?;
        u16::try_from(source).map_err(|_| WindowLoweringError::UnknownSource {
            term: term.id().0,
            source,
        })?;
    }
    Ok(())
}

/// The analysis-grouped atom order, BF-valued atoms first. Mirrors the split the
/// sectioned executor consumes: within a phase the canonical atom order is kept.
fn build_schedule_split(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    analysis: &CoeffGroupingAnalysis,
) -> Result<Vec<ScheduleAtom>, WindowLoweringError> {
    let original_recipes: BTreeMap<_, _> = analysis.term_recipes.iter().cloned().collect();
    if original_recipes.len() != layer.terms.len() {
        return Err(WindowLoweringError::IncompleteTermPartition {
            expected: layer.terms.len(),
            observed: original_recipes.len(),
        });
    }
    let terms_by_id: BTreeMap<_, _> = layer.terms.iter().map(|term| (term.id(), term)).collect();
    let mut grouped_terms = BTreeSet::new();
    let mut atom_specs = Vec::new();
    for group in &analysis.groups {
        let mut members: Vec<TermId> = group.members.iter().map(|member| member.term).collect();
        members.sort();
        grouped_terms.extend(members.iter().copied());
        atom_specs.push(members);
    }
    for term in &layer.terms {
        if !grouped_terms.contains(&term.id()) {
            if !original_recipes.contains_key(&term.id()) {
                return Err(WindowLoweringError::IncompleteTermPartition {
                    expected: layer.terms.len(),
                    observed: original_recipes.len(),
                });
            }
            atom_specs.push(vec![term.id()]);
        }
    }
    atom_specs.sort_by_key(|terms| terms[0]);

    let mut atoms = Vec::with_capacity(atom_specs.len());
    for terms in atom_specs {
        let mut phase = WindowPhase::Bf;
        for term_id in &terms {
            let term = terms_by_id.get(term_id).copied().ok_or(
                WindowLoweringError::IncompleteTermPartition {
                    expected: layer.terms.len(),
                    observed: terms.len(),
                },
            )?;
            if term_value_phase(binding, term)? == WindowPhase::E4 {
                phase = WindowPhase::E4;
            }
            validate_projection_uses(layer, binding, term)?;
        }
        atoms.push(ScheduleAtom { terms, phase });
    }
    let (mut split, e4) = atoms
        .into_iter()
        .partition::<Vec<_>, _>(|atom| atom.phase == WindowPhase::Bf);
    split.extend(e4);
    Ok(split)
}

// ── Grouped program ──────────────────────────────────────────────────────────

fn window_term_class(term: &CoeffTerm) -> Result<u8, WindowLoweringError> {
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
        CoeffTerm::DualProduct { .. } => return Err(WindowLoweringError::UnsupportedTermClass(5)),
    };
    Ok(class)
}

/// Operand order for a mixed base/ext product is BF first, matching the wire's
/// `(bf, e4)` operand convention.
fn window_term_sources(term: &CoeffTerm) -> (SourceId, Option<SourceId>) {
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

fn window_source_slots(binding: &LeanSourceBinding) -> Vec<u16> {
    binding
        .source_slots
        .iter()
        .map(|slot| (u16::from(slot.window) << WINDOW_SOURCE_COLUMN_BITS) | slot.column)
        .collect()
}

fn stored_slot(
    binding: &LeanSourceBinding,
    term: TermId,
    source: SourceId,
) -> Result<u16, WindowLoweringError> {
    let unknown = WindowLoweringError::UnknownSource {
        term: term.0,
        source: source.0,
    };
    let slot = u16::try_from(source.0).map_err(|_| unknown.clone())?;
    if usize::from(slot) >= binding.source_slots.len() {
        return Err(unknown);
    }
    Ok(slot)
}

fn build_window_grouped_program(
    program: &R0LayerProgram,
    analysis: &CoeffGroupingAnalysis,
) -> Result<WindowGroupedProgram, WindowLoweringError> {
    let layer = &program.coefficients;
    let binding = &program.binding;
    let split = build_schedule_split(layer, binding, analysis)?;
    let terms_by_id: BTreeMap<_, _> = layer.terms.iter().map(|term| (term.id(), term)).collect();
    let mut group_of_term = BTreeMap::new();
    for (group_id, group) in analysis.groups.iter().enumerate() {
        for (member_index, member) in group.members.iter().enumerate() {
            group_of_term.insert(member.term, (group_id as u32, member_index as u32));
        }
    }

    let mut atoms = Vec::with_capacity(split.len());
    for atom in &split {
        if atom.terms.len() == 1 {
            let term = terms_by_id.get(&atom.terms[0]).copied().ok_or(
                WindowLoweringError::IncompleteTermPartition {
                    expected: layer.terms.len(),
                    observed: split.len(),
                },
            )?;
            let class = window_term_class(term)?;
            let (source_a, source_b) = window_term_sources(term);
            atoms.push(WindowGroupedAtom::Singleton {
                phase: atom.phase,
                coefficient_id: term.coefficient().0,
                term_class: class,
                source_a: stored_slot(binding, term.id(), source_a)?,
                source_b: source_b
                    .map(|source| stored_slot(binding, term.id(), source))
                    .transpose()?,
            });
            continue;
        }
        let group_id = group_of_term
            .get(&atom.terms[0])
            .map(|entry| entry.0)
            .ok_or_else(|| {
                WindowLoweringError::Encoding("grouped atom has no analysis group".into())
            })?;
        let group = analysis.groups.get(group_id as usize).ok_or_else(|| {
            WindowLoweringError::Encoding("grouped atom references an absent group".into())
        })?;
        let mut members = Vec::with_capacity(group.members.len());
        for (member_index, member) in group.members.iter().enumerate() {
            if group_of_term.get(&member.term) != Some(&(group_id, member_index as u32)) {
                return Err(WindowLoweringError::Encoding(
                    "analysis group members are not in member order".into(),
                ));
            }
            let term = terms_by_id.get(&member.term).copied().ok_or(
                WindowLoweringError::IncompleteTermPartition {
                    expected: layer.terms.len(),
                    observed: group.members.len(),
                },
            )?;
            let class = window_term_class(term)?;
            let (source_a, source_b) = window_term_sources(term);
            members.push(WindowGroupedMember {
                term_class: class,
                immediate: member.immediate,
                source_a: stored_slot(binding, term.id(), source_a)?,
                source_b: source_b
                    .map(|source| stored_slot(binding, term.id(), source))
                    .transpose()?,
            });
        }
        atoms.push(WindowGroupedAtom::Group {
            phase: atom.phase,
            group_id,
            core: group.core.clone(),
            members,
        });
    }
    Ok(WindowGroupedProgram {
        atoms,
        source_slots: window_source_slots(binding),
    })
}

// ── Sectioned lowering ───────────────────────────────────────────────────────

fn checked_u16(value: usize, resource: &'static str) -> Result<u16, WindowLoweringError> {
    u16::try_from(value).map_err(|_| WindowLoweringError::Capacity {
        resource,
        required: value,
        capacity: u16::MAX as usize,
    })
}

fn u32_section_end(value: usize, resource: &'static str) -> Result<u32, WindowLoweringError> {
    u32::try_from(value).map_err(|_| WindowLoweringError::Capacity {
        resource,
        required: value,
        capacity: u32::MAX as usize,
    })
}

fn recipe_for_coefficient(
    recipes: &[NormalizedCoefficientRecipe],
    coefficient: u32,
) -> Result<NormalizedCoefficientRecipe, WindowLoweringError> {
    let id = CoefficientRecipeId(coefficient);
    if id == CoefficientRecipeId::ONE {
        return Ok(NormalizedCoefficientRecipe::one());
    }
    if id == CoefficientRecipeId::NEG_ONE {
        return Ok(NormalizedCoefficientRecipe::neg_one());
    }
    id.bank_index()
        .and_then(|index| recipes.get(index))
        .cloned()
        .ok_or(WindowLoweringError::InvalidCoefficient(coefficient))
}

fn intern_plan(
    plans: &mut Vec<WindowCoefficientPlan>,
    ids: &mut BTreeMap<WindowCoefficientPlan, u16>,
    plan: WindowCoefficientPlan,
) -> Result<u16, WindowLoweringError> {
    if let Some(id) = ids.get(&plan) {
        return Ok(*id);
    }
    let id = checked_u16(
        usize::from(WINDOW_COEFFICIENT_BANK_BIAS) + plans.len(),
        "dedicated coefficient plans",
    )?;
    plans.push(plan.clone());
    ids.insert(plan, id);
    Ok(id)
}

fn push_linear_basis_plans(
    plans: &mut Vec<WindowCoefficientPlan>,
    ids: &mut BTreeMap<WindowCoefficientPlan, u16>,
    recipe: &NormalizedCoefficientRecipe,
) -> Result<u16, WindowLoweringError> {
    let first = checked_u16(
        usize::from(WINDOW_COEFFICIENT_BANK_BIAS) + plans.len(),
        "dedicated linear basis plans",
    )?;
    for limb in 0..4u8 {
        let plan = WindowCoefficientPlan::LinearBasis {
            recipe: recipe.clone(),
            limb,
        };
        let id = checked_u16(
            usize::from(WINDOW_COEFFICIENT_BANK_BIAS) + plans.len(),
            "dedicated linear basis plans",
        )?;
        if id != first + u16::from(limb) {
            return Err(WindowLoweringError::Encoding(
                "dedicated linear basis IDs are not consecutive".to_owned(),
            ));
        }
        if ids.contains_key(&plan) {
            return Err(WindowLoweringError::Encoding(
                "dedicated linear basis plan is duplicated".to_owned(),
            ));
        }
        plans.push(plan.clone());
        ids.insert(plan, id);
    }
    Ok(first)
}

struct WindowSlotSource {
    slot: u16,
    lane: u16,
    procedural_kind: Option<u16>,
}

fn window_slot_source(
    binding: &LeanSourceBinding,
    slot: u16,
) -> Result<WindowSlotSource, WindowLoweringError> {
    let bound = binding
        .source_slots
        .get(usize::from(slot))
        .ok_or_else(|| WindowLoweringError::Encoding("dedicated source slot absent".into()))?;
    let window = binding
        .windows
        .get(usize::from(bound.window))
        .ok_or_else(|| WindowLoweringError::Encoding("dedicated source window absent".into()))?;
    Ok(WindowSlotSource {
        slot,
        lane: (u16::from(bound.window) << WINDOW_SOURCE_COLUMN_BITS) | bound.column,
        procedural_kind: window.procedural_kind().map(u16::from),
    })
}

/// One instruction's operand words, with the source identity of each word that
/// carries an addressing lane (a procedural operand carries a kind, not a lane).
struct WindowOperandWords {
    opcode: u16,
    source_a: u16,
    source_b: u16,
    lane_source_a: Option<u16>,
    lane_source_b: Option<u16>,
}

fn window_operand_words(
    binding: &LeanSourceBinding,
    term_class: u8,
    source_a: u16,
    source_b: Option<u16>,
) -> Result<WindowOperandWords, WindowLoweringError> {
    let a = window_slot_source(binding, source_a)?;
    let b = source_b
        .map(|source| window_slot_source(binding, source))
        .transpose()?;
    let slot_b = b.as_ref().map_or(0, |b| b.lane);
    let unsupported = || {
        WindowLoweringError::Encoding(
            "dedicated procedural source appears in an unsupported term class".to_owned(),
        )
    };
    let words = match (
        term_class,
        a.procedural_kind,
        b.as_ref().and_then(|b| b.procedural_kind),
    ) {
        (0, Some(kind), None) => WindowOperandWords {
            opcode: WINDOW_OPCODE_LINEAR_BF_PROCEDURAL,
            source_a: kind,
            source_b: 0,
            lane_source_a: None,
            lane_source_b: None,
        },
        // A procedural operand is normalized into the `source_b` word, so the
        // addressed half of a mixed product always lands in `source_a`.
        (2, Some(kind), None) => WindowOperandWords {
            opcode: WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B,
            source_a: slot_b,
            source_b: kind,
            lane_source_a: Some(b.as_ref().ok_or_else(unsupported)?.slot),
            lane_source_b: None,
        },
        (2, None, Some(kind)) => WindowOperandWords {
            opcode: WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B,
            source_a: a.lane,
            source_b: kind,
            lane_source_a: Some(a.slot),
            lane_source_b: None,
        },
        (2, Some(kind_a), Some(kind_b)) => WindowOperandWords {
            opcode: WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB,
            source_a: kind_a,
            source_b: kind_b,
            lane_source_a: None,
            lane_source_b: None,
        },
        (class, None, None) => WindowOperandWords {
            opcode: if class == 4 {
                WINDOW_OPCODE_PRODUCT_E4_E4
            } else {
                u16::from(class)
            },
            source_a: a.lane,
            source_b: slot_b,
            lane_source_a: Some(a.slot),
            lane_source_b: b.as_ref().map(|b| b.slot),
        },
        _ => return Err(unsupported()),
    };
    Ok(words)
}

fn window_operands(
    binding: &LeanSourceBinding,
    term_class: u8,
    source_a: u16,
    source_b: Option<u16>,
) -> Result<(u16, u16, u16), WindowLoweringError> {
    let words = window_operand_words(binding, term_class, source_a, source_b)?;
    Ok((words.opcode, words.source_a, words.source_b))
}

/// Derive only those compile-time features that remove work from an active
/// sectioned hot loop. Checked independently from the wire emission so a new
/// grouped-program shape cannot be silently reinterpreted.
fn derive_window_shape(
    binding: &LeanSourceBinding,
    program: &WindowGroupedProgram,
) -> Result<WindowShape, WindowLoweringError> {
    let mut shape = WindowShape::EMPTY;

    for atom in &program.atoms {
        match atom {
            WindowGroupedAtom::Singleton {
                phase: WindowPhase::Bf,
                term_class,
                source_a,
                source_b,
                ..
            } => {
                let (class, _, _) = window_operands(binding, *term_class, *source_a, *source_b)?;
                if matches!(
                    class,
                    WINDOW_OPCODE_LINEAR_BF_PROCEDURAL
                        | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
                        | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
                ) {
                    shape.insert(WindowShape::BF_PROCEDURAL);
                }
                if !matches!(
                    class,
                    0 | 2
                        | WINDOW_OPCODE_LINEAR_BF_PROCEDURAL
                        | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
                        | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
                ) {
                    return Err(WindowLoweringError::Encoding(format!(
                        "unsupported BF singleton class {class}"
                    )));
                }
            }
            WindowGroupedAtom::Singleton {
                phase: WindowPhase::E4,
                term_class,
                source_a,
                source_b,
                ..
            } => {
                let (class, _, _) = window_operands(binding, *term_class, *source_a, *source_b)?;
                match class {
                    1 => {}
                    3 => shape.insert(WindowShape::E4_SINGLETON_CLASS_3),
                    WINDOW_OPCODE_PRODUCT_E4_E4 => shape.insert(WindowShape::E4_SINGLETON_CLASS_5),
                    _ => {
                        return Err(WindowLoweringError::Encoding(format!(
                            "unsupported E4 singleton class {class}"
                        )));
                    }
                }
            }
            WindowGroupedAtom::Group {
                phase: WindowPhase::Bf,
                members,
                ..
            } => {
                let (product_prefix, linear_tail, ordered) = bf_group_partition(members)?;
                if product_prefix > 4 {
                    shape.insert(WindowShape::BF_INNER_REDUCTION);
                }
                if product_prefix == 1 {
                    shape.insert(WindowShape::BF_SINGLE_PRODUCT_PREFIX);
                }
                if linear_tail == 1 {
                    shape.insert(WindowShape::BF_LINEAR_TAIL);
                }
                for member in ordered {
                    if member.immediate != 1 && member.immediate != WINDOW_NEG_ONE_IMMEDIATE {
                        shape.insert(WindowShape::BF_BANKED_IMMEDIATE);
                    }
                    if member.immediate == WINDOW_NEG_ONE_IMMEDIATE {
                        shape.insert(WindowShape::BF_NEGATIVE_FACTOR);
                    }
                    let (class, _, _) = window_operands(
                        binding,
                        member.term_class,
                        member.source_a,
                        member.source_b,
                    )?;
                    if matches!(
                        class,
                        WINDOW_OPCODE_LINEAR_BF_PROCEDURAL
                            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
                            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
                    ) {
                        shape.insert(WindowShape::BF_PROCEDURAL);
                    }
                    if !matches!(
                        class,
                        0 | 2
                            | WINDOW_OPCODE_LINEAR_BF_PROCEDURAL
                            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
                            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
                    ) {
                        return Err(WindowLoweringError::Encoding(format!(
                            "unsupported BF group member class {class}"
                        )));
                    }
                }
            }
            WindowGroupedAtom::Group {
                phase: WindowPhase::E4,
                members,
                ..
            } => {
                let products = e4_group_products(members)?;
                let mut e4_products = 0usize;
                let mut bf_products = 0usize;
                let mut e4_product_classes = Vec::with_capacity(products.len());
                for product in products {
                    if !matches!(product.immediate, 1 | WINDOW_NEG_ONE_IMMEDIATE) {
                        return Err(WindowLoweringError::Encoding(format!(
                            "unsupported E4 product factor {}",
                            product.immediate
                        )));
                    }
                    let (class, _, _) = window_operands(
                        binding,
                        product.term_class,
                        product.source_a,
                        product.source_b,
                    )?;
                    match class {
                        2
                        | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
                        | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB => {
                            bf_products += 1;
                            if product.immediate == WINDOW_NEG_ONE_IMMEDIATE {
                                shape.insert(WindowShape::BF_NEGATIVE_FACTOR);
                            }
                            if class != 2 {
                                shape.insert(WindowShape::BF_PROCEDURAL);
                            }
                        }
                        3 => {
                            e4_products += 1;
                            e4_product_classes.push(class);
                            if product.immediate == WINDOW_NEG_ONE_IMMEDIATE {
                                shape.insert(WindowShape::E4_NEGATIVE_FACTOR);
                            }
                            shape.insert(WindowShape::E4_SINGLETON_CLASS_3);
                        }
                        WINDOW_OPCODE_PRODUCT_E4_E4 => {
                            e4_products += 1;
                            e4_product_classes.push(class);
                            if product.immediate == WINDOW_NEG_ONE_IMMEDIATE {
                                shape.insert(WindowShape::E4_NEGATIVE_FACTOR);
                            }
                            shape.insert(WindowShape::E4_SINGLETON_CLASS_5);
                        }
                        _ => {
                            return Err(WindowLoweringError::Encoding(format!(
                                "unsupported E4 product class {class}"
                            )));
                        }
                    }
                }
                if products.len() == 2 {
                    if bf_products != 0 || e4_products != 2 {
                        return Err(WindowLoweringError::Encoding(
                            "dedicated E4 pair requires exactly two E4-valued products".to_owned(),
                        ));
                    }
                    if e4_product_classes[0] != e4_product_classes[1] {
                        return Err(WindowLoweringError::Encoding(format!(
                            "heterogeneous E4 pair classes {} and {}",
                            e4_product_classes[0], e4_product_classes[1]
                        )));
                    }
                    shape.insert(WindowShape::E4_FIXED_PAIR);
                    shape.insert(if e4_product_classes[0] == 3 {
                        WindowShape::E4_PAIR_CLASS_3
                    } else {
                        WindowShape::E4_PAIR_CLASS_5
                    });
                } else if bf_products + e4_products != 1 {
                    return Err(WindowLoweringError::Encoding(
                        "dedicated E4 singleton extraction produced no product".to_owned(),
                    ));
                }
            }
        }
    }

    Ok(shape)
}

fn bf_group_partition(
    members: &[WindowGroupedMember],
) -> Result<(usize, usize, Vec<&WindowGroupedMember>), WindowLoweringError> {
    let mut ordered = members.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|member| member.term_class != 2);
    let product_prefix = ordered
        .iter()
        .take_while(|member| member.term_class == 2)
        .count();
    let linear_tail = ordered.len() - product_prefix;
    if product_prefix == 0 || linear_tail > 1 {
        return Err(WindowLoweringError::Encoding(format!(
            "dedicated BF group requires one or more products and at most one linear tail; products={product_prefix} tail={linear_tail}"
        )));
    }
    Ok((product_prefix, linear_tail, ordered))
}

fn e4_group_products(
    members: &[WindowGroupedMember],
) -> Result<&[WindowGroupedMember], WindowLoweringError> {
    if !matches!(members.len(), 2 | 3) {
        return Err(WindowLoweringError::Encoding(format!(
            "dedicated E4 group has {} members; expected linear plus one or two products",
            members.len()
        )));
    }
    let linear = &members[0];
    if linear.term_class != 1 || linear.immediate != 1 || linear.source_b.is_some() {
        return Err(WindowLoweringError::Encoding(
            "dedicated E4 group requires exactly one first-position +1 linear member".to_owned(),
        ));
    }
    Ok(&members[1..])
}

fn push_instruction(words: &mut Vec<u16>, class: u16, factor: u16, source_a: u16, source_b: u16) {
    words.extend([class, factor, source_a, source_b]);
}

/// Push one term instruction, recording which of its two operand words carry
/// addressing lanes. `word` positions are section-local and rebased when the
/// sections are concatenated.
fn push_term(
    words: &mut Vec<u16>,
    lanes: &mut Vec<WindowSourceLane>,
    factor: u16,
    operands: &WindowOperandWords,
) {
    let record = words.len() as u32;
    if let Some(source) = operands.lane_source_a {
        lanes.push(WindowSourceLane {
            word: record + 2,
            source,
        });
    }
    if let Some(source) = operands.lane_source_b {
        lanes.push(WindowSourceLane {
            word: record + 3,
            source,
        });
    }
    push_instruction(
        words,
        operands.opcode,
        factor,
        operands.source_a,
        operands.source_b,
    );
}

/// Push the wide linear-E4 form of a term: one lane in `source_a`, an unused
/// `source_b`.
fn push_wide_linear(
    words: &mut Vec<u16>,
    lanes: &mut Vec<WindowSourceLane>,
    basis: u16,
    operands: &WindowOperandWords,
) -> Result<(), WindowLoweringError> {
    let source = operands.lane_source_a.ok_or_else(|| {
        WindowLoweringError::Encoding("dedicated E4 linear member is not addressed".to_owned())
    })?;
    lanes.push(WindowSourceLane {
        word: words.len() as u32 + 2,
        source,
    });
    push_instruction(
        words,
        WINDOW_OPCODE_LINEAR_E4_WIDE,
        basis,
        operands.source_a,
        0,
    );
    Ok(())
}

fn window_immediates(program: &WindowGroupedProgram) -> Vec<u32> {
    let mut values = BTreeSet::new();
    for atom in &program.atoms {
        if let WindowGroupedAtom::Group { members, .. } = atom {
            for member in members {
                if member.immediate != 1 && member.immediate != WINDOW_NEG_ONE_IMMEDIATE {
                    values.insert(member.immediate);
                }
            }
        }
    }
    values.into_iter().collect()
}

fn lower_window_sections(
    inputs: &WindowLoweringInputs<'_>,
    program: &WindowGroupedProgram,
) -> Result<WindowProgram, WindowLoweringError> {
    let binding = inputs.binding;
    let recipes = inputs.coefficient_recipes;
    let one = NormalizedCoefficientRecipe::one();
    let neg_one = NormalizedCoefficientRecipe::neg_one();
    let mut plans = Vec::new();
    let mut plan_ids = BTreeMap::<WindowCoefficientPlan, u16>::new();
    let direct_id = |recipe: &NormalizedCoefficientRecipe,
                     plans: &mut Vec<WindowCoefficientPlan>,
                     plan_ids: &mut BTreeMap<WindowCoefficientPlan, u16>|
     -> Result<u16, WindowLoweringError> {
        if *recipe == one {
            Ok(0)
        } else if *recipe == neg_one {
            Ok(1)
        } else {
            intern_plan(
                plans,
                plan_ids,
                WindowCoefficientPlan::Direct(recipe.clone()),
            )
        }
    };
    let raw_immediates = window_immediates(program);
    let immediate_ids = raw_immediates
        .iter()
        .enumerate()
        .map(|(index, immediate)| (*immediate, WINDOW_COEFFICIENT_BANK_BIAS + index as u16))
        .collect::<BTreeMap<_, _>>();
    let immediate_id = |value: u32| -> Result<u16, WindowLoweringError> {
        if value == 1 {
            Ok(0)
        } else if value == WINDOW_NEG_ONE_IMMEDIATE {
            Ok(1)
        } else {
            immediate_ids
                .get(&value)
                .copied()
                .ok_or_else(|| WindowLoweringError::Encoding("dedicated immediate absent".into()))
        }
    };

    let mut bf = Vec::<u16>::new();
    let mut linear_e4 = Vec::<u16>::new();
    let mut e4_single = Vec::<u16>::new();
    let mut e4_pair = Vec::<u16>::new();
    let mut bf_lanes = Vec::<WindowSourceLane>::new();
    let mut linear_lanes = Vec::<WindowSourceLane>::new();
    let mut single_lanes = Vec::<WindowSourceLane>::new();
    let mut pair_lanes = Vec::<WindowSourceLane>::new();

    for atom in &program.atoms {
        match atom {
            WindowGroupedAtom::Singleton {
                phase: WindowPhase::Bf,
                coefficient_id,
                term_class,
                source_a,
                source_b,
            } => {
                let recipe = recipe_for_coefficient(recipes, *coefficient_id)?;
                let operands = window_operand_words(binding, *term_class, *source_a, *source_b)?;
                push_term(
                    &mut bf,
                    &mut bf_lanes,
                    direct_id(&recipe, &mut plans, &mut plan_ids)?,
                    &operands,
                );
            }
            WindowGroupedAtom::Singleton {
                phase: WindowPhase::E4,
                coefficient_id,
                term_class,
                source_a,
                source_b,
            } => {
                let recipe = recipe_for_coefficient(recipes, *coefficient_id)?;
                let operands = window_operand_words(binding, *term_class, *source_a, *source_b)?;
                let class = operands.opcode;
                if class == 1 {
                    let basis = push_linear_basis_plans(&mut plans, &mut plan_ids, &recipe)?;
                    push_wide_linear(&mut linear_e4, &mut linear_lanes, basis, &operands)?;
                } else if matches!(class, 3 | WINDOW_OPCODE_PRODUCT_E4_E4) {
                    push_term(
                        &mut e4_single,
                        &mut single_lanes,
                        direct_id(&recipe, &mut plans, &mut plan_ids)?,
                        &operands,
                    );
                } else {
                    return Err(WindowLoweringError::Encoding(format!(
                        "unsupported sectioned E4 singleton class {class}"
                    )));
                }
            }
            WindowGroupedAtom::Group {
                phase: WindowPhase::Bf,
                core,
                members,
                ..
            } => {
                let (product_prefix, _, ordered) = bf_group_partition(members)?;
                push_instruction(
                    &mut bf,
                    WINDOW_OPCODE_GROUP_BF,
                    direct_id(core, &mut plans, &mut plan_ids)?,
                    checked_u16(ordered.len(), "dedicated BF group members")?,
                    checked_u16(product_prefix, "dedicated BF product prefix")?
                        | WINDOW_FLAG_HAS_PRODUCT,
                );
                for (index, member) in ordered.iter().enumerate() {
                    let mut factor = immediate_id(member.immediate)?;
                    if index < product_prefix && (index + 1) % 4 == 0 && index + 1 < product_prefix
                    {
                        factor |= WINDOW_FLAG_REDUCE_AFTER;
                    }
                    let operands = window_operand_words(
                        binding,
                        member.term_class,
                        member.source_a,
                        member.source_b,
                    )?;
                    push_term(&mut bf, &mut bf_lanes, factor, &operands);
                }
            }
            WindowGroupedAtom::Group {
                phase: WindowPhase::E4,
                core,
                members,
                ..
            } => {
                let products = e4_group_products(members)?;
                let linear = &members[0];
                let linear_operands = window_operand_words(
                    binding,
                    linear.term_class,
                    linear.source_a,
                    linear.source_b,
                )?;
                if linear_operands.opcode != 1 || linear_operands.source_b != 0 {
                    return Err(WindowLoweringError::Encoding(
                        "dedicated E4 linear member has an invalid source shape".to_owned(),
                    ));
                }
                let basis = push_linear_basis_plans(&mut plans, &mut plan_ids, core)?;
                push_wide_linear(&mut linear_e4, &mut linear_lanes, basis, &linear_operands)?;

                if products.len() == 1 {
                    let product = &products[0];
                    let operands = window_operand_words(
                        binding,
                        product.term_class,
                        product.source_a,
                        product.source_b,
                    )?;
                    let class = operands.opcode;
                    if !matches!(product.immediate, 1 | WINDOW_NEG_ONE_IMMEDIATE) {
                        return Err(WindowLoweringError::Encoding(format!(
                            "unsupported sectioned singleton factor {}",
                            product.immediate
                        )));
                    }
                    let coefficient = basis
                        | if product.immediate == WINDOW_NEG_ONE_IMMEDIATE {
                            WINDOW_FLAG_NEGATE_COEFFICIENT
                        } else {
                            0
                        };
                    if matches!(
                        class,
                        2 | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
                            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
                    ) {
                        push_term(&mut bf, &mut bf_lanes, coefficient, &operands);
                    } else if matches!(class, 3 | WINDOW_OPCODE_PRODUCT_E4_E4) {
                        push_term(&mut e4_single, &mut single_lanes, coefficient, &operands);
                    } else {
                        return Err(WindowLoweringError::Encoding(format!(
                            "unsupported sectioned E4 product class {class}"
                        )));
                    }
                } else {
                    push_instruction(&mut e4_pair, WINDOW_OPCODE_GROUP_E4, basis, 0, 0);
                    let mut pair_class = None;
                    for product in products {
                        let operands = window_operand_words(
                            binding,
                            product.term_class,
                            product.source_a,
                            product.source_b,
                        )?;
                        let class = operands.opcode;
                        if !matches!(class, 3 | WINDOW_OPCODE_PRODUCT_E4_E4) {
                            return Err(WindowLoweringError::Encoding(format!(
                                "unsupported sectioned E4 pair class {class}"
                            )));
                        }
                        if let Some(expected) = pair_class {
                            if class != expected {
                                return Err(WindowLoweringError::Encoding(format!(
                                    "heterogeneous E4 pair classes {expected} and {class}"
                                )));
                            }
                        } else {
                            pair_class = Some(class);
                        }
                        push_term(
                            &mut e4_pair,
                            &mut pair_lanes,
                            immediate_id(product.immediate)?,
                            &operands,
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
    let mut source_lanes = bf_lanes;
    for (base, lanes) in [
        (bf.len(), linear_lanes),
        (bf.len() + linear_e4.len(), single_lanes),
        (bf.len() + linear_e4.len() + e4_single.len(), pair_lanes),
    ] {
        let base = u32::try_from(base)
            .map_err(|_| WindowLoweringError::Encoding("window section base overflow".into()))?;
        source_lanes.extend(lanes.into_iter().map(|lane| WindowSourceLane {
            word: lane.word + base,
            source: lane.source,
        }));
    }
    let mut words = bf;
    words.extend(linear_e4);
    words.extend(e4_single);
    words.extend(e4_pair);
    let mut sections = [0u32; WINDOW_SECTION_WORDS];
    sections[0] = u32_section_end(bf_end, "dedicated BF section")?;
    sections[1] = u32_section_end(linear_end, "dedicated linear E4 section")?;
    sections[2] = u32_section_end(singleton_end, "dedicated singleton E4 section")?;
    sections[3] = u32_section_end(pair_end, "dedicated pair E4 section")?;
    let shape = WindowShape::from_bits(derive_window_shape(binding, program)?.bits())?;
    sections[4] = u32::from(shape.bits());
    let immediates: Vec<u32> = raw_immediates
        .iter()
        .map(|value| Bf::from_u32_unchecked(*value).as_u32_raw_repr_reduced())
        .collect();
    let lowered = WindowProgram {
        layer: inputs.layer,
        words,
        source_slots: program.source_slots.clone(),
        source_lanes,
        windows: binding.windows.clone(),
        immediates,
        sections,
        coefficient_plans: plans,
        shape,
    };
    validate_window_coefficient_ids(&lowered)?;
    validate_window_source_lanes(&lowered)?;
    Ok(lowered)
}

/// Every recorded lane word must hold the lane its named source lowered to, and
/// no other word may carry one. The second half is checked by
/// [`walk_window_source_lanes`], the wire's own decoder.
fn validate_window_source_lanes(program: &WindowProgram) -> Result<(), WindowLoweringError> {
    for lane in &program.source_lanes {
        let word = *program
            .words
            .get(lane.word as usize)
            .ok_or_else(|| WindowLoweringError::Encoding("lane word out of range".into()))?;
        let expected = *program
            .source_slots
            .get(usize::from(lane.source))
            .ok_or_else(|| WindowLoweringError::Encoding("lane source out of range".into()))?;
        if word != expected {
            return Err(WindowLoweringError::Encoding(format!(
                "lane word {} holds {word}, source {} lowered to {expected}",
                lane.word, lane.source
            )));
        }
    }
    let walked = walk_window_source_lanes(program)?;
    let recorded: Vec<u32> = program.source_lanes.iter().map(|lane| lane.word).collect();
    if walked != recorded {
        return Err(WindowLoweringError::Encoding(format!(
            "the wire carries {} lane words, the side table lists {}",
            walked.len(),
            recorded.len()
        )));
    }
    Ok(())
}

/// Walk the instruction stream and return every word position that carries an
/// addressing lane, ascending. Independent of the emission's bookkeeping: this
/// is the wire read the way the kernels read it (group headers reuse the operand
/// words for arity and product prefix, procedural operands carry a kind).
fn walk_window_source_lanes(program: &WindowProgram) -> Result<Vec<u32>, WindowLoweringError> {
    let malformed =
        || WindowLoweringError::Encoding("lane walk observed a malformed section".to_owned());
    let read = |record: usize| -> Result<[u16; 4], WindowLoweringError> {
        let base = record.checked_mul(4).ok_or_else(malformed)?;
        let words = program.words.get(base..base + 4).ok_or_else(malformed)?;
        Ok([words[0], words[1], words[2], words[3]])
    };
    let operand_words = |record: usize, a: bool, b: bool| {
        let base = record as u32 * 4;
        [(a, base + 2), (b, base + 3)]
            .into_iter()
            .filter_map(|(carries, word)| carries.then_some(word))
    };
    let term_lanes = |record: usize,
                      opcode: u16|
     -> Result<Box<dyn Iterator<Item = u32>>, WindowLoweringError> {
        let (a, b) = match opcode {
            0 => (true, false),
            2 | 3 | WINDOW_OPCODE_PRODUCT_E4_E4 => (true, true),
            WINDOW_OPCODE_LINEAR_BF_PROCEDURAL => (false, false),
            WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B => (true, false),
            WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB => (false, false),
            WINDOW_OPCODE_LINEAR_E4_WIDE => (true, false),
            _ => {
                return Err(WindowLoweringError::Encoding(format!(
                    "lane walk met unknown opcode {opcode}"
                )))
            }
        };
        Ok(Box::new(operand_words(record, a, b)))
    };
    let ends = program.sections.map(|end| end as usize);
    let mut lanes = Vec::new();
    let mut record = 0usize;
    // BF section: a lone term, or a group header naming `arity` members.
    while record < ends[0] {
        let instruction = read(record)?;
        if instruction[0] == WINDOW_OPCODE_GROUP_BF {
            let arity = usize::from(instruction[2]);
            record += 1;
            for _ in 0..arity {
                if record >= ends[0] {
                    return Err(malformed());
                }
                let member = read(record)?;
                lanes.extend(term_lanes(record, member[0])?);
                record += 1;
            }
        } else {
            lanes.extend(term_lanes(record, instruction[0])?);
            record += 1;
        }
    }
    // Wide linear-E4 and E4 singleton sections: one term per record.
    for end in [ends[1], ends[2]] {
        while record < end {
            let instruction = read(record)?;
            lanes.extend(term_lanes(record, instruction[0])?);
            record += 1;
        }
    }
    // E4 pair section: a header naming a shared core, then exactly two members.
    while record < ends[3] {
        let instruction = read(record)?;
        if instruction[0] != WINDOW_OPCODE_GROUP_E4 {
            return Err(malformed());
        }
        record += 1;
        for _ in 0..2 {
            if record >= ends[3] {
                return Err(malformed());
            }
            let member = read(record)?;
            lanes.extend(term_lanes(record, member[0])?);
            record += 1;
        }
    }
    lanes.sort_unstable();
    Ok(lanes)
}

fn validate_coefficient_span(
    encoded: u16,
    banked_count: usize,
    span: usize,
    resource: &'static str,
) -> Result<(), WindowLoweringError> {
    let id = usize::from(encoded & WINDOW_FLAG_HAS_PRODUCT.wrapping_sub(1));
    let bias = usize::from(WINDOW_COEFFICIENT_BANK_BIAS);
    if span == 1 && id < bias {
        return Ok(());
    }
    let first = id.checked_sub(bias).ok_or_else(|| {
        WindowLoweringError::Encoding(format!(
            "sectioned {resource} starts at reserved coefficient id {id}"
        ))
    })?;
    let end = first.checked_add(span).ok_or_else(|| {
        WindowLoweringError::Encoding(format!("sectioned {resource} coefficient span overflow"))
    })?;
    if end > banked_count {
        return Err(WindowLoweringError::Encoding(format!(
            "sectioned {resource} coefficient span [{first},{end}) exceeds banked count {banked_count}"
        )));
    }
    Ok(())
}

fn validate_window_coefficient_ids(program: &WindowProgram) -> Result<(), WindowLoweringError> {
    let banked_count = program.coefficient_plans.len();
    if banked_count > WINDOW_MAX_COEFFICIENT_PLANS {
        return Err(WindowLoweringError::Capacity {
            resource: "dedicated sectioned coefficient bank",
            required: banked_count,
            capacity: WINDOW_MAX_COEFFICIENT_PLANS,
        });
    }
    let ends = program.sections.map(|end| end as usize);
    if !ends[..4].windows(2).all(|pair| pair[0] <= pair[1])
        || ends[3].checked_mul(4) != Some(program.words.len())
    {
        return Err(WindowLoweringError::Encoding(
            "sectioned coefficient validation observed malformed endpoints".to_owned(),
        ));
    }

    let instruction = |pc: usize| -> Result<&[u16], WindowLoweringError> {
        program
            .words
            .get(4 * pc..4 * pc + 4)
            .ok_or_else(|| WindowLoweringError::Encoding("sectioned instruction absent".into()))
    };
    let mut pc = 0usize;
    while pc < ends[0] {
        let head = instruction(pc)?;
        validate_coefficient_span(head[1], banked_count, 1, "BF core")?;
        pc += 1;
        if head[0] == WINDOW_OPCODE_GROUP_BF {
            pc = pc.checked_add(usize::from(head[2])).ok_or_else(|| {
                WindowLoweringError::Encoding("sectioned BF group arity overflow".into())
            })?;
            if pc > ends[0] {
                return Err(WindowLoweringError::Encoding(
                    "sectioned BF group crosses its endpoint".into(),
                ));
            }
        }
    }
    while pc < ends[1] {
        let linear = instruction(pc)?;
        validate_coefficient_span(linear[1], banked_count, 4, "linear coefficient span")?;
        pc += 1;
    }
    while pc < ends[2] {
        let singleton = instruction(pc)?;
        validate_coefficient_span(singleton[1], banked_count, 1, "E4 singleton")?;
        pc += 1;
    }
    while pc < ends[3] {
        let head = instruction(pc)?;
        if head[0] != WINDOW_OPCODE_GROUP_E4 {
            return Err(WindowLoweringError::Encoding(
                "sectioned pair section contains a non-pair head".into(),
            ));
        }
        validate_coefficient_span(head[1], banked_count, 1, "E4 pair core")?;
        pc += 3;
        if pc > ends[3] {
            return Err(WindowLoweringError::Encoding(
                "sectioned E4 pair crosses its endpoint".into(),
            ));
        }
    }
    Ok(())
}
