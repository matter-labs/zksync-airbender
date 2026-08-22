use std::collections::{BTreeMap, BTreeSet};

use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::backward::{
    CoeffGroupingAnalysis, CoeffLayer, CoeffTerm, LeanSourceBinding, NormalizedCoefficientRecipe,
    Projection, ProjectionId, TermId,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AccumulatorSides {
    C0Only,
    C2Only,
    Dual,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AtomArity {
    Linear,
    Product,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OperandBacking {
    Bf,
    E4,
    BfBf,
    BfE4,
    E4E4,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ValueField {
    Bf,
    E4,
}

pub use gpu_gkr_compiler::backward::{SemanticSourceKey, SourceProjection};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundSourceUse {
    pub key: SemanticSourceKey,
    pub slot: u16,
    pub packed_window_column: u16,
    pub window: u8,
    pub relative_column: u16,
    pub procedural: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalizedAtom {
    pub terms: Vec<TermId>,
    pub sides: AccumulatorSides,
    pub linear_members: u32,
    pub product_members: u32,
    pub backing_counts: BTreeMap<OperandBacking, u32>,
    pub value_field: ValueField,
    pub coefficient_core: NormalizedCoefficientRecipe,
    pub source_uses: Vec<BoundSourceUse>,
    pub member_source_uses: Vec<Vec<BoundSourceUse>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduleViews {
    pub canonical_terms: Vec<NormalizedAtom>,
    pub production_atoms: Vec<NormalizedAtom>,
    pub analysis_atoms: Vec<NormalizedAtom>,
    pub canonical_split: SplitSchedule,
    pub analysis_split: SplitSchedule,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitSchedule {
    pub bf: Vec<NormalizedAtom>,
    pub e4: Vec<NormalizedAtom>,
    pub moved_records: u64,
    pub canonical_transitions: u64,
    pub split_transitions: u64,
    pub longest_canonical_bf_run: u64,
    pub longest_canonical_e4_run: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScheduleError {
    UnknownSource { term: TermId, source: u32 },
    UnknownWindow { source: u32, window: u8 },
    InvalidRelativeColumn { source: u32, column: u16 },
    MissingSourceField { source: u32 },
    IncompleteTermPartition { expected: usize, observed: usize },
}

fn recipe_for_id(
    layer: &CoeffLayer,
    id: gpu_gkr_compiler::backward::CoefficientRecipeId,
) -> Option<NormalizedCoefficientRecipe> {
    if id == gpu_gkr_compiler::backward::CoefficientRecipeId::ONE {
        return Some(NormalizedCoefficientRecipe::one());
    }
    if id == gpu_gkr_compiler::backward::CoefficientRecipeId::NEG_ONE {
        return Some(NormalizedCoefficientRecipe::neg_one());
    }
    layer.banked_recipe(id).cloned()
}

fn bound_source_use(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    term: TermId,
    projection: ProjectionId,
) -> Result<BoundSourceUse, ScheduleError> {
    let source = projection.source.0;
    layer
        .source(projection.source)
        .ok_or(ScheduleError::UnknownSource { term, source })?;
    let slot = binding
        .source_slots
        .get(source as usize)
        .ok_or(ScheduleError::UnknownSource { term, source })?;
    if slot.column >= 128 {
        return Err(ScheduleError::InvalidRelativeColumn {
            source,
            column: slot.column,
        });
    }
    let window = binding
        .windows
        .get(slot.window as usize)
        .ok_or(ScheduleError::UnknownWindow {
            source,
            window: slot.window,
        })?;
    let slot_id =
        u16::try_from(source).map_err(|_| ScheduleError::UnknownSource { term, source })?;
    Ok(BoundSourceUse {
        key: SemanticSourceKey {
            source,
            projection: match projection.projection {
                Projection::Endpoint0 => SourceProjection::Endpoint0,
                Projection::Delta => SourceProjection::Delta,
            },
        },
        slot: slot_id,
        packed_window_column: (u16::from(slot.window) << 7) | slot.column,
        window: slot.window,
        relative_column: slot.column,
        procedural: window.is_procedural(),
    })
}

fn source_backing_field(
    binding: &LeanSourceBinding,
    term: TermId,
    source: u32,
) -> Result<FieldKind, ScheduleError> {
    let slot = binding
        .source_slots
        .get(source as usize)
        .ok_or(ScheduleError::UnknownSource { term, source })?;
    binding
        .windows
        .get(slot.window as usize)
        .map(|window| window.backing_field())
        .ok_or(ScheduleError::UnknownWindow {
            source,
            window: slot.window,
        })
}

fn term_shape(
    binding: &LeanSourceBinding,
    term: &CoeffTerm,
) -> Result<(AccumulatorSides, AtomArity, OperandBacking, ValueField), ScheduleError> {
    let shape = match term {
        CoeffTerm::C0Linear { value, .. } => {
            let field = source_backing_field(binding, term.id(), value.source.0)?;
            (
                AccumulatorSides::C0Only,
                AtomArity::Linear,
                match field {
                    FieldKind::Base => OperandBacking::Bf,
                    FieldKind::Ext => OperandBacking::E4,
                },
                match field {
                    FieldKind::Base => ValueField::Bf,
                    FieldKind::Ext => ValueField::E4,
                },
            )
        }
        CoeffTerm::C2Product { lhs, rhs, .. } => {
            let lhs_field = source_backing_field(binding, term.id(), lhs.source.0)?;
            let rhs_field = source_backing_field(binding, term.id(), rhs.source.0)?;
            let backing = match (lhs_field, rhs_field) {
                (FieldKind::Base, FieldKind::Base) => OperandBacking::BfBf,
                (FieldKind::Ext, FieldKind::Ext) => OperandBacking::E4E4,
                _ => OperandBacking::BfE4,
            };
            (
                AccumulatorSides::C2Only,
                AtomArity::Product,
                backing,
                if backing == OperandBacking::BfBf {
                    ValueField::Bf
                } else {
                    ValueField::E4
                },
            )
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => {
            let lhs_field = source_backing_field(binding, term.id(), lhs.0)?;
            let rhs_field = source_backing_field(binding, term.id(), rhs.0)?;
            let backing = match (lhs_field, rhs_field) {
                (FieldKind::Base, FieldKind::Base) => OperandBacking::BfBf,
                (FieldKind::Ext, FieldKind::Ext) => OperandBacking::E4E4,
                _ => OperandBacking::BfE4,
            };
            (
                AccumulatorSides::Dual,
                AtomArity::Product,
                backing,
                if backing == OperandBacking::BfBf {
                    ValueField::Bf
                } else {
                    ValueField::E4
                },
            )
        }
    };
    Ok(shape)
}

fn combine_sides(current: Option<AccumulatorSides>, next: AccumulatorSides) -> AccumulatorSides {
    match (current, next) {
        (None, next) => next,
        (Some(AccumulatorSides::C0Only), AccumulatorSides::C0Only) => AccumulatorSides::C0Only,
        (Some(AccumulatorSides::C2Only), AccumulatorSides::C2Only) => AccumulatorSides::C2Only,
        _ => AccumulatorSides::Dual,
    }
}

fn atom_from_terms(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    terms_by_id: &BTreeMap<TermId, &CoeffTerm>,
    term_ids: Vec<TermId>,
    coefficient_core: NormalizedCoefficientRecipe,
) -> Result<NormalizedAtom, ScheduleError> {
    let mut sides = None;
    let mut linear_members = 0u32;
    let mut product_members = 0u32;
    let mut backing_counts = BTreeMap::new();
    let mut value_field = ValueField::Bf;
    let mut source_uses = Vec::new();
    let mut member_source_uses = Vec::new();
    for term_id in &term_ids {
        let term =
            terms_by_id
                .get(term_id)
                .copied()
                .ok_or(ScheduleError::IncompleteTermPartition {
                    expected: layer.terms.len(),
                    observed: term_ids.len(),
                })?;
        let (term_sides, arity, backing, field) = term_shape(binding, term)?;
        sides = Some(combine_sides(sides, term_sides));
        match arity {
            AtomArity::Linear => linear_members += 1,
            AtomArity::Product => product_members += 1,
        }
        *backing_counts.entry(backing).or_insert(0) += 1;
        if field == ValueField::E4 {
            value_field = ValueField::E4;
        }
        let mut projections = Vec::new();
        term.for_each_projection_use(|projection| projections.push(projection));
        let mut member_uses = Vec::with_capacity(projections.len());
        for projection in projections {
            let source = bound_source_use(layer, binding, *term_id, projection)?;
            source_uses.push(source.clone());
            member_uses.push(source);
        }
        member_source_uses.push(member_uses);
    }
    Ok(NormalizedAtom {
        terms: term_ids,
        sides: sides.unwrap_or(AccumulatorSides::C0Only),
        linear_members,
        product_members,
        backing_counts,
        value_field,
        coefficient_core,
        source_uses,
        member_source_uses,
    })
}

fn atoms_from_groups(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    groups: impl IntoIterator<Item = (NormalizedCoefficientRecipe, Vec<TermId>)>,
    original_recipes: &BTreeMap<TermId, NormalizedCoefficientRecipe>,
) -> Result<Vec<NormalizedAtom>, ScheduleError> {
    let terms_by_id: BTreeMap<_, _> = layer.terms.iter().map(|term| (term.id(), term)).collect();
    let mut grouped_terms = BTreeSet::new();
    let mut atom_specs = Vec::new();
    for (core, mut members) in groups {
        members.sort();
        grouped_terms.extend(members.iter().copied());
        atom_specs.push((members, core));
    }
    for term in &layer.terms {
        if !grouped_terms.contains(&term.id()) {
            let recipe = original_recipes.get(&term.id()).cloned().ok_or(
                ScheduleError::IncompleteTermPartition {
                    expected: layer.terms.len(),
                    observed: original_recipes.len(),
                },
            )?;
            atom_specs.push((vec![term.id()], recipe));
        }
    }
    atom_specs.sort_by_key(|(terms, _)| terms[0]);
    atom_specs
        .into_iter()
        .map(|(terms, core)| atom_from_terms(layer, binding, &terms_by_id, terms, core))
        .collect()
}

fn transition_count(atoms: &[NormalizedAtom]) -> u64 {
    atoms
        .windows(2)
        .filter(|pair| pair[0].value_field != pair[1].value_field)
        .count() as u64
}

fn longest_run(atoms: &[NormalizedAtom], field: ValueField) -> u64 {
    let mut longest = 0u64;
    let mut current = 0u64;
    for atom in atoms {
        if atom.value_field == field {
            current += 1;
            longest = longest.max(current);
        } else {
            current = 0;
        }
    }
    longest
}

fn build_split_schedule(atoms: &[NormalizedAtom]) -> SplitSchedule {
    let bf: Vec<_> = atoms
        .iter()
        .filter(|atom| atom.value_field == ValueField::Bf)
        .cloned()
        .collect();
    let e4: Vec<_> = atoms
        .iter()
        .filter(|atom| atom.value_field == ValueField::E4)
        .cloned()
        .collect();
    let split: Vec<_> = bf.iter().chain(&e4).collect();
    let moved_records = atoms
        .iter()
        .enumerate()
        .filter(|(position, atom)| split[*position].terms != atom.terms)
        .count() as u64;
    let split_transitions = u64::from(
        split
            .windows(2)
            .any(|pair| pair[0].value_field != pair[1].value_field),
    );
    SplitSchedule {
        bf,
        e4,
        moved_records,
        canonical_transitions: transition_count(atoms),
        split_transitions,
        longest_canonical_bf_run: longest_run(atoms, ValueField::Bf),
        longest_canonical_e4_run: longest_run(atoms, ValueField::E4),
    }
}

fn assert_exact_term_partition(
    atoms: &[NormalizedAtom],
    split: &SplitSchedule,
) -> Result<(), ScheduleError> {
    let expected: Vec<_> = atoms
        .iter()
        .flat_map(|atom| atom.terms.iter().copied())
        .collect();
    let observed: Vec<_> = split
        .bf
        .iter()
        .chain(&split.e4)
        .flat_map(|atom| atom.terms.iter().copied())
        .collect();
    let expected_set: BTreeSet<_> = expected.iter().copied().collect();
    let observed_set: BTreeSet<_> = observed.iter().copied().collect();
    if expected.len() != observed.len()
        || expected_set.len() != expected.len()
        || observed_set != expected_set
    {
        return Err(ScheduleError::IncompleteTermPartition {
            expected: expected.len(),
            observed: observed.len(),
        });
    }
    Ok(())
}

pub fn build_schedule_views(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    analysis: &CoeffGroupingAnalysis,
) -> Result<ScheduleViews, ScheduleError> {
    let original_recipes: BTreeMap<_, _> = analysis.term_recipes.iter().cloned().collect();
    if original_recipes.len() != layer.terms.len() {
        return Err(ScheduleError::IncompleteTermPartition {
            expected: layer.terms.len(),
            observed: original_recipes.len(),
        });
    }
    let canonical_terms = atoms_from_groups(layer, binding, std::iter::empty(), &original_recipes)?;
    let production_groups = layer.groups.iter().map(|group| {
        let core = recipe_for_id(layer, group.core)
            .expect("validated compiler groups reference an existing coefficient");
        let members = group.members.iter().map(|member| member.term).collect();
        (core, members)
    });
    let production_atoms = atoms_from_groups(layer, binding, production_groups, &original_recipes)?;
    let analysis_groups = analysis.groups.iter().map(|group| {
        (
            group.core.clone(),
            group.members.iter().map(|member| member.term).collect(),
        )
    });
    let analysis_atoms = atoms_from_groups(layer, binding, analysis_groups, &original_recipes)?;
    let canonical_split = build_split_schedule(&canonical_terms);
    let analysis_split = build_split_schedule(&analysis_atoms);
    assert_exact_term_partition(&canonical_terms, &canonical_split)?;
    assert_exact_term_partition(&analysis_atoms, &analysis_split)?;
    Ok(ScheduleViews {
        canonical_terms,
        production_atoms,
        analysis_atoms,
        canonical_split,
        analysis_split,
    })
}

pub fn materialize_term_order(
    layer: &CoeffLayer,
    atoms: &[NormalizedAtom],
) -> Result<CoeffLayer, ScheduleError> {
    let observed: Vec<_> = atoms
        .iter()
        .flat_map(|atom| atom.terms.iter().copied())
        .collect();
    let observed_set: BTreeSet<_> = observed.iter().copied().collect();
    if observed.len() != layer.terms.len() || observed_set.len() != layer.terms.len() {
        return Err(ScheduleError::IncompleteTermPartition {
            expected: layer.terms.len(),
            observed: observed.len(),
        });
    }
    let by_id: BTreeMap<_, _> = layer.terms.iter().map(|term| (term.id(), *term)).collect();
    let new_ids = observed
        .iter()
        .enumerate()
        .map(|(index, old)| (*old, TermId(index as u32)))
        .collect::<BTreeMap<_, _>>();
    let mut reordered = layer.clone();
    reordered.terms = observed
        .iter()
        .map(|term| {
            let mut term =
                by_id
                    .get(term)
                    .copied()
                    .ok_or(ScheduleError::IncompleteTermPartition {
                        expected: layer.terms.len(),
                        observed: observed.len(),
                    })?;
            let id = new_ids[&term.id()];
            match &mut term {
                CoeffTerm::C0Linear { id: term_id, .. }
                | CoeffTerm::C2Product { id: term_id, .. }
                | CoeffTerm::DualProduct { id: term_id, .. } => *term_id = id,
            }
            Ok(term)
        })
        .collect::<Result<_, _>>()?;
    for group in &mut reordered.groups {
        for member in &mut group.members {
            member.term = new_ids[&member.term];
        }
        group.members.sort_unstable_by_key(|member| member.term);
    }
    Ok(reordered)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpecializationMetrics {
    pub literal_one_cores: u64,
    pub literal_neg_one_cores: u64,
    pub one_nonzero_limb_cores: u64,
    pub group_immediate_one: u64,
    pub group_immediate_neg_one: u64,
    pub group_immediate_banked: u64,
    pub self_products: u64,
    pub same_window_products: u64,
    pub linear_members: u64,
    pub product_members: u64,
    pub procedural_operand_uses: u64,
    pub stored_operand_uses: u64,
}

pub fn specialization_metrics(
    layer: &CoeffLayer,
    binding: &LeanSourceBinding,
    analysis: &CoeffGroupingAnalysis,
    atoms: &[NormalizedAtom],
) -> Result<SpecializationMetrics, ScheduleError> {
    let literal_one_cores = atoms
        .iter()
        .filter(|atom| atom.coefficient_core.is_one())
        .count() as u64;
    let literal_neg_one_cores = atoms
        .iter()
        .filter(|atom| atom.coefficient_core.is_neg_one())
        .count() as u64;
    let one_nonzero_limb_cores = atoms
        .iter()
        .filter(|atom| {
            atom.coefficient_core
                .terms
                .iter()
                .all(|product| product.challenges.is_empty())
        })
        .count() as u64;
    let mut group_immediate_one = 0u64;
    let mut group_immediate_neg_one = 0u64;
    let mut group_immediate_banked = 0u64;
    for member in analysis.groups.iter().flat_map(|group| &group.members) {
        match member.immediate {
            1 => group_immediate_one += 1,
            0x7800_0000 => group_immediate_neg_one += 1,
            _ => group_immediate_banked += 1,
        }
    }

    let mut self_products = 0u64;
    let mut same_window_products = 0u64;
    for term in &layer.terms {
        let sources = match term {
            CoeffTerm::C0Linear { .. } => None,
            CoeffTerm::C2Product { lhs, rhs, .. } => Some((lhs.source, rhs.source)),
            CoeffTerm::DualProduct { lhs, rhs, .. } => Some((*lhs, *rhs)),
        };
        let Some((lhs, rhs)) = sources else {
            continue;
        };
        if lhs == rhs {
            self_products += 1;
        }
        let lhs_slot =
            binding
                .source_slots
                .get(lhs.0 as usize)
                .ok_or(ScheduleError::UnknownSource {
                    term: term.id(),
                    source: lhs.0,
                })?;
        let rhs_slot =
            binding
                .source_slots
                .get(rhs.0 as usize)
                .ok_or(ScheduleError::UnknownSource {
                    term: term.id(),
                    source: rhs.0,
                })?;
        if lhs_slot.window == rhs_slot.window {
            same_window_products += 1;
        }
    }
    let linear_members = atoms
        .iter()
        .map(|atom| u64::from(atom.linear_members))
        .sum();
    let product_members = atoms
        .iter()
        .map(|atom| u64::from(atom.product_members))
        .sum();
    let procedural_operand_uses = atoms
        .iter()
        .flat_map(|atom| &atom.source_uses)
        .filter(|source| source.procedural)
        .count() as u64;
    let stored_operand_uses = atoms
        .iter()
        .flat_map(|atom| &atom.source_uses)
        .filter(|source| !source.procedural)
        .count() as u64;
    Ok(SpecializationMetrics {
        literal_one_cores,
        literal_neg_one_cores,
        one_nonzero_limb_cores,
        group_immediate_one,
        group_immediate_neg_one,
        group_immediate_banked,
        self_products,
        same_window_products,
        linear_members,
        product_members,
        procedural_operand_uses,
        stored_operand_uses,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use gkr_eval_ir::{ChallengeKey, ChallengePower, ChallengeRef};
    use gpu_gkr_compiler::backward::{
        analyze_coeff_grouping, CoeffTerm, CoefficientRecipeId, NormalizedCoefficientRecipe,
        ProjectionId, SourceId, WindowFamily,
    };

    use super::*;
    use crate::census::compile_corpus;

    fn synthetic_atom(terms: &[u32], field: ValueField) -> NormalizedAtom {
        NormalizedAtom {
            terms: terms.iter().copied().map(TermId).collect(),
            sides: AccumulatorSides::C0Only,
            linear_members: terms.len() as u32,
            product_members: 0,
            backing_counts: BTreeMap::from([(
                match field {
                    ValueField::Bf => OperandBacking::Bf,
                    ValueField::E4 => OperandBacking::E4,
                },
                terms.len() as u32,
            )]),
            value_field: field,
            coefficient_core: NormalizedCoefficientRecipe::one(),
            source_uses: Vec::new(),
            member_source_uses: vec![Vec::new(); terms.len()],
        }
    }

    #[test]
    fn r0_five_classes_form_a_total_taxonomy() {
        let corpus = compile_corpus().unwrap();
        let mut observed = BTreeSet::new();
        for layer in corpus.layers {
            let analysis = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let views =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &analysis).unwrap();
            assert_eq!(
                views.canonical_terms.len(),
                layer.r0.coefficients.terms.len()
            );
            for atom in views.canonical_terms {
                assert_eq!(atom.terms.len(), 1);
                let arity = if atom.product_members == 0 {
                    AtomArity::Linear
                } else {
                    AtomArity::Product
                };
                assert_eq!(atom.backing_counts.len(), 1);
                observed.insert((
                    atom.sides,
                    arity,
                    *atom.backing_counts.keys().next().unwrap(),
                    atom.value_field,
                ));
            }
        }
        assert_eq!(
            observed,
            BTreeSet::from([
                (
                    AccumulatorSides::C0Only,
                    AtomArity::Linear,
                    OperandBacking::Bf,
                    ValueField::Bf,
                ),
                (
                    AccumulatorSides::C0Only,
                    AtomArity::Linear,
                    OperandBacking::E4,
                    ValueField::E4,
                ),
                (
                    AccumulatorSides::C2Only,
                    AtomArity::Product,
                    OperandBacking::BfBf,
                    ValueField::Bf,
                ),
                (
                    AccumulatorSides::C2Only,
                    AtomArity::Product,
                    OperandBacking::BfE4,
                    ValueField::E4,
                ),
                (
                    AccumulatorSides::C2Only,
                    AtomArity::Product,
                    OperandBacking::E4E4,
                    ValueField::E4,
                ),
            ])
        );
    }

    #[test]
    fn stable_split_preserves_terms_and_keeps_mixed_groups_in_e4() {
        let atoms = vec![
            synthetic_atom(&[0], ValueField::Bf),
            synthetic_atom(&[1, 2], ValueField::E4),
        ];
        let split = build_split_schedule(&atoms);
        assert_eq!(
            split
                .bf
                .iter()
                .flat_map(|atom| atom.terms.iter().copied())
                .collect::<Vec<_>>(),
            vec![TermId(0)]
        );
        assert_eq!(
            split
                .e4
                .iter()
                .flat_map(|atom| atom.terms.iter().copied())
                .collect::<Vec<_>>(),
            vec![TermId(1), TermId(2)]
        );
        assert_exact_term_partition(&atoms, &split).unwrap();
    }

    #[test]
    fn bound_source_identity_includes_projection_role() {
        let corpus = compile_corpus().unwrap();
        let mut found_pair = false;
        for layer in corpus.layers {
            let analysis = analyze_coeff_grouping(&layer.ext.coefficients).unwrap();
            let views =
                build_schedule_views(&layer.ext.coefficients, &layer.ext.binding, &analysis)
                    .unwrap();
            for atom in views.canonical_terms {
                for endpoint in &atom.source_uses {
                    found_pair |= atom.source_uses.iter().any(|delta| {
                        endpoint.key.source == delta.key.source
                            && endpoint.key.projection == SourceProjection::Endpoint0
                            && delta.key.projection == SourceProjection::Delta
                    });
                }
            }
        }
        assert!(
            found_pair,
            "continuation dual products must expose both roles"
        );
    }

    #[test]
    fn specialization_metrics_count_each_structural_opportunity_once() {
        let mut compiled = compile_corpus().unwrap().layers.remove(0).r0;
        assert!(compiled.coefficients.sources.len() >= 2);
        assert!(compiled.binding.windows.len() >= 2);
        let source0 = SourceId(0);
        let source1 = SourceId(1);
        let field0 = compiled.coefficients.sources[0].field;
        let field1 = compiled.coefficients.sources[1].field;
        compiled.binding.source_slots[0].window = 0;
        compiled.binding.source_slots[0].column = 0;
        compiled.binding.source_slots[1].window = 1;
        compiled.binding.source_slots[1].column = 0;
        compiled.binding.windows[0].family = WindowFamily::VirtualSetup { kind: 0 };
        compiled.binding.windows[1].family = WindowFamily::BaseLayerMemory;

        let core = NormalizedCoefficientRecipe::challenge(ChallengeRef {
            key: ChallengeKey::ClaimBatching,
            power: ChallengePower::One,
        });
        let scaled = |scale: u32| {
            let mut products = core.terms.clone();
            products[0].scalar = scale;
            NormalizedCoefficientRecipe::from_terms(products)
        };
        compiled.coefficients.coefficients = vec![scaled(1), scaled(5), scaled(0x7800_0000)];
        compiled.coefficients.coefficients.sort();
        let coefficient = |scale| {
            CoefficientRecipeId::from_bank_index(
                compiled
                    .coefficients
                    .coefficients
                    .binary_search(&scaled(scale))
                    .unwrap(),
            )
        };
        compiled.coefficients.terms = vec![
            CoeffTerm::C0Linear {
                id: TermId(0),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(source0),
                field: field0,
            },
            CoeffTerm::C0Linear {
                id: TermId(1),
                coefficient: CoefficientRecipeId::NEG_ONE,
                value: ProjectionId::endpoint0(source1),
                field: field1,
            },
            CoeffTerm::C2Product {
                id: TermId(2),
                coefficient: coefficient(1),
                lhs: ProjectionId::delta(source0),
                rhs: ProjectionId::delta(source0),
                lhs_field: field0,
                rhs_field: field0,
            },
            CoeffTerm::C2Product {
                id: TermId(3),
                coefficient: coefficient(0x7800_0000),
                lhs: ProjectionId::delta(source0),
                rhs: ProjectionId::delta(source1),
                lhs_field: field0,
                rhs_field: field1,
            },
            CoeffTerm::C2Product {
                id: TermId(4),
                coefficient: coefficient(5),
                lhs: ProjectionId::delta(source1),
                rhs: ProjectionId::delta(source0),
                lhs_field: field1,
                rhs_field: field0,
            },
        ];
        compiled.coefficients.c_init = None;
        compiled.coefficients.groups.clear();
        compiled.coefficients.immediates.clear();

        let analysis = analyze_coeff_grouping(&compiled.coefficients).unwrap();
        let views =
            build_schedule_views(&compiled.coefficients, &compiled.binding, &analysis).unwrap();
        let metrics = specialization_metrics(
            &compiled.coefficients,
            &compiled.binding,
            &analysis,
            &views.analysis_atoms,
        )
        .unwrap();
        assert_eq!(metrics.literal_one_cores, 1);
        assert_eq!(metrics.literal_neg_one_cores, 1);
        assert_eq!(metrics.one_nonzero_limb_cores, 2);
        assert_eq!(metrics.group_immediate_one, 1);
        assert_eq!(metrics.group_immediate_neg_one, 1);
        assert_eq!(metrics.group_immediate_banked, 1);
        assert_eq!(metrics.self_products, 1);
        assert_eq!(metrics.same_window_products, 1);
        assert_eq!(metrics.linear_members, 2);
        assert_eq!(metrics.product_members, 3);
        assert_eq!(metrics.procedural_operand_uses, 5);
        assert_eq!(metrics.stored_operand_uses, 3);
    }

    #[test]
    fn continuation_group_value_field_follows_physical_backing() {
        let corpus = compile_corpus().unwrap();
        let mut bf_groups = 0;
        let mut e4_groups = 0;
        let mut mixed_groups = 0;
        let mut e4_all_size_two = true;
        for layer in corpus.layers {
            let analysis = analyze_coeff_grouping(&layer.ext.coefficients).unwrap();
            let views =
                build_schedule_views(&layer.ext.coefficients, &layer.ext.binding, &analysis)
                    .unwrap();
            let fields = views
                .canonical_terms
                .iter()
                .flat_map(|atom| atom.terms.iter().map(move |term| (*term, atom.value_field)))
                .collect::<BTreeMap<_, _>>();
            for group in analysis.groups {
                let group_fields = group
                    .members
                    .iter()
                    .map(|member| fields[&member.term])
                    .collect::<BTreeSet<_>>();
                if group_fields == BTreeSet::from([ValueField::Bf]) {
                    bf_groups += 1;
                } else if group_fields == BTreeSet::from([ValueField::E4]) {
                    e4_groups += 1;
                    e4_all_size_two &= group.members.len() == 2;
                } else {
                    mixed_groups += 1;
                }
            }
        }
        assert_eq!((bf_groups, e4_groups, mixed_groups), (1_005, 483, 0));
        assert!(e4_all_size_two);
    }
}
