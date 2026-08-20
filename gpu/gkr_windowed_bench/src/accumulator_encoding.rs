use std::collections::{BTreeMap, BTreeSet};

use gpu_gkr_compiler::backward::{
    CoeffGroupingAnalysis, LeanSourceBinding, NormalizedCoefficientRecipe, TermId,
};
use gpu_gkr_compiler::GpuResourceProfile;
use serde::{Deserialize, Serialize};

use crate::accumulator_bounds::BABY_BEAR_ORDER;
use crate::accumulator_schedule::{NormalizedAtom, ScheduleViews, ValueField};
use crate::census::BackwardRegime;
use crate::r0_abi::{
    CUDA_CONSTANT_MEMORY_CEILING_BYTES, KERNEL_ARGUMENT_CEILING_BYTES, R0_COEFFICIENT_CAPACITY,
    R0_CONSTANT_FOOTPRINT_BYTES, R0_EQ_HIGH_ELEMENTS, R0_HISTORICAL_COEFFICIENT_ELEMENTS,
    R0_HISTORICAL_EQ_HIGH_ELEMENTS, R0_PROGRAM_WORDS, R0_SOURCE_SLOTS,
};

const WINDOW_DESCRIPTOR_BYTES: u64 = 1_024;
const POINTER_SCALAR_EQUALITY_BYTES: u64 = 52;
const FIXED_DESCRIPTOR_BYTES: u64 = WINDOW_DESCRIPTOR_BYTES + POINTER_SCALAR_EQUALITY_BYTES;
const DESCRIPTOR_ALIGNMENT_BYTES: u64 = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SourceMode {
    SlotIndex,
    DirectWindowColumn,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AnalyticalLayout {
    CurrentFixed,
    SplitFixed,
    HomogeneousStreams,
    GroupedStreams,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CapacityNamespace {
    CudaKernelArgument,
    ModuleConstant,
    WireU16,
    R0Production,
    ContinuationProduction,
    R0ReferenceAbi,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapacityFact {
    pub namespace: CapacityNamespace,
    pub kind: String,
    pub required: u64,
    pub maximum: u64,
    pub fits: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EncodingBudget {
    pub layout: AnalyticalLayout,
    pub source_mode: SourceMode,
    pub fixed_descriptor_bytes: u64,
    pub metadata_words: u64,
    pub program_words: u64,
    pub immediate_bytes: u64,
    pub source_binding_bytes: u64,
    pub alignment_padding_bytes: u64,
    pub by_value_bytes: u64,
    pub module_constant_bytes: u64,
    pub device_allocation_bytes: u64,
    pub capacity_facts: Vec<CapacityFact>,
}

impl EncodingBudget {
    pub fn module_constant_breakdown(&self) -> (u64, u64, u64) {
        let coefficient_bank = (R0_COEFFICIENT_CAPACITY * 16) as u64;
        let equality = (R0_EQ_HIGH_ELEMENTS * 16) as u64;
        let historical =
            ((R0_HISTORICAL_COEFFICIENT_ELEMENTS + R0_HISTORICAL_EQ_HIGH_ELEMENTS) * 16) as u64;
        (coefficient_bank, equality, historical)
    }
}

pub struct EncodingInput<'a> {
    pub regime: BackwardRegime,
    pub schedules: &'a ScheduleViews,
    pub binding: &'a LeanSourceBinding,
    pub grouping: &'a CoeffGroupingAnalysis,
    pub banked_coefficient_count: usize,
    pub immediate_count: usize,
    pub device_allocation_bytes: u64,
}

fn fact(
    namespace: CapacityNamespace,
    kind: impl Into<String>,
    required: u64,
    maximum: u64,
) -> CapacityFact {
    CapacityFact {
        namespace,
        kind: kind.into(),
        required,
        maximum,
        fits: required <= maximum,
    }
}

fn production_namespace(regime: BackwardRegime) -> CapacityNamespace {
    match regime {
        BackwardRegime::R0 => CapacityNamespace::R0Production,
        BackwardRegime::Ext => CapacityNamespace::ContinuationProduction,
    }
}

fn is_reserved_literal(recipe: &NormalizedCoefficientRecipe) -> bool {
    *recipe == NormalizedCoefficientRecipe::one()
        || *recipe == NormalizedCoefficientRecipe::neg_one()
}

pub fn complete_grouped_bank_population(grouping: &CoeffGroupingAnalysis) -> u64 {
    let recipes = grouping
        .term_recipes
        .iter()
        .cloned()
        .collect::<BTreeMap<TermId, NormalizedCoefficientRecipe>>();
    let mut bank = BTreeSet::new();
    for group in &grouping.groups {
        if !is_reserved_literal(&group.core) {
            bank.insert(group.core.clone());
        }
    }
    for term in &grouping.ungrouped_terms {
        if let Some(recipe) = recipes.get(term) {
            if !is_reserved_literal(recipe) {
                bank.insert(recipe.clone());
            }
        }
    }
    if let Some(recipe) = &grouping.c_init_recipe {
        if !is_reserved_literal(recipe) {
            bank.insert(recipe.clone());
        }
    }
    bank.len() as u64
}

fn grouped_immediates(grouping: &CoeffGroupingAnalysis) -> BTreeSet<u32> {
    grouping
        .groups
        .iter()
        .flat_map(|group| group.members.iter().map(|member| member.immediate))
        .filter(|immediate| *immediate != 1 && u128::from(*immediate) != BABY_BEAR_ORDER - 1)
        .collect()
}

fn compact_record_words(atoms: &[NormalizedAtom]) -> u64 {
    atoms
        .iter()
        .map(|atom| if atom.product_members == 0 { 2 } else { 3 })
        .sum()
}

fn grouped_record_words(input: &EncodingInput<'_>) -> u64 {
    let arity = input
        .schedules
        .canonical_terms
        .iter()
        .flat_map(|atom| {
            atom.terms
                .iter()
                .map(move |term| (*term, atom.product_members > 0))
        })
        .collect::<BTreeMap<_, _>>();
    let singleton_words = input
        .schedules
        .analysis_atoms
        .iter()
        .filter(|atom| atom.terms.len() == 1)
        .map(|atom| if atom.product_members == 0 { 2 } else { 3 })
        .sum::<u64>();
    let group_header_words = input.grouping.groups.len() as u64 * 4;
    let member_words = input
        .grouping
        .groups
        .iter()
        .flat_map(|group| &group.members)
        .map(|member| {
            if arity.get(&member.term).copied().unwrap_or(false) {
                4
            } else {
                3
            }
        })
        .sum::<u64>();
    singleton_words + group_header_words + member_words
}

fn u16_section_facts(
    metadata_words: u64,
    program_words: u64,
    immediate_words: u64,
) -> Vec<CapacityFact> {
    let sections = [
        ("metadata", 0, metadata_words),
        ("program", metadata_words, program_words),
        (
            "immediates",
            metadata_words + program_words,
            immediate_words,
        ),
    ];
    sections
        .into_iter()
        .flat_map(|(name, offset, count)| {
            [
                fact(
                    CapacityNamespace::WireU16,
                    format!("{name}_offset_words"),
                    offset,
                    u16::MAX as u64,
                ),
                fact(
                    CapacityNamespace::WireU16,
                    format!("{name}_count_words"),
                    count,
                    u16::MAX as u64,
                ),
            ]
        })
        .collect()
}

fn build_budget(
    input: &EncodingInput<'_>,
    layout: AnalyticalLayout,
    source_mode: SourceMode,
    metadata_words: u64,
    program_words: u64,
    immediate_bytes: u64,
    record_count: u64,
) -> EncodingBudget {
    let source_binding_bytes = match (layout, source_mode) {
        (AnalyticalLayout::CurrentFixed | AnalyticalLayout::SplitFixed, SourceMode::SlotIndex) => {
            (R0_SOURCE_SLOTS * 2) as u64
        }
        (_, SourceMode::SlotIndex) => input.binding.source_slots.len() as u64 * 2,
        (_, SourceMode::DirectWindowColumn) => 0,
    };
    let unaligned = FIXED_DESCRIPTOR_BYTES
        + 2 * metadata_words
        + 2 * program_words
        + immediate_bytes
        + source_binding_bytes;
    let alignment_padding_bytes = (DESCRIPTOR_ALIGNMENT_BYTES
        - unaligned % DESCRIPTOR_ALIGNMENT_BYTES)
        % DESCRIPTOR_ALIGNMENT_BYTES;
    let by_value_bytes = unaligned + alignment_padding_bytes;
    let immediate_words = immediate_bytes / 2;
    let encoded_program_words = metadata_words + program_words + immediate_words;

    let profile = GpuResourceProfile::production();
    let (
        namespace,
        max_program_words,
        max_records,
        max_immediates,
        max_coefficients,
        max_sources,
        max_projections,
        max_windows,
        max_columns,
    ) = match input.regime {
        BackwardRegime::R0 => (
            CapacityNamespace::R0Production,
            profile.r0.max_program_words as u64,
            profile.r0.max_records as u64,
            profile.r0.max_immediates as u64,
            profile.r0.max_coefficient_recipes as u64,
            profile.r0.max_sources as u64,
            profile.r0.max_projections as u64,
            profile.r0.max_source_windows as u64,
            (profile.r0.source_window_columns - 1) as u64,
        ),
        BackwardRegime::Ext => (
            CapacityNamespace::ContinuationProduction,
            profile.continuations.max_program_words as u64,
            profile.continuations.max_records as u64,
            profile.continuations.max_immediates as u64,
            profile.continuations.max_coefficient_recipes as u64,
            profile.continuations.max_sources as u64,
            profile.continuations.max_projections as u64,
            profile.continuations.max_source_windows as u64,
            (profile.continuations.source_window_columns - 1) as u64,
        ),
    };
    let (
        actual_namespace,
        max_program_words,
        max_records,
        max_immediates,
        max_coefficients,
        max_sources,
        max_projections,
        max_windows,
        max_columns,
    ) = if layout == AnalyticalLayout::CurrentFixed {
        (
            CapacityNamespace::R0ReferenceAbi,
            profile.r0.max_program_words as u64,
            profile.r0.max_records as u64,
            profile.r0.max_immediates as u64,
            profile.r0.max_coefficient_recipes as u64,
            profile.r0.max_sources as u64,
            profile.r0.max_projections as u64,
            profile.r0.max_source_windows as u64,
            (profile.r0.source_window_columns - 1) as u64,
        )
    } else {
        (
            namespace,
            max_program_words,
            max_records,
            max_immediates,
            max_coefficients,
            max_sources,
            max_projections,
            max_windows,
            max_columns,
        )
    };
    let grouped_bank = complete_grouped_bank_population(input.grouping);
    let projection_count = input
        .schedules
        .canonical_terms
        .iter()
        .flat_map(|atom| atom.source_uses.iter().map(|source| source.key))
        .collect::<BTreeSet<_>>()
        .len() as u64;
    let max_relative_column = input
        .binding
        .source_slots
        .iter()
        .map(|slot| slot.column as u64)
        .max()
        .unwrap_or(0);
    let immediate_required =
        (input.immediate_count as u64).max(grouped_immediates(input.grouping).len() as u64);
    let coefficient_required = (input.banked_coefficient_count as u64).max(grouped_bank);
    let mut capacity_facts = vec![
        fact(
            CapacityNamespace::CudaKernelArgument,
            "by_value_bytes",
            by_value_bytes,
            KERNEL_ARGUMENT_CEILING_BYTES as u64,
        ),
        fact(
            CapacityNamespace::ModuleConstant,
            "module_constant_bytes",
            R0_CONSTANT_FOOTPRINT_BYTES as u64,
            CUDA_CONSTANT_MEMORY_CEILING_BYTES as u64,
        ),
        fact(
            actual_namespace,
            "program_words",
            encoded_program_words,
            if layout == AnalyticalLayout::CurrentFixed {
                R0_PROGRAM_WORDS as u64
            } else {
                max_program_words
            },
        ),
        fact(actual_namespace, "records", record_count, max_records),
        fact(
            actual_namespace,
            "coefficient_recipes",
            coefficient_required,
            max_coefficients,
        ),
        fact(
            actual_namespace,
            "immediates",
            immediate_required,
            max_immediates,
        ),
        fact(
            actual_namespace,
            "sources",
            input.binding.source_slots.len() as u64,
            max_sources,
        ),
        fact(
            actual_namespace,
            "projections",
            projection_count,
            max_projections,
        ),
        fact(
            actual_namespace,
            "windows",
            input.binding.windows.len() as u64,
            max_windows,
        ),
        fact(
            actual_namespace,
            "relative_column",
            max_relative_column,
            max_columns,
        ),
    ];
    capacity_facts.extend(u16_section_facts(
        metadata_words,
        program_words,
        immediate_words,
    ));
    let canonical_bf = input
        .schedules
        .canonical_terms
        .iter()
        .filter(|atom| atom.value_field == ValueField::Bf)
        .count() as u64;
    let non_unit_bf = input
        .schedules
        .canonical_terms
        .iter()
        .filter(|atom| {
            atom.value_field == ValueField::Bf
                && atom.coefficient_core != NormalizedCoefficientRecipe::one()
        })
        .count() as u64;
    let analysis_bf = input
        .schedules
        .analysis_atoms
        .iter()
        .filter(|atom| atom.value_field == ValueField::Bf)
        .count() as u64;
    capacity_facts.extend([
        fact(
            production_namespace(input.regime),
            "outer_limb_products_naive",
            canonical_bf * 4,
            u64::MAX,
        ),
        fact(
            production_namespace(input.regime),
            "outer_limb_products_unit_specialized",
            non_unit_bf * 4,
            u64::MAX,
        ),
        fact(
            production_namespace(input.regime),
            "outer_limb_products_analysis_grouped",
            analysis_bf * 4,
            u64::MAX,
        ),
    ]);

    EncodingBudget {
        layout,
        source_mode,
        fixed_descriptor_bytes: FIXED_DESCRIPTOR_BYTES,
        metadata_words,
        program_words,
        immediate_bytes,
        source_binding_bytes,
        alignment_padding_bytes,
        by_value_bytes,
        module_constant_bytes: R0_CONSTANT_FOOTPRINT_BYTES as u64,
        device_allocation_bytes: input.device_allocation_bytes,
        capacity_facts,
    }
}

pub fn encoding_budgets(input: &EncodingInput<'_>) -> Vec<EncodingBudget> {
    let canonical_records = input.schedules.canonical_terms.len() as u64;
    let split_program_words = canonical_records * 4;
    let homogeneous_words = compact_record_words(&input.schedules.canonical_terms);
    let grouped_words = grouped_record_words(input);
    let grouped_immediate_bytes = grouped_immediates(input.grouping).len() as u64 * 4;
    // A grouped stream carries every original singleton/member record plus one
    // explicit header for each group. Semantic grouped atoms are not physical
    // wire records and must not be used for this capacity fact.
    let grouped_physical_records = canonical_records + input.grouping.groups.len() as u64;
    vec![
        build_budget(
            input,
            AnalyticalLayout::CurrentFixed,
            SourceMode::SlotIndex,
            0,
            R0_PROGRAM_WORDS as u64,
            0,
            canonical_records,
        ),
        build_budget(
            input,
            AnalyticalLayout::SplitFixed,
            SourceMode::SlotIndex,
            4,
            split_program_words,
            0,
            canonical_records,
        ),
        build_budget(
            input,
            AnalyticalLayout::SplitFixed,
            SourceMode::DirectWindowColumn,
            4,
            split_program_words,
            0,
            canonical_records,
        ),
        build_budget(
            input,
            AnalyticalLayout::HomogeneousStreams,
            SourceMode::SlotIndex,
            16,
            homogeneous_words,
            0,
            canonical_records,
        ),
        build_budget(
            input,
            AnalyticalLayout::HomogeneousStreams,
            SourceMode::DirectWindowColumn,
            16,
            homogeneous_words,
            0,
            canonical_records,
        ),
        build_budget(
            input,
            AnalyticalLayout::GroupedStreams,
            SourceMode::SlotIndex,
            24,
            grouped_words,
            grouped_immediate_bytes,
            grouped_physical_records,
        ),
        build_budget(
            input,
            AnalyticalLayout::GroupedStreams,
            SourceMode::DirectWindowColumn,
            24,
            grouped_words,
            grouped_immediate_bytes,
            grouped_physical_records,
        ),
    ]
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use gpu_gkr_compiler::backward::{
        analyze_coeff_grouping, CoeffGroupingAnalysis, LeanSourceBinding,
        NormalizedCoefficientRecipe, TermId,
    };

    use crate::accumulator_schedule::{
        build_schedule_views, AccumulatorSides, NormalizedAtom, OperandBacking, ScheduleViews,
        SplitSchedule, ValueField,
    };
    use crate::census::{compile_corpus, BackwardRegime};

    use super::*;

    fn fixture() -> (
        ScheduleViews,
        LeanSourceBinding,
        CoeffGroupingAnalysis,
        usize,
        usize,
    ) {
        let layer = compile_corpus().unwrap().layers.remove(0).r0;
        let grouping = analyze_coeff_grouping(&layer.coefficients).unwrap();
        let schedules =
            build_schedule_views(&layer.coefficients, &layer.binding, &grouping).unwrap();
        (
            schedules,
            layer.binding,
            grouping,
            layer.coefficients.coefficients.len(),
            layer.coefficients.immediates.len(),
        )
    }

    fn input<'a>(
        regime: BackwardRegime,
        schedules: &'a ScheduleViews,
        binding: &'a LeanSourceBinding,
        grouping: &'a CoeffGroupingAnalysis,
        banked_coefficient_count: usize,
        immediate_count: usize,
    ) -> EncodingInput<'a> {
        EncodingInput {
            regime,
            schedules,
            binding,
            grouping,
            banked_coefficient_count,
            immediate_count,
            device_allocation_bytes: 123_456,
        }
    }

    #[test]
    fn current_address_spaces_are_not_conflated() {
        let (schedules, binding, grouping, banked, immediates) = fixture();
        let budgets = encoding_budgets(&input(
            BackwardRegime::R0,
            &schedules,
            &binding,
            &grouping,
            banked,
            immediates,
        ));
        let budget = budgets
            .iter()
            .find(|budget| budget.layout == AnalyticalLayout::CurrentFixed)
            .unwrap();
        assert_eq!(budget.by_value_bytes, 17_536);
        assert_eq!(budget.module_constant_bytes, 45_312);
        assert_eq!(budget.device_allocation_bytes, 123_456);
        assert_eq!(budget.module_constant_breakdown(), (27_648, 8_192, 9_472));
    }

    #[test]
    fn direct_mode_removes_only_the_source_slot_table() {
        let (schedules, binding, grouping, banked, immediates) = fixture();
        let budgets = encoding_budgets(&input(
            BackwardRegime::R0,
            &schedules,
            &binding,
            &grouping,
            banked,
            immediates,
        ));
        let find = |mode| {
            budgets
                .iter()
                .find(|budget| {
                    budget.layout == AnalyticalLayout::HomogeneousStreams
                        && budget.source_mode == mode
                })
                .unwrap()
        };
        let slot = find(SourceMode::SlotIndex);
        let direct = find(SourceMode::DirectWindowColumn);
        assert_eq!(
            slot.source_binding_bytes - direct.source_binding_bytes,
            2 * binding.source_slots.len() as u64
        );
        assert_eq!(slot.program_words, direct.program_words);
    }

    #[test]
    fn every_layout_accounts_for_all_metadata_and_alignment() {
        let (schedules, binding, grouping, banked, immediates) = fixture();
        let budgets = encoding_budgets(&input(
            BackwardRegime::R0,
            &schedules,
            &binding,
            &grouping,
            banked,
            immediates,
        ));
        assert_eq!(budgets.len(), 7);
        for budget in budgets {
            assert_eq!(budget.by_value_bytes % 16, 0);
            assert_eq!(
                budget.by_value_bytes,
                budget.fixed_descriptor_bytes
                    + 2 * budget.metadata_words
                    + 2 * budget.program_words
                    + budget.immediate_bytes
                    + budget.source_binding_bytes
                    + budget.alignment_padding_bytes
            );
        }
    }

    #[test]
    fn grouped_stream_capacity_counts_headers_and_every_member_record() {
        let (schedules, binding, grouping, banked, immediates) = fixture();
        let budgets = encoding_budgets(&input(
            BackwardRegime::R0,
            &schedules,
            &binding,
            &grouping,
            banked,
            immediates,
        ));
        let records = find_fact(
            &budgets,
            AnalyticalLayout::GroupedStreams,
            CapacityNamespace::R0Production,
            "records",
        );
        assert_eq!(
            records.required,
            schedules.canonical_terms.len() as u64 + grouping.groups.len() as u64
        );
    }

    fn product_atom(term: u32) -> NormalizedAtom {
        NormalizedAtom {
            terms: vec![TermId(term)],
            sides: AccumulatorSides::C2Only,
            linear_members: 0,
            product_members: 1,
            backing_counts: BTreeMap::from([(OperandBacking::BfBf, 1)]),
            value_field: ValueField::Bf,
            coefficient_core: NormalizedCoefficientRecipe::one(),
            source_uses: Vec::new(),
            member_source_uses: vec![Vec::new()],
        }
    }

    fn synthetic_schedules(count: usize) -> ScheduleViews {
        let atoms = (0..count)
            .map(|index| product_atom(index as u32))
            .collect::<Vec<_>>();
        let split = SplitSchedule {
            bf: atoms.clone(),
            e4: Vec::new(),
            moved_records: 0,
            canonical_transitions: 0,
            split_transitions: 0,
            longest_canonical_bf_run: count as u64,
            longest_canonical_e4_run: 0,
        };
        ScheduleViews {
            canonical_terms: atoms.clone(),
            production_atoms: atoms.clone(),
            analysis_atoms: atoms,
            canonical_split: split.clone(),
            analysis_split: split,
        }
    }

    fn find_fact<'a>(
        budgets: &'a [EncodingBudget],
        layout: AnalyticalLayout,
        namespace: CapacityNamespace,
        kind: &str,
    ) -> &'a CapacityFact {
        budgets
            .iter()
            .find(|budget| budget.layout == layout && budget.source_mode == SourceMode::SlotIndex)
            .unwrap()
            .capacity_facts
            .iter()
            .find(|fact| fact.namespace == namespace && fact.kind == kind)
            .unwrap()
    }

    #[test]
    fn capacity_failures_are_retained_and_regime_labeled() {
        // Sixteen directory words plus 2,383 three-word product records.
        let schedules = synthetic_schedules(2_383);
        let binding = LeanSourceBinding {
            windows: Vec::new(),
            source_slots: Vec::new(),
        };
        let grouping = CoeffGroupingAnalysis {
            term_recipes: Vec::new(),
            groups: Vec::new(),
            ungrouped_terms: Vec::new(),
            c_init_recipe: None,
        };
        let r0 = encoding_budgets(&input(
            BackwardRegime::R0,
            &schedules,
            &binding,
            &grouping,
            1_139,
            513,
        ));
        let ext = encoding_budgets(&input(
            BackwardRegime::Ext,
            &schedules,
            &binding,
            &grouping,
            1_139,
            513,
        ));
        assert_eq!(
            find_fact(
                &r0,
                AnalyticalLayout::HomogeneousStreams,
                CapacityNamespace::R0Production,
                "program_words",
            ),
            &CapacityFact {
                namespace: CapacityNamespace::R0Production,
                kind: "program_words".into(),
                required: 7_165,
                maximum: 7_164,
                fits: false,
            }
        );
        assert!(
            find_fact(
                &ext,
                AnalyticalLayout::HomogeneousStreams,
                CapacityNamespace::ContinuationProduction,
                "program_words"
            )
            .fits
        );
        assert!(
            !find_fact(
                &r0,
                AnalyticalLayout::HomogeneousStreams,
                CapacityNamespace::R0Production,
                "coefficient_recipes"
            )
            .fits
        );
        assert!(
            !find_fact(
                &ext,
                AnalyticalLayout::HomogeneousStreams,
                CapacityNamespace::ContinuationProduction,
                "immediates"
            )
            .fits
        );
    }
}
