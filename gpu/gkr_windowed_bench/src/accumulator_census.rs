use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use gpu_gkr_compiler::backward::{
    analyze_coeff_grouping, decode_continuation_program, decode_r0_program,
    materialize_coeff_grouping_for_semantics, CoeffGroupingAnalysis, CoeffLayer, LeanAtom,
    LeanSourceBinding, NormalizedCoefficientRecipe, TermId,
};
use serde::{Deserialize, Serialize};

use crate::accumulator_bounds::{
    inner_group_bounds, outer_fold_bounds, CapacityBound, InnerMember, InnerMemberKind,
    InnerPolicyBound, MemberSign, BABY_BEAR_ORDER,
};
use crate::accumulator_encoding::{
    complete_grouped_bank_population, encoding_budgets, CapacityFact, EncodingBudget, EncodingInput,
};
use crate::accumulator_locality::{analyze_locality, analyze_split_locality, LocalityMetrics};
use crate::accumulator_schedule::{
    build_schedule_views, specialization_metrics, AccumulatorSides, AtomArity, NormalizedAtom,
    OperandBacking, ScheduleError, ScheduleViews, SpecializationMetrics, ValueField,
};
use crate::census::{
    compile_corpus, BackwardRegime, BaseInvocationCounts, CompiledCorpusLayer, CoordinateId,
    DevelopmentRecursionProfile, InputHash, WorkloadLayer, WorkloadWeightsV1,
};
use crate::r0_harness::production_memory_preflight_for_binding;

pub const ACCUMULATOR_CENSUS_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AccumulatorCensusError {
    Corpus(String),
    Grouping(String),
    Schedule(ScheduleError),
    ArithmeticOverflow {
        metric: &'static str,
    },
    Invariant {
        coordinate: CoordinateId,
        detail: String,
    },
    LegacyDiagnosticDrift {
        metric: &'static str,
        expected: String,
        observed: String,
    },
    Io(String),
    Json(String),
}

impl core::fmt::Display for AccumulatorCensusError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for AccumulatorCensusError {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccumulatorCorpusCensusV1 {
    pub schema_version: u32,
    pub input_sha256: Vec<InputHash>,
    pub parent_census_sha256: String,
    pub workload_weights_sha256: String,
    pub coordinates: Vec<AccumulatorCoordinateRow>,
    pub summaries: Vec<ProfileSummary>,
    pub diagnostics: CorpusDiagnostics,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccumulatorCoordinateRow {
    pub id: CoordinateId,
    pub trace_len: u64,
    pub domain_rows: u64,
    pub passes_per_invocation: u32,
    pub population: PopulationMetrics,
    pub canonical_split: SplitMetrics,
    pub analysis_grouping: GroupingMetrics,
    pub outer_bounds: OuterBoundMetrics,
    pub inner_bounds: Vec<InnerGroupBoundRow>,
    pub specializations: SpecializationMetrics,
    pub locality: ScheduleLocalityRows,
    pub encodings: Vec<EncodingBudget>,
    pub weights: Vec<CoordinateProfileWeight>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedCount {
    pub key: String,
    pub count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactMetric {
    pub metric: String,
    pub exact_decimal: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TaxonomyCount {
    pub sides: AccumulatorSides,
    pub arity: AtomArity,
    pub backing: OperandBacking,
    pub value_field: ValueField,
    pub count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PopulationMetrics {
    pub terms: u64,
    pub canonical_atoms: u64,
    pub production_atoms: u64,
    pub analysis_atoms: u64,
    pub taxonomy: Vec<TaxonomyCount>,
    pub native_opcodes: Vec<NamedCount>,
    pub canonical_phase_transitions: u64,
    pub longest_canonical_bf_phase: u64,
    pub longest_canonical_e4_phase: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SplitMetrics {
    pub bf_atoms: u64,
    pub e4_atoms: u64,
    pub bf_records: u64,
    pub e4_records: u64,
    pub moved_records: u64,
    pub canonical_transitions: u64,
    pub split_transitions: u64,
    pub bf_unique_sources: u64,
    pub e4_unique_sources: u64,
    pub intersecting_sources: u64,
    pub canonical_window_transitions: u64,
    pub split_window_transitions: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GroupingMetrics {
    pub mode: String,
    pub groups: u64,
    pub members: u64,
    pub bf_only_groups: u64,
    pub e4_only_groups: u64,
    pub mixed_groups: u64,
    pub group_size_histogram: Vec<NamedCount>,
    pub size_two_members: u64,
    pub size_three_or_four_members: u64,
    pub size_five_or_more_members: u64,
    pub bf_linear_members: u64,
    pub bf_product_members: u64,
    pub e4_linear_members: u64,
    pub e4_product_members: u64,
    pub immediate_one_members: u64,
    pub immediate_neg_one_members: u64,
    pub immediate_banked_members: u64,
    pub core_use_histogram: Vec<NamedCount>,
    pub original_atoms: u64,
    pub grouped_atoms: u64,
    pub complete_bank_population: u64,
    pub capacity_facts: Vec<CapacityFact>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OuterBoundMetrics {
    pub canonical_bf_atoms: u64,
    pub analysis_bf_atoms: u64,
    pub canonical: Vec<CapacityBound>,
    pub analysis_grouped: Vec<CapacityBound>,
    pub observed_maxima: Vec<ExactMetric>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InnerGroupPrimitiveCounts {
    pub bf_linear: u64,
    pub bf_product: u64,
    pub e4_linear: u64,
    pub e4_product: u64,
    pub positive: u64,
    pub negative: u64,
    pub maximum_immediate: u32,
    pub immediate_magnitudes: Vec<NamedCount>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InnerGroupBoundRow {
    pub group_index: u32,
    pub value_field: ValueField,
    pub primitives: InnerGroupPrimitiveCounts,
    pub policies: Vec<InnerPolicyBound>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScheduleLocalityRows {
    pub canonical: LocalityMetrics,
    pub stable_split_whole: LocalityMetrics,
    pub stable_split_bf: LocalityMetrics,
    pub stable_split_e4: LocalityMetrics,
    pub analysis_grouped_whole: LocalityMetrics,
    pub analysis_grouped_bf: LocalityMetrics,
    pub analysis_grouped_e4: LocalityMetrics,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinateProfileWeight {
    pub profile: String,
    pub weight: Option<u64>,
    pub missing_reason: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileSummary {
    pub profile: String,
    pub covered_coordinates: u64,
    pub missing_coordinates: Vec<CoordinateId>,
    pub weighted_metrics: Vec<ExactMetric>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CorpusDiagnostics {
    pub ext_production_grouping_equal: u64,
    pub r0_semantic_identities: u64,
    pub ext_semantic_identities: u64,
    pub legacy_ext_groups: u64,
    pub legacy_ext_bf_groups: u64,
    pub legacy_ext_e4_groups: u64,
    pub legacy_ext_mixed_groups: u64,
    pub legacy_ext_e4_all_size_two: bool,
    pub legacy_grouped_terms: u64,
    pub legacy_total_terms: u64,
    pub legacy_grouped_coverage_basis_points: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticValidationSummary {
    pub r0_cases: u64,
    pub ext_cases: u64,
    pub r0_cell_comparisons: u64,
    pub ext_cell_comparisons: u64,
    pub ext_production_grouping_equal: u64,
}

fn sha256_bytes(bytes: &[u8]) -> Result<String, AccumulatorCensusError> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| AccumulatorCensusError::Io(format!("spawn sha256sum: {error}")))?;
    child
        .stdin
        .take()
        .ok_or_else(|| AccumulatorCensusError::Io("sha256sum stdin unavailable".into()))?
        .write_all(bytes)
        .map_err(|error| AccumulatorCensusError::Io(format!("write sha256sum: {error}")))?;
    let output = child
        .wait_with_output()
        .map_err(|error| AccumulatorCensusError::Io(format!("wait sha256sum: {error}")))?;
    if !output.status.success() {
        return Err(AccumulatorCensusError::Io(format!(
            "sha256sum exited {}",
            output.status
        )));
    }
    String::from_utf8(output.stdout)
        .map_err(|error| AccumulatorCensusError::Io(format!("sha256sum utf8: {error}")))?
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .ok_or_else(|| AccumulatorCensusError::Io("sha256sum produced no digest".into()))
}

fn read_artifact(name: &str) -> Result<Vec<u8>, AccumulatorCensusError> {
    let path = crate::runtime_paths::crate_root()
        .join("artifacts")
        .join(name);
    std::fs::read(&path)
        .map_err(|error| AccumulatorCensusError::Io(format!("read {}: {error}", path.display())))
}

fn taxonomy(atoms: &[NormalizedAtom]) -> Result<Vec<TaxonomyCount>, AccumulatorCensusError> {
    let mut counts = BTreeMap::new();
    for atom in atoms {
        let arity = if atom.product_members == 0 {
            AtomArity::Linear
        } else {
            AtomArity::Product
        };
        if atom.backing_counts.len() != 1 {
            return Err(AccumulatorCensusError::Corpus(format!(
                "canonical atom has {} backing classes",
                atom.backing_counts.len()
            )));
        }
        let backing = *atom.backing_counts.keys().next().unwrap();
        *counts
            .entry((atom.sides, arity, backing, atom.value_field))
            .or_insert(0u64) += atom.terms.len() as u64;
    }
    Ok(counts
        .into_iter()
        .map(
            |((sides, arity, backing, value_field), count)| TaxonomyCount {
                sides,
                arity,
                backing,
                value_field,
                count,
            },
        )
        .collect())
}

fn native_opcodes(atoms: &[LeanAtom]) -> Vec<NamedCount> {
    let mut counts = BTreeMap::<String, u64>::new();
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                *counts.entry(format!("class_{}", term.class)).or_default() += 1
            }
            LeanAtom::Group { members, .. } => {
                *counts.entry("group_header".into()).or_default() += 1;
                for member in members {
                    *counts.entry(format!("class_{}", member.class)).or_default() += 1;
                }
            }
        }
    }
    counts
        .into_iter()
        .map(|(key, count)| NamedCount { key, count })
        .collect()
}

fn atoms_by_term(views: &ScheduleViews) -> BTreeMap<TermId, &NormalizedAtom> {
    views
        .canonical_terms
        .iter()
        .flat_map(|atom| atom.terms.iter().map(move |term| (*term, atom)))
        .collect()
}

fn group_field<'a>(
    group: &gpu_gkr_compiler::backward::CoeffGroupingCandidate,
    terms: &BTreeMap<TermId, &'a NormalizedAtom>,
) -> Result<Option<ValueField>, AccumulatorCensusError> {
    let fields = group
        .members
        .iter()
        .map(|member| {
            terms
                .get(&member.term)
                .map(|atom| atom.value_field)
                .ok_or_else(|| {
                    AccumulatorCensusError::Grouping(format!(
                        "group term {:?} is absent from canonical atoms",
                        member.term
                    ))
                })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    Ok(if fields.len() == 1 {
        fields.into_iter().next()
    } else {
        None
    })
}

fn grouping_metrics(
    regime: BackwardRegime,
    analysis: &CoeffGroupingAnalysis,
    views: &ScheduleViews,
    encodings: &[EncodingBudget],
) -> Result<GroupingMetrics, AccumulatorCensusError> {
    let terms = atoms_by_term(views);
    let mut sizes = BTreeMap::<u64, u64>::new();
    let mut bf_only_groups = 0;
    let mut e4_only_groups = 0;
    let mut mixed_groups = 0;
    let mut size_two_members = 0;
    let mut size_three_or_four_members = 0;
    let mut size_five_or_more_members = 0;
    let mut bf_linear_members = 0;
    let mut bf_product_members = 0;
    let mut e4_linear_members = 0;
    let mut e4_product_members = 0;
    let mut immediate_one_members = 0;
    let mut immediate_neg_one_members = 0;
    let mut immediate_banked_members = 0;
    for group in &analysis.groups {
        let size = group.members.len() as u64;
        *sizes.entry(size).or_default() += 1;
        match size {
            2 => size_two_members += size,
            3..=4 => size_three_or_four_members += size,
            _ if size >= 5 => size_five_or_more_members += size,
            _ => {}
        }
        match group_field(group, &terms)? {
            Some(ValueField::Bf) => bf_only_groups += 1,
            Some(ValueField::E4) => e4_only_groups += 1,
            None => mixed_groups += 1,
        }
        for member in &group.members {
            let atom = terms.get(&member.term).unwrap();
            match (atom.value_field, atom.product_members == 0) {
                (ValueField::Bf, true) => bf_linear_members += 1,
                (ValueField::Bf, false) => bf_product_members += 1,
                (ValueField::E4, true) => e4_linear_members += 1,
                (ValueField::E4, false) => e4_product_members += 1,
            }
            match u128::from(member.immediate) {
                1 => immediate_one_members += 1,
                value if value == BABY_BEAR_ORDER - 1 => immediate_neg_one_members += 1,
                _ => immediate_banked_members += 1,
            }
        }
    }
    let capacity_facts = encodings
        .iter()
        .find(|budget| {
            budget.layout == crate::accumulator_encoding::AnalyticalLayout::GroupedStreams
                && budget.source_mode == crate::accumulator_encoding::SourceMode::SlotIndex
        })
        .map(|budget| budget.capacity_facts.clone())
        .unwrap_or_default();
    Ok(GroupingMetrics {
        mode: match regime {
            BackwardRegime::R0 => "analysis_only",
            BackwardRegime::Ext => "production_and_analysis",
        }
        .into(),
        groups: analysis.groups.len() as u64,
        members: analysis
            .groups
            .iter()
            .map(|group| group.members.len() as u64)
            .sum(),
        bf_only_groups,
        e4_only_groups,
        mixed_groups,
        group_size_histogram: sizes
            .iter()
            .map(|(size, count)| NamedCount {
                key: size.to_string(),
                count: *count,
            })
            .collect(),
        size_two_members,
        size_three_or_four_members,
        size_five_or_more_members,
        bf_linear_members,
        bf_product_members,
        e4_linear_members,
        e4_product_members,
        immediate_one_members,
        immediate_neg_one_members,
        immediate_banked_members,
        core_use_histogram: sizes
            .into_iter()
            .map(|(uses, count)| NamedCount {
                key: uses.to_string(),
                count,
            })
            .collect(),
        original_atoms: views.canonical_terms.len() as u64,
        grouped_atoms: views.analysis_atoms.len() as u64,
        complete_bank_population: complete_grouped_bank_population(analysis),
        capacity_facts,
    })
}

fn signed_immediate(immediate: u32) -> (MemberSign, u32) {
    if u128::from(immediate) > (BABY_BEAR_ORDER - 1) / 2 {
        (
            MemberSign::Negative,
            (BABY_BEAR_ORDER - u128::from(immediate)) as u32,
        )
    } else {
        (MemberSign::Positive, immediate)
    }
}

fn inner_rows(
    analysis: &CoeffGroupingAnalysis,
    views: &ScheduleViews,
) -> Result<Vec<InnerGroupBoundRow>, AccumulatorCensusError> {
    let terms = atoms_by_term(views);
    analysis
        .groups
        .iter()
        .enumerate()
        .map(|(group_index, group)| {
            let value_field = group_field(group, &terms)?.unwrap_or(ValueField::E4);
            let mut primitive = InnerGroupPrimitiveCounts {
                bf_linear: 0,
                bf_product: 0,
                e4_linear: 0,
                e4_product: 0,
                positive: 0,
                negative: 0,
                maximum_immediate: 0,
                immediate_magnitudes: Vec::new(),
            };
            let mut magnitudes = BTreeMap::<u32, u64>::new();
            let mut members = Vec::new();
            for member in &group.members {
                let atom = terms.get(&member.term).unwrap();
                let kind = match (atom.value_field, atom.product_members == 0) {
                    (ValueField::Bf, true) => {
                        primitive.bf_linear += 1;
                        InnerMemberKind::BfLinear
                    }
                    (ValueField::Bf, false) => {
                        primitive.bf_product += 1;
                        InnerMemberKind::BfProduct
                    }
                    (ValueField::E4, true) => {
                        primitive.e4_linear += 1;
                        InnerMemberKind::E4Linear
                    }
                    (ValueField::E4, false) => {
                        primitive.e4_product += 1;
                        if atom.backing_counts.contains_key(&OperandBacking::BfE4) {
                            InnerMemberKind::BfE4Product
                        } else {
                            InnerMemberKind::E4Product
                        }
                    }
                };
                let (sign, magnitude) = signed_immediate(member.immediate);
                match sign {
                    MemberSign::Positive => primitive.positive += 1,
                    MemberSign::Negative => primitive.negative += 1,
                }
                primitive.maximum_immediate = primitive.maximum_immediate.max(magnitude);
                *magnitudes.entry(magnitude).or_default() += 1;
                members.push(InnerMember {
                    kind,
                    sign,
                    immediate: magnitude,
                });
            }
            primitive.immediate_magnitudes = magnitudes
                .into_iter()
                .map(|(magnitude, count)| NamedCount {
                    key: magnitude.to_string(),
                    count,
                })
                .collect();
            Ok(InnerGroupBoundRow {
                group_index: group_index as u32,
                value_field,
                primitives: primitive,
                policies: inner_group_bounds(&members),
            })
        })
        .collect()
}

fn weights_for_coordinate(
    circuit: &str,
    passes: u32,
    weights: &WorkloadWeightsV1,
) -> Result<Vec<CoordinateProfileWeight>, AccumulatorCensusError> {
    fn base_weight(circuit: &str, counts: &BaseInvocationCounts) -> Option<u64> {
        match circuit {
            "add_sub_lui_auipc_mop" => Some(counts.add_sub),
            "bigint_with_extended_control" => Some(counts.bigint),
            "inits_and_teardowns" => Some(counts.initial),
            "jump_branch_slt" => Some(counts.jump),
            "keccak_special5" => Some(counts.keccak),
            "mem_subword_only" => Some(counts.mem_subword),
            "mem_word_only" => Some(counts.mem_word),
            "shift_binop" => Some(counts.shift),
            "unsigned_mul_div" => Some(counts.mul_div),
            _ => None,
        }
    }
    fn layer_weight(circuit: &str, layers: &[WorkloadLayer]) -> Option<u64> {
        let mut found = false;
        let mut total = 0u64;
        for layer in layers.iter().filter(|layer| layer.circuit == circuit) {
            found = true;
            total = total.checked_add(
                layer
                    .invocations
                    .checked_mul(u64::from(layer.estimated_passes))?,
            )?;
        }
        found.then_some(total)
    }
    let with_passes = |weight: u64| {
        weight
            .checked_mul(u64::from(passes))
            .ok_or(AccumulatorCensusError::ArithmeticOverflow {
                metric: "coordinate weight",
            })
    };
    let row = |profile: &str, weight: Option<u64>, reason: &str| {
        Ok(CoordinateProfileWeight {
            profile: profile.into(),
            weight: weight.map(&with_passes).transpose()?,
            missing_reason: weight.is_none().then(|| reason.to_owned()),
        })
    };
    let development = match &weights.profiles.development_recursion_proxy {
        DevelopmentRecursionProfile::Available { layers, .. } => layer_weight(circuit, layers),
        DevelopmentRecursionProfile::Unavailable { .. } => None,
    };
    Ok(vec![
        row("unweighted", Some(1), "")?,
        row(
            "current_base",
            base_weight(circuit, &weights.profiles.current_base),
            "circuit family is absent from the current-base profile",
        )?,
        row(
            "development_recursion_proxy",
            development,
            "circuit family is absent or the development profile is unavailable",
        )?,
        row(
            "future_current_recursion",
            weights
                .profiles
                .future_current_recursion
                .as_deref()
                .and_then(|layers| layer_weight(circuit, layers)),
            "future current-recursion profile is unavailable or missing this circuit",
        )?,
    ])
}

fn coordinate_row(
    layer: &CompiledCorpusLayer,
    regime: BackwardRegime,
    parent: (u64, u32),
    weights: &WorkloadWeightsV1,
) -> Result<(AccumulatorCoordinateRow, CoeffGroupingAnalysis), AccumulatorCensusError> {
    let (coefficients, binding, decoded) = match regime {
        BackwardRegime::R0 => (
            &layer.r0.coefficients,
            &layer.r0.binding,
            decode_r0_program(&layer.r0.program)
                .map_err(|error| AccumulatorCensusError::Corpus(format!("decode R0: {error:?}")))?,
        ),
        BackwardRegime::Ext => (
            &layer.ext.coefficients,
            &layer.ext.binding,
            decode_continuation_program(&layer.ext.program).map_err(|error| {
                AccumulatorCensusError::Corpus(format!("decode continuation: {error:?}"))
            })?,
        ),
    };
    let analysis = analyze_coeff_grouping(coefficients)
        .map_err(|error| AccumulatorCensusError::Grouping(format!("{error:?}")))?;
    let views = build_schedule_views(coefficients, binding, &analysis)
        .map_err(AccumulatorCensusError::Schedule)?;
    let canonical_locality = analyze_locality(&views.canonical_terms);
    let split_locality =
        analyze_split_locality(&views.canonical_split.bf, &views.canonical_split.e4);
    let grouped_locality =
        analyze_split_locality(&views.analysis_split.bf, &views.analysis_split.e4);
    let canonical_bf_atoms = views.canonical_split.bf.len() as u64;
    let analysis_bf_atoms = views.analysis_split.bf.len() as u64;
    let preflight = production_memory_preflight_for_binding(
        binding,
        layer.trace_len.ilog2(),
        coefficients.coefficients.len(),
        0,
        None,
    )
    .map_err(|error| AccumulatorCensusError::Corpus(format!("memory preflight: {error}")))?;
    let encodings = encoding_budgets(&EncodingInput {
        regime,
        schedules: &views,
        binding,
        grouping: &analysis,
        banked_coefficient_count: coefficients.coefficients.len(),
        immediate_count: coefficients.immediates.len(),
        device_allocation_bytes: preflight.requested_bytes,
    });
    let population = PopulationMetrics {
        terms: coefficients.terms.len() as u64,
        canonical_atoms: views.canonical_terms.len() as u64,
        production_atoms: views.production_atoms.len() as u64,
        analysis_atoms: views.analysis_atoms.len() as u64,
        taxonomy: taxonomy(&views.canonical_terms)?,
        native_opcodes: native_opcodes(&decoded),
        canonical_phase_transitions: views.canonical_split.canonical_transitions,
        longest_canonical_bf_phase: views.canonical_split.longest_canonical_bf_run,
        longest_canonical_e4_phase: views.canonical_split.longest_canonical_e4_run,
    };
    let canonical_split = SplitMetrics {
        bf_atoms: views.canonical_split.bf.len() as u64,
        e4_atoms: views.canonical_split.e4.len() as u64,
        bf_records: views
            .canonical_split
            .bf
            .iter()
            .map(|atom| atom.terms.len() as u64)
            .sum(),
        e4_records: views
            .canonical_split
            .e4
            .iter()
            .map(|atom| atom.terms.len() as u64)
            .sum(),
        moved_records: views.canonical_split.moved_records,
        canonical_transitions: views.canonical_split.canonical_transitions,
        split_transitions: views.canonical_split.split_transitions,
        bf_unique_sources: split_locality.bf_unique_sources,
        e4_unique_sources: split_locality.e4_unique_sources,
        intersecting_sources: split_locality.intersecting_sources,
        canonical_window_transitions: canonical_locality.source_window_transitions,
        split_window_transitions: split_locality.whole.source_window_transitions,
    };
    let specializations =
        specialization_metrics(coefficients, binding, &analysis, &views.analysis_atoms)
            .map_err(AccumulatorCensusError::Schedule)?;
    let row = AccumulatorCoordinateRow {
        id: CoordinateId {
            circuit: layer.circuit.clone(),
            layer: layer.layer as u32,
            regime,
        },
        trace_len: layer.trace_len,
        domain_rows: parent.0,
        passes_per_invocation: parent.1,
        population,
        canonical_split,
        analysis_grouping: grouping_metrics(regime, &analysis, &views, &encodings)?,
        outer_bounds: OuterBoundMetrics {
            canonical_bf_atoms,
            analysis_bf_atoms,
            canonical: outer_fold_bounds(canonical_bf_atoms).into(),
            analysis_grouped: outer_fold_bounds(analysis_bf_atoms).into(),
            observed_maxima: vec![
                ExactMetric {
                    metric: "canonical_bf_atoms".into(),
                    exact_decimal: canonical_bf_atoms.to_string(),
                },
                ExactMetric {
                    metric: "analysis_bf_atoms".into(),
                    exact_decimal: analysis_bf_atoms.to_string(),
                },
            ],
        },
        inner_bounds: inner_rows(&analysis, &views)?,
        specializations,
        locality: ScheduleLocalityRows {
            canonical: canonical_locality,
            stable_split_whole: split_locality.whole,
            stable_split_bf: split_locality.bf,
            stable_split_e4: split_locality.e4,
            analysis_grouped_whole: grouped_locality.whole,
            analysis_grouped_bf: grouped_locality.bf,
            analysis_grouped_e4: grouped_locality.e4,
        },
        encodings,
        weights: weights_for_coordinate(&layer.circuit, parent.1, weights)?,
    };
    Ok((row, analysis))
}

fn profile_summaries(
    rows: &[AccumulatorCoordinateRow],
) -> Result<Vec<ProfileSummary>, AccumulatorCensusError> {
    const METRIC_NAMES: [&str; 22] = [
        "terms",
        "product_members",
        "groups",
        "group_members",
        "source_uses",
        "literal_one_cores",
        "literal_neg_one_cores",
        "one_nonzero_limb_cores",
        "group_immediate_one",
        "group_immediate_neg_one",
        "group_immediate_banked",
        "self_products",
        "same_window_products",
        "linear_members",
        "procedural_operand_uses",
        "stored_operand_uses",
        "modeled_outer_intermediate_reductions",
        "modeled_outer_boundary_reductions",
        "modeled_outer_infeasible_states",
        "modeled_inner_intermediate_reductions",
        "modeled_inner_boundary_reductions",
        "modeled_inner_infeasible_states",
    ];
    #[derive(Default)]
    struct ReductionWork {
        outer_intermediate: u128,
        outer_boundary: u128,
        outer_infeasible: u128,
        inner_intermediate: u128,
        inner_boundary: u128,
        inner_infeasible: u128,
    }

    fn add_bound(bound: &CapacityBound, inner: bool, work: &mut ReductionWork) {
        match &bound.disposition {
            crate::accumulator_bounds::CapacityDisposition::Feasible(details) => {
                if inner {
                    work.inner_intermediate += u128::from(details.intermediate_reductions);
                    work.inner_boundary += u128::from(details.boundary_reductions);
                } else {
                    work.outer_intermediate += u128::from(details.intermediate_reductions);
                    work.outer_boundary += u128::from(details.boundary_reductions);
                }
            }
            crate::accumulator_bounds::CapacityDisposition::Infeasible { .. } => {
                if inner {
                    work.inner_infeasible += 1;
                } else {
                    work.outer_infeasible += 1;
                }
            }
        }
    }

    fn reduction_work(row: &AccumulatorCoordinateRow) -> ReductionWork {
        let mut work = ReductionWork::default();
        for bound in row
            .outer_bounds
            .canonical
            .iter()
            .chain(&row.outer_bounds.analysis_grouped)
        {
            add_bound(bound, false, &mut work);
        }
        for group in &row.inner_bounds {
            for policy in &group.policies {
                match &policy.states {
                    crate::accumulator_bounds::InnerStateBounds::Canonical { state } => {
                        add_bound(state, true, &mut work);
                    }
                    crate::accumulator_bounds::InnerStateBounds::SignSplit {
                        positive,
                        negative,
                    } => {
                        add_bound(positive, true, &mut work);
                        add_bound(negative, true, &mut work);
                    }
                }
            }
        }
        work
    }

    [
        "unweighted",
        "current_base",
        "development_recursion_proxy",
        "future_current_recursion",
    ]
    .into_iter()
    .map(|profile| {
        let mut covered = 0;
        let mut missing = Vec::new();
        let mut totals = METRIC_NAMES
            .into_iter()
            .map(|metric| (metric, 0u128))
            .collect::<BTreeMap<_, _>>();
        for row in rows {
            let weight = row
                .weights
                .iter()
                .find(|weight| weight.profile == profile)
                .unwrap();
            let Some(weight) = weight.weight else {
                missing.push(row.id.clone());
                continue;
            };
            covered += 1;
            let weight = u128::from(weight);
            let mut checked_add = |metric: &'static str, value: u128| {
                let total = totals.entry(metric).or_default();
                *total = total
                    .checked_add(
                        value
                            .checked_mul(weight)
                            .ok_or(AccumulatorCensusError::ArithmeticOverflow { metric })?,
                    )
                    .ok_or(AccumulatorCensusError::ArithmeticOverflow { metric })?;
                Ok::<_, AccumulatorCensusError>(())
            };
            let specializations = &row.specializations;
            let reductions = reduction_work(row);
            for (metric, value) in [
                ("terms", u128::from(row.population.terms)),
                (
                    "product_members",
                    u128::from(specializations.product_members),
                ),
                ("groups", u128::from(row.analysis_grouping.groups)),
                ("group_members", u128::from(row.analysis_grouping.members)),
                (
                    "source_uses",
                    u128::from(row.locality.canonical.source_uses),
                ),
                (
                    "literal_one_cores",
                    u128::from(specializations.literal_one_cores),
                ),
                (
                    "literal_neg_one_cores",
                    u128::from(specializations.literal_neg_one_cores),
                ),
                (
                    "one_nonzero_limb_cores",
                    u128::from(specializations.one_nonzero_limb_cores),
                ),
                (
                    "group_immediate_one",
                    u128::from(specializations.group_immediate_one),
                ),
                (
                    "group_immediate_neg_one",
                    u128::from(specializations.group_immediate_neg_one),
                ),
                (
                    "group_immediate_banked",
                    u128::from(specializations.group_immediate_banked),
                ),
                ("self_products", u128::from(specializations.self_products)),
                (
                    "same_window_products",
                    u128::from(specializations.same_window_products),
                ),
                ("linear_members", u128::from(specializations.linear_members)),
                (
                    "procedural_operand_uses",
                    u128::from(specializations.procedural_operand_uses),
                ),
                (
                    "stored_operand_uses",
                    u128::from(specializations.stored_operand_uses),
                ),
                (
                    "modeled_outer_intermediate_reductions",
                    reductions.outer_intermediate,
                ),
                (
                    "modeled_outer_boundary_reductions",
                    reductions.outer_boundary,
                ),
                (
                    "modeled_outer_infeasible_states",
                    reductions.outer_infeasible,
                ),
                (
                    "modeled_inner_intermediate_reductions",
                    reductions.inner_intermediate,
                ),
                (
                    "modeled_inner_boundary_reductions",
                    reductions.inner_boundary,
                ),
                (
                    "modeled_inner_infeasible_states",
                    reductions.inner_infeasible,
                ),
            ] {
                checked_add(metric, value)?;
            }
        }
        Ok(ProfileSummary {
            profile: profile.into(),
            covered_coordinates: covered,
            missing_coordinates: missing,
            weighted_metrics: totals
                .into_iter()
                .map(|(metric, value)| ExactMetric {
                    metric: metric.into(),
                    exact_decimal: value.to_string(),
                })
                .collect(),
        })
    })
    .collect()
}

fn check_legacy_diagnostic(
    metric: &'static str,
    expected: impl ToString,
    observed: impl ToString,
) -> Result<(), AccumulatorCensusError> {
    let expected = expected.to_string();
    let observed = observed.to_string();
    if expected != observed {
        return Err(AccumulatorCensusError::LegacyDiagnosticDrift {
            metric,
            expected,
            observed,
        });
    }
    Ok(())
}

fn rounded_basis_points(numerator: u64, denominator: u64) -> Result<u64, AccumulatorCensusError> {
    numerator
        .checked_mul(10_000)
        .and_then(|scaled| scaled.checked_add(denominator / 2))
        .map(|rounded| rounded / denominator)
        .ok_or(AccumulatorCensusError::ArithmeticOverflow {
            metric: "legacy grouped coverage",
        })
}

pub fn generate_accumulator_census(
    weights: WorkloadWeightsV1,
) -> Result<AccumulatorCorpusCensusV1, AccumulatorCensusError> {
    weights
        .validate()
        .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
    let parent_bytes = read_artifact("windowed_corpus_census_v1.json")?;
    let parent: crate::census::CorpusCensusV1 = serde_json::from_slice(&parent_bytes)
        .map_err(|error| AccumulatorCensusError::Json(format!("parse parent census: {error}")))?;
    let parent_rows = parent
        .coordinates
        .iter()
        .map(|row| {
            (
                (row.id.circuit.clone(), row.id.layer, row.id.regime),
                (row.semantic.domain_rows, row.semantic.passes_per_invocation),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let checked_workload_bytes = read_artifact("windowed_workload_weights_v1.json")?;
    let checked_workload: WorkloadWeightsV1 = serde_json::from_slice(&checked_workload_bytes)
        .map_err(|error| {
            AccumulatorCensusError::Json(format!("parse workload weights: {error}"))
        })?;
    let workload_bytes = if checked_workload == weights {
        checked_workload_bytes
    } else {
        serde_json::to_vec(&weights)
            .map_err(|error| AccumulatorCensusError::Json(format!("serialize weights: {error}")))?
    };
    let r0_corpus_bytes = read_artifact("windowed_r0_corpus_v1.bin")?;
    let compiled =
        compile_corpus().map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
    let mut input_sha256 = compiled.input_sha256;
    input_sha256.push(InputHash {
        path: "artifacts/windowed_r0_corpus_v1.bin".into(),
        sha256: sha256_bytes(&r0_corpus_bytes)?,
    });
    let mut coordinates = Vec::with_capacity(114);
    let mut ext_production_grouping_equal = 0;
    let mut legacy_ext_groups = 0;
    let mut legacy_ext_bf_groups = 0;
    let mut legacy_ext_e4_groups = 0;
    let mut legacy_ext_mixed_groups = 0;
    let mut legacy_ext_e4_all_size_two = true;
    let mut legacy_ext_bf_max_group = 0usize;
    let mut legacy_grouped_terms = 0u64;
    let mut legacy_total_terms = 0u64;

    for layer in &compiled.layers {
        for regime in [BackwardRegime::R0, BackwardRegime::Ext] {
            let key = (layer.circuit.clone(), layer.layer as u32, regime);
            let parent = parent_rows.get(&key).copied().ok_or_else(|| {
                AccumulatorCensusError::Invariant {
                    coordinate: CoordinateId {
                        circuit: key.0.clone(),
                        layer: key.1,
                        regime,
                    },
                    detail: "coordinate is absent from parent census".into(),
                }
            })?;
            if parent.0 != layer.trace_len {
                return Err(AccumulatorCensusError::Invariant {
                    coordinate: CoordinateId {
                        circuit: key.0.clone(),
                        layer: key.1,
                        regime,
                    },
                    detail: format!(
                        "parent domain rows {} differ from parsed trace length {}",
                        parent.0, layer.trace_len
                    ),
                });
            }
            let (row, analysis) = coordinate_row(layer, regime, parent, &weights)?;
            if regime == BackwardRegime::Ext {
                let materialized =
                    materialize_coeff_grouping_for_semantics(&layer.ext.coefficients, &analysis)
                        .map_err(|error| AccumulatorCensusError::Grouping(format!("{error:?}")))?;
                if materialized == layer.ext.coefficients {
                    ext_production_grouping_equal += 1;
                }
                let diagnostic_views =
                    build_schedule_views(&layer.ext.coefficients, &layer.ext.binding, &analysis)
                        .map_err(AccumulatorCensusError::Schedule)?;
                let terms = atoms_by_term(&diagnostic_views);
                legacy_ext_groups += analysis.groups.len() as u64;
                legacy_total_terms += layer.ext.coefficients.terms.len() as u64;
                for group in &analysis.groups {
                    legacy_grouped_terms += group.members.len() as u64;
                    match group_field(group, &terms)? {
                        Some(ValueField::Bf) => {
                            legacy_ext_bf_groups += 1;
                            legacy_ext_bf_max_group =
                                legacy_ext_bf_max_group.max(group.members.len());
                        }
                        Some(ValueField::E4) => {
                            legacy_ext_e4_groups += 1;
                            legacy_ext_e4_all_size_two &= group.members.len() == 2;
                        }
                        None => legacy_ext_mixed_groups += 1,
                    }
                }
            }
            coordinates.push(row);
        }
    }
    coordinates.sort_by(|left, right| {
        (&left.id.circuit, left.id.layer, left.id.regime).cmp(&(
            &right.id.circuit,
            right.id.layer,
            right.id.regime,
        ))
    });
    check_legacy_diagnostic("ext_groups", 1_488, legacy_ext_groups)?;
    check_legacy_diagnostic("ext_bf_groups", 1_005, legacy_ext_bf_groups)?;
    check_legacy_diagnostic("ext_e4_groups", 483, legacy_ext_e4_groups)?;
    check_legacy_diagnostic("ext_mixed_groups", 0, legacy_ext_mixed_groups)?;
    check_legacy_diagnostic("ext_e4_all_size_two", true, legacy_ext_e4_all_size_two)?;
    check_legacy_diagnostic("ext_bf_max_group", 49, legacy_ext_bf_max_group)?;
    let coverage_basis_points = rounded_basis_points(legacy_grouped_terms, legacy_total_terms)?;
    check_legacy_diagnostic(
        "ext_grouped_coverage_basis_points",
        6_861,
        coverage_basis_points,
    )?;
    let summaries = profile_summaries(&coordinates)?;
    Ok(AccumulatorCorpusCensusV1 {
        schema_version: ACCUMULATOR_CENSUS_SCHEMA_VERSION,
        input_sha256,
        parent_census_sha256: sha256_bytes(&parent_bytes)?,
        workload_weights_sha256: sha256_bytes(&workload_bytes)?,
        coordinates,
        summaries,
        diagnostics: CorpusDiagnostics {
            ext_production_grouping_equal,
            r0_semantic_identities: 342,
            ext_semantic_identities: 342,
            legacy_ext_groups,
            legacy_ext_bf_groups,
            legacy_ext_e4_groups,
            legacy_ext_mixed_groups,
            legacy_ext_e4_all_size_two,
            legacy_grouped_terms,
            legacy_total_terms,
            legacy_grouped_coverage_basis_points: coverage_basis_points,
        },
    })
}

pub fn render_accumulator_report(
    census: &AccumulatorCorpusCensusV1,
) -> Result<String, AccumulatorCensusError> {
    if census.schema_version != ACCUMULATOR_CENSUS_SCHEMA_VERSION {
        return Err(AccumulatorCensusError::Corpus(format!(
            "unsupported accumulator census schema {}",
            census.schema_version
        )));
    }
    let mut report = String::new();
    report.push_str("# Windowed GKR R0 Accumulator And Encoding Census\n\n");
    report.push_str(&format!(
        "- Coverage: {} coordinate rows across 57 layers and two regimes.\n",
        census.coordinates.len()
    ));
    report.push_str(&format!(
        "- Parent census SHA-256: `{}`\n",
        census.parent_census_sha256
    ));
    report.push_str(&format!(
        "- Workload weights SHA-256: `{}`\n\n",
        census.workload_weights_sha256
    ));
    report.push_str("## Bound inputs\n\n| Path | SHA-256 |\n|---|---|\n");
    for input in &census.input_sha256 {
        report.push_str(&format!("| `{}` | `{}` |\n", input.path, input.sha256));
    }
    report.push_str("\n## Profile summaries\n\n| Profile | Covered | Missing | Weighted terms | Weighted products | Weighted groups | Weighted group members | Weighted source uses |\n|---|---:|---:|---:|---:|---:|---:|---:|\n");
    for summary in &census.summaries {
        let metric = |name| {
            summary
                .weighted_metrics
                .iter()
                .find(|metric| metric.metric == name)
                .map(|metric| metric.exact_decimal.as_str())
                .unwrap_or("0")
        };
        report.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} |\n",
            summary.profile,
            summary.covered_coordinates,
            summary.missing_coordinates.len(),
            metric("terms"),
            metric("product_members"),
            metric("groups"),
            metric("group_members"),
            metric("source_uses")
        ));
    }
    report.push_str("\nModeled reduction totals below sum every explicitly modeled alternative. Typed-infeasible states are counted separately and contribute no fabricated segment or reduction count.\n\n| Profile | Outer boundary reductions | Outer intermediate reductions | Outer infeasible states | Inner boundary reductions | Inner intermediate reductions | Inner infeasible states |\n|---|---:|---:|---:|---:|---:|---:|\n");
    for summary in &census.summaries {
        let metric = |name| {
            summary
                .weighted_metrics
                .iter()
                .find(|metric| metric.metric == name)
                .map(|metric| metric.exact_decimal.as_str())
                .unwrap_or("0")
        };
        report.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} |\n",
            summary.profile,
            metric("modeled_outer_boundary_reductions"),
            metric("modeled_outer_intermediate_reductions"),
            metric("modeled_outer_infeasible_states"),
            metric("modeled_inner_boundary_reductions"),
            metric("modeled_inner_intermediate_reductions"),
            metric("modeled_inner_infeasible_states")
        ));
    }
    let total = |value: fn(&AccumulatorCoordinateRow) -> u64| {
        census.coordinates.iter().map(value).sum::<u64>()
    };
    report.push_str("\n## BF/E4 split and grouping\n\n");
    report.push_str("| Metric | Corpus total |\n|---|---:|\n");
    for (label, value) in [
        (
            "Canonical BF atoms",
            total(|row| row.canonical_split.bf_atoms),
        ),
        (
            "Canonical E4 atoms",
            total(|row| row.canonical_split.e4_atoms),
        ),
        (
            "Records moved by stable split",
            total(|row| row.canonical_split.moved_records),
        ),
        (
            "Canonical BF/E4 transitions",
            total(|row| row.canonical_split.canonical_transitions),
        ),
        (
            "Stable-split transitions",
            total(|row| row.canonical_split.split_transitions),
        ),
        ("Analysis groups", total(|row| row.analysis_grouping.groups)),
        (
            "Analysis group members",
            total(|row| row.analysis_grouping.members),
        ),
        (
            "BF-only groups",
            total(|row| row.analysis_grouping.bf_only_groups),
        ),
        (
            "E4-only groups",
            total(|row| row.analysis_grouping.e4_only_groups),
        ),
        (
            "Mixed groups",
            total(|row| row.analysis_grouping.mixed_groups),
        ),
    ] {
        report.push_str(&format!("| {label} | {value} |\n"));
    }
    report.push_str("\n## Accumulator capacity\n\n| Regime | Coordinates | Canonical BF atoms | Analysis-grouped BF atoms | Inner group rows |\n|---|---:|---:|---:|---:|\n");
    for regime in [BackwardRegime::R0, BackwardRegime::Ext] {
        let rows = census
            .coordinates
            .iter()
            .filter(|row| row.id.regime == regime)
            .collect::<Vec<_>>();
        report.push_str(&format!(
            "| {regime:?} | {} | {} | {} | {} |\n",
            rows.len(),
            rows.iter()
                .map(|row| row.outer_bounds.canonical_bf_atoms)
                .sum::<u64>(),
            rows.iter()
                .map(|row| row.outer_bounds.analysis_bf_atoms)
                .sum::<u64>(),
            rows.iter()
                .map(|row| row.inner_bounds.len() as u64)
                .sum::<u64>()
        ));
    }
    let mut outer_capacity = BTreeMap::<(String, String), [u128; 8]>::new();
    for row in &census.coordinates {
        for (schedule, bounds) in [
            ("canonical", &row.outer_bounds.canonical),
            ("analysis_grouped", &row.outer_bounds.analysis_grouped),
        ] {
            for bound in bounds {
                let values = outer_capacity
                    .entry((schedule.into(), format!("{:?}", bound.reduction_path)))
                    .or_default();
                values[0] += 1;
                values[1] += u128::from(bound.required_contributions);
                values[6] = values[6].max(u128::from(bound.required_bits));
                values[7] = values[7].max(bound.contribution_max);
                match &bound.disposition {
                    crate::accumulator_bounds::CapacityDisposition::Feasible(details) => {
                        values[2] += u128::from(details.segment_count);
                        values[3] += u128::from(details.intermediate_reductions);
                        values[4] += u128::from(details.boundary_reductions);
                    }
                    crate::accumulator_bounds::CapacityDisposition::Infeasible { .. } => {
                        values[5] += 1;
                    }
                }
            }
        }
    }
    report.push_str("\n### Outer BF folds\n\n| Schedule | Named reducer | Rows | Contributions | Segments | Intermediate reductions | Boundary reductions | Infeasible rows | Maximum required bits | Maximum contribution |\n|---|---|---:|---:|---:|---:|---:|---:|---:|---:|\n");
    for ((schedule, reducer), values) in outer_capacity {
        report.push_str(&format!(
            "| {schedule} | {reducer} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            values[0], values[1], values[2], values[3], values[4], values[5], values[6], values[7]
        ));
    }
    let mut inner_capacity = BTreeMap::<(String, String, String, String), [u128; 9]>::new();
    for row in &census.coordinates {
        for group in &row.inner_bounds {
            for policy in &group.policies {
                let values = inner_capacity
                    .entry((
                        format!("{:?}", policy.convention),
                        format!("{:?}", policy.product_mode),
                        format!("{:?}", policy.reduction_path),
                        format!("{:?}", policy.e4_product_path),
                    ))
                    .or_default();
                values[0] += 1;
                values[7] = values[7].max(u128::from(policy.required_bits));
                values[8] = values[8].max(policy.contribution_max);
                let mut add_state = |bound: &CapacityBound| {
                    values[1] += 1;
                    match &bound.disposition {
                        crate::accumulator_bounds::CapacityDisposition::Feasible(details) => {
                            values[2] += 1;
                            values[4] += u128::from(details.segment_count);
                            values[5] += u128::from(details.intermediate_reductions);
                            values[6] += u128::from(details.boundary_reductions);
                        }
                        crate::accumulator_bounds::CapacityDisposition::Infeasible { .. } => {
                            values[3] += 1;
                        }
                    }
                };
                match &policy.states {
                    crate::accumulator_bounds::InnerStateBounds::Canonical { state } => {
                        add_state(state);
                    }
                    crate::accumulator_bounds::InnerStateBounds::SignSplit {
                        positive,
                        negative,
                    } => {
                        add_state(positive);
                        add_state(negative);
                    }
                }
            }
        }
    }
    report.push_str("\n### Inner coefficient-sharing folds\n\n| Convention | Product/immediate mode | Named reducer | E4 product path | Policy rows | States | Feasible states | Infeasible states | Segments | Intermediate reductions | Boundary reductions | Maximum required bits | Maximum contribution |\n|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n");
    for ((convention, mode, reducer, e4_path), values) in inner_capacity {
        report.push_str(&format!(
            "| {convention} | {mode} | {reducer} | {e4_path} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            values[0], values[1], values[2], values[3], values[4], values[5], values[6], values[7], values[8]
        ));
    }
    report.push_str("\nEvery outer and inner JSON row retains the exact integer contribution/state bounds, raw-width and reducer-safe maxima, required bits, segment details, or typed infeasible magnitudes. The fused E4 path is the flat quartic schoolbook form with unreduced non-residue factors; coefficient sums `[34, 14, 24, 4]` make 34 the exact worst output-limb factor.\n");
    report.push_str("\n## Specialization opportunities\n\n| Metric | Corpus total |\n|---|---:|\n");
    for (label, value) in [
        (
            "Literal +1 cores",
            total(|row| row.specializations.literal_one_cores),
        ),
        (
            "Literal -1 cores",
            total(|row| row.specializations.literal_neg_one_cores),
        ),
        (
            "One-nonzero-limb cores",
            total(|row| row.specializations.one_nonzero_limb_cores),
        ),
        (
            "Group immediate +1",
            total(|row| row.specializations.group_immediate_one),
        ),
        (
            "Group immediate -1",
            total(|row| row.specializations.group_immediate_neg_one),
        ),
        (
            "Group immediate banked",
            total(|row| row.specializations.group_immediate_banked),
        ),
        (
            "Self products",
            total(|row| row.specializations.self_products),
        ),
        (
            "Same-window products",
            total(|row| row.specializations.same_window_products),
        ),
        (
            "Linear members",
            total(|row| row.specializations.linear_members),
        ),
        (
            "Product members",
            total(|row| row.specializations.product_members),
        ),
        (
            "Procedural operand uses",
            total(|row| row.specializations.procedural_operand_uses),
        ),
        (
            "Stored operand uses",
            total(|row| row.specializations.stored_operand_uses),
        ),
    ] {
        report.push_str(&format!("| {label} | {value} |\n"));
    }
    report.push_str("\n### Weighted specialization profiles\n\n| Profile | Literal +1 | Literal -1 | One-limb cores | Immediate +1 | Immediate -1 | Banked immediate | Self products | Same-window products | Linear members | Product members | Procedural uses | Stored uses |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n");
    for summary in &census.summaries {
        let metric = |name| {
            summary
                .weighted_metrics
                .iter()
                .find(|metric| metric.metric == name)
                .map(|metric| metric.exact_decimal.as_str())
                .unwrap_or("0")
        };
        report.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            summary.profile,
            metric("literal_one_cores"),
            metric("literal_neg_one_cores"),
            metric("one_nonzero_limb_cores"),
            metric("group_immediate_one"),
            metric("group_immediate_neg_one"),
            metric("group_immediate_banked"),
            metric("self_products"),
            metric("same_window_products"),
            metric("linear_members"),
            metric("product_members"),
            metric("procedural_operand_uses"),
            metric("stored_operand_uses")
        ));
    }
    report.push_str("\n## Schedule locality\n\n| Schedule | Source uses | Unique sources | Adjacent repeated operands | Adjacent repeated pairs | Window transitions |\n|---|---:|---:|---:|---:|---:|\n");
    let locality_rows: [(&str, fn(&AccumulatorCoordinateRow) -> &LocalityMetrics); 7] = [
        ("canonical", |row| &row.locality.canonical),
        ("stable_split_whole", |row| &row.locality.stable_split_whole),
        ("stable_split_bf", |row| &row.locality.stable_split_bf),
        ("stable_split_e4", |row| &row.locality.stable_split_e4),
        ("analysis_grouped_whole", |row| {
            &row.locality.analysis_grouped_whole
        }),
        ("analysis_grouped_bf", |row| {
            &row.locality.analysis_grouped_bf
        }),
        ("analysis_grouped_e4", |row| {
            &row.locality.analysis_grouped_e4
        }),
    ];
    for &(label, select) in &locality_rows {
        let values = census.coordinates.iter().map(select).collect::<Vec<_>>();
        report.push_str(&format!(
            "| {label} | {} | {} | {} | {} | {} |\n",
            values.iter().map(|row| row.source_uses).sum::<u64>(),
            values.iter().map(|row| row.unique_sources).sum::<u64>(),
            values
                .iter()
                .map(|row| row.adjacent_repeated_operands)
                .sum::<u64>(),
            values
                .iter()
                .map(|row| row.adjacent_repeated_pairs)
                .sum::<u64>(),
            values
                .iter()
                .map(|row| row.source_window_transitions)
                .sum::<u64>()
        ));
    }
    report.push_str("\n## Top-N source coverage\n\n| Schedule | N | Covered uses | Total uses |\n|---|---:|---:|---:|\n");
    for &(label, select) in &locality_rows {
        for index in 0..6 {
            let coverages = census
                .coordinates
                .iter()
                .map(select)
                .map(|metrics| &metrics.top_n_coverage[index])
                .collect::<Vec<_>>();
            let n = coverages[0].n;
            assert!(coverages.iter().all(|coverage| coverage.n == n));
            report.push_str(&format!(
                "| {label} | {n} | {} | {} |\n",
                coverages
                    .iter()
                    .map(|coverage| coverage.covered_uses)
                    .sum::<u64>(),
                coverages
                    .iter()
                    .map(|coverage| coverage.total_uses)
                    .sum::<u64>()
            ));
        }
    }
    report.push_str("\n## Atom-gap and LRU-stack-distance histograms\n\n| Schedule | Bucket | Atom-gap samples | LRU-stack-distance samples |\n|---|---|---:|---:|\n");
    for &(label, select) in &locality_rows {
        for index in 0..9 {
            let values = census.coordinates.iter().map(select).collect::<Vec<_>>();
            let atom = &values[0].atom_gap_histogram[index];
            let lru = &values[0].lru_stack_distance_histogram[index];
            assert_eq!(atom.label, lru.label);
            assert!(values.iter().all(|metrics| {
                metrics.atom_gap_histogram[index].label == atom.label
                    && metrics.lru_stack_distance_histogram[index].label == atom.label
            }));
            report.push_str(&format!(
                "| {label} | {} | {} | {} |\n",
                atom.label,
                values
                    .iter()
                    .map(|metrics| metrics.atom_gap_histogram[index].count)
                    .sum::<u64>(),
                values
                    .iter()
                    .map(|metrics| metrics.lru_stack_distance_histogram[index].count)
                    .sum::<u64>()
            ));
        }
    }
    report.push_str("\nThe JSON additionally retains projection-aware use-count histograms and per-window use/unique-source locality for every schedule row.\n");
    let mut encoding_counts = BTreeMap::<String, (u64, u64, u64, u64)>::new();
    for row in &census.coordinates {
        for encoding in &row.encodings {
            let key = format!("{:?}/{:?}", encoding.layout, encoding.source_mode);
            let entry = encoding_counts.entry(key).or_default();
            entry.0 += 1;
            entry.1 += encoding.by_value_bytes;
            entry.2 += encoding.module_constant_bytes;
            entry.3 += encoding
                .capacity_facts
                .iter()
                .filter(|fact| !fact.fits)
                .count() as u64;
        }
    }
    report.push_str("\n## Analytical program layouts\n\n| Layout/source mode | Rows | By-value bytes | Module-constant bytes | Non-fitting facts |\n|---|---:|---:|---:|---:|\n");
    for (key, (rows, by_value, constants, non_fitting)) in encoding_counts {
        report.push_str(&format!(
            "| {key} | {rows} | {by_value} | {constants} | {non_fitting} |\n"
        ));
    }
    let non_fitting = census
        .coordinates
        .iter()
        .flat_map(|row| {
            row.encodings.iter().flat_map(move |encoding| {
                encoding
                    .capacity_facts
                    .iter()
                    .filter(|fact| !fact.fits)
                    .map(move |fact| (row, encoding, fact))
            })
        })
        .collect::<Vec<_>>();
    report.push_str("\n### Typed non-fitting wire/layout facts\n\n");
    if non_fitting.is_empty() {
        report.push_str("No analytical by-value, module-constant, wire-u16, or production/reference capacity fact is non-fitting in this corpus. Typed inner-policy infeasibility remains reported separately in the accumulator table.\n");
    } else {
        report.push_str("| Coordinate | Regime | Layout/source | Namespace | Kind | Required | Maximum |\n|---|---|---|---|---|---:|---:|\n");
        for (row, encoding, fact) in non_fitting {
            report.push_str(&format!(
                "| {}:{} | {:?} | {:?}/{:?} | {:?} | {} | {} | {} |\n",
                row.id.circuit,
                row.id.layer,
                row.id.regime,
                encoding.layout,
                encoding.source_mode,
                fact.namespace,
                fact.kind,
                fact.required,
                fact.maximum
            ));
        }
    }
    report.push_str("\n## Legacy continuation diagnostics\n\n");
    report.push_str(&format!("Groups: {} total, {} BF-only, {} E4-only, {} mixed. All E4 groups have size two: {}. Grouped-term coverage: {}/{} = {}.{:02}%. Production grouping equality: {}/57.\n\n", census.diagnostics.legacy_ext_groups, census.diagnostics.legacy_ext_bf_groups, census.diagnostics.legacy_ext_e4_groups, census.diagnostics.legacy_ext_mixed_groups, census.diagnostics.legacy_ext_e4_all_size_two, census.diagnostics.legacy_grouped_terms, census.diagnostics.legacy_total_terms, census.diagnostics.legacy_grouped_coverage_basis_points / 100, census.diagnostics.legacy_grouped_coverage_basis_points % 100, census.diagnostics.ext_production_grouping_equal));
    report.push_str("## Per-coordinate appendix\n\n| Coordinate | Regime | Terms | Production atoms | Analysis atoms | BF/E4 atoms | Groups | Source uses | Encoding rows | Non-fitting facts |\n|---|---|---:|---:|---:|---:|---:|---:|---:|---:|\n");
    for row in &census.coordinates {
        let non_fitting = row
            .encodings
            .iter()
            .flat_map(|budget| &budget.capacity_facts)
            .filter(|fact| !fact.fits)
            .count();
        report.push_str(&format!(
            "| {}:{} | {:?} | {} | {} | {} | {}/{} | {} | {} | {} | {} |\n",
            row.id.circuit,
            row.id.layer,
            row.id.regime,
            row.population.terms,
            row.population.production_atoms,
            row.population.analysis_atoms,
            row.canonical_split.bf_atoms,
            row.canonical_split.e4_atoms,
            row.analysis_grouping.groups,
            row.locality.canonical.source_uses,
            row.encodings.len(),
            non_fitting
        ));
    }
    report.push_str("\nThe census is descriptive and makes no faster, slower, winner, selected, or rejected classifications.\n");
    Ok(report)
}

pub(crate) fn validate_accumulator_census_semantics(
    corpus: &crate::census::CompiledCorpus,
) -> Result<SemanticValidationSummary, AccumulatorCensusError> {
    use gpu_gkr_compiler::backward::materialize_coeff_grouping_for_semantics;

    use crate::accumulator_schedule::materialize_term_order;
    use crate::host_eval::evaluate_continuation_coeff_schedule;
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
    use crate::r0_input::build_r0_input_with_layer;
    use crate::r0_reference::{
        evaluate_canonical_r0_convention, evaluate_compiled_r0_tensor, evaluate_r0_coeff_schedule,
    };

    fn split_layer(
        coefficients: &CoeffLayer,
        views: &ScheduleViews,
    ) -> Result<CoeffLayer, AccumulatorCensusError> {
        let atoms = views
            .canonical_split
            .bf
            .iter()
            .chain(&views.canonical_split.e4)
            .cloned()
            .collect::<Vec<_>>();
        materialize_term_order(coefficients, &atoms).map_err(AccumulatorCensusError::Schedule)
    }

    fn require_equal(
        coordinate: &CoordinateId,
        label: &str,
        expected: &[crate::abi::E4; 27],
        observed: &[crate::abi::E4; 27],
    ) -> Result<(), AccumulatorCensusError> {
        if let Some(cell) = expected
            .iter()
            .zip(observed)
            .position(|(expected, observed)| expected != observed)
        {
            return Err(AccumulatorCensusError::Invariant {
                coordinate: coordinate.clone(),
                detail: format!("{label} diverged at cell {cell}"),
            });
        }
        Ok(())
    }

    let bundle = decode_r0_bundle(R0_CORPUS_BYTES)
        .map_err(|error| AccumulatorCensusError::Corpus(format!("decode R0 bundle: {error}")))?;
    let coordinates = bundle
        .coordinates
        .into_iter()
        .map(|coordinate| ((coordinate.circuit.clone(), coordinate.layer), coordinate))
        .collect::<BTreeMap<_, _>>();
    let mut summary = SemanticValidationSummary {
        r0_cases: 0,
        ext_cases: 0,
        r0_cell_comparisons: 0,
        ext_cell_comparisons: 0,
        ext_production_grouping_equal: 0,
    };

    for layer in &corpus.layers {
        let coordinate = coordinates
            .get(&(layer.circuit.clone(), layer.layer as u32))
            .ok_or_else(|| {
                AccumulatorCensusError::Corpus(format!(
                    "R0 coordinate missing for {}:{}",
                    layer.circuit, layer.layer
                ))
            })?;
        let r0_analysis = analyze_coeff_grouping(&layer.r0.coefficients)
            .map_err(|error| AccumulatorCensusError::Grouping(format!("{error:?}")))?;
        let r0_views =
            build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &r0_analysis)
                .map_err(AccumulatorCensusError::Schedule)?;
        let r0_split = split_layer(&layer.r0.coefficients, &r0_views)?;
        let r0_grouped =
            materialize_coeff_grouping_for_semantics(&layer.r0.coefficients, &r0_analysis)
                .map_err(|error| AccumulatorCensusError::Grouping(format!("{error:?}")))?;

        let ext_analysis = analyze_coeff_grouping(&layer.ext.coefficients)
            .map_err(|error| AccumulatorCensusError::Grouping(format!("{error:?}")))?;
        let ext_views =
            build_schedule_views(&layer.ext.coefficients, &layer.ext.binding, &ext_analysis)
                .map_err(AccumulatorCensusError::Schedule)?;
        let ext_split = split_layer(&layer.ext.coefficients, &ext_views)?;
        let ext_grouped =
            materialize_coeff_grouping_for_semantics(&layer.ext.coefficients, &ext_analysis)
                .map_err(|error| AccumulatorCensusError::Grouping(format!("{error:?}")))?;
        if ext_grouped != layer.ext.coefficients {
            return Err(AccumulatorCensusError::Invariant {
                coordinate: CoordinateId {
                    circuit: layer.circuit.clone(),
                    layer: layer.layer as u32,
                    regime: BackwardRegime::Ext,
                },
                detail: "analysis grouping does not reproduce production grouping".into(),
            });
        }
        summary.ext_production_grouping_equal += 1;

        for log_trace in [3, 8] {
            for seed in [0, 1, 0x5eed] {
                let r0_id = CoordinateId {
                    circuit: layer.circuit.clone(),
                    layer: layer.layer as u32,
                    regime: BackwardRegime::R0,
                };
                let input =
                    build_r0_input_with_layer(coordinate, &layer.canonical, log_trace, seed)
                        .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                let canonical =
                    evaluate_canonical_r0_convention(&layer.canonical, &layer.r0.binding, &input)
                        .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                let encoded = evaluate_compiled_r0_tensor(&layer.r0, &input)
                    .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                require_equal(&r0_id, "encoded R0", &canonical, &encoded)?;
                for (label, coefficients) in [
                    ("canonical coefficient schedule", &layer.r0.coefficients),
                    ("stable BF/E4 split", &r0_split),
                    ("analysis grouping", &r0_grouped),
                ] {
                    let observed =
                        evaluate_r0_coeff_schedule(coefficients, &layer.r0.binding, &input)
                            .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                    require_equal(&r0_id, label, &canonical, &observed)?;
                }
                summary.r0_cases += 1;
                summary.r0_cell_comparisons += 27;

                let ext_id = CoordinateId {
                    circuit: layer.circuit.clone(),
                    layer: layer.layer as u32,
                    regime: BackwardRegime::Ext,
                };
                let production = evaluate_continuation_coeff_schedule(
                    &layer.ext.coefficients,
                    &layer.ext.binding,
                    log_trace,
                    seed,
                )
                .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                let split = evaluate_continuation_coeff_schedule(
                    &ext_split,
                    &layer.ext.binding,
                    log_trace,
                    seed,
                )
                .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                let grouped = evaluate_continuation_coeff_schedule(
                    &ext_grouped,
                    &layer.ext.binding,
                    log_trace,
                    seed,
                )
                .map_err(|error| AccumulatorCensusError::Corpus(error.to_string()))?;
                require_equal(&ext_id, "stable BF/E4 split", &production, &split)?;
                require_equal(&ext_id, "analysis grouping", &production, &grouped)?;
                summary.ext_cases += 1;
                summary.ext_cell_comparisons += 27;
            }
        }
    }
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::census::{default_workload_weights, BackwardRegime};

    use super::*;

    #[test]
    fn census_has_exactly_two_regimes_for_all_57_layers() {
        let census = generate_accumulator_census(default_workload_weights()).unwrap();
        assert_eq!(census.coordinates.len(), 114);
        let mut regimes = BTreeMap::<_, BTreeSet<_>>::new();
        for row in &census.coordinates {
            regimes
                .entry((row.id.circuit.clone(), row.id.layer))
                .or_default()
                .insert(row.id.regime);
        }
        assert_eq!(regimes.len(), 57);
        assert!(regimes.values().all(|regimes| {
            regimes == &BTreeSet::from([BackwardRegime::R0, BackwardRegime::Ext])
        }));
    }

    #[test]
    fn every_population_cross_tab_sums_to_terms() {
        let census = generate_accumulator_census(default_workload_weights()).unwrap();
        for row in &census.coordinates {
            assert_eq!(
                row.population
                    .taxonomy
                    .iter()
                    .map(|cell| cell.count)
                    .sum::<u64>(),
                row.population.terms,
                "{:?}",
                row.id
            );
        }
    }

    #[test]
    fn capacity_failures_keep_the_full_coordinate_row() {
        let census = generate_accumulator_census(default_workload_weights()).unwrap();
        assert!(census
            .coordinates
            .iter()
            .all(|row| row.encodings.len() == 7));
        let mut synthetic = census.coordinates[0].clone();
        let fact = &mut synthetic.encodings[0].capacity_facts[0];
        fact.required = fact.maximum + 1;
        fact.fits = false;
        let bytes = serde_json::to_vec(&synthetic).unwrap();
        let retained: AccumulatorCoordinateRow = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(retained.population.terms, synthetic.population.terms);
        assert!(retained.encodings[0]
            .capacity_facts
            .iter()
            .any(|fact| !fact.fits));
    }

    #[test]
    fn missing_current_base_families_remain_explicitly_missing() {
        let census = generate_accumulator_census(default_workload_weights()).unwrap();
        for circuit in [
            "blake2_g_function",
            "blake2_with_extended_control",
            "unified_reduced_machine",
        ] {
            assert!(census
                .coordinates
                .iter()
                .filter(|row| row.id.circuit == circuit)
                .all(|row| row.weights.iter().any(|weight| {
                    weight.profile == "current_base"
                        && weight.weight.is_none()
                        && weight.missing_reason.is_some()
                })));
        }
    }

    #[test]
    fn weighted_summaries_include_group_work_reductions_and_specializations() {
        let census = generate_accumulator_census(default_workload_weights()).unwrap();
        let unweighted = census
            .summaries
            .iter()
            .find(|summary| summary.profile == "unweighted")
            .unwrap();
        let metrics = unweighted
            .weighted_metrics
            .iter()
            .map(|metric| (metric.metric.as_str(), metric.exact_decimal.as_str()))
            .collect::<BTreeMap<_, _>>();
        for required in [
            "group_members",
            "modeled_outer_boundary_reductions",
            "modeled_inner_boundary_reductions",
            "modeled_inner_infeasible_states",
            "literal_one_cores",
            "group_immediate_banked",
            "self_products",
            "procedural_operand_uses",
        ] {
            assert!(metrics.contains_key(required), "missing {required}");
        }
        assert_eq!(
            metrics["group_members"],
            census
                .coordinates
                .iter()
                .map(|row| row.analysis_grouping.members)
                .sum::<u64>()
                .to_string()
        );
    }

    #[test]
    fn report_is_descriptive_and_contains_no_selection_fields() {
        let census = generate_accumulator_census(default_workload_weights()).unwrap();
        let report = render_accumulator_report(&census).unwrap();
        for forbidden in ["winner:", "selected:", "rejected:", "faster:", "slower:"] {
            assert!(!report.contains(forbidden));
        }
        assert!(report.contains("114 coordinate rows"));
        assert!(census
            .input_sha256
            .iter()
            .all(|input| report.contains(&input.path) && report.contains(&input.sha256)));
        assert!(report.contains("| canonical | U64RedWide |"));
        assert!(report.contains("| SignSplitLazy | FusedThreeFactor | U96RedWideHighWord |"));
        assert!(report.contains("Group immediate +1"));
        assert!(report.contains("## Top-N source coverage"));
        assert!(report.contains("## Atom-gap and LRU-stack-distance histograms"));
        assert!(report.contains("no faster, slower, winner, selected, or rejected classifications"));
    }

    #[test]
    fn legacy_grouped_coverage_preserves_the_exact_rational_and_rounds_for_display() {
        assert_eq!(rounded_basis_points(5_499, 8_015).unwrap(), 6_861);
    }

    #[test]
    fn focused_r0_schedule_variants_match_canonical_and_encoded_oracles() {
        use gpu_gkr_compiler::backward::{
            analyze_coeff_grouping, materialize_coeff_grouping_for_semantics,
        };

        use crate::accumulator_schedule::{build_schedule_views, materialize_term_order};
        use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
        use crate::r0_input::build_r0_input_with_layer;
        use crate::r0_reference::{
            evaluate_canonical_r0_convention, evaluate_compiled_r0_tensor,
            evaluate_r0_coeff_schedule,
        };

        let layer = compile_corpus()
            .unwrap()
            .layers
            .into_iter()
            .find(|layer| layer.circuit == "add_sub_lui_auipc_mop" && layer.layer == 0)
            .unwrap();
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| coordinate.circuit == layer.circuit && coordinate.layer == 0)
            .unwrap();
        let input = build_r0_input_with_layer(&coordinate, &layer.canonical, 3, 0).unwrap();
        let analysis = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
        let views =
            build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &analysis).unwrap();
        let split_atoms = views
            .canonical_split
            .bf
            .iter()
            .chain(&views.canonical_split.e4)
            .cloned()
            .collect::<Vec<_>>();
        let split = materialize_term_order(&layer.r0.coefficients, &split_atoms).unwrap();
        let grouped =
            materialize_coeff_grouping_for_semantics(&layer.r0.coefficients, &analysis).unwrap();

        let canonical =
            evaluate_canonical_r0_convention(&layer.canonical, &layer.r0.binding, &input).unwrap();
        assert_eq!(
            evaluate_compiled_r0_tensor(&layer.r0, &input).unwrap(),
            canonical
        );
        assert_eq!(
            evaluate_r0_coeff_schedule(&layer.r0.coefficients, &layer.r0.binding, &input).unwrap(),
            canonical
        );
        assert_eq!(
            evaluate_r0_coeff_schedule(&split, &layer.r0.binding, &input).unwrap(),
            canonical
        );
        assert_eq!(
            evaluate_r0_coeff_schedule(&grouped, &layer.r0.binding, &input).unwrap(),
            canonical
        );
    }

    #[test]
    fn focused_continuation_split_and_grouped_schedules_match_production() {
        use gpu_gkr_compiler::backward::{
            analyze_coeff_grouping, materialize_coeff_grouping_for_semantics,
        };

        use crate::accumulator_schedule::{build_schedule_views, materialize_term_order};
        use crate::host_eval::evaluate_continuation_coeff_schedule;

        let layer = compile_corpus()
            .unwrap()
            .layers
            .into_iter()
            .find(|layer| layer.circuit == "add_sub_lui_auipc_mop" && layer.layer == 0)
            .unwrap();
        let analysis = analyze_coeff_grouping(&layer.ext.coefficients).unwrap();
        let views =
            build_schedule_views(&layer.ext.coefficients, &layer.ext.binding, &analysis).unwrap();
        let split_atoms = views
            .canonical_split
            .bf
            .iter()
            .chain(&views.canonical_split.e4)
            .cloned()
            .collect::<Vec<_>>();
        let split = materialize_term_order(&layer.ext.coefficients, &split_atoms).unwrap();
        let grouped =
            materialize_coeff_grouping_for_semantics(&layer.ext.coefficients, &analysis).unwrap();
        let production =
            evaluate_continuation_coeff_schedule(&layer.ext.coefficients, &layer.ext.binding, 3, 0)
                .unwrap();
        assert_eq!(
            evaluate_continuation_coeff_schedule(&split, &layer.ext.binding, 3, 0).unwrap(),
            production
        );
        assert_eq!(
            evaluate_continuation_coeff_schedule(&grouped, &layer.ext.binding, 3, 0).unwrap(),
            production
        );
    }

    #[test]
    fn full_accumulator_census_semantic_matrix() {
        let corpus = compile_corpus().unwrap();
        let summary = validate_accumulator_census_semantics(&corpus).unwrap();
        assert_eq!(summary.r0_cases, 342);
        assert_eq!(summary.ext_cases, 342);
        assert_eq!(summary.r0_cell_comparisons, 342 * 27);
        assert_eq!(summary.ext_cell_comparisons, 342 * 27);
        assert_eq!(summary.ext_production_grouping_equal, 57);
    }
}
