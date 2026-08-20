#[cfg(test)]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, Command, Stdio};

use bincode::Options;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_ir::eval::{
    ChallengeResolver, LookupResolver, ReadResolver, Resolvers, VirtualSetupResolver,
};
use gkr_eval_ir::{
    ChallengeKey, ChallengePower, ChallengeRef, DagCircuit, DagLayer, Expr, ExprId, FieldKind,
    LookupValueKind, PermutationSlot, ReadPlace, SinkKind, SourceKind, VirtualSetupKind,
};
use gpu_gkr_compiler::backward::{
    CoeffChallenge, LeanSourceBinding, NormalizedCoefficientRecipe, WindowFamily,
};
use serde::{Deserialize, Serialize};

use crate::abi::{WindowEqSizes, BF, E4};
use crate::geometry::build_lean_allocation_plan;
use crate::r0_artifact::{FrozenR0Challenge, FrozenR0Coordinate, FrozenR0Recipe};
use crate::r0_reference::{eval_backward_claim_expr, R0ReferenceError};

pub const R0_INPUT_VERSION: u32 = 1;
pub const R0_SOURCE_GENERATOR_VERSION: u32 = 1;
pub const R0_PRODUCTION_SEED: u64 = 0xdead_beef_cafe_babe;
const R0_HASH_BUFFER_BYTES: usize = 1 << 20;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenE4 {
    pub limbs: [u32; 4],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenChallengeValue {
    pub challenge: FrozenR0Challenge,
    pub value: FrozenE4,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenChallengeBase {
    pub key: ChallengeKey,
    pub value: FrozenE4,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenEqSizes {
    pub high: [u32; 2],
    pub low: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FrozenField {
    Bf,
    E4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0HostBacking {
    Bf(Vec<BF>),
    E4(Vec<E4>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0HostWindow {
    pub field: FrozenField,
    pub backing_index: Option<usize>,
    pub first_element: usize,
    pub procedural_kind: Option<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0HostSources {
    pub trace_len: usize,
    pub windows: Vec<R0HostWindow>,
    pub backings: Vec<R0HostBacking>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0FactoredEqTables {
    pub high: [Vec<E4>; 2],
    pub low: Vec<E4>,
    pub sizes: WindowEqSizes,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0InputIdentityV1 {
    pub version: u32,
    pub source_generator_version: u32,
    pub circuit: String,
    pub layer: u32,
    pub log_trace: u32,
    pub seed: u64,
    pub challenge_bases: Vec<FrozenChallengeBase>,
    pub challenge_values: Vec<FrozenChallengeValue>,
    pub equality_point: Vec<FrozenE4>,
    pub coefficient_bank: Vec<FrozenE4>,
    pub eq_sizes: FrozenEqSizes,
    pub source_data_sha256: String,
    pub independent_source_sha256: String,
    pub derived_source_sha256: Option<String>,
    pub coefficient_sha256: String,
    pub direct_eq_sha256: String,
    pub factored_eq_sha256: String,
    pub input_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DerivedSpan {
    backing_index: usize,
    first_element: usize,
    element_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CanonicalSource {
    place: ReadPlace,
    backing: R0HostBacking,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedR0Input {
    pub identity: R0InputIdentityV1,
    pub sources: R0HostSources,
    pub coefficient_bank: Vec<E4>,
    pub eq_tables: R0FactoredEqTables,
    derived_spans: Vec<DerivedSpan>,
    canonical_only_sources: Vec<CanonicalSource>,
}

/// An owned production input whose byte-derived identity was established by
/// the deterministic production builder. The inner input is deliberately
/// available only by shared reference; only this module can construct or
/// unwrap the token.
pub struct PreparedR0ProductionInput {
    coordinate: FrozenR0Coordinate,
    input: ResolvedR0Input,
}

impl PreparedR0ProductionInput {
    pub fn resolved(&self) -> &ResolvedR0Input {
        &self.input
    }

    pub(crate) fn into_parts(self) -> (FrozenR0Coordinate, ResolvedR0Input) {
        (self.coordinate, self.input)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0InputError {
    InvalidLogTrace(u32),
    ReadLayout(String),
    ParseLayout(String),
    LowerLayout(String),
    MissingLayer(u32),
    CoordinateMismatch(String),
    MissingChallengeBase(String),
    NoncanonicalChallenge,
    AmbiguousChallengePower { key: String, power: u32 },
    ConstraintAggregationRecipe,
    Source(String),
    DerivedSourceOverlap(String),
    DerivedFieldMismatch(String),
    Reference(R0ReferenceError),
    Hash(String),
    Codec(String),
    IdentityMismatch(&'static str),
}

impl core::fmt::Display for R0InputError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0InputError {}

impl From<R0ReferenceError> for R0InputError {
    fn from(error: R0ReferenceError) -> Self {
        Self::Reference(error)
    }
}

impl FrozenE4 {
    pub fn from_e4(value: E4) -> Self {
        Self {
            limbs: [
                value.c0.c0.as_u32_reduced(),
                value.c0.c1.as_u32_reduced(),
                value.c1.c0.as_u32_reduced(),
                value.c1.c1.as_u32_reduced(),
            ],
        }
    }

    pub fn to_e4(&self) -> E4 {
        E4::from_array_of_base(self.limbs.map(BF::from_u32_with_reduction))
    }
}

impl From<WindowEqSizes> for FrozenEqSizes {
    fn from(value: WindowEqSizes) -> Self {
        Self {
            high: value.high,
            low: value.low,
        }
    }
}

impl R0HostSources {
    pub fn read_bound_source(
        &self,
        binding: &LeanSourceBinding,
        source: usize,
        row: usize,
    ) -> Result<E4, R0InputError> {
        let slot = binding
            .source_slots
            .get(source)
            .ok_or_else(|| R0InputError::Source(format!("source slot {source} is missing")))?;
        self.read_window(slot.window as usize, slot.column as usize, row)
    }

    pub fn read_place(
        &self,
        binding: &LeanSourceBinding,
        place: &ReadPlace,
        row: usize,
    ) -> Result<E4, R0InputError> {
        let mut found = None;
        for (window_index, window) in binding.windows.iter().enumerate() {
            let Some(column) = place_column_in_family(place, &window.family) else {
                continue;
            };
            if window
                .columns
                .binary_search_by_key(&column, |entry| entry.column)
                .is_err()
            {
                continue;
            }
            if found
                .replace((window_index, column - window.first_column))
                .is_some()
            {
                return Err(R0InputError::Source(format!(
                    "read place {place:?} has multiple bound coordinates"
                )));
            }
        }
        let (window, relative_column) = found.ok_or_else(|| {
            R0InputError::Source(format!("read place {place:?} is not in the R0 binding"))
        })?;
        self.read_window(window, relative_column, row)
    }

    pub fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> BF {
        BF::from_u32_with_reduction(procedural_raw(virtual_setup_tag(kind), row))
    }

    fn read_window(
        &self,
        window: usize,
        relative_column: usize,
        row: usize,
    ) -> Result<E4, R0InputError> {
        let window = self
            .windows
            .get(window)
            .ok_or_else(|| R0InputError::Source(format!("window {window} is missing")))?;
        if row >= self.trace_len {
            return Err(R0InputError::Source(format!(
                "row {row} is outside trace length {}",
                self.trace_len
            )));
        }
        if let Some(kind) = window.procedural_kind {
            return Ok(lift(BF::from_u32_with_reduction(procedural_raw(kind, row))));
        }
        let backing = window
            .backing_index
            .and_then(|index| self.backings.get(index))
            .ok_or_else(|| R0InputError::Source(format!("window {window:?} has no backing")))?;
        let element =
            window
                .first_element
                .checked_add(relative_column.checked_mul(self.trace_len).ok_or_else(|| {
                    R0InputError::Source("source column offset overflow".to_owned())
                })?)
                .and_then(|offset| offset.checked_add(row))
                .ok_or_else(|| R0InputError::Source("source element offset overflow".to_owned()))?;
        match backing {
            R0HostBacking::Bf(values) => values
                .get(element)
                .copied()
                .map(lift)
                .ok_or_else(|| R0InputError::Source("BF source element is missing".to_owned())),
            R0HostBacking::E4(values) => values
                .get(element)
                .copied()
                .ok_or_else(|| R0InputError::Source("E4 source element is missing".to_owned())),
        }
    }
}

impl ResolvedR0Input {
    /// Resolve a canonical-DAG read from the exact independent input bytes used
    /// to derive this input's materialized C0 sinks.  Reads present in the R0
    /// binding come from the GPU-visible backing; intentionally omitted C0-only
    /// reads come from the separately hash-bound canonical input class.
    pub fn read_canonical_place(
        &self,
        binding: &LeanSourceBinding,
        place: &ReadPlace,
        row: usize,
    ) -> Result<E4, R0InputError> {
        match self.sources.read_place(binding, place, row) {
            Ok(value) => Ok(value),
            Err(bound_error) => {
                let Some(source) = self
                    .canonical_only_sources
                    .iter()
                    .find(|source| &source.place == place)
                else {
                    return Err(bound_error);
                };
                if row >= self.sources.trace_len {
                    return Err(R0InputError::Source(format!(
                        "row {row} is outside trace length {}",
                        self.sources.trace_len
                    )));
                }
                Ok(match &source.backing {
                    R0HostBacking::Bf(values) => lift(values[row]),
                    R0HostBacking::E4(values) => values[row],
                })
            }
        }
    }

    pub fn resolve_canonical_challenge(
        &self,
        reference: &ChallengeRef,
    ) -> Result<E4, R0InputError> {
        ChallengeAssignment {
            bases: &self.identity.challenge_bases,
        }
        .resolve_canonical(reference)
    }
}

pub fn build_r0_input(
    coordinate: &FrozenR0Coordinate,
    log_trace: u32,
    seed: u64,
) -> Result<ResolvedR0Input, R0InputError> {
    let dag = load_canonical_dag(coordinate)?;
    let cross_fields = canonical_cross_layer_fields(&dag, coordinate.layer as usize);
    let layer = dag
        .layers
        .get(coordinate.layer as usize)
        .ok_or(R0InputError::MissingLayer(coordinate.layer))?;
    build_r0_input_with_metadata(coordinate, layer, &cross_fields, log_trace, seed)
}

/// Builds the production performance input without loading or evaluating the
/// canonical DAG. Every materialized backing element uses the deterministic
/// traffic generator, including columns that correctness mode derives from
/// canonical sink semantics.
pub fn build_r0_production_input(
    coordinate: &FrozenR0Coordinate,
    log_trace: u32,
    seed: u64,
) -> Result<ResolvedR0Input, R0InputError> {
    let prepared = build_prepared_r0_production_input(coordinate, log_trace, seed)?;
    let (_, input) = prepared.into_parts();
    validate_r0_input(&input)?;
    Ok(input)
}

/// Builds an opaque production input for immediate ownership transfer to the
/// production harness. Unlike the general checked constructor above, this
/// path does not re-hash bytes that this deterministic builder just hashed.
pub fn build_prepared_r0_production_input(
    coordinate: &FrozenR0Coordinate,
    log_trace: u32,
    seed: u64,
) -> Result<PreparedR0ProductionInput, R0InputError> {
    if !(3..=27).contains(&log_trace) {
        return Err(R0InputError::InvalidLogTrace(log_trace));
    }

    let challenge_bases = build_challenge_bases(seed);
    let challenge_values = production_challenge_values(&coordinate.recipes, &challenge_bases)?;

    let coefficient_bank = resolve_r0_coefficients(&coordinate.recipes, &challenge_bases)?;
    let coefficient_bank_frozen = coefficient_bank
        .iter()
        .copied()
        .map(FrozenE4::from_e4)
        .collect::<Vec<_>>();
    let coefficient_sha256 = hash_e4_values(coefficient_bank.iter().copied())?;

    let equality_point = (0..log_trace - 3)
        .map(|index| FrozenE4::from_e4(deterministic_e4(seed, 0x4551_504f_494e_5400, index as u64)))
        .collect::<Vec<_>>();
    let eq_tables = build_factored_eq_tables(&equality_point)?;
    check_equality_algorithms(&equality_point, &eq_tables)?;
    let direct_eq_sha256 = hash_direct_equality(&equality_point)?;
    let factored_eq_sha256 = hash_factored_equality(&eq_tables)?;

    // An empty derived-target set deliberately makes every byte traffic,
    // including columns classified as materialized sinks in correctness mode.
    let (sources, derived_spans) = build_host_sources(&coordinate.binding, log_trace, seed, &[])?;
    let canonical_only_sources = Vec::new();
    let source_hashes = hash_source_classes(&sources, &derived_spans, &canonical_only_sources)?;
    debug_assert!(derived_spans.is_empty());
    debug_assert!(source_hashes.derived.is_none());

    let mut identity = R0InputIdentityV1 {
        version: R0_INPUT_VERSION,
        source_generator_version: R0_SOURCE_GENERATOR_VERSION,
        circuit: coordinate.circuit.clone(),
        layer: coordinate.layer,
        log_trace,
        seed,
        challenge_bases,
        challenge_values,
        equality_point,
        coefficient_bank: coefficient_bank_frozen,
        eq_sizes: eq_tables.sizes.into(),
        source_data_sha256: source_hashes.all,
        independent_source_sha256: source_hashes.independent,
        derived_source_sha256: None,
        coefficient_sha256,
        direct_eq_sha256,
        factored_eq_sha256,
        input_sha256: String::new(),
    };
    identity.input_sha256 = r0_input_identity_sha256(&identity)?;
    Ok(PreparedR0ProductionInput {
        coordinate: coordinate.clone(),
        input: ResolvedR0Input {
            identity,
            sources,
            coefficient_bank,
            eq_tables,
            derived_spans,
            canonical_only_sources,
        },
    })
}

pub fn validate_r0_production_input(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
) -> Result<(), R0InputError> {
    validate_r0_input(input)?;
    if input.identity.circuit != coordinate.circuit || input.identity.layer != coordinate.layer {
        return Err(R0InputError::IdentityMismatch("production coordinate"));
    }
    if !coordinate.trace_len.is_power_of_two()
        || input.identity.log_trace != coordinate.trace_len.ilog2()
        || input.identity.seed != R0_PRODUCTION_SEED
    {
        return Err(R0InputError::IdentityMismatch("production log/seed"));
    }
    if !input.derived_spans.is_empty()
        || !input.canonical_only_sources.is_empty()
        || input.identity.derived_source_sha256.is_some()
        || input.identity.source_data_sha256 != input.identity.independent_source_sha256
    {
        return Err(R0InputError::IdentityMismatch(
            "production traffic-only source class",
        ));
    }

    let expected_challenges =
        production_challenge_values(&coordinate.recipes, &input.identity.challenge_bases)?;
    if input.identity.challenge_values != expected_challenges {
        return Err(R0InputError::IdentityMismatch(
            "production challenge values",
        ));
    }
    let expected_coefficients =
        resolve_r0_coefficients(&coordinate.recipes, &input.identity.challenge_bases)?;
    if input.coefficient_bank != expected_coefficients {
        return Err(R0InputError::IdentityMismatch(
            "production coefficient bank",
        ));
    }

    let plan = build_lean_allocation_plan(&coordinate.binding, input.identity.log_trace)
        .map_err(|error| R0InputError::Source(error.to_string()))?;
    if input.sources.trace_len != plan.trace_len
        || input.sources.windows.len() != plan.windows.len()
        || input.sources.backings.len() != plan.backings.len()
    {
        return Err(R0InputError::IdentityMismatch("production source plan"));
    }
    for (index, (window, planned)) in input.sources.windows.iter().zip(&plan.windows).enumerate() {
        let expected_field = match planned.field {
            FieldKind::Base => FrozenField::Bf,
            FieldKind::Ext => FrozenField::E4,
        };
        if window.field != expected_field
            || window.backing_index != planned.backing
            || window.first_element != planned.base_element
            || window.procedural_kind != planned.procedural_kind
        {
            return Err(R0InputError::Source(format!(
                "production window {index} differs from the shared plan"
            )));
        }
    }
    for (family_index, (backing, planned)) in input
        .sources
        .backings
        .iter()
        .zip(&plan.backings)
        .enumerate()
    {
        match (backing, planned.field) {
            (R0HostBacking::Bf(values), FieldKind::Base) => {
                if values.len().checked_mul(core::mem::size_of::<BF>()) != Some(planned.bytes)
                    || values.iter().copied().enumerate().any(|(element, value)| {
                        value
                            != deterministic_bf(
                                input.identity.seed,
                                0x534f_5552_4345_4246 ^ family_index as u64,
                                element as u64,
                                0,
                            )
                    })
                {
                    return Err(R0InputError::Source(format!(
                        "production BF backing {family_index} is not complete traffic"
                    )));
                }
            }
            (R0HostBacking::E4(values), FieldKind::Ext) => {
                if values.len().checked_mul(core::mem::size_of::<E4>()) != Some(planned.bytes)
                    || values.iter().copied().enumerate().any(|(element, value)| {
                        value
                            != deterministic_e4(
                                input.identity.seed,
                                0x534f_5552_4345_4534 ^ family_index as u64,
                                element as u64,
                            )
                    })
                {
                    return Err(R0InputError::Source(format!(
                        "production E4 backing {family_index} is not complete traffic"
                    )));
                }
            }
            _ => {
                return Err(R0InputError::Source(format!(
                    "production backing {family_index} has the wrong field"
                )));
            }
        }
    }
    Ok(())
}

fn production_challenge_values(
    recipes: &[FrozenR0Recipe],
    challenge_bases: &[FrozenChallengeBase],
) -> Result<Vec<FrozenChallengeValue>, R0InputError> {
    let assignment = ChallengeAssignment {
        bases: challenge_bases,
    };
    let mut challenge_references = BTreeSet::new();
    for recipe in recipes {
        for product in &recipe.products {
            for challenge in &product.challenges {
                let canonical = CoeffChallenge::new(challenge.reference.clone());
                if canonical.0 != challenge.reference {
                    return Err(R0InputError::NoncanonicalChallenge);
                }
                challenge_references.insert(canonical);
            }
        }
    }
    let mut challenge_references = challenge_references.into_iter().collect::<Vec<_>>();
    challenge_references.sort_by_key(|reference| {
        (
            stable_key_index(&reference.0.key),
            match reference.0.power {
                ChallengePower::One => (0u8, 1u32),
                ChallengePower::Static(power) => (1, power),
            },
        )
    });
    challenge_references
        .into_iter()
        .map(|challenge| {
            Ok(FrozenChallengeValue {
                value: FrozenE4::from_e4(assignment.resolve_canonical(&challenge.0)?),
                challenge: FrozenR0Challenge {
                    reference: challenge.0,
                },
            })
        })
        .collect()
}

pub fn build_r0_input_with_layer(
    coordinate: &FrozenR0Coordinate,
    layer: &DagLayer,
    log_trace: u32,
    seed: u64,
) -> Result<ResolvedR0Input, R0InputError> {
    // A lone layer does not carry the producer sink fields needed to type its
    // LayerOutput/CacheOutput reads. Resolve those from the coordinate's
    // canonical, fully validated circuit while retaining the supplied layer.
    let dag = load_canonical_dag(coordinate)?;
    let cross_fields = canonical_cross_layer_fields(&dag, coordinate.layer as usize);
    build_r0_input_with_metadata(coordinate, layer, &cross_fields, log_trace, seed)
}

fn build_r0_input_with_metadata(
    coordinate: &FrozenR0Coordinate,
    layer: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    log_trace: u32,
    seed: u64,
) -> Result<ResolvedR0Input, R0InputError> {
    if !(3..=27).contains(&log_trace) {
        return Err(R0InputError::InvalidLogTrace(log_trace));
    }
    let trace_len = 1usize
        .checked_shl(log_trace)
        .ok_or(R0InputError::InvalidLogTrace(log_trace))?;

    let challenge_bases = build_challenge_bases(seed);
    let challenge_references = collect_challenge_references(layer, &coordinate.recipes)?;
    let assignment = ChallengeAssignment {
        bases: &challenge_bases,
    };
    let challenge_values = challenge_references
        .iter()
        .map(|challenge| {
            Ok(FrozenChallengeValue {
                challenge: FrozenR0Challenge {
                    reference: challenge.0.clone(),
                },
                value: FrozenE4::from_e4(assignment.resolve_canonical(&challenge.0)?),
            })
        })
        .collect::<Result<Vec<_>, R0InputError>>()?;

    let coefficient_bank = resolve_r0_coefficients(&coordinate.recipes, &challenge_bases)?;
    let coefficient_bank_frozen = coefficient_bank
        .iter()
        .copied()
        .map(FrozenE4::from_e4)
        .collect::<Vec<_>>();
    let coefficient_sha256 = hash_e4_values(coefficient_bank.iter().copied())?;

    let equality_point = (0..log_trace - 3)
        .map(|index| FrozenE4::from_e4(deterministic_e4(seed, 0x4551_504f_494e_5400, index as u64)))
        .collect::<Vec<_>>();
    let eq_tables = build_factored_eq_tables(&equality_point)?;
    check_equality_algorithms(&equality_point, &eq_tables)?;
    let direct_eq_sha256 = hash_direct_equality(&equality_point)?;
    let factored_eq_sha256 = hash_factored_equality(&eq_tables)?;

    let classification = classify_sources(layer, &coordinate.binding)?;
    let (mut sources, mut derived_spans) = build_host_sources(
        &coordinate.binding,
        log_trace,
        seed,
        &classification.targets,
    )?;
    let canonical_only_sources = fill_derived_sources(
        layer,
        &coordinate.binding,
        &mut sources,
        &mut derived_spans,
        &assignment,
        cross_fields,
        seed,
        classification,
    )?;
    let source_hashes = hash_source_classes(&sources, &derived_spans, &canonical_only_sources)?;

    let mut identity = R0InputIdentityV1 {
        version: R0_INPUT_VERSION,
        source_generator_version: R0_SOURCE_GENERATOR_VERSION,
        circuit: coordinate.circuit.clone(),
        layer: coordinate.layer,
        log_trace,
        seed,
        challenge_bases,
        challenge_values,
        equality_point,
        coefficient_bank: coefficient_bank_frozen,
        eq_sizes: eq_tables.sizes.into(),
        source_data_sha256: source_hashes.all,
        independent_source_sha256: source_hashes.independent,
        derived_source_sha256: source_hashes.derived,
        coefficient_sha256,
        direct_eq_sha256,
        factored_eq_sha256,
        input_sha256: String::new(),
    };
    identity.input_sha256 = r0_input_identity_sha256(&identity)?;
    let input = ResolvedR0Input {
        identity,
        sources,
        coefficient_bank,
        eq_tables,
        derived_spans,
        canonical_only_sources,
    };
    validate_r0_input(&input)?;
    Ok(input)
}

pub fn resolve_r0_coefficients(
    recipes: &[FrozenR0Recipe],
    challenge_bases: &[FrozenChallengeBase],
) -> Result<Vec<E4>, R0InputError> {
    let assignment = ChallengeAssignment {
        bases: challenge_bases,
    };
    recipes
        .iter()
        .map(|recipe| {
            let mut sum = E4::ZERO;
            for product in &recipe.products {
                let mut value = lift(BF::from_u32_with_reduction(product.scalar));
                for challenge in &product.challenges {
                    value.mul_assign(&assignment.resolve_recipe(&challenge.reference)?);
                }
                for reference in &product.inits_and_teardowns_top_bits {
                    let top_bits = (reference.set_index as u32)
                        .checked_shl(reference.shift)
                        .unwrap_or(0);
                    value.mul_assign(&lift(BF::from_u32_with_reduction(top_bits)));
                }
                sum.add_assign(&value);
            }
            Ok(sum)
        })
        .collect()
}

pub(crate) fn resolve_normalized_coefficients_for_seed(
    recipes: &[NormalizedCoefficientRecipe],
    seed: u64,
) -> Result<Vec<E4>, R0InputError> {
    let challenge_bases = build_challenge_bases(seed);
    let assignment = ChallengeAssignment {
        bases: &challenge_bases,
    };
    recipes
        .iter()
        .map(|recipe| {
            for product in &recipe.terms {
                for challenge in &product.challenges {
                    assignment.resolve_recipe(&challenge.0)?;
                }
            }
            Ok(recipe.evaluate(&assignment))
        })
        .collect()
}

pub fn direct_eq_weight(row: usize, equality_point: &[FrozenE4]) -> E4 {
    let mut result = E4::ONE;
    for (bit, coordinate) in equality_point.iter().enumerate() {
        let coordinate = coordinate.to_e4();
        let factor = if row & (1usize << bit) == 0 {
            e4_sub(E4::ONE, coordinate)
        } else {
            coordinate
        };
        result.mul_assign(&factor);
    }
    result
}

pub fn build_factored_eq_tables(
    equality_point: &[FrozenE4],
) -> Result<R0FactoredEqTables, R0InputError> {
    if equality_point.len() > 24 {
        return Err(R0InputError::InvalidLogTrace(
            u32::try_from(equality_point.len()).unwrap_or(u32::MAX) + 3,
        ));
    }
    let sizes = partition_eq_sizes(equality_point.len() as u32);
    let low_end = sizes.low as usize;
    let high1_end = low_end + sizes.high[1] as usize;
    let high0_end = high1_end + sizes.high[0] as usize;
    let low = build_eq_group(&equality_point[..low_end], true);
    let high1 = build_eq_group(&equality_point[low_end..high1_end], false);
    let high0 = build_eq_group(&equality_point[high1_end..high0_end], false);
    Ok(R0FactoredEqTables {
        high: [high0, high1],
        low,
        sizes,
    })
}

pub fn factored_eq_weight(row: usize, tables: &R0FactoredEqTables) -> Result<E4, R0InputError> {
    let total_bits = tables.sizes.low + tables.sizes.high[0] + tables.sizes.high[1];
    if row >= (1usize << total_bits) {
        return Err(R0InputError::Source(format!(
            "equality row {row} is outside {total_bits} bits"
        )));
    }
    let low_mask = bit_mask(tables.sizes.low);
    let high1_mask = bit_mask(tables.sizes.high[1]);
    let high0_mask = bit_mask(tables.sizes.high[0]);
    let low_index = row & low_mask;
    let high1_index = (row >> tables.sizes.low) & high1_mask;
    let high0_index = (row >> (tables.sizes.low + tables.sizes.high[1])) & high0_mask;
    let mut value = *tables
        .low
        .get(low_index)
        .ok_or_else(|| R0InputError::Source("low equality index is missing".to_owned()))?;
    if tables.sizes.high[1] != 0 {
        value.mul_assign(
            tables.high[1].get(high1_index).ok_or_else(|| {
                R0InputError::Source("high-1 equality index is missing".to_owned())
            })?,
        );
    }
    if tables.sizes.high[0] != 0 {
        value.mul_assign(
            tables.high[0].get(high0_index).ok_or_else(|| {
                R0InputError::Source("high-0 equality index is missing".to_owned())
            })?,
        );
    }
    Ok(value)
}

pub fn r0_input_identity_sha256(identity: &R0InputIdentityV1) -> Result<String, R0InputError> {
    let mut preimage = identity.clone();
    preimage.input_sha256.clear();
    let bytes = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .serialize(&preimage)
        .map_err(|error| R0InputError::Codec(error.to_string()))?;
    hash_bytes(&bytes)
}

/// Refresh every byte-derived field after an intentional semantic-input
/// mutation.  Challenge references and values remain explicit inputs; this
/// routine hashes them as supplied rather than silently re-deriving one from
/// the other.
pub fn refresh_r0_input_hashes(input: &mut ResolvedR0Input) -> Result<(), R0InputError> {
    input.identity.coefficient_bank = input
        .coefficient_bank
        .iter()
        .copied()
        .map(FrozenE4::from_e4)
        .collect();
    input.identity.coefficient_sha256 = hash_e4_values(input.coefficient_bank.iter().copied())?;

    input.eq_tables = build_factored_eq_tables(&input.identity.equality_point)?;
    input.identity.eq_sizes = input.eq_tables.sizes.into();
    input.identity.direct_eq_sha256 = hash_direct_equality(&input.identity.equality_point)?;
    input.identity.factored_eq_sha256 = hash_factored_equality(&input.eq_tables)?;

    let sources = hash_source_classes(
        &input.sources,
        &input.derived_spans,
        &input.canonical_only_sources,
    )?;
    input.identity.source_data_sha256 = sources.all;
    input.identity.independent_source_sha256 = sources.independent;
    input.identity.derived_source_sha256 = sources.derived;
    input.identity.input_sha256 = r0_input_identity_sha256(&input.identity)?;
    Ok(())
}

pub fn validate_r0_input(input: &ResolvedR0Input) -> Result<(), R0InputError> {
    if input.identity.version != R0_INPUT_VERSION {
        return Err(R0InputError::IdentityMismatch("version"));
    }
    if input.identity.source_generator_version != R0_SOURCE_GENERATOR_VERSION {
        return Err(R0InputError::IdentityMismatch("source generator version"));
    }
    if !(3..=27).contains(&input.identity.log_trace)
        || input.identity.equality_point.len() != (input.identity.log_trace - 3) as usize
        || input.sources.trace_len != 1usize << input.identity.log_trace
    {
        return Err(R0InputError::IdentityMismatch("input dimensions"));
    }
    if input.identity.challenge_bases != build_challenge_bases(input.identity.seed) {
        return Err(R0InputError::IdentityMismatch("challenge bases"));
    }
    let expected_equality = (0..input.identity.log_trace - 3)
        .map(|index| {
            FrozenE4::from_e4(deterministic_e4(
                input.identity.seed,
                0x4551_504f_494e_5400,
                index as u64,
            ))
        })
        .collect::<Vec<_>>();
    if input.identity.equality_point != expected_equality {
        return Err(R0InputError::IdentityMismatch("equality point"));
    }
    let assignment = ChallengeAssignment {
        bases: &input.identity.challenge_bases,
    };
    let mut challenge_set = HashSet::new();
    for challenge in &input.identity.challenge_values {
        if CoeffChallenge::new(challenge.challenge.reference.clone()).0
            != challenge.challenge.reference
        {
            return Err(R0InputError::NoncanonicalChallenge);
        }
        if !challenge_set.insert(challenge.challenge.reference.clone()) {
            return Err(R0InputError::IdentityMismatch("duplicate challenge value"));
        }
        if FrozenE4::from_e4(assignment.resolve_canonical(&challenge.challenge.reference)?)
            != challenge.value
        {
            return Err(R0InputError::IdentityMismatch("challenge value"));
        }
    }
    let frozen_coefficients = input
        .coefficient_bank
        .iter()
        .copied()
        .map(FrozenE4::from_e4)
        .collect::<Vec<_>>();
    if frozen_coefficients != input.identity.coefficient_bank {
        return Err(R0InputError::IdentityMismatch("coefficient bank"));
    }
    if hash_e4_values(input.coefficient_bank.iter().copied())? != input.identity.coefficient_sha256
    {
        return Err(R0InputError::IdentityMismatch("coefficient hash"));
    }
    let expected_tables = build_factored_eq_tables(&input.identity.equality_point)?;
    if expected_tables != input.eq_tables {
        return Err(R0InputError::IdentityMismatch("factored equality tables"));
    }
    if FrozenEqSizes::from(input.eq_tables.sizes) != input.identity.eq_sizes {
        return Err(R0InputError::IdentityMismatch("equality sizes"));
    }
    if hash_direct_equality(&input.identity.equality_point)? != input.identity.direct_eq_sha256 {
        return Err(R0InputError::IdentityMismatch("direct equality hash"));
    }
    if hash_factored_equality(&input.eq_tables)? != input.identity.factored_eq_sha256 {
        return Err(R0InputError::IdentityMismatch("factored equality hash"));
    }
    let hashes = hash_source_classes(
        &input.sources,
        &input.derived_spans,
        &input.canonical_only_sources,
    )?;
    if hashes.all != input.identity.source_data_sha256 {
        return Err(R0InputError::IdentityMismatch("source hash"));
    }
    if hashes.independent != input.identity.independent_source_sha256 {
        return Err(R0InputError::IdentityMismatch("independent source hash"));
    }
    if hashes.derived != input.identity.derived_source_sha256 {
        return Err(R0InputError::IdentityMismatch("derived source hash"));
    }
    if r0_input_identity_sha256(&input.identity)? != input.identity.input_sha256 {
        return Err(R0InputError::IdentityMismatch("input hash"));
    }
    Ok(())
}

fn load_canonical_dag(coordinate: &FrozenR0Coordinate) -> Result<DagCircuit, R0InputError> {
    let path = crate::runtime_paths::compiled_circuits_directory()
        .join(format!("{}_layout_gkr.json", coordinate.circuit));
    let bytes = std::fs::read(&path)
        .map_err(|error| R0InputError::ReadLayout(format!("{}: {error}", path.display())))?;
    let artifact: GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes)
        .map_err(|error| R0InputError::ParseLayout(error.to_string()))?;
    if artifact.trace_len as u64 != coordinate.trace_len {
        return Err(R0InputError::CoordinateMismatch(format!(
            "{} trace length {} != {}",
            coordinate.circuit, artifact.trace_len, coordinate.trace_len
        )));
    }
    let dag = gkr_eval_ir::lower_dag(&artifact)
        .map_err(|error| R0InputError::LowerLayout(error.to_string()))?;
    gkr_eval_ir::validate(&dag).map_err(R0InputError::LowerLayout)?;
    Ok(dag)
}

fn canonical_cross_layer_fields(
    dag: &DagCircuit,
    layer_index: usize,
) -> HashMap<ReadPlace, FieldKind> {
    let mut fields = HashMap::new();
    for layer in dag.layers.iter().take(layer_index) {
        for root in &layer.roots {
            if let Some(sink) = &root.materialize {
                let place = match sink.kind {
                    SinkKind::Inner { layer, offset } => ReadPlace::LayerOutput { layer, offset },
                    SinkKind::Cache { layer, offset } => ReadPlace::CacheOutput { layer, offset },
                    SinkKind::Scratch { .. } => continue,
                };
                fields.insert(place, sink.field);
            }
        }
    }
    fields
}

fn stable_challenge_keys() -> Vec<ChallengeKey> {
    use PermutationSlot::*;
    vec![
        ChallengeKey::PermutationLinearization(AddressLow),
        ChallengeKey::PermutationLinearization(AddressHigh),
        ChallengeKey::PermutationLinearization(TimestampLow),
        ChallengeKey::PermutationLinearization(TimestampHigh),
        ChallengeKey::PermutationLinearization(ValueLow),
        ChallengeKey::PermutationLinearization(ValueHigh),
        ChallengeKey::PermutationAdditive,
        ChallengeKey::LookupMultiplicative,
        ChallengeKey::LookupAdditive,
        ChallengeKey::ClaimBatching,
    ]
}

fn stable_key_index(key: &ChallengeKey) -> u8 {
    match key {
        ChallengeKey::PermutationLinearization(PermutationSlot::AddressLow) => 0,
        ChallengeKey::PermutationLinearization(PermutationSlot::AddressHigh) => 1,
        ChallengeKey::PermutationLinearization(PermutationSlot::TimestampLow) => 2,
        ChallengeKey::PermutationLinearization(PermutationSlot::TimestampHigh) => 3,
        ChallengeKey::PermutationLinearization(PermutationSlot::ValueLow) => 4,
        ChallengeKey::PermutationLinearization(PermutationSlot::ValueHigh) => 5,
        ChallengeKey::PermutationAdditive => 6,
        ChallengeKey::LookupMultiplicative => 7,
        ChallengeKey::LookupAdditive => 8,
        ChallengeKey::ClaimBatching => 9,
    }
}

fn build_challenge_bases(seed: u64) -> Vec<FrozenChallengeBase> {
    stable_challenge_keys()
        .into_iter()
        .map(|key| {
            let index = stable_key_index(&key);
            FrozenChallengeBase {
                key,
                value: FrozenE4::from_e4(deterministic_e4(
                    seed,
                    0x4348_414c_4c45_4e47,
                    u64::from(index),
                )),
            }
        })
        .collect()
}

struct ChallengeAssignment<'a> {
    bases: &'a [FrozenChallengeBase],
}

impl ChallengeAssignment<'_> {
    fn base(&self, key: &ChallengeKey) -> Result<E4, R0InputError> {
        self.bases
            .iter()
            .find(|entry| &entry.key == key)
            .map(|entry| entry.value.to_e4())
            .ok_or_else(|| R0InputError::MissingChallengeBase(format!("{key:?}")))
    }

    fn resolve_canonical(&self, reference: &ChallengeRef) -> Result<E4, R0InputError> {
        let power = challenge_power(reference);
        let base = self.base(&reference.key)?;
        match reference.key {
            ChallengeKey::ClaimBatching | ChallengeKey::LookupMultiplicative => Ok(base.pow(power)),
            _ if power == 1 => Ok(base),
            _ => Err(R0InputError::AmbiguousChallengePower {
                key: format!("{:?}", reference.key),
                power,
            }),
        }
    }

    fn resolve_recipe(&self, reference: &ChallengeRef) -> Result<E4, R0InputError> {
        let power = challenge_power(reference);
        let base = self.base(&reference.key)?;
        match reference.key {
            ChallengeKey::ClaimBatching | ChallengeKey::LookupMultiplicative => Ok(base.pow(power)),
            _ if power == 1 => Ok(base),
            _ => Err(R0InputError::AmbiguousChallengePower {
                key: format!("{:?}", reference.key),
                power,
            }),
        }
    }
}

impl ChallengeResolver for ChallengeAssignment<'_> {
    fn challenge(&self, reference: &ChallengeRef) -> E4 {
        self.resolve_canonical(reference)
            .expect("collected canonical challenge references are prevalidated")
    }
}

fn challenge_power(reference: &ChallengeRef) -> u32 {
    match reference.power {
        ChallengePower::One => 1,
        ChallengePower::Static(power) => power,
    }
}

fn collect_challenge_references(
    layer: &DagLayer,
    recipes: &[FrozenR0Recipe],
) -> Result<Vec<CoeffChallenge>, R0InputError> {
    let mut references = BTreeSet::new();
    let mut visited = HashSet::new();
    for root in &layer.batching.roots {
        let root = layer
            .roots
            .get(root.0 as usize)
            .ok_or_else(|| R0InputError::Source("claim root is missing".to_owned()))?;
        collect_expr_inputs(layer, root.expr, &mut visited, &mut references, None)?;
    }
    for recipe in recipes {
        for product in &recipe.products {
            for challenge in &product.challenges {
                let canonical = CoeffChallenge::new(challenge.reference.clone());
                if canonical.0 != challenge.reference {
                    return Err(R0InputError::NoncanonicalChallenge);
                }
                references.insert(canonical);
            }
        }
    }
    let mut references = references.into_iter().collect::<Vec<_>>();
    references.sort_by_key(|reference| {
        (
            stable_key_index(&reference.0.key),
            match reference.0.power {
                ChallengePower::One => (0u8, 1u32),
                ChallengePower::Static(power) => (1, power),
            },
        )
    });
    Ok(references)
}

fn collect_expr_inputs(
    layer: &DagLayer,
    expr: ExprId,
    visited: &mut HashSet<ExprId>,
    challenges: &mut BTreeSet<CoeffChallenge>,
    mut reads: Option<&mut HashSet<ReadPlace>>,
) -> Result<(), R0InputError> {
    if !visited.insert(expr) {
        return Ok(());
    }
    match layer
        .exprs
        .get(expr.0 as usize)
        .ok_or_else(|| R0InputError::Source(format!("expression {} is missing", expr.0)))?
    {
        Expr::Source(source) => match &layer
            .sources
            .get(source.0 as usize)
            .ok_or_else(|| R0InputError::Source(format!("source {} is missing", source.0)))?
        {
            SourceKind::Challenge { reference } => {
                let canonical = CoeffChallenge::new(reference.clone());
                challenges.insert(canonical);
            }
            SourceKind::Read { place } => {
                if let Some(reads) = reads.as_deref_mut() {
                    reads.insert(place.clone());
                }
            }
            SourceKind::LookupValue { query, .. } => {
                collect_expr_inputs(layer, *query, visited, challenges, reads)?;
            }
            _ => {}
        },
        Expr::Add(children) | Expr::Mul(children) => {
            for child in children {
                collect_expr_inputs(layer, *child, visited, challenges, reads.as_deref_mut())?;
            }
        }
    }
    Ok(())
}

fn build_host_sources(
    binding: &LeanSourceBinding,
    log_trace: u32,
    seed: u64,
    derived_targets: &[DerivedTarget],
) -> Result<(R0HostSources, Vec<DerivedSpan>), R0InputError> {
    let plan = build_lean_allocation_plan(binding, log_trace)
        .map_err(|error| R0InputError::Source(error.to_string()))?;
    let trace_len = plan.trace_len;
    let mut backings = Vec::with_capacity(plan.backings.len());
    for (family_index, backing) in plan.backings.iter().enumerate() {
        let field = match backing.field {
            FieldKind::Base => FrozenField::Bf,
            FieldKind::Ext => FrozenField::E4,
        };
        let elements = match field {
            FrozenField::Bf => backing.bytes / core::mem::size_of::<BF>(),
            FrozenField::E4 => backing.bytes / core::mem::size_of::<E4>(),
        };
        let backing = match field {
            FrozenField::Bf => R0HostBacking::Bf(
                (0..elements)
                    .map(|element| {
                        let column = element / trace_len;
                        if is_derived_family_column(derived_targets, &backing.family, column) {
                            BF::ZERO
                        } else {
                            deterministic_bf(
                                seed,
                                0x534f_5552_4345_4246 ^ family_index as u64,
                                element as u64,
                                0,
                            )
                        }
                    })
                    .collect(),
            ),
            FrozenField::E4 => R0HostBacking::E4(
                (0..elements)
                    .map(|element| {
                        let column = element / trace_len;
                        if is_derived_family_column(derived_targets, &backing.family, column) {
                            E4::ZERO
                        } else {
                            deterministic_e4(
                                seed,
                                0x534f_5552_4345_4534 ^ family_index as u64,
                                element as u64,
                            )
                        }
                    })
                    .collect(),
            ),
        };
        backings.push(backing);
    }
    let windows = plan
        .windows
        .iter()
        .map(|window| {
            let field = match window.field {
                FieldKind::Base => FrozenField::Bf,
                FieldKind::Ext => FrozenField::E4,
            };
            Ok(R0HostWindow {
                field,
                backing_index: window.backing,
                first_element: window.base_element,
                procedural_kind: window.procedural_kind,
            })
        })
        .collect::<Result<Vec<_>, R0InputError>>()?;
    Ok((
        R0HostSources {
            trace_len,
            windows,
            backings,
        },
        Vec::new(),
    ))
}

#[derive(Clone)]
struct DerivedTarget {
    place: ReadPlace,
    expr: ExprId,
    field: FieldKind,
}

struct SourceClassification {
    targets: Vec<DerivedTarget>,
    reads: Vec<ReadPlace>,
}

fn classify_sources(
    layer: &DagLayer,
    binding: &LeanSourceBinding,
) -> Result<SourceClassification, R0InputError> {
    let mut targets = HashMap::<ReadPlace, DerivedTarget>::new();
    for root in &layer.roots {
        let (Some(_claim), Some(sink)) = (&root.claim, &root.materialize) else {
            continue;
        };
        let Some(place) = sink_read_place(&sink.kind) else {
            continue;
        };
        if !binding_references_target(binding, &place, sink.field) {
            continue;
        }
        if targets
            .insert(
                place.clone(),
                DerivedTarget {
                    place: place.clone(),
                    expr: root.expr,
                    field: sink.field,
                },
            )
            .is_some()
        {
            return Err(R0InputError::DerivedSourceOverlap(format!(
                "multiple claim roots materialize {place:?}"
            )));
        }
    }

    let mut reads = HashSet::new();
    let mut visited = HashSet::new();
    let mut unused_challenges = BTreeSet::new();
    for root in &layer.batching.roots {
        let root = layer
            .roots
            .get(root.0 as usize)
            .ok_or_else(|| R0InputError::Source("claim root is missing".to_owned()))?;
        collect_expr_inputs(
            layer,
            root.expr,
            &mut visited,
            &mut unused_challenges,
            Some(&mut reads),
        )?;
    }
    if let Some(place) = targets.keys().find(|place| reads.contains(*place)) {
        return Err(R0InputError::DerivedSourceOverlap(format!(
            "{place:?} is both an independent read and a derived sink"
        )));
    }

    let mut targets = targets.into_values().collect::<Vec<_>>();
    targets.sort_by_key(|target| read_place_key(&target.place));
    let mut reads = reads.into_iter().collect::<Vec<_>>();
    reads.sort_by_key(read_place_key);
    Ok(SourceClassification { targets, reads })
}

fn fill_derived_sources(
    layer: &DagLayer,
    binding: &LeanSourceBinding,
    sources: &mut R0HostSources,
    derived_spans: &mut Vec<DerivedSpan>,
    challenges: &ChallengeAssignment<'_>,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    seed: u64,
    classification: SourceClassification,
) -> Result<Vec<CanonicalSource>, R0InputError> {
    let mut canonical_only_sources = Vec::new();
    for (index, place) in classification.reads.into_iter().enumerate() {
        if locate_place(binding, sources, &place)?.is_some() {
            continue;
        }
        let field = gkr_eval_ir::read_place_field(&place)
            .or_else(|| cross_fields.get(&place).copied())
            .ok_or_else(|| {
                R0InputError::Source(format!(
                    "canonical-only read {place:?} has no field in canonical circuit metadata"
                ))
            })?;
        let backing = match field {
            FieldKind::Base => R0HostBacking::Bf(
                (0..sources.trace_len)
                    .map(|row| {
                        deterministic_bf(seed, 0x4341_4e4f_4e52_4442 ^ index as u64, row as u64, 0)
                    })
                    .collect(),
            ),
            FieldKind::Ext => R0HostBacking::E4(
                (0..sources.trace_len)
                    .map(|row| {
                        deterministic_e4(seed, 0x4341_4e4f_4e52_4445 ^ index as u64, row as u64)
                    })
                    .collect(),
            ),
        };
        canonical_only_sources.push(CanonicalSource { place, backing });
    }

    let source_snapshot = sources.clone();
    let read = SourceReadResolver {
        binding,
        sources: &source_snapshot,
        canonical_only_sources: &canonical_only_sources,
    };
    let virtual_setup = SourceVirtualResolver {
        sources: &source_snapshot,
    };
    let lookup = PanicLookupResolver;
    let resolvers = Resolvers {
        read: &read,
        lookup: &lookup,
        virtual_setup: &virtual_setup,
        challenge: challenges,
    };
    for target in classification.targets {
        let (window, backing_index, first_element, actual_field) =
            locate_place(binding, sources, &target.place)?.ok_or_else(|| {
                R0InputError::Source(format!("derived target {:?} vanished", target.place))
            })?;
        let expected_field = match target.field {
            FieldKind::Base => FrozenField::Bf,
            FieldKind::Ext => FrozenField::E4,
        };
        if actual_field != expected_field {
            return Err(R0InputError::DerivedFieldMismatch(format!(
                "{:?}: sink {:?}, backing {:?}",
                target.place, expected_field, actual_field
            )));
        }
        derived_spans.push(DerivedSpan {
            backing_index,
            first_element,
            element_count: sources.trace_len,
        });
        for row in 0..sources.trace_len {
            let value = eval_backward_claim_expr(layer, target.expr, row, &resolvers)?;
            match sources
                .backings
                .get_mut(backing_index)
                .ok_or_else(|| R0InputError::Source("derived backing is missing".to_owned()))?
            {
                R0HostBacking::Bf(values) => {
                    if !value.c0.c1.is_zero() || !value.c1.c0.is_zero() || !value.c1.c1.is_zero() {
                        return Err(R0InputError::DerivedFieldMismatch(format!(
                            "{:?} evaluates outside the base field",
                            target.place
                        )));
                    }
                    values[first_element + row] = value.c0.c0;
                }
                R0HostBacking::E4(values) => values[first_element + row] = value,
            }
        }
        let _ = window;
    }
    derived_spans.sort_by_key(|span| (span.backing_index, span.first_element));
    for pair in derived_spans.windows(2) {
        if pair[0].backing_index == pair[1].backing_index
            && pair[0].first_element + pair[0].element_count > pair[1].first_element
        {
            return Err(R0InputError::DerivedSourceOverlap(
                "derived source spans overlap".to_owned(),
            ));
        }
    }
    Ok(canonical_only_sources)
}

struct SourceReadResolver<'a> {
    binding: &'a LeanSourceBinding,
    sources: &'a R0HostSources,
    canonical_only_sources: &'a [CanonicalSource],
}

impl ReadResolver for SourceReadResolver<'_> {
    fn read(&self, place: &ReadPlace, row: usize) -> E4 {
        if let Ok(value) = self.sources.read_place(self.binding, place, row) {
            return value;
        }
        let source = self
            .canonical_only_sources
            .iter()
            .find(|source| &source.place == place)
            .expect("reachable canonical reads are classified before evaluation");
        match &source.backing {
            R0HostBacking::Bf(values) => lift(values[row]),
            R0HostBacking::E4(values) => values[row],
        }
    }
}

struct SourceVirtualResolver<'a> {
    sources: &'a R0HostSources,
}

impl VirtualSetupResolver for SourceVirtualResolver<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> BF {
        self.sources.virtual_setup(kind, row)
    }
}

struct PanicLookupResolver;

impl LookupResolver for PanicLookupResolver {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        _evaluated_query: E4,
        row: usize,
    ) -> BF {
        panic!("query-substituted R0 evaluation called lookup {kind:?}/{set_index} at row {row}")
    }
}

fn locate_place(
    binding: &LeanSourceBinding,
    sources: &R0HostSources,
    place: &ReadPlace,
) -> Result<Option<(usize, usize, usize, FrozenField)>, R0InputError> {
    let mut found = None;
    for (window_index, window) in binding.windows.iter().enumerate() {
        let Some(column) = place_column_in_family(place, &window.family) else {
            continue;
        };
        if window
            .columns
            .binary_search_by_key(&column, |entry| entry.column)
            .is_err()
        {
            continue;
        }
        let host = sources
            .windows
            .get(window_index)
            .ok_or_else(|| R0InputError::Source("host window is missing".to_owned()))?;
        let Some(backing_index) = host.backing_index else {
            return Err(R0InputError::Source(
                "derived target cannot be procedural".to_owned(),
            ));
        };
        let first_element = column
            .checked_mul(sources.trace_len)
            .ok_or_else(|| R0InputError::Source("derived offset overflow".to_owned()))?;
        if found
            .replace((window_index, backing_index, first_element, host.field))
            .is_some()
        {
            return Err(R0InputError::Source(format!(
                "place {place:?} has multiple bound coordinates"
            )));
        }
    }
    Ok(found)
}

fn place_column_in_family(place: &ReadPlace, family: &WindowFamily) -> Option<usize> {
    match (place, family) {
        (ReadPlace::BaseLayerMemory { column }, WindowFamily::BaseLayerMemory)
        | (ReadPlace::BaseLayerWitness { column }, WindowFamily::BaseLayerWitness)
        | (ReadPlace::Setup { column }, WindowFamily::Setup) => Some(*column),
        (ReadPlace::Scratch { slot }, WindowFamily::Scratch) => Some(*slot),
        (
            ReadPlace::LayerOutput { layer, offset },
            WindowFamily::LayerOutput {
                layer: family_layer,
                ..
            },
        ) if layer == family_layer => Some(*offset),
        (
            ReadPlace::CacheOutput { layer, offset },
            WindowFamily::CacheOutput {
                layer: family_layer,
                ..
            },
        ) if layer == family_layer => Some(*offset),
        _ => None,
    }
}

fn binding_references_target(
    binding: &LeanSourceBinding,
    place: &ReadPlace,
    field: FieldKind,
) -> bool {
    binding.windows.iter().any(|window| {
        family_field(window.family) == field
            && place_column_in_family(place, &window.family).is_some_and(|column| {
                window
                    .columns
                    .binary_search_by_key(&column, |entry| entry.column)
                    .is_ok()
            })
    })
}

fn is_derived_family_column(
    targets: &[DerivedTarget],
    family: &WindowFamily,
    column: usize,
) -> bool {
    targets.iter().any(|target| {
        family_field(*family) == target.field
            && place_column_in_family(&target.place, family) == Some(column)
    })
}

fn family_field(family: WindowFamily) -> FieldKind {
    match family {
        WindowFamily::LayerOutput { ext: true, .. }
        | WindowFamily::CacheOutput { ext: true, .. } => FieldKind::Ext,
        _ => FieldKind::Base,
    }
}

fn sink_read_place(sink: &SinkKind) -> Option<ReadPlace> {
    match sink {
        SinkKind::Inner { layer, offset } => Some(ReadPlace::LayerOutput {
            layer: *layer,
            offset: *offset,
        }),
        SinkKind::Cache { layer, offset } => Some(ReadPlace::CacheOutput {
            layer: *layer,
            offset: *offset,
        }),
        SinkKind::Scratch { slot } => Some(ReadPlace::Scratch { slot: *slot }),
    }
}

fn read_place_key(place: &ReadPlace) -> (u8, usize, usize) {
    match place {
        ReadPlace::BaseLayerMemory { column } => (0, *column, 0),
        ReadPlace::BaseLayerWitness { column } => (1, *column, 0),
        ReadPlace::Setup { column } => (2, *column, 0),
        ReadPlace::Scratch { slot } => (3, *slot, 0),
        ReadPlace::LayerOutput { layer, offset } => (4, *layer, *offset),
        ReadPlace::CacheOutput { layer, offset } => (5, *layer, *offset),
    }
}

fn partition_eq_sizes(challenge_count: u32) -> WindowEqSizes {
    const GROUP_BITS: u32 = 8;
    let group_count = challenge_count.div_ceil(GROUP_BITS);
    let mut high = [0; 2];
    let mut low = 0;
    let mut consumed = 0;
    let mut high_index = 0;
    for group in 0..group_count {
        let group_size = (challenge_count - consumed).min(GROUP_BITS);
        if group + 1 == group_count {
            low = group_size;
        } else {
            high[high_index] = group_size;
            high_index += 1;
        }
        consumed += group_size;
    }
    WindowEqSizes { high, low }
}

fn build_eq_group(point: &[FrozenE4], keep_zero_group: bool) -> Vec<E4> {
    if point.is_empty() && !keep_zero_group {
        return Vec::new();
    }
    let mut values = vec![E4::ONE];
    for coordinate in point {
        let at_one = coordinate.to_e4();
        let at_zero = e4_sub(E4::ONE, at_one);
        let previous_len = values.len();
        values.reserve(previous_len);
        for index in 0..previous_len {
            let previous = values[index];
            values[index].mul_assign(&at_zero);
            let mut selected = previous;
            selected.mul_assign(&at_one);
            values.push(selected);
        }
    }
    values
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EqualityCheckCoverage {
    Exhaustive { checked_rows: usize },
    Sampled { checked_rows: [usize; 6] },
}

fn check_equality_algorithms(
    point: &[FrozenE4],
    tables: &R0FactoredEqTables,
) -> Result<EqualityCheckCoverage, R0InputError> {
    let rows = 1usize << point.len();
    if rows <= 4096 {
        for row in 0..rows {
            if direct_eq_weight(row, point) != factored_eq_weight(row, tables)? {
                return Err(R0InputError::IdentityMismatch("equality algorithms"));
            }
        }
        Ok(EqualityCheckCoverage::Exhaustive { checked_rows: rows })
    } else {
        let samples = [0, 1, rows / 3, rows / 2, rows - 2, rows - 1];
        for row in samples {
            if direct_eq_weight(row, point) != factored_eq_weight(row, tables)? {
                return Err(R0InputError::IdentityMismatch("equality samples"));
            }
        }
        Ok(EqualityCheckCoverage::Sampled {
            checked_rows: samples,
        })
    }
}

fn bit_mask(bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        (1usize << bits) - 1
    }
}

fn hash_direct_equality(point: &[FrozenE4]) -> Result<String, R0InputError> {
    let mut hash = Sha256Writer::new()?;
    for row in 0..1usize << point.len() {
        hash.write_e4(direct_eq_weight(row, point))?;
    }
    hash.finish()
}

fn hash_factored_equality(tables: &R0FactoredEqTables) -> Result<String, R0InputError> {
    hash_e4_values(
        tables.high[0]
            .iter()
            .chain(&tables.high[1])
            .chain(&tables.low)
            .copied(),
    )
}

fn hash_e4_values(values: impl IntoIterator<Item = E4>) -> Result<String, R0InputError> {
    let mut hash = Sha256Writer::new()?;
    for value in values {
        hash.write_e4(value)?;
    }
    hash.finish()
}

struct SourceHashes {
    all: String,
    independent: String,
    derived: Option<String>,
}

#[cfg(test)]
thread_local! {
    static SOURCE_HASH_TRAVERSAL_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
fn reset_source_hash_traversal_count() {
    SOURCE_HASH_TRAVERSAL_COUNT.set(0);
}

#[cfg(test)]
fn source_hash_traversal_count() -> usize {
    SOURCE_HASH_TRAVERSAL_COUNT.get()
}

fn hash_source_classes(
    sources: &R0HostSources,
    derived_spans: &[DerivedSpan],
    canonical_only_sources: &[CanonicalSource],
) -> Result<SourceHashes, R0InputError> {
    #[cfg(test)]
    SOURCE_HASH_TRAVERSAL_COUNT.set(SOURCE_HASH_TRAVERSAL_COUNT.get() + 1);
    let mut all = Sha256Writer::new()?;
    let mut independent = Sha256Writer::new()?;
    let mut derived = (!derived_spans.is_empty())
        .then(Sha256Writer::new)
        .transpose()?;
    for source in canonical_only_sources {
        match &source.backing {
            R0HostBacking::Bf(values) => {
                for value in values.iter().copied() {
                    all.write_bf(value)?;
                    independent.write_bf(value)?;
                }
            }
            R0HostBacking::E4(values) => {
                for value in values.iter().copied() {
                    all.write_e4(value)?;
                    independent.write_e4(value)?;
                }
            }
        }
    }
    for (backing_index, backing) in sources.backings.iter().enumerate() {
        match backing {
            R0HostBacking::Bf(values) => {
                for (element, value) in values.iter().copied().enumerate() {
                    all.write_bf(value)?;
                    if is_derived_element(derived_spans, backing_index, element) {
                        derived
                            .as_mut()
                            .expect("derived hash exists")
                            .write_bf(value)?;
                    } else {
                        independent.write_bf(value)?;
                    }
                }
            }
            R0HostBacking::E4(values) => {
                for (element, value) in values.iter().copied().enumerate() {
                    all.write_e4(value)?;
                    if is_derived_element(derived_spans, backing_index, element) {
                        derived
                            .as_mut()
                            .expect("derived hash exists")
                            .write_e4(value)?;
                    } else {
                        independent.write_e4(value)?;
                    }
                }
            }
        }
    }
    Ok(SourceHashes {
        all: all.finish()?,
        independent: independent.finish()?,
        derived: derived.map(Sha256Writer::finish).transpose()?,
    })
}

fn is_derived_element(spans: &[DerivedSpan], backing: usize, element: usize) -> bool {
    spans.iter().any(|span| {
        span.backing_index == backing
            && element >= span.first_element
            && element < span.first_element + span.element_count
    })
}

struct Sha256Writer {
    child: Child,
    stdin: Option<BufWriter<ChildStdin>>,
}

fn buffered_hash_input<W: Write>(writer: W) -> BufWriter<W> {
    BufWriter::with_capacity(R0_HASH_BUFFER_BYTES, writer)
}

#[cfg(test)]
fn hash_write_call_upper_bound(encoded_bytes: u64) -> u64 {
    let buffer_bytes = R0_HASH_BUFFER_BYTES as u64;
    encoded_bytes / buffer_bytes + u64::from(encoded_bytes % buffer_bytes != 0)
}

impl Sha256Writer {
    fn new() -> Result<Self, R0InputError> {
        let mut child = Command::new("sha256sum")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|error| R0InputError::Hash(format!("run sha256sum: {error}")))?;
        let stdin = child.stdin.take().map(buffered_hash_input);
        Ok(Self { child, stdin })
    }

    fn write_bf(&mut self, value: BF) -> Result<(), R0InputError> {
        self.write_all(&value.as_u32_reduced().to_le_bytes())
    }

    fn write_e4(&mut self, value: E4) -> Result<(), R0InputError> {
        for limb in FrozenE4::from_e4(value).limbs {
            self.write_all(&limb.to_le_bytes())?;
        }
        Ok(())
    }

    fn write_all(&mut self, bytes: &[u8]) -> Result<(), R0InputError> {
        self.stdin
            .as_mut()
            .ok_or_else(|| R0InputError::Hash("sha256sum stdin is closed".to_owned()))?
            .write_all(bytes)
            .map_err(|error| R0InputError::Hash(format!("write sha256sum stdin: {error}")))
    }

    fn finish(mut self) -> Result<String, R0InputError> {
        if let Some(stdin) = self.stdin.as_mut() {
            stdin
                .flush()
                .map_err(|error| R0InputError::Hash(format!("flush sha256sum stdin: {error}")))?;
        }
        drop(self.stdin.take());
        let output = self
            .child
            .wait_with_output()
            .map_err(|error| R0InputError::Hash(format!("wait for sha256sum: {error}")))?;
        if !output.status.success() {
            return Err(R0InputError::Hash("sha256sum failed".to_owned()));
        }
        let output = String::from_utf8(output.stdout)
            .map_err(|_| R0InputError::Hash("sha256sum output is not UTF-8".to_owned()))?;
        let value = output.split_whitespace().next().unwrap_or_default();
        if value.len() != 64
            || !value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(R0InputError::Hash(
                "sha256sum output is not lowercase SHA-256".to_owned(),
            ));
        }
        Ok(value.to_owned())
    }
}

fn hash_bytes(bytes: &[u8]) -> Result<String, R0InputError> {
    let mut hash = Sha256Writer::new()?;
    hash.write_all(bytes)?;
    hash.finish()
}

fn lift(value: BF) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(value)
}

fn e4_sub(mut left: E4, right: E4) -> E4 {
    left.sub_assign(&right);
    left
}

fn deterministic_bf(seed: u64, domain: u64, index: u64, component: u64) -> BF {
    let value =
        splitmix64(seed ^ domain.rotate_left(17) ^ index.wrapping_mul(0x9e37_79b9) ^ component);
    BF::from_u32_with_reduction(value as u32)
}

fn deterministic_e4(seed: u64, domain: u64, index: u64) -> E4 {
    E4::from_array_of_base([
        deterministic_bf(seed, domain, index, 0),
        deterministic_bf(seed, domain, index, 1),
        deterministic_bf(seed, domain, index, 2),
        deterministic_bf(seed, domain, index, 3),
    ])
}

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn virtual_setup_tag(kind: &VirtualSetupKind) -> u8 {
    match kind {
        VirtualSetupKind::RangeCheck16Bits => 0,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    }
}

fn procedural_raw(kind: u8, index: usize) -> u32 {
    let index = index as u32;
    match kind {
        0 => u32::from(index < (1 << 16)) * index,
        1 => u32::from(index < (1 << 19)) * index,
        2 => (index << 2) & 0xffff,
        3 => index >> 14,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r0_artifact::{decode_r0_bundle, FrozenR0Coordinate, R0_CORPUS_BYTES};
    use gpu_gkr_compiler::backward::{CoeffProduct, NormalizedCoefficientRecipe};

    #[derive(Debug, Default)]
    struct CountingWriter {
        bytes: u64,
        writes: u64,
    }

    impl Write for CountingWriter {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.bytes += bytes.len() as u64;
            self.writes += 1;
            Ok(bytes.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn cpu_source_hash_writer_batches_element_writes_with_production_bound() {
        let sink = CountingWriter::default();
        let mut writer = buffered_hash_input(sink);
        let element_writes = 1_048_576u64;
        for index in 0..element_writes {
            writer.write_all(&(index as u32).to_le_bytes()).unwrap();
        }
        writer.flush().unwrap();
        let sink = writer.into_inner().unwrap();
        assert_eq!(sink.bytes, element_writes * 4);
        assert!(
            sink.writes <= 5,
            "observed {} underlying writes",
            sink.writes
        );

        // The largest Task 9 source set is 28,722,593,792 bytes. Hashing all
        // plus its traffic-only independent class streams each byte twice.
        let largest_production_hash_bytes = 2 * 28_722_593_792u64;
        assert!(hash_write_call_upper_bound(largest_production_hash_bytes) <= 54_784);
    }

    #[test]
    fn cpu_source_hash_writer_preserves_bf_e4_byte_stream() {
        let mut writer = Sha256Writer::new().unwrap();
        writer.write_bf(BF::from_u32_with_reduction(1)).unwrap();
        writer
            .write_e4(E4::from_array_of_base([
                BF::from_u32_with_reduction(2),
                BF::from_u32_with_reduction(3),
                BF::from_u32_with_reduction(4),
                BF::from_u32_with_reduction(5),
            ]))
            .unwrap();
        assert_eq!(
            writer.finish().unwrap(),
            "4f6addc9659d6fb90fe94b6688a79f2a1fa8d36ec43f8f3e1d9b6528c448a384"
        );
    }

    fn fixture_coordinate_at(layer: u32) -> FrozenR0Coordinate {
        decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == layer
            })
            .unwrap()
    }

    fn fixture_coordinate() -> FrozenR0Coordinate {
        fixture_coordinate_at(0)
    }

    fn fixture_dag(coordinate: &FrozenR0Coordinate) -> gkr_eval_ir::DagCircuit {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits")
            .join(format!("{}_layout_gkr.json", coordinate.circuit));
        let bytes = std::fs::read(path).unwrap();
        let artifact: GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        gkr_eval_ir::validate(&dag).unwrap();
        dag
    }

    fn fixture_resolved_input(log_trace: u32) -> ResolvedR0Input {
        build_r0_input(&fixture_coordinate(), log_trace, 7).unwrap()
    }

    #[test]
    fn cpu_production_input_is_traffic_only_without_canonical_dag() {
        let mut coordinate = fixture_coordinate();
        coordinate.circuit = "missing_production_layout".to_owned();
        let input = build_r0_production_input(&coordinate, 3, R0_PRODUCTION_SEED).unwrap();
        assert_eq!(input.identity.derived_source_sha256, None);
        assert_eq!(
            input.identity.source_data_sha256,
            input.identity.independent_source_sha256
        );
        assert!(input.derived_spans.is_empty());
        assert!(input.canonical_only_sources.is_empty());
    }

    #[test]
    fn cpu_prepared_production_input_hashes_source_classes_exactly_once() {
        reset_source_hash_traversal_count();
        let coordinate = fixture_coordinate();
        let prepared =
            build_prepared_r0_production_input(&coordinate, 3, R0_PRODUCTION_SEED).unwrap();
        assert_eq!(source_hash_traversal_count(), 1);
        assert_eq!(prepared.resolved().identity.circuit, coordinate.circuit);

        let prepared_input = prepared.resolved().clone();
        reset_source_hash_traversal_count();
        let checked = build_r0_production_input(&coordinate, 3, R0_PRODUCTION_SEED).unwrap();
        assert_eq!(source_hash_traversal_count(), 2);
        assert_eq!(prepared_input, checked);
    }

    #[test]
    fn cpu_production_input_hash_covers_each_complete_backing() {
        let coordinate = fixture_coordinate();
        let input = build_r0_production_input(&coordinate, 3, R0_PRODUCTION_SEED).unwrap();
        for (backing_index, backing) in input.sources.backings.iter().enumerate() {
            let len = match backing {
                R0HostBacking::Bf(values) => values.len(),
                R0HostBacking::E4(values) => values.len(),
            };
            for element_index in [0, len / 2, len - 1] {
                let mut mutated = input.clone();
                match &mut mutated.sources.backings[backing_index] {
                    R0HostBacking::Bf(values) => {
                        values[element_index].add_assign(&BF::ONE);
                    }
                    R0HostBacking::E4(values) => {
                        values[element_index].add_assign(&E4::ONE);
                    }
                }
                refresh_r0_input_hashes(&mut mutated).unwrap();
                assert_ne!(
                    mutated.identity.source_data_sha256,
                    input.identity.source_data_sha256
                );
                assert_ne!(
                    mutated.identity.independent_source_sha256,
                    input.identity.independent_source_sha256
                );
                assert_eq!(mutated.identity.derived_source_sha256, None);
            }
        }
    }

    #[test]
    fn cpu_production_validator_rejects_rehashed_traffic_mutation() {
        let coordinate = fixture_coordinate();
        let input = build_r0_production_input(&coordinate, 3, R0_PRODUCTION_SEED).unwrap();
        let mut mutated = input.clone();
        match &mut mutated.sources.backings[0] {
            R0HostBacking::Bf(values) => {
                values[0].add_assign(&BF::ONE);
            }
            R0HostBacking::E4(values) => {
                values[0].add_assign(&E4::ONE);
            }
        }
        refresh_r0_input_hashes(&mut mutated).unwrap();
        validate_r0_input(&mutated).unwrap();
        assert!(validate_r0_production_input(&coordinate, &mutated).is_err());
    }

    fn source_function_body<'a>(source: &'a str, signature: &str) -> &'a str {
        let start = source.find(signature).unwrap();
        let source = &source[start..];
        let open = source.find('{').unwrap();
        let mut depth = 0usize;
        for (offset, byte) in source[open..].bytes().enumerate() {
            match byte {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        return &source[..open + offset + 1];
                    }
                }
                _ => {}
            }
        }
        panic!("function {signature} has no closing brace")
    }

    #[test]
    fn cpu_r0_input_hash_changes_with_every_semantic_input() {
        let coordinate = fixture_coordinate();
        let a = build_r0_input(&coordinate, 8, 7).unwrap();
        let b = build_r0_input(&coordinate, 8, 8).unwrap();
        assert_ne!(a.identity.input_sha256, b.identity.input_sha256);
        assert_eq!(a.identity.equality_point.len(), 5);
        assert!(!a.identity.challenge_values.is_empty());
        assert_ne!(
            a.identity.independent_source_sha256,
            a.identity.coefficient_sha256
        );
        assert!(a.identity.derived_source_sha256.is_some());
        assert_ne!(
            Some(a.identity.independent_source_sha256.clone()),
            a.identity.derived_source_sha256,
        );
    }

    #[test]
    fn cpu_layer1_canonical_only_cross_layer_read_uses_producer_field() {
        let coordinate = fixture_coordinate_at(1);
        let dag = fixture_dag(&coordinate);
        let layer = &dag.layers[coordinate.layer as usize];
        let place = ReadPlace::LayerOutput {
            layer: 1,
            offset: 0,
        };
        let compiler_fields = gpu_gkr_compiler::analysis::build_cross_layer_field_map(&dag);
        let cross_fields = canonical_cross_layer_fields(&dag, coordinate.layer as usize);
        assert_eq!(gkr_eval_ir::read_place_field(&place), None);
        assert!(dag
            .layers
            .iter()
            .flat_map(|layer| &layer.roots)
            .any(|root| {
                matches!(
                    root.materialize.as_ref(),
                    Some(gkr_eval_ir::SinkInfo {
                        kind: SinkKind::Inner {
                            layer: 1,
                            offset: 0,
                        },
                        field: FieldKind::Base,
                    })
                )
            }));
        assert_eq!(compiler_fields.get(&place), Some(&FieldKind::Base));
        assert_eq!(cross_fields.get(&place), Some(&FieldKind::Base));
        assert!(classify_sources(layer, &coordinate.binding)
            .unwrap()
            .reads
            .contains(&place));
        assert!(coordinate.binding.windows.iter().all(|window| {
            place_column_in_family(&place, &window.family).is_none_or(|column| {
                window
                    .columns
                    .binary_search_by_key(&column, |entry| entry.column)
                    .is_err()
            })
        }));

        let input = build_r0_input(&coordinate, 3, 0).unwrap();
        let source = input
            .canonical_only_sources
            .iter()
            .find(|source| source.place == place)
            .unwrap();
        assert!(matches!(source.backing, R0HostBacking::Bf(_)));
    }

    #[test]
    fn cpu_cross_layer_field_map_matches_validator_publication_boundary() {
        let layer = |sinks: Vec<gkr_eval_ir::SinkInfo>| DagLayer {
            sources: Vec::new(),
            exprs: Vec::new(),
            roots: sinks
                .into_iter()
                .map(|sink| gkr_eval_ir::Root {
                    expr: ExprId(0),
                    materialize: Some(sink),
                    claim: None,
                })
                .collect(),
            batching: gkr_eval_ir::BatchingOrder { roots: Vec::new() },
            resolutions: BTreeMap::new(),
            forward_skip_roots: Default::default(),
        };
        let dag = DagCircuit {
            layers: vec![
                layer(vec![
                    gkr_eval_ir::SinkInfo {
                        kind: SinkKind::Inner {
                            layer: 1,
                            offset: 4,
                        },
                        field: FieldKind::Base,
                    },
                    gkr_eval_ir::SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 0,
                            offset: 5,
                        },
                        field: FieldKind::Ext,
                    },
                    gkr_eval_ir::SinkInfo {
                        kind: SinkKind::Scratch { slot: 6 },
                        field: FieldKind::Base,
                    },
                ]),
                layer(vec![gkr_eval_ir::SinkInfo {
                    kind: SinkKind::Inner {
                        layer: 2,
                        offset: 8,
                    },
                    field: FieldKind::Ext,
                }]),
                layer(vec![gkr_eval_ir::SinkInfo {
                    kind: SinkKind::Cache {
                        layer: 2,
                        offset: 9,
                    },
                    field: FieldKind::Base,
                }]),
            ],
        };

        assert_eq!(
            canonical_cross_layer_fields(&dag, 1),
            HashMap::from([
                (
                    ReadPlace::LayerOutput {
                        layer: 1,
                        offset: 4,
                    },
                    FieldKind::Base,
                ),
                (
                    ReadPlace::CacheOutput {
                        layer: 0,
                        offset: 5,
                    },
                    FieldKind::Ext,
                ),
            ])
        );
    }

    #[test]
    fn cpu_all_corpus_coordinates_build_log3_inputs() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        assert_eq!(bundle.coordinates.len(), 57);
        for coordinate in &bundle.coordinates {
            build_r0_input(coordinate, 3, 0).unwrap_or_else(|error| {
                panic!(
                    "{}:{} log3 input failed: {error:?}",
                    coordinate.circuit, coordinate.layer
                )
            });
        }
    }

    #[test]
    fn cpu_direct_and_factored_eq_are_equal_but_built_separately() {
        let input = fixture_resolved_input(8);
        for row in 0..32 {
            assert_eq!(
                direct_eq_weight(row, &input.identity.equality_point),
                factored_eq_weight(row, &input.eq_tables).unwrap(),
            );
        }
    }

    #[test]
    fn cpu_factored_table_builder_does_not_call_the_direct_oracle() {
        let source = include_str!("r0_input.rs");
        let body = source_function_body(source, "fn build_eq_group(");
        assert!(
            !body.contains("direct_eq_weight"),
            "factored group construction must not call the direct equality oracle"
        );
    }

    #[test]
    fn cpu_production_log24_equality_uses_fixed_sample_rows() {
        let coordinate = fixture_coordinate();
        assert_eq!(coordinate.trace_len, 1 << 24);
        let log_trace = coordinate.trace_len.ilog2();
        assert_eq!(log_trace, 24);
        let point = (0..log_trace - 3)
            .map(|index| {
                FrozenE4::from_e4(deterministic_e4(7, 0x4551_504f_494e_5400, index as u64))
            })
            .collect::<Vec<_>>();
        let tables = build_factored_eq_tables(&point).unwrap();
        let rows = 1usize << point.len();

        assert_eq!(
            check_equality_algorithms(&point, &tables).unwrap(),
            EqualityCheckCoverage::Sampled {
                checked_rows: [0, 1, rows / 3, rows / 2, rows - 2, rows - 1],
            }
        );
    }

    #[test]
    fn cpu_log3_equality_has_one_identity_low_entry() {
        let input = fixture_resolved_input(3);
        assert_eq!(input.identity.equality_point.len(), 0);
        assert_eq!(input.identity.eq_sizes.high, [0, 0]);
        assert_eq!(input.identity.eq_sizes.low, 0);
        assert_eq!(input.eq_tables.high, [Vec::new(), Vec::new()]);
        assert_eq!(input.eq_tables.low, vec![E4::ONE]);
        assert_eq!(direct_eq_weight(0, &[]), E4::ONE);
        assert_eq!(factored_eq_weight(0, &input.eq_tables).unwrap(), E4::ONE);
    }

    #[test]
    fn cpu_input_hash_covers_each_semantic_input_class() {
        let input = fixture_resolved_input(8);
        let original = input.identity.input_sha256.clone();

        let mut challenge_base = input.clone();
        challenge_base.identity.challenge_bases[0].value.limbs[0] ^= 1;
        refresh_r0_input_hashes(&mut challenge_base).unwrap();

        let mut challenge_value = input.clone();
        challenge_value.identity.challenge_values[0].value.limbs[0] ^= 1;
        refresh_r0_input_hashes(&mut challenge_value).unwrap();

        let mut equality = input.clone();
        equality.identity.equality_point[0].limbs[0] ^= 1;
        refresh_r0_input_hashes(&mut equality).unwrap();

        let mut independent_source = input.clone();
        match &mut independent_source.canonical_only_sources[0].backing {
            R0HostBacking::Bf(values) => {
                let raw = values[0].as_u32_reduced() ^ 1;
                values[0] = BF::from_u32_with_reduction(raw);
            }
            R0HostBacking::E4(values) => {
                let raw = values[0].c0.c0.as_u32_reduced() ^ 1;
                values[0].c0.c0 = BF::from_u32_with_reduction(raw);
            }
        }
        refresh_r0_input_hashes(&mut independent_source).unwrap();

        let mut derived_source = input.clone();
        let span = derived_source.derived_spans[0].clone();
        match &mut derived_source.sources.backings[span.backing_index] {
            R0HostBacking::Bf(values) => {
                let raw = values[span.first_element].as_u32_reduced() ^ 1;
                values[span.first_element] = BF::from_u32_with_reduction(raw);
            }
            R0HostBacking::E4(values) => {
                let raw = values[span.first_element].c0.c0.as_u32_reduced() ^ 1;
                values[span.first_element].c0.c0 = BF::from_u32_with_reduction(raw);
            }
        }
        refresh_r0_input_hashes(&mut derived_source).unwrap();

        let mut coefficient = input.clone();
        let raw = coefficient.coefficient_bank[0].c0.c0.as_u32_reduced() ^ 1;
        coefficient.coefficient_bank[0].c0.c0 = BF::from_u32_with_reduction(raw);
        refresh_r0_input_hashes(&mut coefficient).unwrap();

        for (name, hash) in [
            ("challenge base", challenge_base.identity.input_sha256),
            ("challenge value", challenge_value.identity.input_sha256),
            ("equality", equality.identity.input_sha256),
            (
                "independent source",
                independent_source.identity.input_sha256,
            ),
            ("derived source", derived_source.identity.input_sha256),
            ("coefficient", coefficient.identity.input_sha256),
        ] {
            assert_ne!(hash, original, "{name} mutation was not hash-bound");
        }
    }

    #[test]
    fn cpu_challenge_assignment_has_explicit_order_and_canonical_references() {
        let input = fixture_resolved_input(8);
        assert_eq!(
            input
                .identity
                .challenge_bases
                .iter()
                .map(|entry| entry.key.clone())
                .collect::<Vec<_>>(),
            stable_challenge_keys(),
        );
        assert_eq!(input.identity.challenge_bases.len(), 10);
        for value in &input.identity.challenge_values {
            assert_eq!(
                CoeffChallenge::new(value.challenge.reference.clone()).0,
                value.challenge.reference,
            );
        }
    }

    struct UpstreamRecipeResolver<'a>(ChallengeAssignment<'a>);

    impl ChallengeResolver for UpstreamRecipeResolver<'_> {
        fn challenge(&self, reference: &ChallengeRef) -> E4 {
            self.0.resolve_recipe(reference).unwrap()
        }
    }

    #[test]
    fn cpu_recipe_bank_matches_normalized_recipe_evaluation() {
        let coordinate = fixture_coordinate();
        let bases = build_challenge_bases(7);
        let actual = resolve_r0_coefficients(&coordinate.recipes, &bases).unwrap();
        let resolver = UpstreamRecipeResolver(ChallengeAssignment { bases: &bases });
        let expected = coordinate
            .recipes
            .iter()
            .map(|recipe| NormalizedCoefficientRecipe {
                terms: recipe
                    .products
                    .iter()
                    .map(|product| CoeffProduct {
                        scalar: product.scalar,
                        challenges: product
                            .challenges
                            .iter()
                            .map(|challenge| CoeffChallenge::new(challenge.reference.clone()))
                            .collect(),
                        inits_and_teardowns_top_bits: product.inits_and_teardowns_top_bits.clone(),
                    })
                    .collect(),
            })
            .map(|recipe| recipe.evaluate(&resolver))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn cpu_recipe_resolution_rejects_ambiguous_ignoring_power() {
        let coordinate = fixture_coordinate();
        let input = fixture_resolved_input(8);
        let bases = build_challenge_bases(7);
        let mut recipes = coordinate.recipes.clone();
        let mut ignoring = input
            .identity
            .challenge_values
            .iter()
            .find(|challenge| {
                matches!(
                    challenge.challenge.reference.key,
                    ChallengeKey::LookupAdditive
                        | ChallengeKey::PermutationAdditive
                        | ChallengeKey::PermutationLinearization(_)
                )
            })
            .unwrap()
            .challenge
            .clone();
        ignoring.reference.power = ChallengePower::Static(2);
        recipes[0].products[0].challenges.push(ignoring);
        assert!(matches!(
            resolve_r0_coefficients(&recipes, &bases),
            Err(R0InputError::AmbiguousChallengePower { power: 2, .. })
        ));
    }
}
