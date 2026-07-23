use std::io::Write;
use std::ops::RangeInclusive;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bwd::distill::{DistilledLayer, StableBwdConsumer, StableBwdExprKey, StableBwdSiteKey};
use crate::bwd::fragment::FactorKey;
use crate::bwd::source::{BwdSpecial, FoldState, OriginLeaf};
use crate::eval_plan::backward::CompiledBackwardEvaluation;
use crate::fwd::binding::{BackingKey, SourceWindowTable};
use crate::fwd::isa::OperandField;
use crate::fwd::source::virtual_setup_kind_code;

use super::artifact::{DomainCertificate, EvaluationArtifactError, certificate_from_serializable};
use super::backward_search::pager::PagingAction;
use super::backward_search::problem::{
    BackwardSearchProblem, build_backward_search_problem, decode_order_indices,
    rebuild_problem_for_stable_order,
};
use super::backward_search::production::{
    ProductionBackwardPlan, ProductionSearchIdentity, ProductionSearchProgress,
    select_production_backward_seeds_with_progress,
};
use super::backward_search::{
    BackwardScore, BackwardSearchError, CertifiedBackwardCandidate, PagingCertificate, SourceCost,
    SourceOriginKind, compile_and_certify_paging, reconstruct_paging_plan,
};

const MIN_BUDGET_CELLS: usize = 2;
const MAX_BUDGET_CELLS: usize = 16;
const BUDGET_PLAN_COUNT: usize = MAX_BUDGET_CELLS - MIN_BUDGET_CELLS + 1;
static PUBLICATION_NONCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonicalU128(u128);

impl CanonicalU128 {
    pub fn value(self) -> u128 {
        self.0
    }
}

impl From<u128> for CanonicalU128 {
    fn from(value: u128) -> Self {
        Self(value)
    }
}

impl Serialize for CanonicalU128 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0.to_string())
    }
}

impl<'de> Deserialize<'de> for CanonicalU128 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        let canonical = !value.is_empty()
            && value.bytes().all(|byte| byte.is_ascii_digit())
            && (value == "0" || !value.starts_with('0'));
        if !canonical {
            return Err(serde::de::Error::custom(
                "expected canonical unsigned decimal u128",
            ));
        }
        value
            .parse()
            .map(Self)
            .map_err(|_| serde::de::Error::custom("u128 decimal is out of range"))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceCostArtifact {
    pub plain_read_bytes: CanonicalU128,
    pub lazy_read_bytes: CanonicalU128,
    pub materialized_read_bytes: CanonicalU128,
    pub materialization_write_bytes: CanonicalU128,
    pub bf_add: CanonicalU128,
    pub bf_mul: CanonicalU128,
    pub mixed_add: CanonicalU128,
    pub mixed_mul: CanonicalU128,
    pub ext_add: CanonicalU128,
    pub ext_mul: CanonicalU128,
}

impl From<SourceCost> for SourceCostArtifact {
    fn from(cost: SourceCost) -> Self {
        Self {
            plain_read_bytes: cost.plain_read_bytes.into(),
            lazy_read_bytes: cost.lazy_read_bytes.into(),
            materialized_read_bytes: cost.materialized_read_bytes.into(),
            materialization_write_bytes: cost.materialization_write_bytes.into(),
            bf_add: cost.ops.bf_add.into(),
            bf_mul: cost.ops.bf_mul.into(),
            mixed_add: cost.ops.mixed_add.into(),
            mixed_mul: cost.ops.mixed_mul.into(),
            ext_add: cost.ops.ext_add.into(),
            ext_mul: cost.ops.ext_mul.into(),
        }
    }
}

impl SourceCostArtifact {
    pub(crate) fn matches_cost(&self, cost: SourceCost) -> bool {
        self == &Self::from(cost)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackwardScoreArtifact {
    pub infeasible: bool,
    pub whole_pass_dram_bytes: CanonicalU128,
    pub primitive_source_ops: CanonicalU128,
    pub instructions: usize,
    pub encoded_lanes: usize,
    pub arithmetic_ops: usize,
}

impl BackwardScoreArtifact {
    pub fn from_score(score: &BackwardScore) -> Self {
        Self {
            infeasible: score.infeasible,
            whole_pass_dram_bytes: score.whole_pass_dram_bytes.into(),
            primitive_source_ops: score.primitive_source_ops.into(),
            instructions: score.instructions,
            encoded_lanes: score.encoded_lanes,
            arithmetic_ops: score.arithmetic_ops,
        }
    }

    pub(crate) fn matches_score(&self, score: &BackwardScore) -> bool {
        self.infeasible == score.infeasible
            && self.whole_pass_dram_bytes.value() == score.whole_pass_dram_bytes
            && self.primitive_source_ops.value() == score.primitive_source_ops
            && self.instructions == score.instructions
            && self.encoded_lanes == score.encoded_lanes
            && self.arithmetic_ops == score.arithmetic_ops
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackwardPagingCertificateArtifact {
    pub actions_consumed: usize,
    pub diverged: Option<usize>,
    pub refused_retains: usize,
    pub predicted_source_reads: u64,
    pub realized_source_reads: u64,
    pub predicted_read_cost: SourceCostArtifact,
    pub realized_read_cost: SourceCostArtifact,
    pub fixed_write_cost: SourceCostArtifact,
    pub peak_live_lanes: usize,
    pub placement_relocations: usize,
}

impl BackwardPagingCertificateArtifact {
    pub(crate) fn from_certificate(certificate: &PagingCertificate) -> Self {
        Self {
            actions_consumed: certificate.actions_consumed,
            diverged: certificate.diverged,
            refused_retains: certificate.refused_retains,
            predicted_source_reads: certificate.predicted_source_reads,
            realized_source_reads: certificate.realized_source_reads,
            predicted_read_cost: certificate.predicted_read_cost.into(),
            realized_read_cost: certificate.realized_read_cost.into(),
            fixed_write_cost: certificate.fixed_write_cost.into(),
            peak_live_lanes: certificate.peak_live_lanes,
            placement_relocations: certificate.placement_relocations,
        }
    }

    pub(crate) fn matches_certificate(&self, certificate: &PagingCertificate) -> bool {
        self == &Self::from_certificate(certificate)
    }
}

pub type BackwardProblemCertificate = DomainCertificate;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackwardPlanArtifact {
    pub budget_cells: usize,
    pub problem: BackwardProblemCertificate,
    pub fragment_order: Vec<u32>,
    pub retained_demands: Vec<u32>,
    pub expected_score: BackwardScoreArtifact,
    pub expected_paging: BackwardPagingCertificateArtifact,
    pub instruction_digest: [u64; 4],
    pub encoded_digest: [u64; 4],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackwardRegimeArtifact {
    pub plans: Vec<BackwardPlanArtifact>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackwardRegimeChainProgress {
    Search {
        budget_cells: usize,
        search: ProductionSearchProgress,
    },
    Completed {
        budget_cells: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackwardLayerArtifact {
    pub layer: usize,
    pub r0: BackwardRegimeArtifact,
    pub ext: BackwardRegimeArtifact,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackwardEvaluationCircuitArtifact {
    pub circuit: String,
    pub layout_fixture: String,
    pub layers: Vec<BackwardLayerArtifact>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackwardArtifactCoordinate {
    pub circuit: String,
    pub layer: usize,
    pub regime: BwdRegime,
    pub budget_cells: usize,
}

#[derive(Debug)]
pub enum BackwardArtifactError {
    Load(String),
    Domain(EvaluationArtifactError),
    Search(BackwardSearchError),
    CircuitMismatch {
        expected: String,
        actual: String,
    },
    LayoutFixtureMismatch {
        expected: String,
        actual: String,
    },
    DuplicateOrUnorderedLayer {
        layer: usize,
    },
    MissingLayer {
        coordinate: BackwardArtifactCoordinate,
    },
    InvalidBudgetCoverage {
        coordinate: BackwardArtifactCoordinate,
    },
    BudgetOutOfRange {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    ProblemCertificateMismatch {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    InvalidFragmentPermutation {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    InvalidRetainedDemand {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
        position: usize,
    },
    ScoreCertificateMismatch {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    PagingCertificateMismatch {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    InstructionDigestMismatch {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    EncodedDigestMismatch {
        circuit: String,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    ReplaySearch {
        coordinate: BackwardArtifactCoordinate,
        source: BackwardSearchError,
    },
    IncompleteGeneration {
        failures: Vec<BackwardArtifactCoordinate>,
    },
    Publish(String),
}

impl From<EvaluationArtifactError> for BackwardArtifactError {
    fn from(value: EvaluationArtifactError) -> Self {
        Self::Domain(value)
    }
}

impl From<BackwardSearchError> for BackwardArtifactError {
    fn from(value: BackwardSearchError) -> Self {
        Self::Search(value)
    }
}

impl BackwardEvaluationCircuitArtifact {
    pub fn new(
        circuit: impl Into<String>,
        layout_fixture: impl Into<String>,
        layers: Vec<BackwardLayerArtifact>,
    ) -> Result<Self, BackwardArtifactError> {
        let artifact = Self {
            circuit: circuit.into(),
            layout_fixture: layout_fixture.into(),
            layers,
        };
        artifact.validate_self_consistency()?;
        Ok(artifact)
    }

    pub fn validate_self_consistency(&self) -> Result<(), BackwardArtifactError> {
        if self.circuit.is_empty() {
            return Err(BackwardArtifactError::CircuitMismatch {
                expected: "nonempty circuit".to_owned(),
                actual: self.circuit.clone(),
            });
        }
        if self.layout_fixture.is_empty() {
            return Err(BackwardArtifactError::LayoutFixtureMismatch {
                expected: "nonempty layout fixture".to_owned(),
                actual: self.layout_fixture.clone(),
            });
        }
        for layers in self.layers.windows(2) {
            if layers[0].layer >= layers[1].layer {
                return Err(BackwardArtifactError::DuplicateOrUnorderedLayer {
                    layer: layers[1].layer,
                });
            }
        }
        for layer in &self.layers {
            validate_regime(&self.circuit, layer.layer, BwdRegime::R0, &layer.r0)?;
            validate_regime(&self.circuit, layer.layer, BwdRegime::Ext, &layer.ext)?;
        }
        Ok(())
    }
}

fn produce_regime_chain_with<T>(
    identity: &ProductionSearchIdentity,
    budgets: RangeInclusive<usize>,
    mut produce: impl FnMut(usize, Option<&[usize]>) -> Result<(T, Vec<usize>), BackwardArtifactError>,
) -> Result<Vec<T>, BackwardArtifactError> {
    let mut plans = Vec::new();
    let mut preceding_order = None;
    let mut failures = Vec::new();
    for budget_cells in budgets {
        match produce(budget_cells, preceding_order.as_deref()) {
            Ok((plan, order)) => {
                plans.push(plan);
                preceding_order = Some(order);
            }
            Err(BackwardArtifactError::Search(
                BackwardSearchError::ProductionPagerResourceLimit { .. },
            )) => {
                failures.push(BackwardArtifactCoordinate {
                    circuit: identity.circuit.clone(),
                    layer: identity.layer,
                    regime: identity.regime,
                    budget_cells,
                });
                preceding_order = None;
            }
            Err(error) => return Err(error),
        }
    }
    if failures.is_empty() {
        Ok(plans)
    } else {
        Err(BackwardArtifactError::IncompleteGeneration { failures })
    }
}

pub fn produce_backward_regime_chain(
    identity: &ProductionSearchIdentity,
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budgets: RangeInclusive<usize>,
) -> Result<BackwardRegimeArtifact, BackwardArtifactError> {
    produce_backward_regime_chain_with_progress(
        identity,
        canonical,
        distilled,
        trace_len,
        budgets,
        &|_| {},
    )
}

pub fn produce_backward_regime_chain_with_progress(
    identity: &ProductionSearchIdentity,
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budgets: RangeInclusive<usize>,
    progress: &(dyn Fn(BackwardRegimeChainProgress) + Sync),
) -> Result<BackwardRegimeArtifact, BackwardArtifactError> {
    let plans = produce_regime_chain_with(identity, budgets, |budget_cells, preceding_order| {
        let searched = select_production_backward_seeds_with_progress(
            identity,
            canonical,
            distilled,
            trace_len,
            budget_cells,
            preceding_order,
            &|search| {
                progress(BackwardRegimeChainProgress::Search {
                    budget_cells,
                    search,
                });
            },
        )?;
        let order = searched.order.clone();
        let artifact = capture_backward_plan_artifact(&searched)?;
        progress(BackwardRegimeChainProgress::Completed { budget_cells });
        Ok((artifact, order))
    })?;
    Ok(BackwardRegimeArtifact { plans })
}

pub fn publish_backward_evaluation_artifact(
    path: &Path,
    artifact: &BackwardEvaluationCircuitArtifact,
    validator: impl FnOnce(&BackwardEvaluationCircuitArtifact) -> Result<(), BackwardArtifactError>,
) -> Result<(), BackwardArtifactError> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            BackwardArtifactError::Publish(format!("invalid destination {}", path.display()))
        })?;
    let nonce = PUBLICATION_NONCE.fetch_add(1, Ordering::Relaxed);
    let temporary = parent.join(format!(".{file_name}.tmp-{}-{nonce}", std::process::id(),));

    publish_backward_evaluation_artifact_to_temporary(path, &temporary, artifact, validator)
}

fn publish_backward_evaluation_artifact_to_temporary(
    path: &Path,
    temporary: &Path,
    artifact: &BackwardEvaluationCircuitArtifact,
    validator: impl FnOnce(&BackwardEvaluationCircuitArtifact) -> Result<(), BackwardArtifactError>,
) -> Result<(), BackwardArtifactError> {
    artifact.validate_self_consistency()?;
    let mut created = false;
    let publication = (|| {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(temporary)
            .map_err(|error| {
                BackwardArtifactError::Publish(format!("create {}: {error}", temporary.display()))
            })?;
        created = true;
        serde_json::to_writer_pretty(&mut file, artifact).map_err(|error| {
            BackwardArtifactError::Publish(format!("serialize {}: {error}", temporary.display()))
        })?;
        file.write_all(b"\n")
            .and_then(|()| file.sync_all())
            .map_err(|error| {
                BackwardArtifactError::Publish(format!("sync {}: {error}", temporary.display()))
            })?;
        drop(file);

        let reloaded = load_backward_evaluation_artifact(&temporary)?;
        if reloaded != *artifact {
            return Err(BackwardArtifactError::Publish(
                "temporary artifact changed across serialization".to_owned(),
            ));
        }
        validator(&reloaded)?;
        std::fs::rename(&temporary, path).map_err(|error| {
            BackwardArtifactError::Publish(format!(
                "rename {} to {}: {error}",
                temporary.display(),
                path.display(),
            ))
        })?;
        Ok(())
    })();
    if created && publication.is_err() {
        let _ = std::fs::remove_file(temporary);
    }
    publication
}

fn validate_regime(
    circuit: &str,
    layer: usize,
    regime: BwdRegime,
    artifact: &BackwardRegimeArtifact,
) -> Result<(), BackwardArtifactError> {
    for plan in &artifact.plans {
        if !(MIN_BUDGET_CELLS..=MAX_BUDGET_CELLS).contains(&plan.budget_cells) {
            return Err(BackwardArtifactError::BudgetOutOfRange {
                circuit: circuit.to_owned(),
                layer,
                regime,
                budget_cells: plan.budget_cells,
            });
        }
    }
    if artifact.plans.len() != BUDGET_PLAN_COUNT {
        let budget_cells = (MIN_BUDGET_CELLS..=MAX_BUDGET_CELLS)
            .find(|&budget| {
                artifact
                    .plans
                    .get(budget - MIN_BUDGET_CELLS)
                    .is_none_or(|plan| plan.budget_cells != budget)
            })
            .unwrap_or(MAX_BUDGET_CELLS + 1);
        return Err(BackwardArtifactError::InvalidBudgetCoverage {
            coordinate: BackwardArtifactCoordinate {
                circuit: circuit.to_owned(),
                layer,
                regime,
                budget_cells,
            },
        });
    }
    for (offset, plan) in artifact.plans.iter().enumerate() {
        let expected = MIN_BUDGET_CELLS + offset;
        if plan.budget_cells != expected {
            return Err(BackwardArtifactError::InvalidBudgetCoverage {
                coordinate: BackwardArtifactCoordinate {
                    circuit: circuit.to_owned(),
                    layer,
                    regime,
                    budget_cells: expected,
                },
            });
        }
        if let Some(pair) = plan
            .retained_demands
            .windows(2)
            .find(|pair| pair[0] >= pair[1])
        {
            return Err(BackwardArtifactError::InvalidRetainedDemand {
                circuit: circuit.to_owned(),
                layer,
                regime,
                budget_cells: plan.budget_cells,
                position: pair[1] as usize,
            });
        }
    }
    Ok(())
}

pub fn load_backward_evaluation_artifact(
    path: &Path,
) -> Result<BackwardEvaluationCircuitArtifact, BackwardArtifactError> {
    let bytes = std::fs::read(path).map_err(|error| {
        BackwardArtifactError::Load(format!("read {}: {error}", path.display()))
    })?;
    let artifact: BackwardEvaluationCircuitArtifact =
        serde_json::from_slice(&bytes).map_err(|error| {
            BackwardArtifactError::Load(format!("parse {}: {error}", path.display()))
        })?;
    artifact.validate_self_consistency()?;
    Ok(artifact)
}

pub fn select_backward_plan(
    artifact: &BackwardEvaluationCircuitArtifact,
    layer: usize,
    regime: BwdRegime,
    budget_cells: usize,
) -> Result<&BackwardPlanArtifact, BackwardArtifactError> {
    if !(MIN_BUDGET_CELLS..=MAX_BUDGET_CELLS).contains(&budget_cells) {
        return Err(BackwardArtifactError::BudgetOutOfRange {
            circuit: artifact.circuit.clone(),
            layer,
            regime,
            budget_cells,
        });
    }
    let layer_artifact = artifact
        .layers
        .binary_search_by_key(&layer, |entry| entry.layer)
        .ok()
        .map(|index| &artifact.layers[index])
        .ok_or_else(|| BackwardArtifactError::MissingLayer {
            coordinate: BackwardArtifactCoordinate {
                circuit: artifact.circuit.clone(),
                layer,
                regime,
                budget_cells,
            },
        })?;
    let regime_artifact = match regime {
        BwdRegime::R0 => &layer_artifact.r0,
        BwdRegime::Ext => &layer_artifact.ext,
    };
    let plan = regime_artifact
        .plans
        .get(budget_cells - MIN_BUDGET_CELLS)
        .ok_or_else(|| BackwardArtifactError::InvalidBudgetCoverage {
            coordinate: BackwardArtifactCoordinate {
                circuit: artifact.circuit.clone(),
                layer,
                regime,
                budget_cells,
            },
        })?;
    if plan.budget_cells != budget_cells {
        return Err(BackwardArtifactError::InvalidBudgetCoverage {
            coordinate: BackwardArtifactCoordinate {
                circuit: artifact.circuit.clone(),
                layer,
                regime,
                budget_cells,
            },
        });
    }
    Ok(plan)
}

pub fn capture_backward_plan_artifact(
    plan: &ProductionBackwardPlan,
) -> Result<BackwardPlanArtifact, BackwardArtifactError> {
    let fragment_order = plan
        .problem
        .selected_order
        .iter()
        .map(|fragment| {
            plan.problem
                .fragment_domain
                .iter()
                .position(|candidate| candidate == fragment)
                .ok_or(BackwardSearchError::InvalidFragmentPermutation)
                .and_then(|index| {
                    u32::try_from(index).map_err(|_| BackwardSearchError::CostOverflow)
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let order = fragment_order
        .iter()
        .copied()
        .map(|index| index as usize)
        .collect::<Vec<_>>();
    decode_order_indices(&plan.problem, &order)?;
    let retained_demands = plan
        .candidate
        .paging
        .actions
        .iter()
        .enumerate()
        .filter_map(|(position, action)| {
            (*action == PagingAction::Retain)
                .then(|| u32::try_from(position).map_err(|_| BackwardSearchError::CostOverflow))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (instruction_digest, encoded_digest) = backward_output_digests(&plan.candidate.compiled)?;
    Ok(BackwardPlanArtifact {
        budget_cells: plan.problem.budget_cells,
        problem: backward_problem_certificate(&plan.problem)?,
        fragment_order,
        retained_demands,
        expected_score: BackwardScoreArtifact::from_score(&plan.candidate.score),
        expected_paging: BackwardPagingCertificateArtifact::from_certificate(
            &plan.candidate.certificate,
        ),
        instruction_digest,
        encoded_digest,
    })
}

pub fn compile_backward_plan_artifact(
    circuit: &str,
    layer_index: usize,
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    artifact: &BackwardPlanArtifact,
) -> Result<CertifiedBackwardCandidate, BackwardArtifactError> {
    let regime = distilled.regime;
    let budget_cells = artifact.budget_cells;
    if !(MIN_BUDGET_CELLS..=MAX_BUDGET_CELLS).contains(&budget_cells) {
        return Err(BackwardArtifactError::BudgetOutOfRange {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        });
    }
    let coordinate = || BackwardArtifactCoordinate {
        circuit: circuit.to_owned(),
        layer: layer_index,
        regime,
        budget_cells,
    };
    let (_, constructive) =
        build_backward_search_problem(canonical, distilled, trace_len, budget_cells).map_err(
            |source| BackwardArtifactError::ReplaySearch {
                coordinate: coordinate(),
                source,
            },
        )?;
    let Some(constructive) = constructive else {
        return Err(BackwardArtifactError::ReplaySearch {
            coordinate: coordinate(),
            source: BackwardSearchError::SearchDriverFailure {
                reason: "artifact problem is infeasible",
            },
        });
    };
    let order = artifact
        .fragment_order
        .iter()
        .copied()
        .map(|index| index as usize)
        .collect::<Vec<_>>();
    let stable_order = decode_order_indices(&constructive, &order).map_err(|_| {
        BackwardArtifactError::InvalidFragmentPermutation {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        }
    })?;
    let problem = rebuild_problem_for_stable_order(
        canonical,
        distilled,
        &constructive,
        trace_len,
        &stable_order,
    )
    .map_err(|error| match error {
        BackwardSearchError::InvalidFragmentPermutation => {
            BackwardArtifactError::InvalidFragmentPermutation {
                circuit: circuit.to_owned(),
                layer: layer_index,
                regime,
                budget_cells,
            }
        }
        source => BackwardArtifactError::ReplaySearch {
            coordinate: coordinate(),
            source,
        },
    })?;
    if backward_problem_certificate(&problem)? != artifact.problem {
        return Err(BackwardArtifactError::ProblemCertificateMismatch {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        });
    }

    let mut actions = vec![PagingAction::Bypass; problem.demands.len()];
    let mut previous = None;
    for &encoded_position in &artifact.retained_demands {
        let position = encoded_position as usize;
        if previous.is_some_and(|previous| previous >= position) || position >= actions.len() {
            return Err(BackwardArtifactError::InvalidRetainedDemand {
                circuit: circuit.to_owned(),
                layer: layer_index,
                regime,
                budget_cells,
                position,
            });
        }
        actions[position] = PagingAction::Retain;
        previous = Some(position);
    }
    let paging =
        reconstruct_paging_plan(&problem.demands, &actions).map_err(|error| match error {
            BackwardSearchError::IllegalPagingRetain { demand_position }
            | BackwardSearchError::PagingLiveSetOverCapacity { demand_position } => {
                BackwardArtifactError::InvalidRetainedDemand {
                    circuit: circuit.to_owned(),
                    layer: layer_index,
                    regime,
                    budget_cells,
                    position: demand_position,
                }
            }
            source => BackwardArtifactError::ReplaySearch {
                coordinate: coordinate(),
                source,
            },
        })?;
    let candidate =
        compile_and_certify_paging(distilled, &problem, &paging, 0).map_err(|source| {
            BackwardArtifactError::ReplaySearch {
                coordinate: coordinate(),
                source,
            }
        })?;
    if !artifact.expected_score.matches_score(&candidate.score) {
        return Err(BackwardArtifactError::ScoreCertificateMismatch {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        });
    }
    if !artifact
        .expected_paging
        .matches_certificate(&candidate.certificate)
    {
        return Err(BackwardArtifactError::PagingCertificateMismatch {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        });
    }
    let (instruction_digest, encoded_digest) = backward_output_digests(&candidate.compiled)?;
    if instruction_digest != artifact.instruction_digest {
        return Err(BackwardArtifactError::InstructionDigestMismatch {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        });
    }
    if encoded_digest != artifact.encoded_digest {
        return Err(BackwardArtifactError::EncodedDigestMismatch {
            circuit: circuit.to_owned(),
            layer: layer_index,
            regime,
            budget_cells,
        });
    }
    Ok(candidate)
}

fn backward_output_digests(
    compiled: &CompiledBackwardEvaluation,
) -> Result<([u64; 4], [u64; 4]), BackwardArtifactError> {
    let encoded_bytes = encoded_lane_bytes(&compiled.encoded);
    let mut instruction_bytes = encoded_bytes.clone();
    push_u64(
        &mut instruction_bytes,
        compiled.compiled.specials.len() as u64,
    );
    for index in 0..compiled.compiled.specials.len() {
        let special = compiled
            .compiled
            .specials
            .get(index as u16)
            .expect("descriptor index below table length must resolve");
        serialize_bwd_special(&mut instruction_bytes, special);
    }
    serialize_source_windows(&mut instruction_bytes, &compiled.compiled.source_windows);
    Ok((
        four_lane_digest(&instruction_bytes)?,
        four_lane_digest(&encoded_bytes)?,
    ))
}

fn serialize_source_windows(bytes: &mut Vec<u8>, table: &SourceWindowTable) {
    push_u64(bytes, table.len() as u64);
    for window in table.windows() {
        serialize_backing_key(bytes, &window.backing);
        push_u64(bytes, window.first_column as u64);
        let columns: Vec<_> = window.referenced_columns().collect();
        push_u64(bytes, columns.len() as u64);
        for column in columns {
            push_u64(bytes, column as u64);
        }
        let folds: Vec<_> = window.fold_descriptors().collect();
        push_u64(bytes, folds.len() as u64);
        for (column, desc) in folds {
            push_u64(bytes, column as u64);
            bytes.extend_from_slice(&desc.to_le_bytes());
        }
    }
}

fn serialize_backing_key(bytes: &mut Vec<u8>, key: &BackingKey) {
    match key {
        BackingKey::BaseLayerMemory => bytes.push(0),
        BackingKey::BaseLayerWitness => bytes.push(1),
        BackingKey::Setup => bytes.push(2),
        BackingKey::Scratch => bytes.push(3),
        BackingKey::LayerOutput { layer, field } => {
            bytes.push(4);
            push_u64(bytes, *layer as u64);
            serialize_operand_field(bytes, *field);
        }
        BackingKey::CacheOutput { layer, field } => {
            bytes.push(5);
            push_u64(bytes, *layer as u64);
            serialize_operand_field(bytes, *field);
        }
    }
}

fn serialize_operand_field(bytes: &mut Vec<u8>, field: OperandField) {
    bytes.push(match field {
        OperandField::Base => 0,
        OperandField::Ext => 1,
    });
}

fn encoded_lane_bytes(lanes: &[u16]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(lanes.len() * 2);
    for lane in lanes {
        bytes.extend_from_slice(&lane.to_le_bytes());
    }
    bytes
}

fn four_lane_digest(bytes: &[u8]) -> Result<[u64; 4], BackwardArtifactError> {
    Ok(certificate_from_serializable(bytes.len(), bytes)?.digest)
}

fn push_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn serialize_read_place(bytes: &mut Vec<u8>, place: &ReadPlace) {
    match place {
        ReadPlace::BaseLayerMemory { column } => {
            bytes.push(0);
            push_u64(bytes, *column as u64);
        }
        ReadPlace::BaseLayerWitness { column } => {
            bytes.push(1);
            push_u64(bytes, *column as u64);
        }
        ReadPlace::Setup { column } => {
            bytes.push(2);
            push_u64(bytes, *column as u64);
        }
        ReadPlace::Scratch { slot } => {
            bytes.push(3);
            push_u64(bytes, *slot as u64);
        }
        ReadPlace::LayerOutput { layer, offset } => {
            bytes.push(4);
            push_u64(bytes, *layer as u64);
            push_u64(bytes, *offset as u64);
        }
        ReadPlace::CacheOutput { layer, offset } => {
            bytes.push(5);
            push_u64(bytes, *layer as u64);
            push_u64(bytes, *offset as u64);
        }
    }
}

fn serialize_bwd_special(bytes: &mut Vec<u8>, special: &BwdSpecial) {
    match special {
        BwdSpecial::FoldSource { origin } => {
            bytes.push(0);
            match origin {
                OriginLeaf::Read(place) => {
                    bytes.push(0);
                    serialize_read_place(bytes, place);
                }
                OriginLeaf::VirtualSetup { kind } => {
                    bytes.push(1);
                    push_u32(bytes, virtual_setup_kind_code(kind));
                }
            }
        }
        BwdSpecial::VirtualSetup { kind } => {
            bytes.push(1);
            push_u32(bytes, virtual_setup_kind_code(kind));
        }
        BwdSpecial::Coefficient { fragment } => {
            bytes.push(2);
            push_u32(bytes, *fragment);
        }
        BwdSpecial::AccInit => bytes.push(3),
    }
}

#[derive(Serialize)]
enum StableExprProjection {
    Canonical { expr: u32 },
    BatchingTerm { root: u32 },
    CombinedSpine,
}

impl From<StableBwdExprKey> for StableExprProjection {
    fn from(value: StableBwdExprKey) -> Self {
        match value {
            StableBwdExprKey::Canonical(expr) => Self::Canonical { expr: expr.0 },
            StableBwdExprKey::BatchingTerm(root) => Self::BatchingTerm { root: root.0 },
            StableBwdExprKey::CombinedSpine => Self::CombinedSpine,
        }
    }
}

#[derive(Serialize)]
enum StableConsumerProjection {
    Expr {
        expr: StableExprProjection,
        duplicate_ordinal: u32,
    },
    RootOutput,
}

impl From<StableBwdConsumer> for StableConsumerProjection {
    fn from(value: StableBwdConsumer) -> Self {
        match value {
            StableBwdConsumer::Expr {
                expr,
                duplicate_ordinal,
            } => Self::Expr {
                expr: expr.into(),
                duplicate_ordinal,
            },
            StableBwdConsumer::RootOutput => Self::RootOutput,
        }
    }
}

#[derive(Serialize)]
struct StableSiteProjection {
    consumer: StableConsumerProjection,
    value: StableExprProjection,
}

impl From<StableBwdSiteKey> for StableSiteProjection {
    fn from(value: StableBwdSiteKey) -> Self {
        Self {
            consumer: value.consumer.into(),
            value: value.value.into(),
        }
    }
}

#[derive(Serialize)]
enum FactorProjection {
    Challenge(cs::gkr_compiler::dag_ir::ChallengeRef),
    Constant(u32),
    Expr(StableExprProjection),
}

impl From<&FactorKey> for FactorProjection {
    fn from(value: &FactorKey) -> Self {
        match value {
            FactorKey::Challenge(challenge) => Self::Challenge(challenge.clone()),
            FactorKey::Constant(value) => Self::Constant(*value),
            FactorKey::Expr(expr) => Self::Expr((*expr).into()),
        }
    }
}

#[derive(Serialize)]
struct StableFragmentProjection {
    atoms: Vec<StableExprProjection>,
    recipe: Vec<Vec<FactorProjection>>,
}

impl From<&super::backward_search::problem::StableFragmentKey> for StableFragmentProjection {
    fn from(value: &super::backward_search::problem::StableFragmentKey) -> Self {
        Self {
            atoms: value.atoms.iter().copied().map(Into::into).collect(),
            recipe: value
                .recipe
                .iter()
                .map(|factors| factors.iter().map(FactorProjection::from).collect())
                .collect(),
        }
    }
}

#[derive(Serialize)]
struct StableDemandProjection {
    fragment: StableFragmentProjection,
    site: StableSiteProjection,
    occurrence_in_fragment: u32,
}

#[derive(Serialize)]
struct DemandProjection {
    key: StableDemandProjection,
    physical: [u64; 2],
    source_desc: Option<u16>,
    width_lanes: u8,
    gap_capacity_lanes: u8,
    miss_cost: SourceCostArtifact,
    has_next: bool,
}

#[derive(Serialize)]
struct SourceRoundUseProjection {
    desc: u16,
    round: u8,
    structural_occurrences: u32,
    origin: SourceOriginProjection,
}

#[derive(Serialize)]
enum SourceOriginProjection {
    Read { field: FieldProjection },
    VirtualSetup,
}

#[derive(Serialize)]
enum FieldProjection {
    Base,
    Ext,
}

impl From<FieldKind> for FieldProjection {
    fn from(value: FieldKind) -> Self {
        match value {
            FieldKind::Base => Self::Base,
            FieldKind::Ext => Self::Ext,
        }
    }
}

#[derive(Serialize)]
struct SourceRoundBindingProjection {
    desc: u16,
    round: u8,
    state: FoldStateProjection,
    store_for_next_round: bool,
}

#[derive(Serialize)]
enum FoldStateProjection {
    Materialized,
    LazyFromOriginals { depth: u8 },
}

#[derive(Serialize)]
struct RoundProfileProjection {
    round: u8,
    rows: u64,
}

#[derive(Serialize)]
struct BackwardProblemProjection {
    fragment_domain: Vec<StableFragmentProjection>,
    leaf_domain: Vec<StableDemandProjection>,
    demands: Vec<DemandProjection>,
    source_round_uses: Vec<SourceRoundUseProjection>,
    source_round_bindings: Vec<SourceRoundBindingProjection>,
    all_ext_from: Option<u8>,
    fixed_cost: SourceCostArtifact,
    fixed_writes: SourceCostArtifact,
    round_profiles: Vec<RoundProfileProjection>,
    stream_reductions: bool,
    epoch: u64,
    budget_cells: usize,
    budget_lanes: usize,
}

pub fn backward_problem_certificate(
    problem: &BackwardSearchProblem,
) -> Result<BackwardProblemCertificate, BackwardArtifactError> {
    let projection = BackwardProblemProjection {
        fragment_domain: problem
            .fragment_domain
            .iter()
            .map(StableFragmentProjection::from)
            .collect(),
        leaf_domain: problem
            .leaf_domain
            .iter()
            .map(|demand| StableDemandProjection {
                fragment: (&demand.fragment).into(),
                site: demand.site.into(),
                occurrence_in_fragment: demand.occurrence_in_fragment,
            })
            .collect(),
        demands: problem
            .demands
            .iter()
            .map(|demand| DemandProjection {
                key: StableDemandProjection {
                    fragment: (&demand.key.fragment).into(),
                    site: demand.key.site.into(),
                    occurrence_in_fragment: demand.key.occurrence_in_fragment,
                },
                physical: demand.physical.0,
                source_desc: demand.source_desc,
                width_lanes: demand.width_lanes,
                gap_capacity_lanes: demand.gap_capacity_lanes,
                miss_cost: demand.miss_cost.into(),
                has_next: demand.has_next,
            })
            .collect(),
        source_round_uses: problem
            .source_round_uses
            .iter()
            .map(|source| SourceRoundUseProjection {
                desc: source.desc,
                round: source.round,
                structural_occurrences: source.structural_occurrences,
                origin: match source.origin {
                    SourceOriginKind::Read { field } => SourceOriginProjection::Read {
                        field: field.into(),
                    },
                    SourceOriginKind::VirtualSetup => SourceOriginProjection::VirtualSetup,
                },
            })
            .collect(),
        source_round_bindings: problem
            .materialization
            .bindings
            .iter()
            .map(|(&(desc, round), binding)| SourceRoundBindingProjection {
                desc,
                round,
                state: match binding.state {
                    FoldState::Materialized => FoldStateProjection::Materialized,
                    FoldState::LazyFromOriginals { depth } => {
                        FoldStateProjection::LazyFromOriginals { depth }
                    }
                },
                store_for_next_round: binding.store_for_next_round,
            })
            .collect(),
        all_ext_from: problem.materialization.all_ext_from,
        fixed_cost: problem.fixed_cost.into(),
        fixed_writes: problem.materialization.fixed_writes.into(),
        round_profiles: problem
            .round_profiles
            .iter()
            .map(|profile| RoundProfileProjection {
                round: profile.round,
                rows: profile.rows,
            })
            .collect(),
        stream_reductions: problem.stream_reductions,
        epoch: problem.epoch,
        budget_cells: problem.budget_cells,
        budget_lanes: problem.budget_lanes,
    };
    certificate_from_serializable(problem.fragment_domain.len(), &projection).map_err(Into::into)
}

#[cfg(test)]
mod generation_tests {
    use super::*;

    #[test]
    fn generation_chain_clears_failed_seed_and_recovers_after_later_success() {
        let identity = ProductionSearchIdentity {
            circuit: "circuit".to_owned(),
            layout_fixture: "fixture".to_owned(),
            layer: 7,
            regime: BwdRegime::Ext,
        };
        let mut observed = Vec::new();
        let result = produce_regime_chain_with(&identity, 2..=5, |budget, preceding| {
            observed.push((budget, preceding.map(<[usize]>::to_vec)));
            if budget == 3 {
                return Err(BackwardArtifactError::Search(
                    BackwardSearchError::ProductionPagerResourceLimit { max_states: 99 },
                ));
            }
            Ok((budget, vec![budget]))
        });

        assert_eq!(
            observed,
            vec![(2, None), (3, Some(vec![2])), (4, None), (5, Some(vec![4])),]
        );
        assert!(matches!(
            result,
            Err(BackwardArtifactError::IncompleteGeneration { failures })
                if failures == vec![BackwardArtifactCoordinate {
                    circuit: "circuit".to_owned(),
                    layer: 7,
                    regime: BwdRegime::Ext,
                    budget_cells: 3,
                }]
        ));
    }

    #[test]
    fn publication_collision_preserves_foreign_temporary_and_destination() {
        let directory = std::env::temp_dir().join(format!(
            "plan4-publication-collision-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let destination = directory.join("artifact.json");
        let temporary = directory.join(".artifact.json.foreign.tmp");
        std::fs::write(&destination, b"certified-destination").unwrap();
        std::fs::write(&temporary, b"foreign-temporary").unwrap();
        let artifact =
            BackwardEvaluationCircuitArtifact::new("circuit", "fixture", Vec::new()).unwrap();

        assert!(matches!(
            publish_backward_evaluation_artifact_to_temporary(
                &destination,
                &temporary,
                &artifact,
                |_| Ok(()),
            ),
            Err(BackwardArtifactError::Publish(_))
        ));
        assert_eq!(
            std::fs::read(&destination).unwrap(),
            b"certified-destination"
        );
        assert_eq!(std::fs::read(&temporary).unwrap(), b"foreign-temporary");
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_u128_preserves_u128_maximum() {
        let value = CanonicalU128::from(u128::MAX);
        assert_eq!(value.value(), u128::MAX);
        assert_eq!(
            serde_json::from_str::<CanonicalU128>(&serde_json::to_string(&value).unwrap()).unwrap(),
            value
        );
    }

    #[test]
    fn canonical_u128_rejects_noncanonical_strings() {
        for spelling in ["-1", "+1", "01", "", " 1"] {
            assert!(serde_json::from_str::<CanonicalU128>(&format!("\"{spelling}\"")).is_err());
        }
    }
}
