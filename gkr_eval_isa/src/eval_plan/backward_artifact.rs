use std::path::Path;

use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bwd::distill::{StableBwdConsumer, StableBwdExprKey, StableBwdSiteKey};
use crate::bwd::fragment::FactorKey;
use crate::bwd::source::FoldState;

use super::artifact::{DomainCertificate, EvaluationArtifactError, certificate_from_serializable};
use super::backward_search::problem::BackwardSearchProblem;
use super::backward_search::{
    BackwardScore, BackwardSearchError, PagingCertificate, SourceCost, SourceOriginKind,
};

const MIN_BUDGET_CELLS: usize = 2;
const MAX_BUDGET_CELLS: usize = 16;
const BUDGET_PLAN_COUNT: usize = MAX_BUDGET_CELLS - MIN_BUDGET_CELLS + 1;

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
        layer: usize,
    },
    InvalidBudgetCoverage {
        layer: usize,
        regime: BwdRegime,
    },
    BudgetOutOfRange {
        budget_cells: usize,
    },
    ProblemCertificateMismatch {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    InvalidFragmentPermutation {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    InvalidRetainedDemand {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
        position: usize,
    },
    ScoreCertificateMismatch {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    PagingCertificateMismatch {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    InstructionDigestMismatch {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    },
    EncodedDigestMismatch {
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
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
            validate_regime(layer.layer, BwdRegime::R0, &layer.r0)?;
            validate_regime(layer.layer, BwdRegime::Ext, &layer.ext)?;
        }
        Ok(())
    }
}

fn validate_regime(
    layer: usize,
    regime: BwdRegime,
    artifact: &BackwardRegimeArtifact,
) -> Result<(), BackwardArtifactError> {
    for plan in &artifact.plans {
        if !(MIN_BUDGET_CELLS..=MAX_BUDGET_CELLS).contains(&plan.budget_cells) {
            return Err(BackwardArtifactError::BudgetOutOfRange {
                budget_cells: plan.budget_cells,
            });
        }
    }
    if artifact.plans.len() != BUDGET_PLAN_COUNT {
        return Err(BackwardArtifactError::InvalidBudgetCoverage { layer, regime });
    }
    for (offset, plan) in artifact.plans.iter().enumerate() {
        let expected = MIN_BUDGET_CELLS + offset;
        if plan.budget_cells != expected {
            return Err(BackwardArtifactError::InvalidBudgetCoverage { layer, regime });
        }
        if let Some(pair) = plan
            .retained_demands
            .windows(2)
            .find(|pair| pair[0] >= pair[1])
        {
            return Err(BackwardArtifactError::InvalidRetainedDemand {
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
