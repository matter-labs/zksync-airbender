use std::collections::{BTreeMap, HashMap};
use std::path::Path;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{DagCircuit, DagLayer, ExprId, FieldKind, ReadPlace, RootId};
use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription};
use field::baby_bear::base::BabyBearField;

use crate::fwd::compile::{build_cross_layer_field_map, expr_operand_field};
use crate::fwd::context::{ForwardAction, build_forward_actions};
use crate::fwd::error::CompileError;
use crate::fwd::isa::OperandField;
use crate::fwd::validate::validate_compiled;

use super::genome::root_cmp;
use super::{
    ConcreteBindError, ConcreteEvalProgram, EvaluationGenome, FitnessError, IdentityError,
    MutationSearchConfig, MutationSearchError, PackConfig, PackError, PlacementStatus, PlanFitness,
    PlanSearchContext, RootKey, bind_packed_plan_with_actions, mutation_search, pack_plan,
    structural_fingerprints, validate_structural_identity,
};

pub const EVALUATION_GENOME_SCHEMA_VERSION: u32 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum EvaluationPass {
    Forward,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum EvaluationLayoutVariant {
    WithCaches,
    NoCaches,
    PreprocessedWithCaches,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SearchProvenance {
    pub algorithm: String,
    pub seed: u64,
    pub evaluations: usize,
    pub staging_evaluations: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum ForwardActionProvenance {
    Compute,
    CopyAlias {
        src_addr: GKRAddress,
        dst_addr: GKRAddress,
    },
    SkipScratchPrefill,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ForwardActionRecord {
    pub root: RootKey,
    pub action: ForwardActionProvenance,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DomainCertificate {
    pub count: usize,
    pub digest: [u64; 4],
}

/// A versioned, arena-independent genome for one concrete circuit layer and
/// lane budget. Dense genes are tied to the semantic domains stored alongside
/// them, so a stale genome cannot silently target different sites or units.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct EvaluationGenomeArtifact {
    pub schema_version: u32,
    pub circuit: String,
    pub layer: usize,
    pub budget_lanes: usize,
    pub unit_domain: DomainCertificate,
    pub selected_root_domain: DomainCertificate,
    pub site_domain: DomainCertificate,
    pub staging_domain: DomainCertificate,
    pub forward_action_domain: DomainCertificate,
    pub genome: EvaluationGenome,
    pub expected_fitness: PlanFitness,
}

/// One forward compiler artifact for one exact layout fixture and lane budget.
/// Layers are index-aligned with both `DagCircuit.layers` and the GKR layout.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct EvaluationGenomeCircuitArtifact {
    pub schema_version: u32,
    pub circuit: String,
    pub pass: EvaluationPass,
    pub layout_variant: EvaluationLayoutVariant,
    pub layout_fixture: String,
    pub budget_lanes: usize,
    pub expected_fitness: PlanFitness,
    pub search: SearchProvenance,
    pub layers: Vec<EvaluationGenomeArtifact>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum EvaluationArtifactError {
    Identity(IdentityError),
    Fitness(FitnessError),
    UnsupportedSchema { expected: u32, actual: u32 },
    CircuitMismatch { expected: String, actual: String },
    LayerMismatch { expected: usize, actual: usize },
    BudgetMismatch { expected: usize, actual: usize },
    UnitDomainMismatch,
    SelectedRootDomainMismatch,
    SiteDomainMismatch,
    StagingDomainMismatch,
    ForwardActionDomainMismatch,
    DomainEncoding(String),
    GenomeNotConcrete(PlacementStatus),
}

impl From<IdentityError> for EvaluationArtifactError {
    fn from(value: IdentityError) -> Self {
        Self::Identity(value)
    }
}

impl From<FitnessError> for EvaluationArtifactError {
    fn from(value: FitnessError) -> Self {
        Self::Fitness(value)
    }
}

impl EvaluationGenomeArtifact {
    /// Capture a concrete search winner. This is intentionally stricter than
    /// plain serialization: infeasible or placement-unverified genomes are not
    /// valid production artifacts.
    pub fn capture(
        circuit: impl Into<String>,
        context: &PlanSearchContext<'_>,
        actions: &HashMap<RootId, ForwardAction>,
        genome: EvaluationGenome,
    ) -> Result<Self, EvaluationArtifactError> {
        validate_structural_identity(context.layer())?;
        let forward_actions = forward_action_records(context.layer(), actions)?;
        let unit_keys = context
            .units()
            .iter()
            .map(|unit| unit.key.clone())
            .collect::<Vec<_>>();
        let selected_root_keys = context.selected_root_keys();
        let scored = context.score(&genome)?;
        if scored.placement != PlacementStatus::Concrete {
            return Err(EvaluationArtifactError::GenomeNotConcrete(scored.placement));
        }
        Ok(Self {
            schema_version: EVALUATION_GENOME_SCHEMA_VERSION,
            circuit: circuit.into(),
            layer: context.layer_index(),
            budget_lanes: context.budget_lanes(),
            unit_domain: domain_certificate(&unit_keys)?,
            selected_root_domain: domain_certificate(&selected_root_keys)?,
            site_domain: domain_certificate(context.site_index().sites())?,
            staging_domain: domain_certificate(context.site_index().staging_pairs())?,
            forward_action_domain: domain_certificate(&forward_actions)?,
            genome,
            expected_fitness: scored.fitness,
        })
    }

    pub fn validate_against(
        &self,
        circuit: &str,
        context: &PlanSearchContext<'_>,
        actions: &HashMap<RootId, ForwardAction>,
    ) -> Result<(), EvaluationArtifactError> {
        if self.schema_version != EVALUATION_GENOME_SCHEMA_VERSION {
            return Err(EvaluationArtifactError::UnsupportedSchema {
                expected: EVALUATION_GENOME_SCHEMA_VERSION,
                actual: self.schema_version,
            });
        }
        if self.circuit != circuit {
            return Err(EvaluationArtifactError::CircuitMismatch {
                expected: circuit.to_owned(),
                actual: self.circuit.clone(),
            });
        }
        if self.layer != context.layer_index() {
            return Err(EvaluationArtifactError::LayerMismatch {
                expected: context.layer_index(),
                actual: self.layer,
            });
        }
        if self.budget_lanes != context.budget_lanes() {
            return Err(EvaluationArtifactError::BudgetMismatch {
                expected: context.budget_lanes(),
                actual: self.budget_lanes,
            });
        }
        validate_structural_identity(context.layer())?;
        let unit_keys = context
            .units()
            .iter()
            .map(|unit| unit.key.clone())
            .collect::<Vec<_>>();
        if self.unit_domain != domain_certificate(&unit_keys)? {
            return Err(EvaluationArtifactError::UnitDomainMismatch);
        }
        if self.selected_root_domain != domain_certificate(&context.selected_root_keys())? {
            return Err(EvaluationArtifactError::SelectedRootDomainMismatch);
        }
        if self.site_domain != domain_certificate(context.site_index().sites())? {
            return Err(EvaluationArtifactError::SiteDomainMismatch);
        }
        if self.staging_domain != domain_certificate(context.site_index().staging_pairs())? {
            return Err(EvaluationArtifactError::StagingDomainMismatch);
        }
        let forward_actions = forward_action_records(context.layer(), actions)?;
        if self.forward_action_domain != domain_certificate(&forward_actions)? {
            return Err(EvaluationArtifactError::ForwardActionDomainMismatch);
        }
        Ok(())
    }
}

fn forward_action_records(
    layer: &DagLayer,
    actions: &HashMap<RootId, ForwardAction>,
) -> Result<Vec<ForwardActionRecord>, IdentityError> {
    let fingerprints = structural_fingerprints(layer)?;
    let mut records = actions
        .iter()
        .map(|(&root_id, action)| {
            let root = &layer.roots[root_id.0 as usize];
            ForwardActionRecord {
                root: RootKey {
                    expr: fingerprints[root.expr.0 as usize],
                    materialize: root.materialize.clone(),
                    claim_origin: root.claim.as_ref().map(|claim| claim.origin.clone()),
                },
                action: match action {
                    ForwardAction::Compute => ForwardActionProvenance::Compute,
                    ForwardAction::CopyAlias { src_addr, dst_addr } => {
                        ForwardActionProvenance::CopyAlias {
                            src_addr: *src_addr,
                            dst_addr: *dst_addr,
                        }
                    }
                    ForwardAction::SkipScratchPrefill => {
                        ForwardActionProvenance::SkipScratchPrefill
                    }
                },
            }
        })
        .collect::<Vec<_>>();
    records.sort_by(|a, b| root_cmp(&a.root, &b.root).then_with(|| a.action.cmp(&b.action)));
    Ok(records)
}

fn domain_certificate<T: serde::Serialize>(
    values: &[T],
) -> Result<DomainCertificate, EvaluationArtifactError> {
    let bytes = serde_json::to_vec(values)
        .map_err(|error| EvaluationArtifactError::DomainEncoding(error.to_string()))?;
    let mut digest = [
        0xcbf2_9ce4_8422_2325u64,
        0x8422_2325_cbf2_9ce4,
        0x6a09_e667_f3bc_c909,
        0xbb67_ae85_84ca_a73b,
    ];
    let primes = [
        0x0000_0100_0000_01b3u64,
        0x9e37_79b1_85eb_ca87,
        0xc2b2_ae3d_27d4_eb4f,
        0x1656_67b1_9e37_79f9,
    ];
    for byte in bytes {
        for lane in 0..digest.len() {
            digest[lane] ^= u64::from(byte).wrapping_add((lane as u64) << 8);
            digest[lane] = digest[lane].wrapping_mul(primes[lane]);
        }
    }
    Ok(DomainCertificate {
        count: values.len(),
        digest,
    })
}

#[derive(Debug)]
pub enum EvaluationCompileError {
    Artifact(EvaluationArtifactError),
    Load(String),
    Forward(CompileError),
    Fitness(FitnessError),
    Search(MutationSearchError),
    Pack(PackError),
    Concrete(ConcreteBindError),
    GenomeNotConcrete(PlacementStatus),
    MissingPlan,
    UnsupportedPass(EvaluationPass),
    LayoutVariantMismatch {
        expected: EvaluationLayoutVariant,
        actual: EvaluationLayoutVariant,
    },
    LayoutFixtureMismatch {
        expected: String,
        actual: String,
    },
    LayerCountMismatch {
        expected: usize,
        actual: usize,
    },
    LayerHeaderMismatch {
        layer: usize,
    },
    FitnessCertificateMismatch {
        expected: PlanFitness,
        actual: PlanFitness,
    },
    InstructionCertificateMismatch {
        scored: usize,
        emitted: usize,
    },
    EncodingCertificateMismatch {
        scored: usize,
        emitted: usize,
    },
    TrafficCertificateMismatch {
        scored: usize,
        emitted: usize,
    },
}

impl From<EvaluationArtifactError> for EvaluationCompileError {
    fn from(value: EvaluationArtifactError) -> Self {
        Self::Artifact(value)
    }
}

impl From<FitnessError> for EvaluationCompileError {
    fn from(value: FitnessError) -> Self {
        Self::Fitness(value)
    }
}

impl From<MutationSearchError> for EvaluationCompileError {
    fn from(value: MutationSearchError) -> Self {
        Self::Search(value)
    }
}

impl From<PackError> for EvaluationCompileError {
    fn from(value: PackError) -> Self {
        Self::Pack(value)
    }
}

impl From<ConcreteBindError> for EvaluationCompileError {
    fn from(value: ConcreteBindError) -> Self {
        Self::Concrete(value)
    }
}

/// Result of the final artifact-driven layer compile. `root_order` is the
/// arena-local decoding of the artifact's semantic unit-order genes.
pub struct CompiledEvaluationLayer {
    pub concrete: ConcreteEvalProgram,
    pub fitness: PlanFitness,
    pub root_order: Vec<RootId>,
}

pub struct CompiledEvaluationCircuit {
    pub circuit: String,
    pub pass: EvaluationPass,
    pub layout_variant: EvaluationLayoutVariant,
    pub layout_fixture: String,
    pub budget_lanes: usize,
    pub fitness: PlanFitness,
    pub layers: Vec<CompiledEvaluationLayer>,
}

impl EvaluationGenomeCircuitArtifact {
    pub fn new(
        circuit: impl Into<String>,
        layout_variant: EvaluationLayoutVariant,
        layout_fixture: impl Into<String>,
        budget_lanes: usize,
        search: SearchProvenance,
        layers: Vec<EvaluationGenomeArtifact>,
    ) -> Result<Self, EvaluationCompileError> {
        let artifact = Self {
            schema_version: EVALUATION_GENOME_SCHEMA_VERSION,
            circuit: circuit.into(),
            pass: EvaluationPass::Forward,
            layout_variant,
            layout_fixture: layout_fixture.into(),
            budget_lanes,
            expected_fitness: aggregate_fitness(layers.iter().map(|layer| layer.expected_fitness)),
            search,
            layers,
        };
        artifact.validate_self_consistency()?;
        Ok(artifact)
    }

    fn validate_self_consistency(&self) -> Result<(), EvaluationCompileError> {
        if self.schema_version != EVALUATION_GENOME_SCHEMA_VERSION {
            return Err(EvaluationArtifactError::UnsupportedSchema {
                expected: EVALUATION_GENOME_SCHEMA_VERSION,
                actual: self.schema_version,
            }
            .into());
        }
        if self.pass != EvaluationPass::Forward {
            return Err(EvaluationCompileError::UnsupportedPass(self.pass));
        }
        for (layer, artifact) in self.layers.iter().enumerate() {
            if artifact.schema_version != self.schema_version
                || artifact.circuit != self.circuit
                || artifact.layer != layer
                || artifact.budget_lanes != self.budget_lanes
            {
                return Err(EvaluationCompileError::LayerHeaderMismatch { layer });
            }
        }
        let actual = aggregate_fitness(self.layers.iter().map(|layer| layer.expected_fitness));
        if self.expected_fitness != actual {
            return Err(EvaluationCompileError::FitnessCertificateMismatch {
                expected: self.expected_fitness,
                actual,
            });
        }
        Ok(())
    }
}

fn aggregate_fitness(fitnesses: impl IntoIterator<Item = PlanFitness>) -> PlanFitness {
    fitnesses.into_iter().fold(
        PlanFitness {
            infeasible: false,
            dram_read_lanes: 0,
            program_instructions: 0,
            encoded_lanes: 0,
            arithmetic_ops: 0,
        },
        |mut total, fitness| {
            total.infeasible |= fitness.infeasible;
            total.dram_read_lanes += fitness.dram_read_lanes;
            total.program_instructions += fitness.program_instructions;
            total.encoded_lanes += fitness.encoded_lanes;
            total.arithmetic_ops += fitness.arithmetic_ops;
            total
        },
    )
}

pub fn load_evaluation_genome_artifact(
    path: &Path,
) -> Result<EvaluationGenomeCircuitArtifact, EvaluationCompileError> {
    let bytes = std::fs::read(path).map_err(|error| {
        EvaluationCompileError::Load(format!("read {}: {error}", path.display()))
    })?;
    let artifact: EvaluationGenomeCircuitArtifact =
        serde_json::from_slice(&bytes).map_err(|error| {
            EvaluationCompileError::Load(format!("parse {}: {error}", path.display()))
        })?;
    artifact.validate_self_consistency()?;
    Ok(artifact)
}

#[allow(clippy::too_many_arguments)]
pub fn compile_circuit_with_evaluation_genomes(
    dag: &DagCircuit,
    layout: &GKRCircuitArtifact<BabyBearField>,
    expected_circuit: &str,
    expected_layout_fixture: &str,
    expected_layout_variant: EvaluationLayoutVariant,
    artifact: &EvaluationGenomeCircuitArtifact,
) -> Result<CompiledEvaluationCircuit, EvaluationCompileError> {
    artifact.validate_self_consistency()?;
    if artifact.circuit != expected_circuit {
        return Err(EvaluationArtifactError::CircuitMismatch {
            expected: expected_circuit.to_owned(),
            actual: artifact.circuit.clone(),
        }
        .into());
    }
    if artifact.layout_fixture != expected_layout_fixture {
        return Err(EvaluationCompileError::LayoutFixtureMismatch {
            expected: expected_layout_fixture.to_owned(),
            actual: artifact.layout_fixture.clone(),
        });
    }
    if artifact.layout_variant != expected_layout_variant {
        return Err(EvaluationCompileError::LayoutVariantMismatch {
            expected: expected_layout_variant,
            actual: artifact.layout_variant,
        });
    }
    if dag.layers.len() != layout.layers.len() {
        return Err(EvaluationCompileError::LayerCountMismatch {
            expected: dag.layers.len(),
            actual: layout.layers.len(),
        });
    }
    if artifact.layers.len() != dag.layers.len() {
        return Err(EvaluationCompileError::LayerCountMismatch {
            expected: dag.layers.len(),
            actual: artifact.layers.len(),
        });
    }

    let cross_layer_fields = build_cross_layer_field_map(dag);
    let mut layers = Vec::with_capacity(dag.layers.len());
    for (layer, (dag_layer, layout_layer)) in dag.layers.iter().zip(&layout.layers).enumerate() {
        let compiled = compile_layer_with_evaluation_genome(
            expected_circuit,
            dag_layer,
            layout_layer,
            &layout.scratch_space_mapping,
            &cross_layer_fields,
            artifact.budget_lanes,
            &artifact.layers[layer],
        )?;
        layers.push(compiled);
    }
    let fitness = aggregate_fitness(layers.iter().map(|layer| layer.fitness));
    if fitness != artifact.expected_fitness {
        return Err(EvaluationCompileError::FitnessCertificateMismatch {
            expected: artifact.expected_fitness,
            actual: fitness,
        });
    }

    Ok(CompiledEvaluationCircuit {
        circuit: artifact.circuit.clone(),
        pass: artifact.pass,
        layout_variant: artifact.layout_variant,
        layout_fixture: artifact.layout_fixture.clone(),
        budget_lanes: artifact.budget_lanes,
        fitness,
        layers,
    })
}

/// Search every layer offline and capture a whole-circuit artifact. A valid
/// incumbent is retained independently per layer whenever search does not find
/// a strictly better concrete fitness, making repeated production monotonic.
#[allow(clippy::too_many_arguments)]
pub fn produce_searched_evaluation_genome_artifact(
    dag: &DagCircuit,
    layout: &GKRCircuitArtifact<BabyBearField>,
    circuit: &str,
    layout_fixture: &str,
    layout_variant: EvaluationLayoutVariant,
    budget_lanes: usize,
    config: MutationSearchConfig,
    incumbent: Option<&EvaluationGenomeCircuitArtifact>,
) -> Result<EvaluationGenomeCircuitArtifact, EvaluationCompileError> {
    if let Some(incumbent) = incumbent {
        compile_circuit_with_evaluation_genomes(
            dag,
            layout,
            circuit,
            layout_fixture,
            layout_variant,
            incumbent,
        )?;
        if incumbent.budget_lanes != budget_lanes {
            return Err(EvaluationArtifactError::BudgetMismatch {
                expected: budget_lanes,
                actual: incumbent.budget_lanes,
            }
            .into());
        }
    }
    if dag.layers.len() != layout.layers.len() {
        return Err(EvaluationCompileError::LayerCountMismatch {
            expected: dag.layers.len(),
            actual: layout.layers.len(),
        });
    }

    let cross_layer_fields = build_cross_layer_field_map(dag);
    let mut layers = Vec::with_capacity(dag.layers.len());
    for (layer_index, (dag_layer, layout_layer)) in
        dag.layers.iter().zip(&layout.layers).enumerate()
    {
        let actions = build_forward_actions(dag_layer, layout_layer, &layout.scratch_space_mapping)
            .map_err(EvaluationCompileError::Forward)?;
        let compute_roots = actions
            .iter()
            .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
            .collect::<Vec<_>>();
        let expr_fields = (0..dag_layer.exprs.len())
            .map(|index| {
                match expr_operand_field(dag_layer, ExprId(index as u32), &cross_layer_fields) {
                    OperandField::Base => FieldKind::Base,
                    OperandField::Ext => FieldKind::Ext,
                }
            })
            .collect::<Vec<_>>();
        let context = PlanSearchContext::build_for_roots(
            dag_layer,
            &expr_fields,
            layout_layer.layer,
            budget_lanes,
            &compute_roots,
        )?;
        let outcome = mutation_search(&context, config)?;
        let mut selected_genome = outcome.best_genome;
        let mut selected_fitness = outcome.best.fitness;

        if let Some(incumbent) = incumbent {
            let incumbent_layer = &incumbent.layers[layer_index];
            incumbent_layer.validate_against(circuit, &context, &actions)?;
            let scored = context.score(&incumbent_layer.genome)?;
            if scored.fitness != incumbent_layer.expected_fitness {
                return Err(EvaluationCompileError::FitnessCertificateMismatch {
                    expected: incumbent_layer.expected_fitness,
                    actual: scored.fitness,
                });
            }
            if scored.placement == PlacementStatus::Concrete && scored.fitness <= selected_fitness {
                selected_genome = incumbent_layer.genome.clone();
                selected_fitness = scored.fitness;
            }
        }

        let captured =
            EvaluationGenomeArtifact::capture(circuit, &context, &actions, selected_genome)?;
        debug_assert_eq!(captured.expected_fitness, selected_fitness);
        layers.push(captured);
    }

    EvaluationGenomeCircuitArtifact::new(
        circuit,
        layout_variant,
        layout_fixture,
        budget_lanes,
        SearchProvenance {
            algorithm: "mutation-guided-staging-v1".to_owned(),
            seed: config.seed,
            evaluations: config.evaluations,
            staging_evaluations: config.staging_evaluations,
        },
        layers,
    )
}

/// Compile one layer from an offline genome artifact through the complete
/// action-aware path. Classification, domain verification, elaboration,
/// packing, binding, encoding, and ISA validation are one atomic contract.
#[allow(clippy::too_many_arguments)]
pub fn compile_layer_with_evaluation_genome(
    circuit: &str,
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    budget_lanes: usize,
    artifact: &EvaluationGenomeArtifact,
) -> Result<CompiledEvaluationLayer, EvaluationCompileError> {
    let actions = build_forward_actions(layer, artifact_layer, scratch_mapping)
        .map_err(EvaluationCompileError::Forward)?;
    let compute_roots = actions
        .iter()
        .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
        .collect::<Vec<_>>();
    let expr_fields = (0..layer.exprs.len())
        .map(
            |index| match expr_operand_field(layer, ExprId(index as u32), cross_layer_fields) {
                OperandField::Base => FieldKind::Base,
                OperandField::Ext => FieldKind::Ext,
            },
        )
        .collect::<Vec<_>>();
    let context = PlanSearchContext::build_for_roots(
        layer,
        &expr_fields,
        artifact_layer.layer,
        budget_lanes,
        &compute_roots,
    )?;
    artifact.validate_against(circuit, &context, &actions)?;

    let scored = context.score(&artifact.genome)?;
    if scored.placement != PlacementStatus::Concrete {
        return Err(EvaluationCompileError::GenomeNotConcrete(scored.placement));
    }
    if scored.fitness != artifact.expected_fitness {
        return Err(EvaluationCompileError::FitnessCertificateMismatch {
            expected: artifact.expected_fitness,
            actual: scored.fitness,
        });
    }
    let plan = scored
        .plan
        .as_ref()
        .ok_or(EvaluationCompileError::MissingPlan)?;
    let packed = pack_plan(plan, layer, PackConfig::default())?;
    let concrete = bind_packed_plan_with_actions(
        &packed,
        layer,
        context.materialized_roots(),
        artifact_layer.layer,
        budget_lanes,
        &actions,
        cross_layer_fields,
    )?;
    validate_compiled(&concrete.compiled, layer).map_err(EvaluationCompileError::Forward)?;

    if scored.fitness.program_instructions != concrete.compiled.stats.program_lanes {
        return Err(EvaluationCompileError::InstructionCertificateMismatch {
            scored: scored.fitness.program_instructions,
            emitted: concrete.compiled.stats.program_lanes,
        });
    }
    if scored.fitness.encoded_lanes != concrete.stats.encoded_lanes {
        return Err(EvaluationCompileError::EncodingCertificateMismatch {
            scored: scored.fitness.encoded_lanes,
            emitted: concrete.stats.encoded_lanes,
        });
    }
    if scored.fitness.dram_read_lanes != concrete.compiled.stats.dram_traffic {
        return Err(EvaluationCompileError::TrafficCertificateMismatch {
            scored: scored.fitness.dram_read_lanes,
            emitted: concrete.compiled.stats.dram_traffic,
        });
    }

    Ok(CompiledEvaluationLayer {
        concrete,
        fitness: scored.fitness,
        root_order: scored.root_order,
    })
}
