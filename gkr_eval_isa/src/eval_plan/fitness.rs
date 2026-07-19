use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};

use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, FieldKind, RootGroup, RootId, relation_units_with_caches,
};

use super::genome::root_cmp;
use super::{
    ConcreteBindError, EvalPlan, GenomeOracle, GenomeOracleError, PackConfig, PackError,
    PlacementTelemetry, PlanError, RootKey, StructuralSiteIndex, ValueFingerprint,
    bind_packed_plan, budget_lanes_from_cells,
    concrete::{bind_packed_plan_for_search, bind_packed_plan_greedy},
    elaborate_with_oracle_and_sinks, pack_plan, structural_fingerprints,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum EvaluationUnitKey {
    Relation {
        group: RootGroup,
        relation_index: usize,
    },
    Standalone(RootKey),
}

/// One indivisible forward scheduling unit. Atom roots drive traversal; cache
/// roots are sink obligations discharged eagerly when their expression is
/// produced. Roots are sorted by semantic identity rather than arena/root ID.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationUnit {
    pub key: EvaluationUnitKey,
    pub roots: Vec<RootId>,
}

#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct EvaluationGenome {
    pub root_order_key: Vec<f64>,
    pub cache_priority: Vec<f64>,
    /// Sparse Add→Mul→computed-operand staging priorities.
    pub staging_priority: Vec<f64>,
}

impl EvaluationGenome {
    pub fn neutral(context: &PlanSearchContext<'_>) -> Self {
        let unit_count = context.units.len();
        let denominator = unit_count.max(1) as f64;
        Self {
            root_order_key: (0..unit_count)
                .map(|index| index as f64 / denominator)
                .collect(),
            cache_priority: vec![0.0; context.site_index.len()],
            staging_priority: vec![0.0; context.site_index.staging_pairs().len()],
        }
    }

    /// Admit every real backing-read leaf that still has future demand. This is
    /// the zero-overhead baseline: compound retention is deliberately deferred
    /// to secondary instruction optimization so it cannot crowd out read leaves.
    pub fn retentive(context: &PlanSearchContext<'_>) -> Self {
        let mut genome = Self::neutral(context);
        for (index, site) in context.site_index.sites().iter().enumerate() {
            if context
                .site_index
                .profile(site.value)
                .is_some_and(|profile| profile.is_dram_leaf)
            {
                genome.cache_priority[index] = 1.0;
            }
        }
        genome
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum FitnessError {
    BudgetCellsOutOfRange { budget_cells: usize },
    UnitConstruction(String),
    Oracle(GenomeOracleError),
    Pack(PackError),
    Concrete(ConcreteBindError),
    Plan(PlanError),
    OrderGeneCount { expected: usize, actual: usize },
    NonFiniteOrderGene { index: usize, value: f64 },
    ActiveSitesRemaining(usize),
}

impl From<GenomeOracleError> for FitnessError {
    fn from(value: GenomeOracleError) -> Self {
        Self::Oracle(value)
    }
}

impl From<PackError> for FitnessError {
    fn from(value: PackError) -> Self {
        Self::Pack(value)
    }
}

/// Lexicographic objective: feasibility, width-weighted DRAM reads, emitted
/// program instructions, encoded VM lanes, then post-normalization scalar
/// arithmetic work. Before placement, instruction/lane counts are relocation-
/// free lower bounds; concrete binding replaces them with the actual totals.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct PlanFitness {
    pub infeasible: bool,
    pub dram_read_lanes: usize,
    pub program_instructions: usize,
    pub encoded_lanes: usize,
    pub arithmetic_ops: usize,
}

pub fn fitness_key(fitness: PlanFitness) -> (u8, usize, usize, usize, usize) {
    (
        fitness.infeasible as u8,
        fitness.dram_read_lanes,
        fitness.program_instructions,
        fitness.encoded_lanes,
        fitness.arithmetic_ops,
    )
}

#[derive(Clone, Debug)]
pub struct ScoredEvaluation {
    pub root_order: Vec<RootId>,
    /// Symbolic plan when elaboration succeeded. `Unverified` plans must still
    /// pass `bind_packed_plan` before they can be emitted or become winners.
    pub plan: Option<EvalPlan>,
    pub fitness: PlanFitness,
    pub placement: PlacementStatus,
    pub placement_telemetry: PlacementTelemetry,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlacementStatus {
    /// Greedy or exact placement produced a concrete certificate.
    Concrete,
    /// Exact placement was skipped because this fitness could not replace the
    /// concrete incumbent. The candidate remains useful as a search parent.
    Unverified,
    /// Exact placement was attempted but did not find a placement within its
    /// bounded search budget.
    PlacementInfeasible,
    /// Elaboration itself exceeded the accumulator/resident lane budget.
    ElaborationInfeasible,
}

pub struct PlanSearchContext<'a> {
    layer: &'a DagLayer,
    expr_fields: Vec<FieldKind>,
    expr_fingerprints: Vec<ValueFingerprint>,
    /// Artifact layer identity used when concrete certification binds Export sinks.
    this_layer: usize,
    budget_cells: usize,
    units: Vec<EvaluationUnit>,
    fallback_roots: Vec<RootId>,
    /// Every selected root whose sink must be discharged. Cache roots live
    /// here but do not become independently scheduled evaluation roots.
    selected_roots: Vec<RootId>,
    site_index: StructuralSiteIndex,
}

impl<'a> PlanSearchContext<'a> {
    /// Build a search context for every materialized root in one artifact layer.
    /// `this_layer` is required for faithful concrete binding of Export sinks.
    pub fn build(
        layer: &'a DagLayer,
        expr_fields: &[FieldKind],
        this_layer: usize,
        budget_cells: usize,
    ) -> Result<Self, FitnessError> {
        Self::build_selected(layer, expr_fields, this_layer, budget_cells, None)
    }

    /// Build a search domain for an explicitly selected set of materialized
    /// roots. The forward compiler uses this seam after classifying roots into
    /// `Compute`, copy-alias, and scratch-prefill actions: only `Compute` roots
    /// belong in expression evaluation. `this_layer` is the artifact layer
    /// identity used by every search-time concrete certificate.
    pub fn build_for_roots(
        layer: &'a DagLayer,
        expr_fields: &[FieldKind],
        this_layer: usize,
        budget_cells: usize,
        roots: &[RootId],
    ) -> Result<Self, FitnessError> {
        Self::build_selected(layer, expr_fields, this_layer, budget_cells, Some(roots))
    }

    fn build_selected(
        layer: &'a DagLayer,
        expr_fields: &[FieldKind],
        this_layer: usize,
        budget_cells: usize,
        roots: Option<&[RootId]>,
    ) -> Result<Self, FitnessError> {
        Self::build_selected_with_units_inner(
            layer,
            expr_fields,
            this_layer,
            budget_cells,
            roots,
            adapt_forward_relations(layer)?,
        )
    }

    #[cfg(test)]
    pub(crate) fn build_selected_with_units(
        layer: &'a DagLayer,
        expr_fields: &[FieldKind],
        this_layer: usize,
        budget_cells: usize,
        roots: Option<&[RootId]>,
        units: Vec<EvaluationUnit>,
    ) -> Result<Self, FitnessError> {
        Self::build_selected_with_units_inner(
            layer,
            expr_fields,
            this_layer,
            budget_cells,
            roots,
            units,
        )
    }

    fn build_selected_with_units_inner(
        layer: &'a DagLayer,
        expr_fields: &[FieldKind],
        this_layer: usize,
        budget_cells: usize,
        roots: Option<&[RootId]>,
        mut units: Vec<EvaluationUnit>,
    ) -> Result<Self, FitnessError> {
        budget_lanes_from_cells(budget_cells)
            .ok_or(FitnessError::BudgetCellsOutOfRange { budget_cells })?;
        let mut selected_roots = roots.map_or_else(
            || {
                layer
                    .roots
                    .iter()
                    .enumerate()
                    .filter_map(|(index, root)| {
                        root.materialize.is_some().then_some(RootId(index as u32))
                    })
                    .collect::<Vec<_>>()
            },
            <[RootId]>::to_vec,
        );
        let selected = selected_roots.iter().copied().collect::<HashSet<_>>();
        if selected.len() != selected_roots.len() {
            return Err(FitnessError::UnitConstruction(
                "selected forward roots contain duplicates".into(),
            ));
        }
        for &root in &selected_roots {
            let Some(root_info) = layer.roots.get(root.0 as usize) else {
                return Err(FitnessError::UnitConstruction(format!(
                    "selected forward root {} is out of bounds",
                    root.0
                )));
            };
            if root_info.materialize.is_none() {
                return Err(FitnessError::UnitConstruction(format!(
                    "selected forward root {} has no materialization sink",
                    root.0
                )));
            }
        }
        units.retain_mut(|unit| {
            unit.roots.retain(|root| selected.contains(root));
            !unit.roots.is_empty()
        });
        let fingerprints = structural_fingerprints(layer)
            .map_err(PlanError::from)
            .map_err(FitnessError::Plan)?;
        sort_roots(layer, &fingerprints, &mut selected_roots);
        let atom_roots = units
            .iter()
            .flat_map(|unit| unit.roots.iter().copied())
            .collect::<Vec<_>>();
        let reachable = reachable_exprs(layer, &atom_roots);
        let atom_set = atom_roots.iter().copied().collect::<HashSet<_>>();
        let mut fallback_by_expr = BTreeMap::<ExprId, RootId>::new();
        for &root in &selected_roots {
            let expr = layer.roots[root.0 as usize].expr;
            if !atom_set.contains(&root) && !reachable.contains(&expr) {
                fallback_by_expr.entry(expr).or_insert(root);
            }
        }
        let fallback_roots = fallback_by_expr.into_values().collect::<Vec<_>>();
        let driver_roots = atom_roots
            .iter()
            .chain(&fallback_roots)
            .copied()
            .collect::<Vec<_>>();
        let site_index = StructuralSiteIndex::build(layer, expr_fields, &driver_roots)?;
        Ok(Self {
            layer,
            expr_fields: expr_fields.to_vec(),
            expr_fingerprints: fingerprints,
            this_layer,
            budget_cells,
            units,
            fallback_roots,
            selected_roots,
            site_index,
        })
    }

    pub fn units(&self) -> &[EvaluationUnit] {
        &self.units
    }

    pub fn selected_roots(&self) -> &[RootId] {
        &self.selected_roots
    }

    pub fn materialized_roots(&self) -> &[RootId] {
        &self.selected_roots
    }

    pub fn site_index(&self) -> &StructuralSiteIndex {
        &self.site_index
    }

    pub fn layer_index(&self) -> usize {
        self.this_layer
    }

    pub fn budget_cells(&self) -> usize {
        self.budget_cells
    }

    pub(crate) fn budget_lanes(&self) -> usize {
        budget_lanes_from_cells(self.budget_cells)
            .expect("PlanSearchContext validates its immutable cell budget at construction")
    }

    pub fn selected_root_keys(&self) -> Vec<RootKey> {
        self.selected_roots
            .iter()
            .map(|&root| root_key(self.layer, &self.expr_fingerprints, root))
            .collect()
    }

    pub(crate) fn layer(&self) -> &DagLayer {
        self.layer
    }

    pub(crate) fn expression_fingerprint(&self, expr: ExprId) -> ValueFingerprint {
        self.expr_fingerprints[expr.0 as usize]
    }

    pub(crate) fn unit_index_for_root_key(&self, key: &RootKey) -> Option<usize> {
        self.units.iter().position(|unit| {
            unit.roots
                .iter()
                .any(|&root| root_key(self.layer, &self.expr_fingerprints, root) == *key)
        })
    }

    pub fn decode_root_order(&self, keys: &[f64]) -> Result<Vec<RootId>, FitnessError> {
        if keys.len() != self.units.len() {
            return Err(FitnessError::OrderGeneCount {
                expected: self.units.len(),
                actual: keys.len(),
            });
        }
        if let Some((index, &value)) = keys
            .iter()
            .enumerate()
            .find(|(_, value)| !value.is_finite())
        {
            return Err(FitnessError::NonFiniteOrderGene { index, value });
        }
        let mut unit_order: Vec<_> = (0..self.units.len()).collect();
        unit_order.sort_by(|&a, &b| keys[a].total_cmp(&keys[b]).then_with(|| a.cmp(&b)));
        let mut roots = unit_order
            .into_iter()
            .flat_map(|unit| self.units[unit].roots.iter().copied())
            .collect::<Vec<_>>();
        roots.extend_from_slice(&self.fallback_roots);
        Ok(roots)
    }

    pub fn score(&self, genome: &EvaluationGenome) -> Result<ScoredEvaluation, FitnessError> {
        self.score_internal(genome, None)
    }

    pub(crate) fn score_for_search(
        &self,
        genome: &EvaluationGenome,
        concrete_incumbent: PlanFitness,
    ) -> Result<ScoredEvaluation, FitnessError> {
        self.score_internal(genome, Some(concrete_incumbent))
    }

    fn score_internal(
        &self,
        genome: &EvaluationGenome,
        exact_gate: Option<PlanFitness>,
    ) -> Result<ScoredEvaluation, FitnessError> {
        let root_order = self.decode_root_order(&genome.root_order_key)?;
        let mut oracle = GenomeOracle::new(
            &self.site_index,
            &genome.cache_priority,
            &genome.staging_priority,
        )?;
        match elaborate_with_oracle_and_sinks(
            self.layer,
            &self.expr_fields,
            &root_order,
            &self.selected_roots,
            self.budget_lanes(),
            &mut oracle,
        ) {
            Ok(plan) => {
                let active = oracle.active_site_count();
                if active != 0 {
                    return Err(FitnessError::ActiveSitesRemaining(active));
                }
                let packed = pack_plan(&plan, self.layer, PackConfig::default())?;
                let fitness = PlanFitness {
                    infeasible: false,
                    dram_read_lanes: plan.stats.dram_read_lanes,
                    program_instructions: packed.stats.packed_instructions,
                    encoded_lanes: packed.stats.encoded_lanes,
                    arithmetic_ops: packed.stats.scalar_arithmetic_ops,
                };
                match bind_packed_plan_greedy(
                    &packed,
                    self.layer,
                    &self.selected_roots,
                    self.this_layer,
                    self.budget_lanes(),
                ) {
                    Ok(concrete) => {
                        let fitness = concrete_fitness(fitness, &concrete);
                        return Ok(ScoredEvaluation {
                            root_order,
                            plan: Some(plan),
                            fitness,
                            placement: PlacementStatus::Concrete,
                            placement_telemetry: concrete.stats.placement,
                        });
                    }
                    Err(ConcreteBindError::PlacementFailed { .. }) => {}
                    Err(error) => return Err(FitnessError::Concrete(error)),
                }
                if exact_gate.is_some_and(|incumbent| fitness >= incumbent) {
                    return Ok(ScoredEvaluation {
                        root_order,
                        plan: Some(plan),
                        fitness,
                        placement: PlacementStatus::Unverified,
                        placement_telemetry: PlacementTelemetry::default(),
                    });
                }
                let concrete = if exact_gate.is_some() {
                    bind_packed_plan_for_search(
                        &packed,
                        self.layer,
                        &self.selected_roots,
                        self.this_layer,
                        self.budget_lanes(),
                    )
                } else {
                    bind_packed_plan(
                        &packed,
                        self.layer,
                        &self.selected_roots,
                        self.this_layer,
                        self.budget_lanes(),
                    )
                };
                match concrete {
                    Ok(concrete) => {
                        let fitness = concrete_fitness(fitness, &concrete);
                        Ok(ScoredEvaluation {
                            root_order,
                            plan: Some(plan),
                            fitness,
                            placement: PlacementStatus::Concrete,
                            placement_telemetry: concrete.stats.placement,
                        })
                    }
                    Err(ConcreteBindError::PlacementFailed { telemetry, .. }) => {
                        Ok(infeasible_evaluation(
                            root_order,
                            PlacementStatus::PlacementInfeasible,
                            telemetry,
                        ))
                    }
                    Err(error) => Err(FitnessError::Concrete(error)),
                }
            }
            Err(PlanError::BudgetExceeded { .. }) => Ok(infeasible_evaluation(
                root_order,
                PlacementStatus::ElaborationInfeasible,
                PlacementTelemetry::default(),
            )),
            Err(error) => Err(FitnessError::Plan(error)),
        }
    }
}

fn concrete_fitness(
    mut fitness: PlanFitness,
    concrete: &super::ConcreteEvalProgram,
) -> PlanFitness {
    fitness.encoded_lanes = concrete.stats.encoded_lanes;
    fitness.program_instructions = concrete.compiled.stats.program_lanes;
    fitness
}

fn infeasible_evaluation(
    root_order: Vec<RootId>,
    placement: PlacementStatus,
    placement_telemetry: PlacementTelemetry,
) -> ScoredEvaluation {
    ScoredEvaluation {
        root_order,
        plan: None,
        fitness: PlanFitness {
            infeasible: true,
            dram_read_lanes: usize::MAX,
            program_instructions: usize::MAX,
            encoded_lanes: usize::MAX,
            arithmetic_ops: usize::MAX,
        },
        placement,
        placement_telemetry,
    }
}

pub fn adapt_forward_relations(layer: &DagLayer) -> Result<Vec<EvaluationUnit>, FitnessError> {
    let fingerprints = structural_fingerprints(layer)
        .map_err(PlanError::from)
        .map_err(FitnessError::Plan)?;
    let canonical = relation_units_with_caches(layer).map_err(FitnessError::UnitConstruction)?;
    let mut included = vec![false; layer.roots.len()];
    let mut units = Vec::with_capacity(canonical.len());

    for relation in canonical {
        let mut cache_roots = relation.cache_roots;
        let mut atom_roots = relation.atom_roots;
        sort_roots(layer, &fingerprints, &mut cache_roots);
        sort_roots(layer, &fingerprints, &mut atom_roots);
        for root in cache_roots.iter().chain(&atom_roots) {
            included[root.0 as usize] = true;
        }
        units.push(EvaluationUnit {
            key: EvaluationUnitKey::Relation {
                group: relation.group,
                relation_index: relation.relation_index,
            },
            roots: atom_roots,
        });
    }

    // Materialized roots outside the relation decomposition remain forward
    // work and receive stable singleton order genes. Claim-only roots do not.
    for (index, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() || included[index] {
            continue;
        }
        let root_id = RootId(index as u32);
        units.push(EvaluationUnit {
            key: EvaluationUnitKey::Standalone(root_key(layer, &fingerprints, root_id)),
            roots: vec![root_id],
        });
    }
    units.sort_by(unit_cmp);
    Ok(units)
}

#[cfg(test)]
mod tests;

fn reachable_exprs(layer: &DagLayer, roots: &[RootId]) -> HashSet<ExprId> {
    let mut reachable = HashSet::new();
    let mut stack = roots
        .iter()
        .map(|root| layer.roots[root.0 as usize].expr)
        .collect::<Vec<_>>();
    while let Some(expr) = stack.pop() {
        if !reachable.insert(expr) || layer.resolutions.contains_key(&expr) {
            continue;
        }
        match &layer.exprs[expr.0 as usize] {
            Expr::Source(_) => {}
            Expr::Add(children) | Expr::Mul(children) => stack.extend(children.iter().copied()),
        }
    }
    reachable
}

fn sort_roots(layer: &DagLayer, fingerprints: &[ValueFingerprint], roots: &mut [RootId]) {
    roots.sort_by(|&a, &b| {
        root_cmp(
            &root_key(layer, fingerprints, a),
            &root_key(layer, fingerprints, b),
        )
    });
}

fn root_key(layer: &DagLayer, fingerprints: &[ValueFingerprint], root_id: RootId) -> RootKey {
    let root = &layer.roots[root_id.0 as usize];
    RootKey {
        expr: fingerprints[root.expr.0 as usize],
        materialize: root.materialize.clone(),
        claim_origin: root.claim.as_ref().map(|claim| claim.origin.clone()),
    }
}

fn unit_cmp(a: &EvaluationUnit, b: &EvaluationUnit) -> Ordering {
    match (&a.key, &b.key) {
        (
            EvaluationUnitKey::Relation {
                group: a_group,
                relation_index: a_index,
            },
            EvaluationUnitKey::Relation {
                group: b_group,
                relation_index: b_index,
            },
        ) => group_key(a_group)
            .cmp(&group_key(b_group))
            .then_with(|| a_index.cmp(b_index)),
        (EvaluationUnitKey::Relation { .. }, EvaluationUnitKey::Standalone(_)) => Ordering::Less,
        (EvaluationUnitKey::Standalone(_), EvaluationUnitKey::Relation { .. }) => Ordering::Greater,
        (EvaluationUnitKey::Standalone(a), EvaluationUnitKey::Standalone(b)) => root_cmp(a, b),
    }
}

fn group_key(group: &RootGroup) -> u8 {
    match group {
        RootGroup::Gates => 0,
        RootGroup::GatesExternal => 1,
    }
}
