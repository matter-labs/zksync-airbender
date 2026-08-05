use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};

use gkr_eval_ir::{
    DagLayer, Expr, ExprId, FieldKind, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind,
    SourceKind,
};

use super::{
    CacheOracle, CacheStateView, PlanError, ReductionOp, RetentionPreference, RootKey, SiteId,
    StagingPreference, ValueFingerprint, enumerate_structural_sites, field_lanes,
    structural_fingerprints,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueCostProfile {
    /// Width occupied while this value is resident (Base=1, Ext=4).
    pub cache_lanes: usize,
    /// This value is itself a real backing read, rather than a compound whose
    /// recomputation merely reaches backing reads in its cone.
    pub is_dram_leaf: bool,
    /// Width-weighted direct `Read` traffic incurred by recomputing its full
    /// expression cone with no cache hits.
    pub recompute_dram_lanes: usize,
    /// Scalar Add/Mul work incurred by recomputing its full expression cone
    /// with no cache hits. This admits compute-only values into cache search.
    pub recompute_arithmetic_ops: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub enum GenomeOracleError {
    Plan(PlanError),
    GeneCount {
        expected: usize,
        actual: usize,
    },
    NonFiniteGene {
        index: usize,
        value: f64,
    },
    FingerprintProfileConflict {
        value: ValueFingerprint,
        first: ValueCostProfile,
        second: ValueCostProfile,
    },
}

impl From<PlanError> for GenomeOracleError {
    fn from(value: PlanError) -> Self {
        Self::Plan(value)
    }
}

/// Stable dense serialization of the execution-independent structural site
/// domain. The ordering compares semantic root/path fields explicitly and does
/// not use arena IDs, root execution order, or randomized hash iteration.
#[derive(Clone, Debug)]
pub struct StructuralSiteIndex {
    sites: Vec<SiteId>,
    positions: HashMap<SiteId, usize>,
    profiles: HashMap<ValueFingerprint, ValueCostProfile>,
    staging_pairs: Vec<StagingPair>,
    dram_priority_scale: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct StagingPair {
    pub boundary: SiteId,
    pub staged: SiteId,
}

impl StructuralSiteIndex {
    pub fn build(
        layer: &DagLayer,
        expr_fields: &[FieldKind],
        roots: &[RootId],
    ) -> Result<Self, GenomeOracleError> {
        if expr_fields.len() != layer.exprs.len() {
            return Err(PlanError::FieldCount {
                expected: layer.exprs.len(),
                actual: expr_fields.len(),
            }
            .into());
        }

        let mut sites: Vec<_> = enumerate_structural_sites(layer, roots)?
            .into_iter()
            .collect();
        sites.sort_by(stable_site_cmp);
        let positions: HashMap<SiteId, usize> = sites
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, site)| (site, index))
            .collect();

        let fingerprints = structural_fingerprints(layer).map_err(PlanError::from)?;
        let mut read_memo = vec![None; layer.exprs.len()];
        let mut arithmetic_memo = vec![None; layer.exprs.len()];
        let mut profiles = HashMap::new();
        let mut reductions = HashMap::new();
        for expr_index in 0..layer.exprs.len() {
            let expr = ExprId(expr_index as u32);
            let profile = ValueCostProfile {
                cache_lanes: field_lanes(expr_fields[expr_index]),
                is_dram_leaf: !layer.resolutions.contains_key(&expr)
                    && matches!(
                        &layer.exprs[expr_index],
                        Expr::Source(source)
                            if matches!(
                                layer.sources[source.0 as usize].kind,
                                SourceKind::Read { .. }
                            )
                    ),
                recompute_dram_lanes: recompute_dram_lanes(
                    layer,
                    expr_fields,
                    expr,
                    &mut read_memo,
                ),
                recompute_arithmetic_ops: recompute_arithmetic_ops(
                    layer,
                    expr,
                    &mut arithmetic_memo,
                ),
            };
            let fingerprint = fingerprints[expr_index];
            if let Some(&first) = profiles.get(&fingerprint) {
                if first != profile {
                    return Err(GenomeOracleError::FingerprintProfileConflict {
                        value: fingerprint,
                        first,
                        second: profile,
                    });
                }
            } else {
                profiles.insert(fingerprint, profile);
            }
            let reduction = match layer.exprs[expr_index] {
                Expr::Add(_) => Some(ReductionOp::Add),
                Expr::Mul(_) => Some(ReductionOp::Mul),
                Expr::Source(_) => None,
            };
            reductions.entry(fingerprint).or_insert(reduction);
        }

        let dram_priority_scale = profiles
            .values()
            .map(|profile| profile.recompute_arithmetic_ops)
            .max()
            .unwrap_or(0)
            .saturating_add(1);
        let mut staging_pairs = Vec::new();
        for staged in &sites {
            if profiles
                .get(&staged.value)
                .is_none_or(|profile| profile.recompute_arithmetic_ops == 0)
            {
                continue;
            }

            // Readiness at the reduction itself represents computing an input
            // in the middle of its parent's operation. This is useful for a
            // wide Mul, and for a structurally shared/nested Add operand.
            if let Some(last) = staged.path.last() {
                let ready_at_reduction = last.operation == ReductionOp::Mul
                    || (last.operation == ReductionOp::Add
                        && reductions.get(&staged.value) == Some(&Some(ReductionOp::Add)));
                if ready_at_reduction {
                    push_staging_pair(
                        &mut staging_pairs,
                        &positions,
                        staged,
                        staged.path.len() - 1,
                    );
                }
            }

            // A computed factor under Add -> Mul must instead be ready before
            // the Add starts if the product is to join that additive FMA run.
            // Keeping both boundaries in the genome is the explicit choice
            // between an upfront fused frontier and mid-operation splitting.
            if staged.path.len() >= 2 {
                let boundary_depth = staged.path.len() - 2;
                if staged.path[boundary_depth].operation == ReductionOp::Add
                    && staged.path[boundary_depth + 1].operation == ReductionOp::Mul
                {
                    push_staging_pair(&mut staging_pairs, &positions, staged, boundary_depth);
                }
            }
        }
        staging_pairs.sort_by(|a, b| {
            stable_site_cmp(&a.boundary, &b.boundary)
                .then_with(|| stable_site_cmp(&a.staged, &b.staged))
        });
        staging_pairs.dedup();
        Ok(Self {
            sites,
            positions,
            profiles,
            staging_pairs,
            dram_priority_scale,
        })
    }

    pub fn sites(&self) -> &[SiteId] {
        &self.sites
    }

    pub fn len(&self) -> usize {
        self.sites.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    pub fn position(&self, site: &SiteId) -> Option<usize> {
        self.positions.get(site).copied()
    }

    pub fn profile(&self, value: ValueFingerprint) -> Option<ValueCostProfile> {
        self.profiles.get(&value).copied()
    }

    pub fn staging_pairs(&self) -> &[StagingPair] {
        &self.staging_pairs
    }
}

fn push_staging_pair(
    pairs: &mut Vec<StagingPair>,
    positions: &HashMap<SiteId, usize>,
    staged: &SiteId,
    boundary_depth: usize,
) {
    let boundary = SiteId {
        root: staged.root.clone(),
        path: staged.path[..boundary_depth].to_vec(),
        value: if boundary_depth == 0 {
            staged.root.expr
        } else {
            staged.path[boundary_depth - 1].child
        },
    };
    if positions.contains_key(&boundary) {
        pairs.push(StagingPair {
            boundary,
            staged: staged.clone(),
        });
    }
}

/// Stateful decoder for one cache-priority genome.
///
/// A gene scores the importance of its future demand site; it is not a literal
/// "cache here" bit. At each actual traversal callback the oracle consumes the
/// current demand, prunes descendants skipped by a cache hit, and derives a
/// ranked survivor set from the still-active future demands. Non-positive genes
/// produce the no-caching baseline.
pub struct GenomeOracle<'a> {
    index: &'a StructuralSiteIndex,
    genes: &'a [f64],
    staging_genes: &'a [f64],
    active: Vec<bool>,
}

impl<'a> GenomeOracle<'a> {
    pub fn new(
        index: &'a StructuralSiteIndex,
        genes: &'a [f64],
        staging_genes: &'a [f64],
    ) -> Result<Self, GenomeOracleError> {
        if genes.len() != index.len() {
            return Err(GenomeOracleError::GeneCount {
                expected: index.len(),
                actual: genes.len(),
            });
        }
        if let Some((index, &value)) = genes
            .iter()
            .enumerate()
            .find(|(_, value)| !value.is_finite())
        {
            return Err(GenomeOracleError::NonFiniteGene { index, value });
        }
        if staging_genes.len() != index.staging_pairs.len() {
            return Err(GenomeOracleError::GeneCount {
                expected: index.staging_pairs.len(),
                actual: staging_genes.len(),
            });
        }
        if let Some((index, &value)) = staging_genes
            .iter()
            .enumerate()
            .find(|(_, value)| !value.is_finite())
        {
            return Err(GenomeOracleError::NonFiniteGene { index, value });
        }
        Ok(Self {
            index,
            genes,
            staging_genes,
            active: vec![true; index.len()],
        })
    }

    pub fn active_site_count(&self) -> usize {
        self.active.iter().filter(|&&active| active).count()
    }

    fn retire_descendants(&mut self, site: &SiteId) {
        for (index, candidate) in self.index.sites.iter().enumerate() {
            if self.active[index] && is_strict_descendant(candidate, site) {
                self.active[index] = false;
            }
        }
    }

    /// Demands that occur after the current expression has completed. Active
    /// strict descendants belong to the expression's own evaluation cone, so
    /// they are deliberately excluded: they can justify producing a survivor,
    /// but cannot justify keeping it beyond this scope by themselves.
    fn demands_after(&self, site: &SiteId) -> BTreeMap<ValueFingerprint, DemandSummary> {
        let mut demands = BTreeMap::new();
        for (index, candidate) in self.index.sites.iter().enumerate() {
            if !self.active[index] || is_strict_descendant(candidate, site) {
                continue;
            }
            let gene = self.genes[index];
            demands
                .entry(candidate.value)
                .and_modify(|summary: &mut DemandSummary| {
                    summary.max_gene = summary.max_gene.max(gene);
                })
                .or_insert(DemandSummary { max_gene: gene });
        }
        demands
    }
}

impl CacheOracle for GenomeOracle<'_> {
    fn stage_before(&mut self, boundary: &SiteId) -> Vec<StagingPreference> {
        self.index
            .staging_pairs
            .iter()
            .zip(self.staging_genes)
            .filter(|(pair, priority)| pair.boundary == *boundary && **priority > 0.0)
            .map(|(pair, &priority)| StagingPreference {
                site: pair.staged.clone(),
                priority,
            })
            .collect()
    }

    fn desired_after(
        &mut self,
        site: &SiteId,
        entry: CacheStateView<'_>,
    ) -> Vec<RetentionPreference> {
        let index = self
            .index
            .position(site)
            .unwrap_or_else(|| panic!("actual traversal site is absent from structural index"));
        assert!(
            self.active[index],
            "structural site was visited twice or after its cone was pruned: {site:?}"
        );
        self.active[index] = false;

        let hit = entry
            .residents
            .iter()
            .any(|resident| resident.fingerprint == site.value);
        if hit {
            self.retire_descendants(site);
        }

        let after = self.demands_after(site);
        // Current and resident values already exist. Descendants are candidates
        // only because this cone can produce them; every selected value must
        // also have a demand outside the cone in `after`.
        let mut candidates = BTreeMap::<ValueFingerprint, ()>::new();
        candidates.insert(site.value, ());
        for resident in entry.residents {
            candidates.insert(resident.fingerprint, ());
        }
        for (candidate_index, candidate) in self.index.sites.iter().enumerate() {
            if self.active[candidate_index] && is_strict_descendant(candidate, site) {
                candidates.insert(candidate.value, ());
            }
        }

        candidates
            .into_iter()
            .filter_map(|(value, ())| {
                let demand = after.get(&value)?;
                if demand.max_gene <= 0.0 {
                    return None;
                }
                let profile = self
                    .index
                    .profile(value)
                    .expect("every structural value must have a cost profile");
                if profile.recompute_dram_lanes == 0 && profile.recompute_arithmetic_ops == 0 {
                    return None;
                }
                let weighted_recompute = profile
                    .recompute_dram_lanes
                    .saturating_mul(self.index.dram_priority_scale)
                    .saturating_add(profile.recompute_arithmetic_ops);
                Some(RetentionPreference {
                    value,
                    priority: demand.max_gene * weighted_recompute as f64
                        / profile.cache_lanes as f64,
                })
            })
            .collect()
    }
}

#[derive(Clone, Copy)]
struct DemandSummary {
    max_gene: f64,
}

fn is_strict_descendant(candidate: &SiteId, ancestor: &SiteId) -> bool {
    candidate.root == ancestor.root
        && candidate.path.len() > ancestor.path.len()
        && candidate.path.starts_with(&ancestor.path)
}

fn recompute_dram_lanes(
    layer: &DagLayer,
    expr_fields: &[FieldKind],
    expr: ExprId,
    memo: &mut [Option<usize>],
) -> usize {
    let index = expr.0 as usize;
    if let Some(value) = memo[index] {
        return value;
    }
    let value = if layer.resolutions.contains_key(&expr) {
        0
    } else {
        match &layer.exprs[index] {
            Expr::Source(source) => match &layer.sources[source.0 as usize].kind {
                SourceKind::Read { .. } => field_lanes(expr_fields[index]),
                SourceKind::Constant { .. }
                | SourceKind::Challenge { .. }
                | SourceKind::VirtualSetup { .. }
                | SourceKind::LookupValue { .. } => 0,
            },
            Expr::Add(children) | Expr::Mul(children) => children
                .iter()
                .map(|&child| recompute_dram_lanes(layer, expr_fields, child, memo))
                .sum(),
        }
    };
    memo[index] = Some(value);
    value
}

fn recompute_arithmetic_ops(layer: &DagLayer, expr: ExprId, memo: &mut [Option<usize>]) -> usize {
    let index = expr.0 as usize;
    if let Some(value) = memo[index] {
        return value;
    }
    let value = if layer.resolutions.contains_key(&expr) {
        0
    } else {
        match &layer.exprs[index] {
            Expr::Source(_) => 0,
            Expr::Add(children) | Expr::Mul(children) => children
                .iter()
                .map(|&child| recompute_arithmetic_ops(layer, child, memo))
                .sum::<usize>()
                .saturating_add(children.len().saturating_sub(1)),
        }
    };
    memo[index] = Some(value);
    value
}

fn stable_site_cmp(a: &SiteId, b: &SiteId) -> Ordering {
    root_cmp(&a.root, &b.root)
        .then_with(|| path_cmp(a, b))
        .then_with(|| a.value.cmp(&b.value))
}

pub(super) fn root_cmp(a: &RootKey, b: &RootKey) -> Ordering {
    a.expr
        .cmp(&b.expr)
        .then_with(|| optional_sink_cmp(&a.materialize, &b.materialize))
        .then_with(|| optional_origin_cmp(&a.claim_origin, &b.claim_origin))
}

fn optional_sink_cmp(a: &Option<SinkInfo>, b: &Option<SinkInfo>) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => sink_kind_key(&a.kind)
            .cmp(&sink_kind_key(&b.kind))
            .then_with(|| field_key(a.field).cmp(&field_key(b.field))),
    }
}

fn sink_kind_key(kind: &SinkKind) -> (u8, usize, usize) {
    match kind {
        SinkKind::Inner { layer, offset } => (0, *layer, *offset),
        SinkKind::Cache { layer, offset } => (1, *layer, *offset),
        SinkKind::Export { slot } => (2, *slot, 0),
        SinkKind::Scratch { slot } => (3, *slot, 0),
    }
}

fn field_key(field: FieldKind) -> u8 {
    match field {
        FieldKind::Base => 0,
        FieldKind::Ext => 1,
    }
}

fn optional_origin_cmp(a: &Option<RootOrigin>, b: &Option<RootOrigin>) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => origin_key(a).cmp(&origin_key(b)),
    }
}

fn origin_key(origin: &RootOrigin) -> (u8, usize, u8, usize) {
    let group = match origin.group {
        RootGroup::Gates => 0,
        RootGroup::GatesExternal => 1,
    };
    let (slot, index) = match origin.slot {
        RootSlot::Output(index) => (0, index),
        RootSlot::Constraint(index) => (1, index),
    };
    (group, origin.relation_index, slot, index)
}

fn path_cmp(a: &SiteId, b: &SiteId) -> Ordering {
    for (a, b) in a.path.iter().zip(&b.path) {
        let ordering = a
            .parent
            .cmp(&b.parent)
            .then_with(|| reduction_key(a.operation).cmp(&reduction_key(b.operation)))
            .then_with(|| a.child.cmp(&b.child))
            .then_with(|| a.duplicate_ordinal.cmp(&b.duplicate_ordinal));
        if ordering != Ordering::Equal {
            return ordering;
        }
    }
    a.path.len().cmp(&b.path.len())
}

fn reduction_key(operation: ReductionOp) -> u8 {
    match operation {
        ReductionOp::Add => 0,
        ReductionOp::Mul => 1,
    }
}
