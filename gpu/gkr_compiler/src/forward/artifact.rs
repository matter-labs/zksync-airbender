//! Persisted offline-search result for the forward pass.
use gkr_eval_ir::{ExprId, RootId};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForwardArtifactError {
    Malformed { origin: String, message: String },
    Invalid(String),
}

impl fmt::Display for ForwardArtifactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { origin, message } => {
                write!(f, "malformed forward artifact {origin}: {message}")
            }
            Self::Invalid(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for ForwardArtifactError {}

pub fn parse_forward_artifact(
    bytes: &[u8],
    origin: &str,
) -> Result<ForwardSearchArtifact, ForwardArtifactError> {
    serde_json::from_slice(bytes).map_err(|error| ForwardArtifactError::Malformed {
        origin: origin.to_owned(),
        message: error.to_string(),
    })
}

#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForwardSearchArtifact {
    pub circuit: String,
    pub budget_buckets: usize,
    pub layers: Vec<ForwardLayerArtifact>,
}

#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForwardLayerArtifact {
    pub units: Vec<RelationUnit>,
    pub sites: Vec<(SiteKey, f64)>,
    pub predicted_traffic: usize,
}

#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RelationUnit {
    pub group: RootGroup,
    pub relation_index: usize,
}

impl ForwardLayerArtifact {
    pub(crate) fn atom_order(&self, layer: &DagLayer) -> Vec<RootId> {
        atom_order(layer, &self.units)
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[serde(deny_unknown_fields)]
pub struct SiteKey {
    pub root: RootId,
    pub consumer: SiteConsumer,
    pub value: ExprId,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[serde(deny_unknown_fields)]
pub enum SiteConsumer {
    Expr { expr: ExprId, input_index: u32 },
    RootOutput,
}

use crate::forward::compile::decisions::enumerate_site_domain;
use crate::forward::context::build_compute_roots;
use gkr_eval_ir::{DagCircuit, DagLayer, RootGroup};
use std::collections::BTreeSet;

/// Canonical relation units in first-occurrence order.
pub(crate) fn relation_units(layer: &DagLayer) -> Vec<RelationUnit> {
    let mut units = Vec::new();
    for claim in layer
        .roots
        .iter()
        .filter(|root| root.materialize.is_some())
        .filter_map(|root| root.claim.as_ref())
    {
        if !units.iter().any(|unit: &RelationUnit| {
            unit.group == claim.group && unit.relation_index == claim.relation_index
        }) {
            units.push(RelationUnit {
                group: claim.group,
                relation_index: claim.relation_index,
            });
        }
    }
    units
}

pub(crate) fn atom_order(layer: &DagLayer, units: &[RelationUnit]) -> Vec<RootId> {
    use std::collections::HashMap;
    let ranks: HashMap<_, _> = units
        .iter()
        .enumerate()
        .map(|(rank, unit)| ((unit.group, unit.relation_index), rank))
        .collect();
    let mut roots = vec![Vec::new(); units.len()];
    for (index, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() {
            continue;
        }
        let Some(claim) = root.claim.as_ref() else {
            continue;
        };
        if let Some(&rank) = ranks.get(&(claim.group, claim.relation_index)) {
            roots[rank].push(RootId(index as u32));
        }
    }
    roots.into_iter().flatten().collect()
}

pub(crate) fn validate_forward_artifact_inner(
    circuit: &DagCircuit,
    sched: &ForwardSearchArtifact,
) -> Result<(), String> {
    if sched.layers.len() != circuit.layers.len() {
        return Err(format!(
            "schedule has {} layers, circuit has {}",
            sched.layers.len(),
            circuit.layers.len()
        ));
    }
    for (li, (layer, ls)) in circuit.layers.iter().zip(&sched.layers).enumerate() {
        validate_layer_schedule(layer, ls).map_err(|e| format!("layer {li}: {e}"))?;
    }
    Ok(())
}

pub(crate) fn validate_forward_artifact(
    circuit: &DagCircuit,
    artifact: &ForwardSearchArtifact,
) -> Result<(), ForwardArtifactError> {
    validate_forward_artifact_inner(circuit, artifact).map_err(ForwardArtifactError::Invalid)
}

fn validate_layer_schedule(layer: &DagLayer, ls: &ForwardLayerArtifact) -> Result<(), String> {
    let canonical = relation_units(layer);
    if canonical.is_empty() && layer.roots.iter().any(|root| root.materialize.is_some()) {
        return Err("materialized layer has no claim-bearing roots".into());
    }
    use std::collections::HashMap;
    let canon_by_id: HashMap<(RootGroup, usize), &RelationUnit> = canonical
        .iter()
        .map(|u| ((u.group, u.relation_index), u))
        .collect();

    let mut seen_ids: HashMap<(RootGroup, usize), ()> = HashMap::new();
    for u in &ls.units {
        let id = (u.group, u.relation_index);
        if seen_ids.insert(id, ()).is_some() {
            return Err(format!("units has duplicate relation {:?}/{}", id.0, id.1));
        }
        if !canon_by_id.contains_key(&id) {
            return Err(format!(
                "stale schedule: unit {:?}/{} is not a relation of this layer",
                id.0, id.1
            ));
        }
    }
    if seen_ids.len() != canonical.len() {
        return Err(format!(
            "units cover {} relations, layer has {}",
            seen_ids.len(),
            canonical.len()
        ));
    }

    let mut stored: BTreeSet<SiteKey> = BTreeSet::new();
    for (k, _) in &ls.sites {
        if !stored.insert(*k) {
            return Err(format!(
                "sites has a duplicate SiteKey for value {}",
                k.value.0
            ));
        }
    }
    let order = atom_order(layer, &ls.units);
    let compute_roots = build_compute_roots(layer);
    let domain = enumerate_site_domain(layer, &order, &compute_roots);
    check_site_domain_match(&stored, &domain)?;

    for (k, p) in &ls.sites {
        if !(-1.0..=1.0).contains(p) {
            return Err(format!(
                "site priority for root {} value {} is outside [-1, 1] ({p})",
                k.root.0, k.value.0
            ));
        }
    }

    Ok(())
}

fn check_site_domain_match(
    stored: &BTreeSet<SiteKey>,
    domain: &BTreeSet<SiteKey>,
) -> Result<(), String> {
    if let Some(extra) = stored.difference(domain).next() {
        return Err(format!(
            "stale schedule: stored site (root {}, value {}) is not in the lowering site domain",
            extra.root.0, extra.value.0
        ));
    }
    if let Some(missing) = domain.difference(stored).next() {
        return Err(format!(
            "stale schedule: lowering site (root {}, value {}) is missing from the stored set",
            missing.root.0, missing.value.0
        ));
    }
    Ok(())
}
