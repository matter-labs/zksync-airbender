//! CPU-only diagnostic audit pass for the GKR backward path. Test-only
//! infrastructure: structural counters, post-compaction descriptor sizes,
//! and per-circuit regression tests. The production items it depends on
//! live in the sibling [`super::gkr_address_audit`] module.

use std::collections::{BTreeMap, BTreeSet};

use super::backward::flat::FLAT_ROUND0_MAX_SOURCES;
use super::gkr_address_audit::{
    classify, collect_addresses_from_cache_relation, collect_addresses_from_relation, AddressClass,
    GKR_MAX_POLYS_PER_SLOT, GKR_MAX_SLOTS,
};
use crate::upstream::{
    GKRAddress, GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, NoFieldGKRRelation,
    PrimeField,
};

pub(crate) const KERNEL_ARG_HARD_CEILING_BYTES: usize = 32 * 1024;
pub(crate) const KERNEL_ARG_SOFT_TARGET_BYTES: usize = 16 * 1024;

/// Maximum `(batch_challenge_offset, claim_idx)` pairs the
/// `build_combined_claim` kernel-arg descriptor can hold.
/// Largest measured: 686 pairs (blake2_with_extended_control layer 0).
/// 1024 leaves ~50% headroom and keeps the descriptor at
/// `8 + 1024*8 = 8200` bytes — well under the 32 KB inline kernel-arg ceiling.
pub(crate) const GKR_COMBINED_CLAIM_MAX_PAIRS: usize = 1024;

/// Maximum source addresses the `gather_e_addresses` kernel-arg descriptor
/// can hold. Sized off the per-layer distinct-source upper bound
/// (`FLAT_ROUND0_MAX_SOURCES = 1280`).
pub(crate) const GKR_GATHER_MAX_ADDRESSES: usize = 1280;

/// Per-kernel summary (one gate = one kernel launch in the main-layer flat
/// path).
#[derive(Debug, Clone)]
pub(crate) struct KernelAudit {
    pub(crate) num_distinct_reads: usize,
    pub(crate) num_distinct_writes: usize,
}

/// Per-layer audit summary.
#[derive(Debug, Clone)]
pub(crate) struct LayerAudit {
    pub(crate) layer_idx: usize,
    pub(crate) output_layer: usize,
    /// Kernel count for this layer (= `gates.len() + gates_with_external_connections.len()`).
    pub(crate) num_kernels: usize,
    /// Per-kernel I/O.
    pub(crate) kernels: Vec<KernelAudit>,
    /// Distinct GKRAddresses, broken down by class.
    pub(crate) class_polys: BTreeMap<AddressClass, BTreeSet<GKRAddress>>,
    /// Variant-level histogram for taxonomy revision.
    pub(crate) variant_polys: BTreeMap<&'static str, BTreeSet<GKRAddress>>,
    /// Union of all addresses read across all kernels in this layer (= the
    /// `num_sources` upper bound for the flat-path source list).
    pub(crate) all_reads: BTreeSet<GKRAddress>,
    /// Union of all addresses written across all kernels in this layer.
    pub(crate) all_writes: BTreeSet<GKRAddress>,
    /// Cache-relation reads (these become PrevInnerLayer / PrevCached reads
    /// when the cache is materialized).
    pub(crate) cache_reads: BTreeSet<GKRAddress>,
}

/// Top-level audit of a single circuit.
#[derive(Debug, Clone)]
pub(crate) struct CircuitAudit {
    pub(crate) name: String,
    pub(crate) cached_mode: bool,
    pub(crate) num_layers: usize,
    pub(crate) layers: Vec<LayerAudit>,
}

fn variant_name(rel: &NoFieldGKRRelation) -> &'static str {
    use NoFieldGKRRelation::*;
    match rel {
        LinearBaseFieldRelation { .. } => "LinearBaseFieldRelation",
        MaxQuadratic { .. } => "MaxQuadratic",
        EnforceSingleMaxQuadraticConstraint { .. } => "EnforceSingleMaxQuadraticConstraint",
        EnforceConstraintsMaxQuadratic { .. } => "EnforceConstraintsMaxQuadratic",
        CopyInBaseField { .. } => "CopyInBaseField",
        CopyInExtensionField { .. } => "CopyInExtensionField",
        InitialGrandProductFromCaches { .. } => "InitialGrandProductFromCaches",
        InitialGrandProductWithoutCaches { .. } => "InitialGrandProductWithoutCaches",
        UnbalancedGrandProductWithCache { .. } => "UnbalancedGrandProductWithCache",
        MaterializeGrandProductTermExpression { .. } => "MaterializeGrandProductTermExpression",
        TrivialProduct { .. } => "TrivialProduct",
        MaskIntoIdentityProduct { .. } => "MaskIntoIdentityProduct",
        MaterializeSingleLookupInput { .. } => "MaterializeSingleLookupInput",
        MaterializedVectorLookupInput { .. } => "MaterializedVectorLookupInput",
        LookupWithCachedDensAndSetup { .. } => "LookupWithCachedDensAndSetup",
        LookupWithDensAndSetupExpressions { .. } => "LookupWithDensAndSetupExpressions",
        LookupPairFromBaseInputs { .. } => "LookupPairFromBaseInputs",
        LookupPairFromMaterializedBaseInputs { .. } => "LookupPairFromMaterializedBaseInputs",
        LookupFromMaterializedBaseInputWithSetup { .. } => {
            "LookupFromMaterializedBaseInputWithSetup"
        }
        LookupUnbalancedPairWithMaterializedBaseInputs { .. } => {
            "LookupUnbalancedPairWithMaterializedBaseInputs"
        }
        LookupPairFromVectorInputs { .. } => "LookupPairFromVectorInputs",
        LookupPairFromMaterializedVectorInputs { .. } => "LookupPairFromMaterializedVectorInputs",
        LookupPairFromCachedVectorInputs { .. } => "LookupPairFromCachedVectorInputs",
        LookupFromVectorInputWithSetup { .. } => "LookupFromVectorInputWithSetup",
        LookupFromMaterializedVectorInputWithSetup { .. } => {
            "LookupFromMaterializedVectorInputWithSetup"
        }
        LookupUnbalancedPairWithVectorInputs { .. } => "LookupUnbalancedPairWithVectorInputs",
        LookupUnbalancedPairWithMaterializedVectorInputs { .. } => {
            "LookupUnbalancedPairWithMaterializedVectorInputs"
        }
        AggregateLookupRationalPair { .. } => "AggregateLookupRationalPair",
        InitsOrTeardownsInitialPair { .. } => "InitsOrTeardownsInitialPair",
    }
}

fn audit_layer(layer_idx: usize, layer: &GKRLayerDescription) -> LayerAudit {
    let output_layer = layer.layer;

    let mut audit = LayerAudit {
        layer_idx,
        output_layer,
        num_kernels: 0,
        kernels: Vec::new(),
        class_polys: BTreeMap::new(),
        variant_polys: BTreeMap::new(),
        all_reads: BTreeSet::new(),
        all_writes: BTreeSet::new(),
        cache_reads: BTreeSet::new(),
    };

    let all_gates: Vec<&GateArtifacts> = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .collect();
    audit.num_kernels = all_gates.len();

    let record_addrs =
        |addrs: &[GKRAddress],
         target: &mut BTreeSet<GKRAddress>,
         class_polys: &mut BTreeMap<AddressClass, BTreeSet<GKRAddress>>,
         variant: &'static str,
         variant_polys: &mut BTreeMap<&'static str, BTreeSet<GKRAddress>>| {
            for a in addrs {
                target.insert(*a);
                class_polys
                    .entry(classify(a, output_layer))
                    .or_default()
                    .insert(*a);
                variant_polys.entry(variant).or_default().insert(*a);
            }
        };

    for gate in all_gates.iter() {
        let mut reads: Vec<GKRAddress> = Vec::new();
        let mut writes: Vec<GKRAddress> = Vec::new();
        collect_addresses_from_relation(&gate.enforced_relation, &mut reads, &mut writes);
        let v = variant_name(&gate.enforced_relation);

        let read_set: BTreeSet<GKRAddress> = reads.iter().copied().collect();
        let write_set: BTreeSet<GKRAddress> = writes.iter().copied().collect();
        audit.kernels.push(KernelAudit {
            num_distinct_reads: read_set.len(),
            num_distinct_writes: write_set.len(),
        });

        record_addrs(
            &reads,
            &mut audit.all_reads,
            &mut audit.class_polys,
            v,
            &mut audit.variant_polys,
        );
        record_addrs(
            &writes,
            &mut audit.all_writes,
            &mut audit.class_polys,
            v,
            &mut audit.variant_polys,
        );
    }

    for (cache_addr, cache_rel) in layer.cached_relations.iter() {
        let mut reads = Vec::new();
        collect_addresses_from_cache_relation(cache_rel, &mut reads);
        for a in reads.iter() {
            audit.cache_reads.insert(*a);
            audit
                .class_polys
                .entry(classify(a, output_layer))
                .or_default()
                .insert(*a);
        }
        // The cache itself is a write target this layer.
        audit.all_writes.insert(*cache_addr);
        audit
            .class_polys
            .entry(classify(cache_addr, output_layer))
            .or_default()
            .insert(*cache_addr);
    }

    audit
}

pub(crate) fn audit_circuit<F: PrimeField>(
    name: &str,
    artifact: &GKRCircuitArtifact<F>,
) -> CircuitAudit {
    let cached_mode = artifact
        .layers
        .iter()
        .any(|l| !l.cached_relations.is_empty());
    let layers: Vec<LayerAudit> = artifact
        .layers
        .iter()
        .enumerate()
        .map(|(idx, l)| audit_layer(idx, l))
        .collect();
    CircuitAudit {
        name: name.to_string(),
        cached_mode,
        num_layers: layers.len(),
        layers,
    }
}

/// Numbers we care about, packed into a single struct that's easy to log.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CircuitMaxima {
    pub(crate) max_kernels_per_layer: usize,
    pub(crate) max_distinct_reads_per_kernel: usize,
    pub(crate) max_distinct_writes_per_kernel: usize,
    pub(crate) max_layer_distinct_reads: usize,
    pub(crate) max_layer_distinct_writes: usize,
    pub(crate) max_polys_per_class: usize,
    pub(crate) max_address_classes_in_one_layer: usize,
    pub(crate) any_other_class: bool,
}

pub(crate) fn maxima(audit: &CircuitAudit) -> CircuitMaxima {
    let mut m = CircuitMaxima {
        max_kernels_per_layer: 0,
        max_distinct_reads_per_kernel: 0,
        max_distinct_writes_per_kernel: 0,
        max_layer_distinct_reads: 0,
        max_layer_distinct_writes: 0,
        max_polys_per_class: 0,
        max_address_classes_in_one_layer: 0,
        any_other_class: false,
    };
    for layer in audit.layers.iter() {
        m.max_kernels_per_layer = m.max_kernels_per_layer.max(layer.num_kernels);
        for k in layer.kernels.iter() {
            m.max_distinct_reads_per_kernel =
                m.max_distinct_reads_per_kernel.max(k.num_distinct_reads);
            m.max_distinct_writes_per_kernel =
                m.max_distinct_writes_per_kernel.max(k.num_distinct_writes);
        }
        m.max_layer_distinct_reads = m.max_layer_distinct_reads.max(layer.all_reads.len());
        m.max_layer_distinct_writes = m.max_layer_distinct_writes.max(layer.all_writes.len());
        m.max_address_classes_in_one_layer = m
            .max_address_classes_in_one_layer
            .max(layer.class_polys.len());
        for (cls, polys) in layer.class_polys.iter() {
            if matches!(cls, AddressClass::Other) {
                m.any_other_class = true;
            }
            m.max_polys_per_class = m.max_polys_per_class.max(polys.len());
        }
    }
    m
}

/// Pretty-print a single circuit audit. Every line is structural data the
/// plan authors will consult when locking ceilings.
pub(crate) fn log_circuit_audit(audit: &CircuitAudit) {
    let m = maxima(audit);
    log::info!(
        "[gkr-audit] circuit={} mode={} layers={}",
        audit.name,
        if audit.cached_mode {
            "CACHED"
        } else {
            "NO_CACHE"
        },
        audit.num_layers,
    );
    log::info!(
        "[gkr-audit]   maxima: kernels/layer={} reads/kernel={} writes/kernel={} layer_reads={} layer_writes={} polys/class={} classes/layer={} other_class={}",
        m.max_kernels_per_layer,
        m.max_distinct_reads_per_kernel,
        m.max_distinct_writes_per_kernel,
        m.max_layer_distinct_reads,
        m.max_layer_distinct_writes,
        m.max_polys_per_class,
        m.max_address_classes_in_one_layer,
        m.any_other_class,
    );
    for layer in audit.layers.iter() {
        let class_summary: Vec<String> = layer
            .class_polys
            .iter()
            .map(|(c, polys)| format!("{}={}", c.label(), polys.len()))
            .collect();
        let variant_summary: Vec<String> = layer
            .variant_polys
            .iter()
            .map(|(v, polys)| format!("{}={}", v, polys.len()))
            .collect();
        log::info!(
            "[gkr-audit]   layer[{}] output_layer={} kernels={} reads={} writes={} cache_reads={} | classes: [{}] | variants: [{}]",
            layer.layer_idx,
            layer.output_layer,
            layer.num_kernels,
            layer.all_reads.len(),
            layer.all_writes.len(),
            layer.cache_reads.len(),
            class_summary.join(", "),
            variant_summary.join(", "),
        );
    }
}

/// Hard-ceiling assertions. Any failure should abort the audit so we discuss
/// numbers before touching kernel ABIs.
///
/// Note: the gate count from `compiled_circuit.layers[i].gates` does NOT map
/// to the dim-reducing batch's `record_count` budget. Layer 0's gates fold
/// into a single main-layer flat-path kernel via term tables; `record_count`
/// is bounded structurally by `OutputType` slots on dim-reducing layers.
#[derive(Debug)]
pub(crate) enum AuditError {
    SlotOverflow {
        circuit: String,
        layer_idx: usize,
        classes: usize,
        max: usize,
    },
    PolyIndexOverflow {
        circuit: String,
        layer_idx: usize,
        class: AddressClass,
        polys: usize,
        max: usize,
    },
    SourceOverflow {
        circuit: String,
        layer_idx: usize,
        sources: usize,
        max: usize,
    },
}

impl std::fmt::Display for AuditError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SlotOverflow {
                circuit,
                layer_idx,
                classes,
                max,
            } => write!(
                f,
                "circuit '{}' layer[{}] uses {} address classes (limit {})",
                circuit, layer_idx, classes, max,
            ),
            Self::PolyIndexOverflow {
                circuit,
                layer_idx,
                class,
                polys,
                max,
            } => write!(
                f,
                "circuit '{}' layer[{}] class={:?} has {} polys (audit poly_idx limit {})",
                circuit, layer_idx, class, polys, max,
            ),
            Self::SourceOverflow {
                circuit,
                layer_idx,
                sources,
                max,
            } => write!(
                f,
                "circuit '{}' layer[{}] has {} distinct sources (FLAT_ROUND0_MAX_SOURCES={})",
                circuit, layer_idx, sources, max,
            ),
        }
    }
}

pub(crate) fn check_audit_against_budgets(audit: &CircuitAudit) -> Result<(), AuditError> {
    for layer in audit.layers.iter() {
        if layer.class_polys.len() > GKR_MAX_SLOTS {
            return Err(AuditError::SlotOverflow {
                circuit: audit.name.clone(),
                layer_idx: layer.layer_idx,
                classes: layer.class_polys.len(),
                max: GKR_MAX_SLOTS,
            });
        }
        for (cls, polys) in layer.class_polys.iter() {
            if polys.len() > GKR_MAX_POLYS_PER_SLOT {
                return Err(AuditError::PolyIndexOverflow {
                    circuit: audit.name.clone(),
                    layer_idx: layer.layer_idx,
                    class: *cls,
                    polys: polys.len(),
                    max: GKR_MAX_POLYS_PER_SLOT,
                });
            }
        }
        if layer.all_reads.len() > FLAT_ROUND0_MAX_SOURCES {
            return Err(AuditError::SourceOverflow {
                circuit: audit.name.clone(),
                layer_idx: layer.layer_idx,
                sources: layer.all_reads.len(),
                max: FLAT_ROUND0_MAX_SOURCES,
            });
        }
    }
    Ok(())
}

/// Per-layer flat-path round-0 term counts. Mirrors the term-table fields of
/// `GpuFlatRound0StaticDesc` so a per-circuit max can be compared
/// against the locked `FLAT_ROUND0_MAX_*` ceilings.
#[derive(Default, Debug, Clone, Copy)]
pub(crate) struct FlatRound0TermCounts {
    pub(crate) c0_bf: u32,
    pub(crate) c0_ext: u32,
    pub(crate) c1_bf_bf: u32,
    pub(crate) c1_e4_e4: u32,
    pub(crate) c1_bf_e4: u32,
    pub(crate) c1_linear: u32,
}

impl FlatRound0TermCounts {
    fn merge_max(&mut self, other: &Self) {
        self.c0_bf = self.c0_bf.max(other.c0_bf);
        self.c0_ext = self.c0_ext.max(other.c0_ext);
        self.c1_bf_bf = self.c1_bf_bf.max(other.c1_bf_bf);
        self.c1_e4_e4 = self.c1_e4_e4.max(other.c1_e4_e4);
        self.c1_bf_e4 = self.c1_bf_e4.max(other.c1_bf_e4);
        self.c1_linear = self.c1_linear.max(other.c1_linear);
    }
}

/// `NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL` from `backward.rs` — the magic
/// `lhs`/`input` value that marks the constant-offset row in linear-form
/// metadata. Cross-product / materialize / single-times-linear-form gates
/// skip these rows when emitting `c1_*` terms; constraint gates do not.
pub(super) const FLAT_LINEAR_FORM_SENTINEL: u32 = u32::MAX;

fn count_metadata_terms<E>(
    src: &Option<crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource<E>>,
    filter_sentinel: bool,
) -> (usize, usize) {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    let (qt, lt): (Box<dyn Iterator<Item = u32>>, Box<dyn Iterator<Item = u32>>) = match src {
        Some(MS::Immediate(meta)) => (
            Box::new(meta.quadratic_terms.iter().map(|t| t.lhs)),
            Box::new(meta.linear_terms.iter().map(|t| t.input)),
        ),
        Some(MS::Deferred(tmpl)) => (
            Box::new(tmpl.quadratic_terms.iter().map(|t| t.lhs)),
            Box::new(tmpl.linear_terms.iter().map(|t| t.input)),
        ),
        None => return (0, 0),
    };
    if filter_sentinel {
        (
            qt.filter(|x| *x != FLAT_LINEAR_FORM_SENTINEL).count(),
            lt.filter(|x| *x != FLAT_LINEAR_FORM_SENTINEL).count(),
        )
    } else {
        (qt.count(), lt.count())
    }
}

/// Project the flat-path round-0 term counts a layer's gates would push when
/// `build_flat_round0_plan` runs against them. Mirrors the per-`kind` dispatch
/// in `backward_flat::build_flat_round0_plan` exactly. Used by the audit
/// to find the per-circuit max for tightening `FLAT_ROUND0_MAX_*`.
pub(crate) fn project_layer_flat_round0_term_counts<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> FlatRound0TermCounts {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelKind as K;
    let mut counts = FlatRound0TermCounts::default();
    for bp in blueprints {
        match bp.kind {
            K::BaseCopy | K::LinearBaseOutput => counts.c0_bf += 1,
            K::ExtCopy => counts.c0_ext += 1,
            K::Product => {
                counts.c0_ext += 1;
                counts.c1_e4_e4 += 1;
            }
            K::MaskIdentity => {
                counts.c0_ext += 1;
                counts.c1_bf_e4 += 1;
            }
            K::LookupPair => {
                counts.c0_ext += 2;
                counts.c1_e4_e4 += 3;
            }
            K::LookupBasePair => {
                counts.c0_ext += 2;
                counts.c1_bf_bf += 1;
            }
            K::LookupBaseMinusMultiplicityByBase => {
                counts.c0_ext += 2;
                counts.c1_bf_bf += 2;
            }
            K::LookupExtMinusMultiplicityByExt => {
                counts.c0_ext += 2;
                counts.c1_bf_e4 += 1;
                counts.c1_e4_e4 += 1;
            }
            K::LookupUnbalanced => {
                counts.c0_ext += 2;
                counts.c1_bf_e4 += 2;
            }
            K::LookupUnbalancedExtension => {
                counts.c0_ext += 2;
                counts.c1_e4_e4 += 2;
            }
            K::LookupWithCachedDensAndSetup => {
                counts.c0_ext += 2;
                counts.c1_bf_e4 += 2;
                counts.c1_e4_e4 += 1;
            }
            K::LookupExtPair => {
                counts.c0_ext += 2;
                counts.c1_e4_e4 += 1;
            }
            K::EnforceConstraintsMaxQuadratic => {
                // `emit_constraint_gate` iterates all quadratic terms (no
                // sentinel filter), one c1_bf_bf push per term.
                let (qt, _) = count_metadata_terms(&bp.constraint_metadata_source, false);
                counts.c1_bf_bf += qt as u32;
            }
            K::MaxQuadraticBaseOutput => {
                // c0 = β * output (bf) + c1 quadratic terms via emit_constraint_gate.
                counts.c0_bf += 1;
                let (qt, _) = count_metadata_terms(&bp.constraint_metadata_source, false);
                counts.c1_bf_bf += qt as u32;
            }
            K::InitsAndTeardownsInitialPair => {
                counts.c0_ext += 1;
                let (qt, _) = count_metadata_terms(&bp.constraint_metadata_source, false);
                counts.c1_bf_bf += qt as u32;
            }
            K::InitialGrandProductWithoutCaches => {
                counts.c0_ext += 1;
                let (qt, lt) = count_metadata_terms(&bp.constraint_metadata_source, true);
                counts.c1_bf_bf += (qt * lt) as u32;
            }
            K::MaterializeGrandProductTermExpression => {
                counts.c0_ext += 1;
                let (_, lt) = count_metadata_terms(&bp.constraint_metadata_source, true);
                counts.c1_linear += lt as u32;
            }
            K::LookupPairFromBaseInputs | K::LookupPairFromVectorInputs => {
                counts.c0_ext += 2;
                let (qt, lt) = count_metadata_terms(&bp.constraint_metadata_source, true);
                counts.c1_bf_bf += (qt * lt) as u32;
            }
            K::LookupWithDensAndSetupExpressions => {
                counts.c0_ext += 2;
                let (qt, lt) = count_metadata_terms(&bp.constraint_metadata_source, true);
                counts.c1_bf_bf += (lt + qt + qt * lt) as u32;
            }
            K::LookupFromVectorInputWithSetup => {
                counts.c0_ext += 2;
                let (qt, lt) = count_metadata_terms(&bp.constraint_metadata_source, true);
                counts.c1_bf_bf += (qt + qt * lt) as u32;
            }
            K::LookupUnbalancedPairWithVectorInputs => {
                counts.c0_ext += 2;
                let (_, lt) = count_metadata_terms(&bp.constraint_metadata_source, true);
                counts.c1_bf_e4 += (2 * lt) as u32;
            }
        }
    }
    counts
}

/// Project the `combined_claim_desc_pairs` length a main-layer would push when
/// `build_combined_claim`'s kernel-arg descriptor is filled. Mirrors the loop at
/// `backward.rs:6647-6657` exactly: 2 u32 entries per output (base + ext)
/// across every kernel that is NOT `EnforceConstraintsMaxQuadratic`.
///
/// Returns the count in u32 entries; H2D bytes = `result * 4`.
pub(super) fn project_layer_main_combined_claim_pair_count<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> usize {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelKind as K;
    let mut entries = 0usize;
    for bp in blueprints {
        if bp.kind == K::EnforceConstraintsMaxQuadratic {
            continue;
        }
        entries += 2 * (bp.inputs.outputs_in_base.len() + bp.inputs.outputs_in_extension.len());
    }
    entries
}

/// Collect the unique `E4` immediate-factor values that the production
/// flat-path emit functions would put into `GpuRecipeHeader.immediate_factor`
/// across the round-0 + continuation recipe streams, deduplicated.
/// Matches what would land in the device-resident `immediate_factors[]` table
/// under the on-device-evaluation refactor: the buffer is sized at this set's
/// cardinality + 1 (for the shared `E::ONE` slot used by Deferred/bare paths).
///
/// Caller should pass `external_challenges` set to a *distinct* non-zero value
/// per linearization slot so we get a structurally-tight estimate rather than
/// accidental coincidence-equalities.
pub(crate) fn collect_unique_immediates_for_layer<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> std::collections::HashSet<[u32; 4]>
where
    E: field::Field,
{
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelKind as K;
    let mut set: std::collections::HashSet<[u32; 4]> = std::collections::HashSet::new();

    let key_of = |e: &E| -> [u32; 4] {
        // SAFETY: E is always BabyBearExt4 in the audit and is `#[repr(C, align(16))]`
        // with 4 × u32 limbs (size_of::<E>() == 16). Reinterpret as 4 u32 words.
        // This gives a stable hash key without requiring `E: Hash`.
        let mut out = [0u32; 4];
        unsafe {
            std::ptr::copy_nonoverlapping(e as *const E as *const u32, out.as_mut_ptr(), 4);
        }
        out
    };

    for bp in blueprints {
        let Some(MS::Immediate(meta)) = &bp.constraint_metadata_source else {
            continue;
        };

        // Single-challenge values used by emit_constraint_gate /
        // emit_materialize_gate / single_times_linear / linear_form / etc.
        for qt in &meta.quadratic_terms {
            set.insert(key_of(&qt.challenge));
        }
        for lt in &meta.linear_terms {
            set.insert(key_of(&lt.challenge));
        }
        if !meta.constant_offset.is_zero() {
            set.insert(key_of(&meta.constant_offset));
        }

        // Cross-product gate kinds: emit_cross_product_gate computes
        // `qt.challenge * lt.challenge` per (i, j) pair, which appears as
        // immediate_factor in the resulting recipe.
        let is_xprod = matches!(
            bp.kind,
            K::InitialGrandProductWithoutCaches
                | K::LookupPairFromBaseInputs
                | K::LookupPairFromVectorInputs
                | K::LookupWithDensAndSetupExpressions
                | K::LookupFromVectorInputWithSetup
        );
        if is_xprod {
            for qt in &meta.quadratic_terms {
                for lt in &meta.linear_terms {
                    let mut prod = qt.challenge;
                    prod.mul_assign(&lt.challenge);
                    set.insert(key_of(&prod));
                }
            }
        }
    }

    set
}

pub(crate) fn collect_structural_immediates_for_layer<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> (usize, usize)
where
    E: field::Field,
{
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelKind as K;
    use crate::prover::gkr::immediate_factors::ImmediateFactorInterner;

    let mut interner = ImmediateFactorInterner::new();
    for bp in blueprints {
        let Some(MS::Immediate(meta)) = &bp.constraint_metadata_source else {
            continue;
        };

        for qt in &meta.quadratic_terms {
            interner.intern(qt.immediate_recipe.clone());
        }
        for lt in &meta.linear_terms {
            interner.intern(lt.immediate_recipe.clone());
        }
        if !meta.constant_offset.is_zero() {
            interner.intern(meta.constant_offset_recipe.clone());
        }

        let is_xprod = matches!(
            bp.kind,
            K::InitialGrandProductWithoutCaches
                | K::LookupPairFromBaseInputs
                | K::LookupPairFromVectorInputs
                | K::LookupWithDensAndSetupExpressions
                | K::LookupFromVectorInputWithSetup
        );
        if is_xprod {
            for qt in &meta.quadratic_terms {
                for lt in &meta.linear_terms {
                    interner.intern(qt.immediate_recipe.mul(&lt.immediate_recipe));
                }
            }
        }
    }
    let (headers, monomials) = interner.materialize();
    (headers.len(), monomials.len())
}

/// Per-side `challenge_terms.len()` lists for a constraint metadata source.
/// Used by `project_layer_flat_round0_recipe_audit` to compute per-recipe
/// prefactor-term counts. `Immediate` metadata has no `challenge_terms` (the
/// challenges are already evaluated into a single `E`), so per-term length
/// is reported as 0.
pub(super) fn metadata_qt_lt_term_lens<E>(
    src: &Option<crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource<E>>,
    filter_sentinel: bool,
) -> (Vec<usize>, Vec<usize>) {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    match src {
        None => (Vec::new(), Vec::new()),
        Some(MS::Immediate(meta)) => {
            let qt: Vec<usize> = meta
                .quadratic_terms
                .iter()
                .filter(|t| !filter_sentinel || t.lhs != FLAT_LINEAR_FORM_SENTINEL)
                .map(|_| 0)
                .collect();
            let lt: Vec<usize> = meta
                .linear_terms
                .iter()
                .filter(|t| !filter_sentinel || t.input != FLAT_LINEAR_FORM_SENTINEL)
                .map(|_| 0)
                .collect();
            (qt, lt)
        }
        Some(MS::Deferred(tmpl)) => {
            let qt: Vec<usize> = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| !filter_sentinel || t.lhs != FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .collect();
            let lt: Vec<usize> = tmpl
                .linear_terms
                .iter()
                .filter(|t| !filter_sentinel || t.input != FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .collect();
            (qt, lt)
        }
    }
}

/// Project the per-layer main-layer gather payload size. Mirrors
/// `final_evaluation_sources_for_last_step` (`backward.rs:6237-6275`) by
/// counting distinct, non-placeholder addresses across every kernel's
/// `inputs_in_base ∪ inputs_in_extension`. The result bounds
/// `gather_e_addresses`'s `num_addresses` argument.
pub(super) fn project_layer_main_gather_num_addresses<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> usize {
    let mut seen: std::collections::BTreeSet<cs::definitions::GKRAddress> =
        std::collections::BTreeSet::new();
    let placeholder = cs::definitions::GKRAddress::placeholder();
    for bp in blueprints {
        for addr in bp
            .inputs
            .inputs_in_base
            .iter()
            .chain(bp.inputs.inputs_in_extension.iter())
        {
            if *addr == placeholder {
                continue;
            }
            seen.insert(*addr);
        }
    }
    seen.len()
}

mod compaction_sizes;
mod flat_recipe_audit;

pub(crate) use compaction_sizes::{
    check_descriptor_sizes_under_hard_ceiling, log_post_compaction_sizes,
    projected_post_compaction_sizes,
};
pub(crate) use flat_recipe_audit::{
    project_layer_flat_continuation_recipe_audit, project_layer_flat_round0_recipe_audit,
    FlatRecipeAudit,
};

#[cfg(test)]
mod tests;
