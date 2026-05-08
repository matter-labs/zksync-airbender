//! Phase 0 (blocking) — CPU-only diagnostic measurement pass for the GKR
//! backward path. Produces, per-circuit / per-layer / per-mode (cached +
//! no-cache), the counts that determine whether the planned compact-`u16`
//! encoding fits inside the `cudaLaunchKernelExC` 32 KB inline kernel-arg
//! ceiling without falling back to driver H2D.
//!
//! See `/home/rr/.claude/plans/i-would-actually-put-kind-thacker.md`.
//!
//! The pass walks `cs::gkr_compiler::GKRCircuitArtifact` directly — no GPU
//! allocations, no challenges, no kernel launches. It is structural only.
//!
//! 8-slot pointer-table taxonomy (the per-launch `bases[8]`):
//!
//! | slot | class                      |
//! |------|----------------------------|
//! | 0    | BaseLayerWitness           |
//! | 1    | BaseLayerMemory            |
//! | 2    | Setup + VirtualSetup       |
//! | 3    | prev-layer InnerLayer      |
//! | 4    | prev-layer Cached          |
//! | 5    | this-layer Cached write    |
//! | 6    | this-layer InnerLayer      |
//! | 7    | reserved (also ScratchSpace)|

use std::collections::{BTreeMap, BTreeSet};

use cs::definitions::gkr::{
    NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
    RamWordRepresentation,
};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, NoFieldGKRCacheRelation,
    NoFieldGKRRelation, NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldSpecialMemoryContributionRelation,
};
use field::PrimeField;

use super::backward_flat::{
    FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES, FLAT_CONT_MAX_SOURCES,
    FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES, FLAT_CONT_UNIFIED_MAX_TERMS, FLAT_CONT_UNIFIED_MAX_TILES,
    FLAT_ROUND0_MAX_C0_BF, FLAT_ROUND0_MAX_C0_EXT, FLAT_ROUND0_MAX_C1_BF_BF,
    FLAT_ROUND0_MAX_C1_BF_E4, FLAT_ROUND0_MAX_C1_E4_E4, FLAT_ROUND0_MAX_C1_LINEAR,
    FLAT_ROUND0_MAX_SOURCES,
};
use super::backward_kernels::GKR_BACKWARD_MAX_KERNELS_PER_LAYER;

/// Hard cap on `OutputType` slots driving the dim-reducing batch fan-out.
/// Today the compiler emits at most one entry per `OutputType` (at most 4:
/// `PermutationProduct`, `Lookup16Bits`, `LookupTimestamps`, `GenericLookup`).
/// Phase 0 surfaces the observed maximum so this stays accurate.
pub(crate) const GKR_BACKWARD_MAX_OUTPUT_TYPES: usize = 4;

/// Plan-targeted ceilings. Phase 0 verifies every circuit fits these.
pub(crate) const GKR_MAX_SLOTS: usize = 8;
pub(crate) const GKR_MAX_POLYS_PER_SLOT: usize = 4096;
pub(crate) const KERNEL_ARG_HARD_CEILING_BYTES: usize = 32 * 1024;
pub(crate) const KERNEL_ARG_SOFT_TARGET_BYTES: usize = 16 * 1024;

/// Maximum `(batch_challenge_offset, claim_idx)` pairs the
/// `build_combined_claim` kernel-arg descriptor can hold.
/// Largest measured: 686 pairs (blake2_with_extended_control layer 0).
/// 1024 leaves ~50% headroom and keeps the descriptor at
/// `8 + 1024*8 = 8200` bytes — well under the 32 KB inline kernel-arg ceiling.
/// Production builders panic if exceeded; the Phase 0 audit doubles as the
/// regression check.
pub(crate) const GKR_COMBINED_CLAIM_MAX_PAIRS: usize = 1024;

/// Maximum source addresses the `gather_e_addresses` kernel-arg descriptor
/// can hold. Sized off the per-layer distinct-source upper bound from Phase 0
/// (`FLAT_ROUND0_MAX_SOURCES = 1280`); the gather payload is always ≤ that
/// bound (it dedupes by `GKRAddress` over each kernel's
/// `inputs_in_base ∪ inputs_in_extension`). Keeps the descriptor at
/// `8 + 1280*8 = 10248` bytes — well under the 32 KB inline kernel-arg ceiling.
/// Production builders panic if exceeded; the Phase 0 audit doubles as the
/// regression check.
pub(crate) const GKR_GATHER_MAX_ADDRESSES: usize = 1280;

/// 8-slot taxonomy. `Other` is anything outside the 8 slots and triggers an
/// abort (Phase 0 must show no real circuit hits it).
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum AddressClass {
    BaseLayerWitness = 0,
    BaseLayerMemory = 1,
    Setup = 2,
    PrevInnerLayer = 3,
    PrevCached = 4,
    ThisLayerCachedWrite = 5,
    ThisLayerInnerLayerWrite = 6,
    Reserved = 7,
    /// Outside the 8-slot taxonomy (taxonomy revision needed).
    Other = 255,
}

impl AddressClass {
    fn label(self) -> &'static str {
        match self {
            Self::BaseLayerWitness => "BaseLayerWitness",
            Self::BaseLayerMemory => "BaseLayerMemory",
            Self::Setup => "Setup",
            Self::PrevInnerLayer => "PrevInnerLayer",
            Self::PrevCached => "PrevCached",
            Self::ThisLayerCachedWrite => "ThisLayerCachedWrite",
            Self::ThisLayerInnerLayerWrite => "ThisLayerInnerLayer",
            Self::Reserved => "Reserved",
            Self::Other => "Other",
        }
    }
}

/// Map a `GKRAddress` to its 8-slot class given the layer the gate writes its
/// output to.
pub(crate) fn classify(addr: &GKRAddress, output_layer: usize) -> AddressClass {
    match addr {
        GKRAddress::BaseLayerWitness(_) => AddressClass::BaseLayerWitness,
        GKRAddress::BaseLayerMemory(_) => AddressClass::BaseLayerMemory,
        GKRAddress::Setup(_) | GKRAddress::VirtualSetup(_) => AddressClass::Setup,
        GKRAddress::InnerLayer { layer, .. } => {
            if *layer + 1 == output_layer {
                AddressClass::PrevInnerLayer
            } else if *layer == output_layer {
                AddressClass::ThisLayerInnerLayerWrite
            } else {
                AddressClass::Other
            }
        }
        GKRAddress::Cached { layer, .. } => {
            if *layer + 1 == output_layer {
                AddressClass::PrevCached
            } else if *layer == output_layer {
                AddressClass::ThisLayerCachedWrite
            } else {
                AddressClass::Other
            }
        }
        GKRAddress::ScratchSpace(_) => AddressClass::Reserved,
    }
}

/// Replicates `cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation::dependencies`,
/// which is `pub(crate)` upstream and not callable from this crate.
fn collect_memory_dependencies(
    m: &NoFieldSpecialMemoryContributionRelation,
    reads: &mut Vec<GKRAddress>,
) {
    match &m.address_space {
        CompiledAddressSpaceRelationStrict::Constant(_) => {}
        CompiledAddressSpaceRelationStrict::IsRegister(offset)
        | CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            reads.push(GKRAddress::BaseLayerMemory(*offset));
        }
    }
    match &m.address {
        CompiledAddressStrict::ConstantU16(_) | CompiledAddressStrict::Constant(_) => {}
        CompiledAddressStrict::U16Space(offset) => {
            reads.push(GKRAddress::BaseLayerMemory(*offset));
        }
        CompiledAddressStrict::U32Space(offsets) => {
            reads.push(GKRAddress::BaseLayerMemory(offsets[0]));
            reads.push(GKRAddress::BaseLayerMemory(offsets[1]));
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset: _,
            high,
        } => {
            reads.push(GKRAddress::BaseLayerMemory(*low_base));
            reads.push(GKRAddress::BaseLayerMemory(*high));
            if let Some((_, offset)) = low_dynamic_offset {
                reads.push(GKRAddress::BaseLayerMemory(*offset));
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(_) => {
            // Upstream `dependencies()` is unimplemented for this case; treat
            // as a measurement gap and surface via the audit's "Other" class.
        }
    }
    match &m.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            for &el in ts {
                reads.push(GKRAddress::BaseLayerMemory(el));
            }
        }
    }
    match &m.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(els) => {
            for &el in els {
                reads.push(GKRAddress::BaseLayerMemory(el));
            }
        }
        RamWordRepresentation::U8Limbs(els) => {
            for &el in els {
                reads.push(GKRAddress::BaseLayerMemory(el));
            }
        }
    }
}

/// Walk a `NoFieldGKRRelation` and collect every `GKRAddress` it touches,
/// classified as "read" (input/source) or "write" (output/sink).
pub(crate) fn collect_addresses_from_relation(
    rel: &NoFieldGKRRelation,
    reads: &mut Vec<GKRAddress>,
    writes: &mut Vec<GKRAddress>,
) {
    use NoFieldGKRRelation::*;

    let push_linear = |r: &NoFieldLinearRelation, reads: &mut Vec<GKRAddress>| {
        for (_, a) in r.linear_terms.iter() {
            reads.push(*a);
        }
    };
    let push_vector = |v: &NoFieldVectorLookupRelation, reads: &mut Vec<GKRAddress>| {
        for col in v.columns.iter() {
            for (_, a) in col.linear_terms.iter() {
                reads.push(*a);
            }
        }
    };
    let push_single_lookup = |s: &NoFieldSingleColumnLookupRelation,
                              reads: &mut Vec<GKRAddress>| {
        push_linear(&s.input, reads)
    };
    let push_max_quadratic = |q: &NoFieldMaxQuadraticGKRRelation, reads: &mut Vec<GKRAddress>| {
        for (a, b) in q.quadratic_terms.iter() {
            reads.push(*a);
            for (_, c) in b.iter() {
                reads.push(*c);
            }
        }
        for (_, a) in q.linear_terms.iter() {
            reads.push(*a);
        }
    };
    let push_max_quadratic_constraints =
        |q: &NoFieldMaxQuadraticConstraintsGKRRelation, reads: &mut Vec<GKRAddress>| {
            for ((a, b), _) in q.quadratic_terms.iter() {
                reads.push(*a);
                reads.push(*b);
            }
            for (a, _) in q.linear_terms.iter() {
                reads.push(*a);
            }
        };
    let push_memory = collect_memory_dependencies;

    match rel {
        LinearBaseFieldRelation { input, output } => {
            push_linear(input, reads);
            writes.push(*output);
        }
        MaxQuadratic { input, output } => {
            push_max_quadratic(input, reads);
            writes.push(*output);
        }
        EnforceSingleMaxQuadraticConstraint { input } => {
            push_max_quadratic(input, reads);
        }
        EnforceConstraintsMaxQuadratic { input } => {
            push_max_quadratic_constraints(input, reads);
        }
        CopyInBaseField { input, output } | CopyInExtensionField { input, output } => {
            reads.push(*input);
            writes.push(*output);
        }
        InitialGrandProductFromCaches { input, output } | TrivialProduct { input, output } => {
            reads.extend_from_slice(input);
            writes.push(*output);
        }
        InitialGrandProductWithoutCaches { input, output } => {
            for el in input.iter() {
                push_memory(el, reads);
            }
            writes.push(*output);
        }
        UnbalancedGrandProductWithCache {
            scalar,
            input,
            output,
        } => {
            reads.push(*scalar);
            reads.push(*input);
            writes.push(*output);
        }
        MaterializeGrandProductTermExpression { input, output } => {
            push_memory(input, reads);
            writes.push(*output);
        }
        MaskIntoIdentityProduct {
            input,
            mask,
            output,
        } => {
            reads.push(*input);
            reads.push(*mask);
            writes.push(*output);
        }
        MaterializeSingleLookupInput {
            input,
            output,
            range_check_width: _,
        } => {
            push_single_lookup(input, reads);
            writes.push(*output);
        }
        MaterializedVectorLookupInput { input, output } => {
            push_vector(input, reads);
            writes.push(*output);
        }
        LookupWithCachedDensAndSetup {
            input,
            setup,
            output,
        } => {
            reads.extend_from_slice(input);
            reads.extend_from_slice(setup);
            writes.extend_from_slice(output);
        }
        LookupWithDensAndSetupExpressions {
            input,
            setup,
            output,
        } => {
            reads.push(input.0);
            push_vector(&input.1, reads);
            reads.push(setup.0);
            for a in setup.1.iter() {
                reads.push(*a);
            }
            writes.extend_from_slice(output);
        }
        LookupPairFromBaseInputs {
            input,
            output,
            range_check_width: _,
        } => {
            for el in input.iter() {
                push_single_lookup(el, reads);
            }
            writes.extend_from_slice(output);
        }
        LookupPairFromMaterializedBaseInputs { input, output } => {
            reads.extend_from_slice(input);
            writes.extend_from_slice(output);
        }
        LookupFromMaterializedBaseInputWithSetup {
            input,
            setup,
            output,
        } => {
            reads.push(*input);
            reads.extend_from_slice(setup);
            writes.extend_from_slice(output);
        }
        LookupUnbalancedPairWithMaterializedBaseInputs {
            input,
            remainder,
            output,
        } => {
            reads.extend_from_slice(input);
            reads.push(*remainder);
            writes.extend_from_slice(output);
        }
        LookupPairFromVectorInputs { input, output } => {
            for el in input.iter() {
                push_vector(el, reads);
            }
            writes.extend_from_slice(output);
        }
        LookupPairFromMaterializedVectorInputs { input, output }
        | LookupPairFromCachedVectorInputs { input, output } => {
            reads.extend_from_slice(input);
            writes.extend_from_slice(output);
        }
        LookupFromVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            push_vector(input, reads);
            reads.push(setup.0);
            for a in setup.1.iter() {
                reads.push(*a);
            }
            writes.extend_from_slice(output);
        }
        LookupFromMaterializedVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            reads.push(*input);
            reads.extend_from_slice(setup);
            writes.extend_from_slice(output);
        }
        LookupUnbalancedPairWithVectorInputs {
            input,
            remainder,
            output,
        } => {
            reads.extend_from_slice(input);
            push_vector(remainder, reads);
            writes.extend_from_slice(output);
        }
        LookupUnbalancedPairWithMaterializedVectorInputs {
            input,
            remainder,
            output,
        } => {
            reads.extend_from_slice(input);
            reads.push(*remainder);
            writes.extend_from_slice(output);
        }
        AggregateLookupRationalPair { input, output } => {
            for pair in input.iter() {
                reads.extend_from_slice(pair);
            }
            writes.extend_from_slice(output);
        }
        InitsOrTeardownsInitialPair {
            timestamp_and_value,
            setup,
            output,
            set_idxes: _,
        } => {
            reads.extend_from_slice(setup);
            if let cs::gkr_compiler::InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp,
                lhs_value,
                rhs_timestamp,
                rhs_value,
            } = timestamp_and_value
            {
                for &col in lhs_timestamp.iter().chain(rhs_timestamp.iter()) {
                    reads.push(GKRAddress::BaseLayerMemory(col));
                }
                for &col in lhs_value.iter().chain(rhs_value.iter()) {
                    reads.push(GKRAddress::BaseLayerMemory(col));
                }
            }
            writes.push(*output);
        }
    }
}

/// Walk a cache relation (these are the prepare-cache kernels for the layer)
/// and collect every `GKRAddress` it reads. The output is the cache's own
/// address (the BTreeMap key in `cached_relations`).
pub(crate) fn collect_addresses_from_cache_relation(
    rel: &NoFieldGKRCacheRelation,
    reads: &mut Vec<GKRAddress>,
) {
    for a in rel.dependencies() {
        reads.push(a);
    }
}

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

/// Hard-ceiling assertions. Any failure should abort Phase 0 so we discuss
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
    OtherClassPresent {
        circuit: String,
        layer_idx: usize,
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
            Self::OtherClassPresent { circuit, layer_idx } => write!(
                f,
                "circuit '{}' layer[{}] has GKRAddresses outside the 8-slot taxonomy (taxonomy revision needed)",
                circuit, layer_idx,
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
        if layer.class_polys.contains_key(&AddressClass::Other) {
            return Err(AuditError::OtherClassPresent {
                circuit: audit.name.clone(),
                layer_idx: layer.layer_idx,
            });
        }
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

/// Post-compaction descriptor sizes, given the planned encoding. Reported per
/// descriptor type so we know each launch fits the 32 KB inline ceiling
/// without driver H2D before any code that bakes the encoding into a kernel
/// ABI lands.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PostCompactionSizes {
    pub(crate) dim_reducing_round0_batch: usize,
    pub(crate) dim_reducing_continuation_batch: usize,
    pub(crate) flat_round0_static_desc: usize,
    pub(crate) flat_round1_unified_desc: usize,
    pub(crate) flat_round2_unified_desc: usize,
    pub(crate) flat_continuation_unified_desc: usize,
}

// `bases:[*const u8;N] + log2_stride:[u32;N]`, where
// `N = GKR_DIM_REDUCING_BASE_SLOTS`.
const TABLES_BYTES: usize =
    crate::prover::gkr::backward_kernels::GKR_DIM_REDUCING_BASE_SLOTS * (8 + 4);
const HEADER_HOT_PTRS_BYTES: usize = 8 * 8; // four hot pointers (eq, batch_challenge, fold_challenge, contributions) + slack
const RECORD_BYTES: usize = 16; // BatchRecord { inputs: PayloadRange16, outputs: PayloadRange16 }

/// What the post-compaction `inline_payload` (in dual-u16 source records) expands to in
/// bytes. Kept separate so we can plug in the Phase 0-measured worst-case
/// payload size as a constant and still see the resulting struct size.
fn dim_reducing_struct_bytes(inline_record_budget: usize) -> usize {
    HEADER_HOT_PTRS_BYTES
        + TABLES_BYTES
        + GKR_BACKWARD_MAX_KERNELS_PER_LAYER * RECORD_BYTES
        + 4 * inline_record_budget
}

/// Compute the post-compaction descriptor sizes for the planned encoding
/// using the budgets we will lock in Phase 0.
pub(crate) fn projected_post_compaction_sizes() -> PostCompactionSizes {
    // Reserve enough u16s to fit the largest measured layer's source list.
    // For Phase 0 we use the existing FLAT_ROUND0_MAX_SOURCES ceiling as a
    // pessimistic bound (each source = one u16).
    let inline_record_budget = FLAT_ROUND0_MAX_SOURCES;

    let dim_reducing = dim_reducing_struct_bytes(inline_record_budget);

    // Round struct size up to its natural alignment (8 B, set by the
    // `*const u8` pointers in `tables`). Rust `#[repr(C)]` rounds the total
    // struct size to a multiple of the max member alignment; this matches
    // `std::mem::size_of::<...>()`.
    fn align_up(n: usize, align: usize) -> usize {
        (n + align - 1) & !(align - 1)
    }
    const STRUCT_ALIGN: usize = 8;

    // Flat round 0: dual-u16 source records + u32 counts + tables + term tables.
    let flat_round0 = align_up(
        4 // num_sources
            + FLAT_ROUND0_MAX_SOURCES * 4
            + TABLES_BYTES
            + 4 + FLAT_ROUND0_MAX_C0_BF * 2 // GpuFlatC0Ref { source_idx: u16 }
            + 4 + FLAT_ROUND0_MAX_C0_EXT * 2
            + 4 + FLAT_ROUND0_MAX_C1_BF_BF * 4  // GpuFlatC1Pair { source_a: u16, source_b: u16 }
            + 4 + FLAT_ROUND0_MAX_C1_E4_E4 * 4
            + 4 + FLAT_ROUND0_MAX_C1_BF_E4 * 4
            + 4 + FLAT_ROUND0_MAX_C1_LINEAR * 2,
        STRUCT_ALIGN,
    );

    // Continuation/round1/round2 unified descs: source entries become 4-byte
    // dual-u16 records instead of larger entries that hold pointers, then term
    // tables stay the same (4 B/term), tile metadata stays.
    // GpuFlatUnifiedTerm = 8 B (source_a:u16, source_b:u16, term_type:u16, coeff_idx:u16).
    const TERM_BYTES: usize = 8;
    const TILE_OFFSETS_BYTES: usize = 2 * (FLAT_CONT_UNIFIED_MAX_TILES + 1) * 2;
    const FOLD_SOURCES_BYTES: usize = FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES * 2;

    let flat_round1 = align_up(
        TABLES_BYTES
            + 4 + 4 // base_layer_half_size, next_layer_size
            + FLAT_CONT_MAX_BASE_SOURCES * 4 // base source records
            + 4 + FLAT_CONT_MAX_EXT_SOURCES * 4
            + 4 + FLAT_CONT_UNIFIED_MAX_TERMS * TERM_BYTES
            + 4 + 4 // num_constant_terms, num_tiles
            + TILE_OFFSETS_BYTES
            + FOLD_SOURCES_BYTES,
        STRUCT_ALIGN,
    );
    // Round 2: same shape as round 1, plus an extra `base_quarter_size` u32.
    let flat_round2 = flat_round1 + 4;
    let flat_continuation = align_up(
        TABLES_BYTES
            + crate::prover::gkr::backward_kernels::GKR_DIM_REDUCING_BASE_SLOTS * 4 * 2 // prev_per_poly_offset[N], cache_per_poly_offset[N] (per-slot)
            + 4 + FLAT_CONT_MAX_SOURCES * 4 // single source record array
            + 4 + FLAT_CONT_UNIFIED_MAX_TERMS * TERM_BYTES
            + 4 + 4
            + TILE_OFFSETS_BYTES
            + FOLD_SOURCES_BYTES,
        STRUCT_ALIGN,
    );

    PostCompactionSizes {
        dim_reducing_round0_batch: dim_reducing,
        dim_reducing_continuation_batch: dim_reducing,
        flat_round0_static_desc: flat_round0,
        flat_round1_unified_desc: flat_round1,
        flat_round2_unified_desc: flat_round2,
        flat_continuation_unified_desc: flat_continuation,
    }
}

pub(crate) fn log_post_compaction_sizes(sizes: &PostCompactionSizes) {
    let report = |name: &str, bytes: usize| {
        let status = if bytes <= KERNEL_ARG_SOFT_TARGET_BYTES {
            "SOFT_TARGET"
        } else if bytes <= KERNEL_ARG_HARD_CEILING_BYTES {
            "OVER_SOFT_TARGET"
        } else {
            "OVER_HARD_CEILING"
        };
        log::info!(
            "[gkr-audit] post-compaction size: {} = {} B (soft={}KB hard={}KB) [{}]",
            name,
            bytes,
            KERNEL_ARG_SOFT_TARGET_BYTES / 1024,
            KERNEL_ARG_HARD_CEILING_BYTES / 1024,
            status,
        );
    };
    report("dim_reducing_round0_batch", sizes.dim_reducing_round0_batch);
    report(
        "dim_reducing_continuation_batch",
        sizes.dim_reducing_continuation_batch,
    );
    report("flat_round0_static_desc", sizes.flat_round0_static_desc);
    report("flat_round1_unified_desc", sizes.flat_round1_unified_desc);
    report("flat_round2_unified_desc", sizes.flat_round2_unified_desc);
    report(
        "flat_continuation_unified_desc",
        sizes.flat_continuation_unified_desc,
    );
}

#[cfg(test)]
pub(crate) fn check_descriptor_sizes_under_hard_ceiling(
    sizes: &PostCompactionSizes,
) -> Result<(), String> {
    let pairs = [
        ("dim_reducing_round0_batch", sizes.dim_reducing_round0_batch),
        (
            "dim_reducing_continuation_batch",
            sizes.dim_reducing_continuation_batch,
        ),
        ("flat_round0_static_desc", sizes.flat_round0_static_desc),
        ("flat_round1_unified_desc", sizes.flat_round1_unified_desc),
        ("flat_round2_unified_desc", sizes.flat_round2_unified_desc),
        (
            "flat_continuation_unified_desc",
            sizes.flat_continuation_unified_desc,
        ),
    ];
    for (name, bytes) in pairs.iter() {
        if *bytes > KERNEL_ARG_HARD_CEILING_BYTES {
            return Err(format!(
                "{} = {} B exceeds 32 KB inline kernel-arg ceiling",
                name, bytes,
            ));
        }
    }
    Ok(())
}

/// Per-layer flat-path round-0 term counts. Mirrors the term-table fields of
/// `GpuFlatRound0StaticDescCompact` so a per-circuit max can be compared
/// against the locked `FLAT_ROUND0_MAX_*` ceilings.
#[cfg(test)]
#[derive(Default, Debug, Clone, Copy)]
pub(crate) struct FlatRound0TermCounts {
    pub(crate) c0_bf: u32,
    pub(crate) c0_ext: u32,
    pub(crate) c1_bf_bf: u32,
    pub(crate) c1_e4_e4: u32,
    pub(crate) c1_bf_e4: u32,
    pub(crate) c1_linear: u32,
}

#[cfg(test)]
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
#[cfg(test)]
const FLAT_LINEAR_FORM_SENTINEL: u32 = u32::MAX;

#[cfg(test)]
fn count_metadata_terms<E>(
    src: &Option<crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource<E>>,
    filter_sentinel: bool,
) -> (usize, usize) {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
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
/// in `backward_flat::build_flat_round0_plan` exactly. Used by the Phase 0
/// audit to find the per-circuit max for tightening `FLAT_ROUND0_MAX_*`.
#[cfg(test)]
pub(crate) fn project_layer_flat_round0_term_counts<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> FlatRound0TermCounts {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelKind as K;
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
#[cfg(test)]
pub(super) fn project_layer_main_combined_claim_pair_count<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> usize {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelKind as K;
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
#[cfg(test)]
pub(crate) fn collect_unique_immediates_for_layer<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> std::collections::HashSet<[u32; 4]>
where
    E: field::Field,
{
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelKind as K;
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

#[cfg(test)]
pub(crate) fn collect_structural_immediates_for_layer<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> (usize, usize)
where
    E: field::Field,
{
    use crate::ops::immediate_factors::ImmediateFactorInterner;
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelKind as K;

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
#[cfg(test)]
fn metadata_qt_lt_term_lens<E>(
    src: &Option<crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource<E>>,
    filter_sentinel: bool,
) -> (Vec<usize>, Vec<usize>) {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
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

/// Per-layer flat-path round-0 audit: total recipes (= `GpuRecipeHeader`
/// count), total prefactor terms (= `GpuPrefactorTerm` count, summed over
/// recipe groups), and the qt×lt cross-product blowup accounting.
///
/// Mirrors the gate-kind dispatch in [`backward_flat::build_flat_round0_plan`]
/// and the per-emitter recipe shapes:
/// - bare bc0/bc1/neg_bc0 recipes (output evaluations) → 1 recipe, 0 terms
/// - `emit_constraint_gate` → M recipes, each with 1 group of qt[i].ct
/// - `emit_cross_product_gate` → M·N recipes, each with 2 groups (qt[i].ct, lt[j].ct)
/// - `emit_materialize_gate` → N recipes, each with 1 group of lt[j].ct
/// - `emit_single_times_linear_form` → N recipes, each with 1 group of lt[j].ct
/// - `emit_linear_form_times_ext` → N recipes, each with 1 group of lt[j].ct
#[cfg(test)]
#[derive(Default, Debug, Clone, Copy)]
pub(crate) struct FlatRecipeAudit {
    pub(crate) total_recipes: u32,
    pub(crate) total_terms: u32,
    /// Recipes from blueprints with `Immediate` constraint metadata
    /// (immediate_factor = host-pre-evaluated E4 from external_challenges,
    /// prefactors empty). `immediate_factor` is per-recipe distinct in
    /// general; dedup-via-shared-slot doesn't trivially apply.
    pub(crate) recipes_immediate: u32,
    /// Recipes from blueprints with `Deferred` constraint metadata
    /// (immediate_factor = E::ONE, prefactors carry the structural
    /// `(coeff, source, power)` triples that the kernel evaluates on-device).
    /// All such recipes share `immediate_factor = ONE` ⇒ dedup-trivial.
    pub(crate) recipes_deferred: u32,
    /// Recipes emitted by gate-kind paths that don't consult constraint
    /// metadata at all (BaseCopy, ExtCopy, Product, MaskIdentity, LookupPair,
    /// LookupBasePair, etc.) — bare bc0/bc1/neg_bc0/gamma recipes. Same
    /// immediate (= E::ONE) and no prefactors. Dedup-trivial.
    pub(crate) recipes_bare: u32,
    /// Number of blueprints that route through `emit_cross_product_gate`.
    pub(crate) xprod_gates: u32,
    /// Σ M·N — recipes shipped today from cross-product expansion.
    pub(crate) xprod_expanded_recipes: u32,
    /// Σ (M+N) — source-index entries needed if the kernel ABI accepted a
    /// "product of two sums" term type (one recipe per gate, plus M+N source
    /// indices on the side arrays).
    pub(crate) xprod_source_indices_compact: u32,
    /// Σ M·N · (avg terms per recipe) — terms shipped today from the
    /// expansion. Used together with `xprod_source_indices_compact` to bound
    /// the byte-savings of a hypothetical pair-of-sums ABI.
    pub(crate) xprod_expanded_terms: u32,
    /// Σ (Σ qt.ct + Σ lt.ct) — terms across all cross-product gates if the
    /// kernel kept the prefactor groups merged (one (Σ qt.ct) group + one
    /// (Σ lt.ct) group per gate).
    pub(crate) xprod_compact_terms: u32,
    /// Largest single-gate M·N (worst per-gate blowup).
    pub(crate) xprod_max_m_times_n: u32,
    /// Largest single-gate (M, N).
    pub(crate) xprod_max_m: u32,
    pub(crate) xprod_max_n: u32,
}

#[cfg(test)]
impl FlatRecipeAudit {
    fn merge_max(&mut self, other: &Self) {
        // For totals we keep per-layer (max layer wins), since the H2D is
        // also per-layer.
        if other.total_recipes > self.total_recipes {
            *self = *other;
        }
    }
}

#[cfg(test)]
pub(crate) fn project_layer_flat_round0_recipe_audit<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> FlatRecipeAudit {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelKind as K;
    let mut a = FlatRecipeAudit::default();

    // Helper: account for one cross-product expansion (qt × lt). The path
    // tag (Immediate vs Deferred) determines whether we count the M·N
    // recipes as immediate-bucket (16 B `immediate_factor` per recipe set
    // to qt.challenge·lt.challenge) or deferred-bucket (immediate_factor =
    // ONE, prefactors carry the structural terms).
    let mut account_xprod =
        |a: &mut FlatRecipeAudit, qt_lens: &[usize], lt_lens: &[usize], is_immediate: bool| {
            let m = qt_lens.len();
            let n = lt_lens.len();
            if m == 0 || n == 0 {
                return;
            }
            let mn = (m * n) as u32;
            let qt_total: usize = qt_lens.iter().sum();
            let lt_total: usize = lt_lens.iter().sum();
            let xprod_terms_today = (n * qt_total + m * lt_total) as u32;
            let xprod_terms_compact = (qt_total + lt_total) as u32;

            a.xprod_gates += 1;
            a.xprod_expanded_recipes += mn;
            a.xprod_source_indices_compact += (m + n) as u32;
            a.xprod_expanded_terms += xprod_terms_today;
            a.xprod_compact_terms += xprod_terms_compact;
            a.xprod_max_m_times_n = a.xprod_max_m_times_n.max(mn);
            a.xprod_max_m = a.xprod_max_m.max(m as u32);
            a.xprod_max_n = a.xprod_max_n.max(n as u32);

            a.total_recipes += mn;
            a.total_terms += xprod_terms_today;
            if is_immediate {
                a.recipes_immediate += mn;
            } else {
                a.recipes_deferred += mn;
            }
        };

    // Helper: account for a list of recipes whose prefactors carry one group
    // of `lens[i]` terms each. `lens.len()` recipes, Σ lens terms.
    // `is_immediate` selects the path bucket.
    let account_single_group = |a: &mut FlatRecipeAudit, lens: &[usize], is_immediate: bool| {
        let n = lens.len() as u32;
        a.total_recipes += n;
        a.total_terms += lens.iter().sum::<usize>() as u32;
        if is_immediate {
            a.recipes_immediate += n;
        } else {
            a.recipes_deferred += n;
        }
    };

    // Helper: bare bc0/bc1/neg_bc0 recipes (immediate=ONE, no prefactors).
    let account_bare = |a: &mut FlatRecipeAudit, n: u32| {
        a.total_recipes += n;
        a.recipes_bare += n;
    };

    let is_immediate = |src: &Option<MS<E>>| matches!(src, Some(MS::Immediate(_)));

    for bp in blueprints {
        let imm = is_immediate(&bp.constraint_metadata_source);
        match bp.kind {
            K::BaseCopy | K::LinearBaseOutput => account_bare(&mut a, 1),
            K::ExtCopy => account_bare(&mut a, 1),
            K::Product => account_bare(&mut a, 2),
            K::MaskIdentity => account_bare(&mut a, 2),
            K::LookupPair => account_bare(&mut a, 5),
            K::LookupBasePair => account_bare(&mut a, 3),
            K::LookupBaseMinusMultiplicityByBase => account_bare(&mut a, 4),
            K::LookupExtMinusMultiplicityByExt => account_bare(&mut a, 4),
            K::LookupUnbalanced => account_bare(&mut a, 4),
            K::LookupUnbalancedExtension => account_bare(&mut a, 4),
            K::LookupWithCachedDensAndSetup => account_bare(&mut a, 5),
            K::LookupExtPair => account_bare(&mut a, 3),
            K::EnforceConstraintsMaxQuadratic => {
                let (qt, _) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, false);
                account_single_group(&mut a, &qt, imm);
            }
            K::InitsAndTeardownsInitialPair => {
                account_bare(&mut a, 1);
                let (qt, _) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, false);
                account_single_group(&mut a, &qt, imm);
            }
            K::InitialGrandProductWithoutCaches => {
                account_bare(&mut a, 1);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::MaterializeGrandProductTermExpression => {
                account_bare(&mut a, 1);
                let (_, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &lt, imm);
            }
            K::LookupPairFromBaseInputs | K::LookupPairFromVectorInputs => {
                account_bare(&mut a, 2);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::LookupWithDensAndSetupExpressions => {
                account_bare(&mut a, 2);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &lt, imm);
                account_single_group(&mut a, &qt, imm);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::LookupFromVectorInputWithSetup => {
                account_bare(&mut a, 2);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &qt, imm);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::LookupUnbalancedPairWithVectorInputs => {
                account_bare(&mut a, 2);
                let (_, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &lt, imm);
                account_single_group(&mut a, &lt, imm);
            }
        }
    }

    a
}

/// Per-layer flat-path **continuation** audit — same shape as the round-0
/// audit but mirrors `backward_flat::build_flat_continuation_plan` and its
/// `emit_continuation_*` helpers. Continuation runs on rounds 3+ (after the
/// dimension-reducing folds), so the recipe shapes differ from round-0.
///
/// Same fields as `FlatRecipeAudit`. Cross-product accounting follows the
/// (qt, lt) loop in `emit_continuation_cross_product_gate` exactly: real
/// (qt, lt) pairs and (qt, lt_const) / (qt_const, lt) / (qt_const, lt_const)
/// fan-out are all counted as expanded recipes today.
#[cfg(test)]
pub(crate) fn project_layer_flat_continuation_recipe_audit<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> FlatRecipeAudit {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelKind as K;
    let mut a = FlatRecipeAudit::default();

    // Bare-recipe accumulator (n recipes, 0 terms — no prefactors).
    let bare = |a: &mut FlatRecipeAudit, n: u32| {
        a.total_recipes += n;
        a.recipes_bare += n;
    };
    // Gamma-recipe accumulator (n recipes, n terms each carrying 1 ChallengeTerm
    // — `bc0_gamma`/`bc1_gamma`/`neg_bc0_gamma`). The kernel evaluates the
    // gamma against on-device `lookup_add`, so gamma recipes are deferred-bucket
    // (immediate_factor = ONE).
    let gamma = |a: &mut FlatRecipeAudit, n: u32| {
        a.total_recipes += n;
        a.total_terms += n;
        a.recipes_deferred += n;
    };

    // emit_continuation_constraint_gate: walks qt, non-sentinel lt, plus
    // sentinel-lt push_constants and a tail constant_terms push_constant.
    // `is_immediate` selects the bucket.
    let emit_constraint = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        let (qt_lens, lt_lens, qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts) =
            metadata_split_with_consts(src);
        let n = qt_lens.len() as u32 + lt_lens.len() as u32 + n_lt_consts as u32;
        a.total_recipes += n;
        a.total_terms += qt_lens.iter().sum::<usize>() as u32;
        a.total_terms += lt_lens.iter().sum::<usize>() as u32;
        a.total_terms += lt_consts_total as u32;
        if is_immediate {
            a.recipes_immediate += n;
        } else {
            a.recipes_deferred += n;
        }
        let _ = (qt_consts_total, n_qt_consts);
    };

    // emit_continuation_cross_product_gate: walks (qt_real × lt_real) +
    // (qt_real × lt_const) + (lt_real × qt_const) + (qt_const × lt_const).
    let emit_xprod = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        let (qt_lens, lt_lens, qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts) =
            metadata_split_with_consts(src);
        let m = qt_lens.len();
        let n = lt_lens.len();
        let qt_total: usize = qt_lens.iter().sum();
        let lt_total: usize = lt_lens.iter().sum();
        if m == 0 && n == 0 && n_qt_consts == 0 && n_lt_consts == 0 {
            return;
        }

        let xprod_mn = (m * n) as u32;
        let xprod_mn_terms = (n * qt_total + m * lt_total) as u32;
        let mn_lc = (m * n_lt_consts) as u32;
        let mn_lc_terms = (n_lt_consts * qt_total + m * lt_consts_total) as u32;
        let nm_qc = (n * n_qt_consts) as u32;
        let nm_qc_terms = (n_qt_consts * lt_total + n * qt_consts_total) as u32;
        let cc = (n_qt_consts * n_lt_consts) as u32;
        let cc_terms = (n_lt_consts * qt_consts_total + n_qt_consts * lt_consts_total) as u32;

        let total_recipes = xprod_mn + mn_lc + nm_qc + cc;
        let total_terms = xprod_mn_terms + mn_lc_terms + nm_qc_terms + cc_terms;
        a.total_recipes += total_recipes;
        a.total_terms += total_terms;
        if is_immediate {
            a.recipes_immediate += total_recipes;
        } else {
            a.recipes_deferred += total_recipes;
        }

        if total_recipes > 0 {
            a.xprod_gates += 1;
            a.xprod_expanded_recipes += total_recipes;
            a.xprod_expanded_terms += total_terms;
            a.xprod_max_m_times_n = a.xprod_max_m_times_n.max(xprod_mn);
            a.xprod_max_m = a.xprod_max_m.max(m as u32);
            a.xprod_max_n = a.xprod_max_n.max(n as u32);
            a.xprod_source_indices_compact += (m + n + n_qt_consts + n_lt_consts) as u32;
            a.xprod_compact_terms +=
                (qt_total + lt_total + qt_consts_total + lt_consts_total) as u32;
        }
    };

    let emit_materialize = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        let (_, lt_lens, _, lt_consts_total, _, n_lt_consts) = metadata_split_with_consts(src);
        let n = lt_lens.len() as u32 + n_lt_consts as u32;
        a.total_recipes += n;
        a.total_terms += lt_lens.iter().sum::<usize>() as u32;
        a.total_terms += lt_consts_total as u32;
        if is_immediate {
            a.recipes_immediate += n;
        } else {
            a.recipes_deferred += n;
        }
    };

    let emit_single_times_linear =
        |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, use_qt_side: bool, is_immediate: bool| {
            let (qt_lens, lt_lens, qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts) =
                metadata_split_with_consts(src);
            let (lens, consts_total, n_consts) = if use_qt_side {
                (&qt_lens, qt_consts_total, n_qt_consts)
            } else {
                (&lt_lens, lt_consts_total, n_lt_consts)
            };
            let n = lens.len() as u32 + n_consts as u32;
            a.total_recipes += n;
            a.total_terms += lens.iter().sum::<usize>() as u32;
            a.total_terms += consts_total as u32;
            if is_immediate {
                a.recipes_immediate += n;
            } else {
                a.recipes_deferred += n;
            }
        };

    let emit_linear_form = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        emit_single_times_linear(a, src, false, is_immediate);
    };

    let is_immediate = |src: &Option<MS<E>>| matches!(src, Some(MS::Immediate(_)));

    for bp in blueprints {
        let src = &bp.constraint_metadata_source;
        let imm = is_immediate(src);
        match bp.kind {
            K::BaseCopy | K::ExtCopy => bare(&mut a, 1),
            K::LinearBaseOutput => emit_constraint(&mut a, src, imm),
            K::Product => bare(&mut a, 1),
            K::MaskIdentity => bare(&mut a, 3),
            K::LookupPair => bare(&mut a, 3),
            K::LookupBasePair => {
                bare(&mut a, 3);
                gamma(&mut a, 4);
            }
            K::LookupBaseMinusMultiplicityByBase => {
                bare(&mut a, 3);
                gamma(&mut a, 5);
            }
            K::LookupExtMinusMultiplicityByExt => {
                bare(&mut a, 3);
                gamma(&mut a, 5);
            }
            K::LookupUnbalanced => {
                bare(&mut a, 3);
                gamma(&mut a, 2);
            }
            K::LookupUnbalancedExtension => {
                bare(&mut a, 3);
                gamma(&mut a, 2);
            }
            K::LookupWithCachedDensAndSetup => {
                bare(&mut a, 3);
                gamma(&mut a, 5);
            }
            K::EnforceConstraintsMaxQuadratic => emit_constraint(&mut a, src, imm),
            K::InitsAndTeardownsInitialPair => emit_constraint(&mut a, src, imm),
            K::InitialGrandProductWithoutCaches => emit_xprod(&mut a, src, imm),
            K::MaterializeGrandProductTermExpression => emit_materialize(&mut a, src, imm),
            K::LookupPairFromBaseInputs | K::LookupPairFromVectorInputs => {
                emit_linear_form(&mut a, src, imm);
                emit_linear_form(&mut a, src, imm);
                emit_xprod(&mut a, src, imm);
            }
            K::LookupExtPair => {
                bare(&mut a, 3);
                gamma(&mut a, 4);
            }
            K::LookupWithDensAndSetupExpressions => {
                emit_single_times_linear(&mut a, src, false, imm);
                emit_single_times_linear(&mut a, src, true, imm);
                emit_xprod(&mut a, src, imm);
            }
            K::LookupFromVectorInputWithSetup => {
                emit_single_times_linear(&mut a, src, false, imm);
                emit_linear_form(&mut a, src, imm);
                emit_xprod(&mut a, src, imm);
            }
            K::LookupUnbalancedPairWithVectorInputs => {
                emit_linear_form(&mut a, src, imm);
                emit_linear_form(&mut a, src, imm);
                bare(&mut a, 1);
            }
        }
    }

    a
}

/// Helper: split constraint metadata into (qt_real_lens, lt_real_lens,
/// qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts).
/// `_real_lens` are per-term `challenge_terms.len()` for non-sentinel rows;
/// `_consts_total` is summed `challenge_terms.len()` across sentinel rows;
/// `n_*_consts` is the count of sentinel rows.
/// `Immediate` metadata reports 0-len for everything (no challenge_terms).
#[cfg(test)]
fn metadata_split_with_consts<E>(
    src: &Option<crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource<E>>,
) -> (Vec<usize>, Vec<usize>, usize, usize, usize, usize) {
    use crate::prover::gkr::backward_kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    match src {
        None => (Vec::new(), Vec::new(), 0, 0, 0, 0),
        Some(MS::Immediate(meta)) => {
            let qt_real: Vec<usize> = meta
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs != FLAT_LINEAR_FORM_SENTINEL)
                .map(|_| 0)
                .collect();
            let lt_real: Vec<usize> = meta
                .linear_terms
                .iter()
                .filter(|t| t.input != FLAT_LINEAR_FORM_SENTINEL)
                .map(|_| 0)
                .collect();
            let n_qt_consts = meta
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            let n_lt_consts = meta
                .linear_terms
                .iter()
                .filter(|t| t.input == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            (qt_real, lt_real, 0, 0, n_qt_consts, n_lt_consts)
        }
        Some(MS::Deferred(tmpl)) => {
            let qt_real: Vec<usize> = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs != FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .collect();
            let lt_real: Vec<usize> = tmpl
                .linear_terms
                .iter()
                .filter(|t| t.input != FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .collect();
            let qt_consts_total: usize = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs == FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .sum();
            let lt_consts_total: usize = tmpl
                .linear_terms
                .iter()
                .filter(|t| t.input == FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .sum();
            let n_qt_consts = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            let n_lt_consts = tmpl
                .linear_terms
                .iter()
                .filter(|t| t.input == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            (
                qt_real,
                lt_real,
                qt_consts_total,
                lt_consts_total,
                n_qt_consts,
                n_lt_consts,
            )
        }
    }
}

/// Project the per-layer main-layer gather payload size. Mirrors
/// `final_evaluation_sources_for_last_step` (`backward.rs:6237-6275`) by
/// counting distinct, non-placeholder addresses across every kernel's
/// `inputs_in_base ∪ inputs_in_extension`. The result bounds
/// `gather_e_addresses`'s `num_addresses` argument.
#[cfg(test)]
pub(super) fn project_layer_main_gather_num_addresses<E>(
    blueprints: &[crate::prover::gkr::backward_kernels::GpuGKRMainLayerKernelBlueprint<E>],
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

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Once;

    use field::baby_bear::base::BabyBearField;

    use super::*;

    static LOGGER_INIT: Once = Once::new();

    fn init_logger() {
        LOGGER_INIT.call_once(|| {
            let _ = env_logger::Builder::from_default_env()
                .filter_level(log::LevelFilter::Info)
                .is_test(true)
                .try_init();
        });
    }

    fn artifact_path(relative: &str) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join(relative)
    }

    fn load_artifact(relative: &str) -> GKRCircuitArtifact<BabyBearField> {
        let f = std::fs::File::open(artifact_path(relative))
            .unwrap_or_else(|e| panic!("opening {}: {}", relative, e));
        serde_json::from_reader(f).unwrap_or_else(|e| panic!("parsing {}: {}", relative, e))
    }

    /// All committed circuit layouts under `cs/compiled_circuits/`. A new
    /// circuit MUST be added here so the audit covers it. Phase 0 enumerates
    /// the cached + no-cache pair for every entry so missing modes show up at
    /// the top of the test output.
    const CIRCUIT_BASENAMES: &[&str] = &[
        "add_sub_lui_auipc_mop_preprocessed",
        "bigint_with_extended_control",
        "blake2_with_extended_control",
        "inits_and_teardowns_preprocessed",
        "jump_branch_slt_preprocessed",
        "keccak_special5",
        "mem_subword_only_preprocessed",
        "mem_word_only_preprocessed",
        "shift_binop_preprocessed",
        "unsigned_mul_div_preprocessed",
    ];

    /// Phase 0 — measurement pass. Walks every layout JSON in
    /// `cs/compiled_circuits/` (cached + no-cache), audits per-layer
    /// structural counts against the locked Phase-0 ceilings, and reports
    /// post-compaction descriptor sizes against the 32 KB inline kernel-arg
    /// ceiling.
    ///
    /// Run with `RUST_LOG=info cargo test -p gpu_prover --lib gkr_address_audit -- --nocapture`
    /// to see the full per-layer dump.
    #[test]
    fn phase0_gkr_address_audit() {
        init_logger();

        let sizes = projected_post_compaction_sizes();
        log_post_compaction_sizes(&sizes);
        if let Err(msg) = check_descriptor_sizes_under_hard_ceiling(&sizes) {
            panic!("phase 0 abort: descriptor size exceeds 32 KB hard ceiling: {msg}");
        }

        let mut audited = Vec::new();
        let mut errors: Vec<String> = Vec::new();
        let mut global_term_max = super::FlatRound0TermCounts::default();
        let mut global_combined_claim_pair_max: usize = 0;
        let mut global_combined_claim_max_circuit = String::new();
        let mut global_combined_claim_max_layer: usize = 0;
        let mut global_gather_num_addresses_max: usize = 0;
        let mut global_gather_max_circuit = String::new();
        let mut global_gather_max_layer: usize = 0;

        for base in CIRCUIT_BASENAMES.iter() {
            for (suffix, mode_label) in [("_layout_gkr.json", "cached")] {
                let rel = format!("cs/compiled_circuits/{}{}", base, suffix);
                let path = artifact_path(&rel);
                if !path.exists() {
                    log::warn!("[gkr-audit] missing {} ({})", rel, mode_label);
                    continue;
                }
                let artifact = load_artifact(&rel);
                let name = format!("{} [{}]", base, mode_label);
                let audit = audit_circuit(&name, &artifact);
                log_circuit_audit(&audit);
                if let Err(e) = check_audit_against_budgets(&audit) {
                    errors.push(format!("{}", e));
                }
                let circuit_term_max = project_circuit_flat_round0_term_counts(&name, &artifact);
                global_term_max.merge_max(&circuit_term_max);
                let (circuit_pair_max, circuit_pair_max_layer) =
                    project_circuit_main_combined_claim_pair_max(&name, &artifact);
                if circuit_pair_max > global_combined_claim_pair_max {
                    global_combined_claim_pair_max = circuit_pair_max;
                    global_combined_claim_max_circuit = name.clone();
                    global_combined_claim_max_layer = circuit_pair_max_layer;
                }
                let (circuit_gather_max, circuit_gather_max_layer) =
                    project_circuit_main_gather_num_addresses_max(&name, &artifact);
                if circuit_gather_max > global_gather_num_addresses_max {
                    global_gather_num_addresses_max = circuit_gather_max;
                    global_gather_max_circuit = name.clone();
                    global_gather_max_layer = circuit_gather_max_layer;
                }
                let _ = project_circuit_flat_recipe_audit(&name, &artifact);
                audited.push(audit);
            }
        }

        log::info!(
            "[gkr-audit] phase 0 audited {} circuit/mode combinations",
            audited.len(),
        );
        log::info!(
            "[gkr-audit] flat round-0 term-count max across all circuits/layers: \
             c0_bf={} c0_ext={} c1_bf_bf={} c1_e4_e4={} c1_bf_e4={} c1_linear={}",
            global_term_max.c0_bf,
            global_term_max.c0_ext,
            global_term_max.c1_bf_bf,
            global_term_max.c1_e4_e4,
            global_term_max.c1_bf_e4,
            global_term_max.c1_linear,
        );
        log::info!(
            "[gkr-audit] main-layer combined_claim_desc_pairs max across all circuits: \
             {} u32 entries = {} bytes (circuit={}, layer={})",
            global_combined_claim_pair_max,
            global_combined_claim_pair_max * 4,
            global_combined_claim_max_circuit,
            global_combined_claim_max_layer,
        );
        let combined_claim_pair_count = global_combined_claim_pair_max / 2;
        if combined_claim_pair_count > super::GKR_COMBINED_CLAIM_MAX_PAIRS {
            errors.push(format!(
                "{}: combined_claim_desc_pairs has {} pairs ({} u32 entries) — exceeds \
                 GKR_COMBINED_CLAIM_MAX_PAIRS = {} (layer {})",
                global_combined_claim_max_circuit,
                combined_claim_pair_count,
                global_combined_claim_pair_max,
                super::GKR_COMBINED_CLAIM_MAX_PAIRS,
                global_combined_claim_max_layer,
            ));
        }

        log::info!(
            "[gkr-audit] main-layer gather num_addresses max across all circuits: \
             {} ({} B src_ptrs) (circuit={}, layer={})",
            global_gather_num_addresses_max,
            global_gather_num_addresses_max * 8,
            global_gather_max_circuit,
            global_gather_max_layer,
        );
        if global_gather_num_addresses_max > super::GKR_GATHER_MAX_ADDRESSES {
            errors.push(format!(
                "{}: main-layer gather has {} distinct addresses — exceeds \
                 GKR_GATHER_MAX_ADDRESSES = {} (layer {})",
                global_gather_max_circuit,
                global_gather_num_addresses_max,
                super::GKR_GATHER_MAX_ADDRESSES,
                global_gather_max_layer,
            ));
        }

        if !errors.is_empty() {
            panic!(
                "phase 0 abort: {} circuit(s) exceed locked Phase-0 budgets:\n{}",
                errors.len(),
                errors.join("\n"),
            );
        }
    }

    /// Walk every layer of a circuit, build the same kernel blueprints the
    /// production prover does (CPU-only via the `is_base_field_at_layer`
    /// closure), then project the per-layer flat round-0 term counts. Returns
    /// the per-circuit max across layers; the test merges into a global max.
    fn project_circuit_flat_round0_term_counts(
        circuit_name: &str,
        artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    ) -> super::FlatRound0TermCounts {
        use crate::prover::gkr::backward::{
            build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
        };
        use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
        use field::baby_bear::ext4::BabyBearExt4;
        use prover::definitions::GKRExternalChallenges;
        use prover::gkr::high_bits_offset_for_inits_and_teardowns;

        let layout = GpuGKRStorageLayout::from_artifact(artifact);
        let inits_top_bits =
            canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
        let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
        };
        let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();

        let mut circuit_max = super::FlatRound0TermCounts::default();
        for (layer_idx, layer) in artifact.layers.iter().enumerate() {
            // Skip layers that use relations the GPU main-layer dispatch
            // doesn't implement. The static blueprint builder panics on these,
            // and circuits containing them aren't currently GPU-provable.
            if layer_has_unsupported_relations(layer) {
                log::warn!(
                    "[gkr-audit] {} layer {} has unsupported relations; skipping term-count projection",
                    circuit_name,
                    layer_idx,
                );
                continue;
            }
            let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
                layout
                    .layers
                    .get(layer_idx)
                    .and_then(|l| l.lookup(addr))
                    .map(|(_, ft, _)| ft == FieldType::Base)
                    .unwrap_or(false)
            };
            let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
                layer,
                layer_idx,
                &is_base_field_at_layer,
                &external_challenges,
                &inits_top_bits,
                inits_high_bits_shift,
                artifact.memory_layout.total_width,
                artifact.witness_layout.total_width,
            );
            let layer_counts = super::project_layer_flat_round0_term_counts(&blueprints);
            log::debug!(
                "[gkr-audit] {} layer {}: c0_bf={} c0_ext={} c1_bf_bf={} c1_e4_e4={} c1_bf_e4={} c1_linear={}",
                circuit_name,
                layer_idx,
                layer_counts.c0_bf,
                layer_counts.c0_ext,
                layer_counts.c1_bf_bf,
                layer_counts.c1_e4_e4,
                layer_counts.c1_bf_e4,
                layer_counts.c1_linear,
            );
            circuit_max.merge_max(&layer_counts);
        }
        log::info!(
            "[gkr-audit] {} flat round-0 term-count max: c0_bf={} c0_ext={} c1_bf_bf={} c1_e4_e4={} c1_bf_e4={} c1_linear={}",
            circuit_name,
            circuit_max.c0_bf,
            circuit_max.c0_ext,
            circuit_max.c1_bf_bf,
            circuit_max.c1_e4_e4,
            circuit_max.c1_bf_e4,
            circuit_max.c1_linear,
        );
        circuit_max
    }

    /// Walk every supported main-layer of a circuit, build the same blueprints
    /// the production prover does, and compute the per-layer
    /// `combined_claim_desc_pairs` u32 entry count. Returns
    /// `(max_entries, layer_idx_at_max)`.
    fn project_circuit_main_combined_claim_pair_max(
        circuit_name: &str,
        artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    ) -> (usize, usize) {
        use crate::prover::gkr::backward::{
            build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
        };
        use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
        use field::baby_bear::ext4::BabyBearExt4;
        use prover::definitions::GKRExternalChallenges;
        use prover::gkr::high_bits_offset_for_inits_and_teardowns;

        let layout = GpuGKRStorageLayout::from_artifact(artifact);
        let inits_top_bits =
            canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
        let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
        };
        let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();

        let mut max_entries: usize = 0;
        let mut max_layer: usize = 0;
        for (layer_idx, layer) in artifact.layers.iter().enumerate() {
            if layer_has_unsupported_relations(layer) {
                continue;
            }
            let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
                layout
                    .layers
                    .get(layer_idx)
                    .and_then(|l| l.lookup(addr))
                    .map(|(_, ft, _)| ft == FieldType::Base)
                    .unwrap_or(false)
            };
            let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
                layer,
                layer_idx,
                &is_base_field_at_layer,
                &external_challenges,
                &inits_top_bits,
                inits_high_bits_shift,
                artifact.memory_layout.total_width,
                artifact.witness_layout.total_width,
            );
            let entries = super::project_layer_main_combined_claim_pair_count(&blueprints);
            log::debug!(
                "[gkr-audit] {} layer {}: combined_claim_desc_pairs={} u32 ({} B)",
                circuit_name,
                layer_idx,
                entries,
                entries * 4,
            );
            if entries > max_entries {
                max_entries = entries;
                max_layer = layer_idx;
            }
        }
        log::info!(
            "[gkr-audit] {} main combined_claim_desc_pairs max: {} u32 ({} B) at layer {}",
            circuit_name,
            max_entries,
            max_entries * 4,
            max_layer,
        );
        (max_entries, max_layer)
    }

    /// Walk every supported main-layer of a circuit and dump the flat round-0
    /// recipe audit (recipe count, term count, qt×lt blowup) per layer.
    /// Logs at INFO; returns the per-circuit max recipe-count layer.
    fn project_circuit_flat_recipe_audit(
        circuit_name: &str,
        artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    ) -> super::FlatRecipeAudit {
        use crate::ops::eval_recipes::{
            GpuFlatRecipeEvalDesc, FLAT_IMMEDIATE_MAX_MONOMIALS, FLAT_IMMEDIATE_MAX_RECIPES,
            FLAT_RECIPE_MAX_HEADERS, FLAT_RECIPE_MAX_TERMS,
        };
        use crate::prover::gkr::backward::{
            build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
        };
        use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
        use field::baby_bear::ext4::BabyBearExt4;
        use prover::definitions::GKRExternalChallenges;
        use prover::gkr::high_bits_offset_for_inits_and_teardowns;

        let layout = GpuGKRStorageLayout::from_artifact(artifact);
        let inits_top_bits =
            canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
        let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
        };
        // Set distinct non-zero linearization challenges so that the
        // qt.challenge / lt.challenge values produced by the Immediate-path
        // metadata builders end up structurally distinct (same hardcoded form
        // → same E4; different forms → different E4). This gives a tight
        // upper bound on the unique-immediate count.
        let mut external_challenges =
            GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();
        use field::baby_bear::ext2::BabyBearExt2;
        let make_e4 = |seed: u32| -> BabyBearExt4 {
            BabyBearExt4 {
                c0: BabyBearExt2 {
                    c0: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 17),
                    c1: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 23),
                },
                c1: BabyBearExt2 {
                    c0: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 31),
                    c1: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 41),
                },
            }
        };
        for (i, c) in external_challenges
            .permutation_argument_linearization_challenges
            .iter_mut()
            .enumerate()
        {
            *c = make_e4(i as u32 + 1);
        }
        external_challenges.permutation_argument_additive_part = make_e4(1000);

        let mut circuit_max = super::FlatRecipeAudit::default();
        for (layer_idx, layer) in artifact.layers.iter().enumerate() {
            if layer_has_unsupported_relations(layer) {
                continue;
            }
            let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
                layout
                    .layers
                    .get(layer_idx)
                    .and_then(|l| l.lookup(addr))
                    .map(|(_, ft, _)| ft == FieldType::Base)
                    .unwrap_or(false)
            };
            let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
                layer,
                layer_idx,
                &is_base_field_at_layer,
                &external_challenges,
                &inits_top_bits,
                inits_high_bits_shift,
                artifact.memory_layout.total_width,
                artifact.witness_layout.total_width,
            );
            let r0 = super::project_layer_flat_round0_recipe_audit(&blueprints);
            let cont = super::project_layer_flat_continuation_recipe_audit(&blueprints);
            let unique_immediates = super::collect_unique_immediates_for_layer(&blueprints);
            let (structural_immediates, structural_monomials) =
                super::collect_structural_immediates_for_layer(&blueprints);
            let r0_bytes = r0.total_recipes as usize * 48 + r0.total_terms as usize * 12;
            let cont_bytes = cont.total_recipes as usize * 48 + cont.total_terms as usize * 12;
            assert!(
                (r0.total_recipes as usize) <= FLAT_RECIPE_MAX_HEADERS,
                "{circuit_name} L{layer_idx}: round-0 recipes exceed inline cap"
            );
            assert!(
                (cont.total_recipes as usize) <= FLAT_RECIPE_MAX_HEADERS,
                "{circuit_name} L{layer_idx}: continuation recipes exceed inline cap"
            );
            assert!(
                (r0.total_terms as usize) <= FLAT_RECIPE_MAX_TERMS,
                "{circuit_name} L{layer_idx}: round-0 terms exceed inline cap"
            );
            assert!(
                (cont.total_terms as usize) <= FLAT_RECIPE_MAX_TERMS,
                "{circuit_name} L{layer_idx}: continuation terms exceed inline cap"
            );
            assert!(
                structural_immediates <= FLAT_IMMEDIATE_MAX_RECIPES,
                "{circuit_name} L{layer_idx}: structural immediate recipes {structural_immediates} exceed inline cap {FLAT_IMMEDIATE_MAX_RECIPES}"
            );
            assert!(
                structural_monomials <= FLAT_IMMEDIATE_MAX_MONOMIALS,
                "{circuit_name} L{layer_idx}: structural immediate monomials {structural_monomials} exceed inline cap {FLAT_IMMEDIATE_MAX_MONOMIALS}"
            );
            assert!(
                std::mem::size_of::<GpuFlatRecipeEvalDesc>() <= 32 * 1024,
                "flat recipe descriptor must stay within the 32 KB kernel argument ceiling"
            );
            log::info!(
                "[gkr-audit] {} L{}  \
                 R0: rec={:>5} (imm={:>5} def={:>4} bare={:>4}) term={:>5} bytes={:>7}  \
                 CONT: rec={:>5} (imm={:>5} def={:>4} bare={:>4}) term={:>5} bytes={:>7}  \
                 unique_imm_E4_values_for_layer={:>5} (+1 for ONE slot, total dev_buf_E4s={:>5})  \
                 structural_imm_recipes={:>4} structural_monomials={:>4}",
                circuit_name,
                layer_idx,
                r0.total_recipes,
                r0.recipes_immediate,
                r0.recipes_deferred,
                r0.recipes_bare,
                r0.total_terms,
                r0_bytes,
                cont.total_recipes,
                cont.recipes_immediate,
                cont.recipes_deferred,
                cont.recipes_bare,
                cont.total_terms,
                cont_bytes,
                unique_immediates.len(),
                unique_immediates.len() + 1,
                structural_immediates,
                structural_monomials,
            );
            circuit_max.merge_max(&r0);
        }
        log::info!(
            "[gkr-audit] {} flat round-0 recipe-audit MAX: \
             recipes={} terms={} xprod_gates={} xprod_expanded={} max_MxN={}",
            circuit_name,
            circuit_max.total_recipes,
            circuit_max.total_terms,
            circuit_max.xprod_gates,
            circuit_max.xprod_expanded_recipes,
            circuit_max.xprod_max_m_times_n,
        );
        circuit_max
    }

    /// Walk every supported main-layer of a circuit, build the same blueprints
    /// the production prover does, and compute the per-layer
    /// `gather_e_addresses` payload size (distinct, non-placeholder addresses
    /// across kernel `inputs_in_base ∪ inputs_in_extension`).
    /// Returns `(max_addresses, layer_idx_at_max)`.
    fn project_circuit_main_gather_num_addresses_max(
        circuit_name: &str,
        artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    ) -> (usize, usize) {
        use crate::prover::gkr::backward::{
            build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
        };
        use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
        use field::baby_bear::ext4::BabyBearExt4;
        use prover::definitions::GKRExternalChallenges;
        use prover::gkr::high_bits_offset_for_inits_and_teardowns;

        let layout = GpuGKRStorageLayout::from_artifact(artifact);
        let inits_top_bits =
            canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
        let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
        };
        let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();

        let mut max_addresses: usize = 0;
        let mut max_layer: usize = 0;
        for (layer_idx, layer) in artifact.layers.iter().enumerate() {
            if layer_has_unsupported_relations(layer) {
                continue;
            }
            let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
                layout
                    .layers
                    .get(layer_idx)
                    .and_then(|l| l.lookup(addr))
                    .map(|(_, ft, _)| ft == FieldType::Base)
                    .unwrap_or(false)
            };
            let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
                layer,
                layer_idx,
                &is_base_field_at_layer,
                &external_challenges,
                &inits_top_bits,
                inits_high_bits_shift,
                artifact.memory_layout.total_width,
                artifact.witness_layout.total_width,
            );
            let n = super::project_layer_main_gather_num_addresses(&blueprints);
            log::debug!(
                "[gkr-audit] {} layer {}: gather num_addresses={}",
                circuit_name,
                layer_idx,
                n,
            );
            if n > max_addresses {
                max_addresses = n;
                max_layer = layer_idx;
            }
        }
        log::info!(
            "[gkr-audit] {} main gather num_addresses max: {} at layer {}",
            circuit_name,
            max_addresses,
            max_layer,
        );
        (max_addresses, max_layer)
    }

    /// Detect relations the GPU main-layer dispatch doesn't implement. The
    /// static blueprint builder panics on these via `unimplemented!()`, and
    /// production callers can't process them either — so they're transparent
    /// holes in our term-count projection.
    fn layer_has_unsupported_relations(layer: &cs::gkr_compiler::GKRLayerDescription) -> bool {
        use cs::gkr_compiler::NoFieldGKRRelation as R;
        layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
            .any(|g| {
                matches!(
                    &g.enforced_relation,
                    R::MaxQuadratic { .. } | R::UnbalancedGrandProductWithCache { .. }
                ) || matches!(
                    &g.enforced_relation,
                    R::EnforceConstraintsMaxQuadratic { .. }
                )
            })
    }
}
