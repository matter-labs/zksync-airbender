//! CPU-only diagnostic measurement pass for the GKR backward path. Produces,
//! per-circuit / per-layer / per-mode (cached + no-cache), the counts that
//! determine whether the compact-`u16` encoding fits inside the
//! `cudaLaunchKernelExC` 32 KB inline kernel-arg ceiling without falling back
//! to driver H2D.
//!
//! The pass walks `cs::gkr_compiler::GKRCircuitArtifact` directly — no GPU
//! allocations, no challenges, no kernel launches. It is structural only.
//!
//! Storage-partition taxonomy used as the backing-buffer key by
//! `base_class_backings` / `ext_class_backings` and as the per-launch slot
//! key by the dim-reducing kernel's dynamic `bases[16]` pointer table.
//! Slot assignment within a launch is now dynamic and deduplicated by
//! backing pointer (see `SlotTableBuilder` in `backward::compact::encoder`),
//! so the per-layer ceiling is the kernel's `bases[]` width.
//!
//! | class                       | role                                      |
//! |-----------------------------|-------------------------------------------|
//! | BaseLayerWitness            | base-layer witness columns                |
//! | BaseLayerMemory             | base-layer memory columns                 |
//! | Setup / VirtualSetup        | setup polys (shared across all layers)    |
//! | PrevInnerLayer              | reads of layer (out-1)'s inner-layer      |
//! | PrevCached                  | reads of layer (out-1)'s cached output    |
//! | ThisLayerInnerLayerWrite    | this layer's own inner-layer writes/reads |
//! | ThisLayerCachedWrite        | this layer's own cached writes/reads      |
//! | ScratchSpace                | ext scratch backing                       |
//! | Other                       | cross-layer reads outside ±1 (real        |
//! |                             | backing partition; not an error sentinel) |

use crate::upstream::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp, GKRAddress,
    NoFieldGKRCacheRelation, NoFieldGKRRelation, NoFieldLinearRelation,
    NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldSingleColumnLookupRelation, NoFieldSpecialMemoryContributionRelation,
    NoFieldVectorLookupRelation, RamWordRepresentation,
};

/// Per-launch hard cap on distinct backings. Matches the dim-reducing
/// kernel's `bases: [*const u8; 16]` pointer table width
/// (`GKR_DIM_REDUCING_BASE_SLOTS` in `backward::kernels::encoding`).
pub const GKR_MAX_SLOTS: usize = 16;
pub const GKR_MAX_POLYS_PER_SLOT: usize = 4096;

impl AddressClass {
    pub fn label(self) -> &'static str {
        match self {
            Self::BaseLayerWitness => "BaseLayerWitness",
            Self::BaseLayerMemory => "BaseLayerMemory",
            Self::Setup => "Setup",
            Self::PrevInnerLayer => "PrevInnerLayer",
            Self::PrevCached => "PrevCached",
            Self::ThisLayerCachedWrite => "ThisLayerCachedWrite",
            Self::ThisLayerInnerLayerWrite => "ThisLayerInnerLayer",
            Self::ScratchSpace => "ScratchSpace",
            Self::Other => "Other",
        }
    }
}

/// Storage-partition class. Each variant maps to a distinct backing
/// allocation in `GpuGKRStorage::{base,ext}_class_backings`, so it also
/// serves as a backing-pointer identity proxy for the kernel's dynamic
/// 16-slot pointer table. No variant is treated as an error.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AddressClass {
    BaseLayerWitness = 0,
    BaseLayerMemory = 1,
    Setup = 2,
    PrevInnerLayer = 3,
    PrevCached = 4,
    ThisLayerCachedWrite = 5,
    ThisLayerInnerLayerWrite = 6,
    ScratchSpace = 7,
    /// Cross-layer reads outside the ±1 relative-layer window. Has its
    /// own backing partition at runtime; counted as one slot.
    Other = 255,
}

/// Map a `GKRAddress` to its 8-slot class given the layer the gate writes its
/// output to.
pub fn classify(addr: &GKRAddress, output_layer: usize) -> AddressClass {
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
        GKRAddress::ScratchSpace(_) => AddressClass::ScratchSpace,
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
pub fn collect_addresses_from_relation(
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
        MaxQuadratic { input, output, .. } => {
            push_max_quadratic(input, reads);
            writes.push(*output);
        }
        EnforceSingleMaxQuadraticConstraint { input, .. } => {
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
        LookupWithDensAndCachedSetup {
            input,
            setup,
            output,
        } => {
            reads.push(input.0);
            push_vector(&input.1, reads);
            reads.push(setup.0);
            reads.push(setup.1);
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
pub fn collect_addresses_from_cache_relation(
    rel: &NoFieldGKRCacheRelation,
    reads: &mut Vec<GKRAddress>,
) {
    for a in rel.dependencies() {
        reads.push(a);
    }
}
