use proc_macro2::TokenStream;
use quote::quote;

use std::collections::BTreeSet;

use prover::cs::definitions::gkr::RamWordRepresentation;
use prover::cs::definitions::{GKRAddress, VirtualSetupPoly};
use prover::cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRLayerDescription, NoFieldGKRRelation, NoFieldSpecialMemoryContributionRelation,
};
use prover::field::PrimeField;

pub mod sumcheck;
pub mod transcript;

pub fn coeff_to_internal_repr<F: PrimeField>(coeff: u32) -> u32 {
    F::from_u32_with_reduction(coeff).as_u32_raw_repr_reduced()
}

pub fn addr_to_idx(addr: &GKRAddress, sorted: &[GKRAddress]) -> usize {
    sorted
        .binary_search(addr)
        .unwrap_or_else(|_| panic!("address {:?} not found in sorted list", addr))
}

pub fn transform_gkr_address(addr: &GKRAddress) -> TokenStream {
    match addr {
        GKRAddress::BaseLayerWitness(offset) => {
            quote! { GKRAddress::BaseLayerWitness(#offset) }
        }
        GKRAddress::BaseLayerMemory(offset) => {
            quote! { GKRAddress::BaseLayerMemory(#offset) }
        }
        GKRAddress::InnerLayer { layer, offset } => {
            quote! { GKRAddress::InnerLayer { layer: #layer, offset: #offset } }
        }
        GKRAddress::Setup(offset) => {
            quote! { GKRAddress::Setup(#offset) }
        }
        GKRAddress::ScratchSpace(offset) => {
            quote! { GKRAddress::ScratchSpace(#offset) }
        }
        GKRAddress::Cached { layer, offset } => {
            quote! { GKRAddress::Cached { layer: #layer, offset: #offset } }
        }
        GKRAddress::VirtualSetup(poly) => {
            let variant = match poly {
                VirtualSetupPoly::RangeCheck16Bits => {
                    quote! { VirtualSetupPoly::RangeCheck16Bits }
                }
                VirtualSetupPoly::RangeCheckTimestamp => {
                    quote! { VirtualSetupPoly::RangeCheckTimestamp }
                }
                VirtualSetupPoly::InitsAndTeardownsLow => {
                    quote! { VirtualSetupPoly::InitsAndTeardownsLow }
                }
                VirtualSetupPoly::InitsAndTeardownsHigh => {
                    quote! { VirtualSetupPoly::InitsAndTeardownsHigh }
                }
            };
            quote! { GKRAddress::VirtualSetup(#variant) }
        }
    }
}

/// Collect all `BaseLayerMemory` addresses referenced by a memory expression.
fn collect_mem_expr_addrs(
    rel: &NoFieldSpecialMemoryContributionRelation,
    addrs: &mut BTreeSet<GKRAddress>,
) {
    match &rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(_) => {}
        CompiledAddressSpaceRelationStrict::IsRam(offset)
        | CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            addrs.insert(GKRAddress::BaseLayerMemory(*offset));
        }
    }
    match &rel.address {
        CompiledAddressStrict::ConstantU16(_) | CompiledAddressStrict::Constant(_) => {}
        CompiledAddressStrict::U16Space(offset) => {
            addrs.insert(GKRAddress::BaseLayerMemory(*offset));
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            addrs.insert(GKRAddress::BaseLayerMemory(*low));
            addrs.insert(GKRAddress::BaseLayerMemory(*high));
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            high,
            ..
        } => {
            addrs.insert(GKRAddress::BaseLayerMemory(*low_base));
            if let Some((_, offset)) = low_dynamic_offset {
                addrs.insert(GKRAddress::BaseLayerMemory(*offset));
            }
            addrs.insert(GKRAddress::BaseLayerMemory(*high));
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            panic!("U32SpaceGeneric not supported");
        }
    }
    match &rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            addrs.insert(GKRAddress::BaseLayerMemory(ts[0]));
            addrs.insert(GKRAddress::BaseLayerMemory(ts[1]));
        }
    }
    match &rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(limbs) => {
            addrs.insert(GKRAddress::BaseLayerMemory(limbs[0]));
            addrs.insert(GKRAddress::BaseLayerMemory(limbs[1]));
        }
        RamWordRepresentation::U8Limbs(bytes) => {
            for &b in bytes {
                addrs.insert(GKRAddress::BaseLayerMemory(b));
            }
        }
    }
}

pub fn collect_sorted_unique_addrs(layer: &GKRLayerDescription) -> Vec<GKRAddress> {
    use std::collections::BTreeSet;
    let mut addrs = BTreeSet::new();

    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::LinearBaseFieldRelation { input, .. } => {
                for (_, addr) in input.linear_terms.iter() {
                    addrs.insert(*addr);
                }
            }
            R::MaxQuadratic { input, .. } => {
                for (addr, terms) in input.quadratic_terms.iter() {
                    addrs.insert(*addr);
                    for &(_, b) in terms.iter() {
                        addrs.insert(b);
                    }
                }
                for &(_, addr) in input.linear_terms.iter() {
                    addrs.insert(addr);
                }
            }
            R::EnforceConstraintsMaxQuadratic { input } => {
                for ((a, b), _) in &input.quadratic_terms {
                    addrs.insert(*a);
                    addrs.insert(*b);
                }
                for (addr, _) in &input.linear_terms {
                    addrs.insert(*addr);
                }
            }
            R::Copy { input, .. } => {
                addrs.insert(*input);
            }
            R::InitialGrandProductFromCaches { input, .. } | R::TrivialProduct { input, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
            }
            R::UnbalancedGrandProductWithCache { scalar, input, .. } => {
                addrs.insert(*scalar);
                addrs.insert(*input);
            }
            R::MaskIntoIdentityProduct { input, mask, .. } => {
                addrs.insert(*input);
                addrs.insert(*mask);
            }
            R::MaterializeSingleLookupInput { input, .. } => {
                for (_, addr) in &input.input.linear_terms {
                    addrs.insert(*addr);
                }
            }
            R::MaterializedVectorLookupInput { input, .. } => {
                for col in &input.columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::LookupWithCachedDensAndSetup { input, setup, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                addrs.insert(setup[0]);
                addrs.insert(setup[1]);
            }
            R::LookupPairFromBaseInputs { input, .. } => {
                for (_, addr) in &input[0].input.linear_terms {
                    addrs.insert(*addr);
                }
                for (_, addr) in &input[1].input.linear_terms {
                    addrs.insert(*addr);
                }
            }
            R::LookupPairFromMaterializedBaseInputs { input, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
            }
            R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. } => {
                addrs.insert(*input);
                addrs.insert(setup[0]);
                addrs.insert(setup[1]);
            }
            R::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
                addrs.insert(*input);
                addrs.insert(setup[0]);
                addrs.insert(setup[1]);
            }
            R::LookupUnbalancedPairWithMaterializedBaseInputs {
                input, remainder, ..
            } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                addrs.insert(*remainder);
            }
            R::LookupPairFromVectorInputs { input, .. } => {
                for col in &input[0].columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
                for col in &input[1].columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::LookupPairFromMaterializedVectorInputs { input, .. }
            | R::LookupPairFromCachedVectorInputs { input, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
            }
            R::LookupUnbalancedPairWithMaterializedVectorInputs {
                input, remainder, ..
            } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                addrs.insert(*remainder);
            }
            R::AggregateLookupRationalPair { input, .. } => {
                addrs.insert(input[0][0]);
                addrs.insert(input[0][1]);
                addrs.insert(input[1][0]);
                addrs.insert(input[1][1]);
            }
            // No-caches variants: memory expressions reference base-layer columns
            // but those are NOT GKRAddresses in the layer's sorted addrs — they're
            // accessed via the memory expression evaluation at runtime. Only the
            // output address is tracked.
            R::EnforceSingleMaxQuadraticConstraint { input } => {
                for (addr, terms) in input.quadratic_terms.iter() {
                    addrs.insert(*addr);
                    for &(_, b) in terms.iter() {
                        addrs.insert(b);
                    }
                }
                for &(_, addr) in input.linear_terms.iter() {
                    addrs.insert(addr);
                }
            }
            R::InitialGrandProductWithoutCaches { input, .. } => {
                collect_mem_expr_addrs(&input[0], &mut addrs);
                collect_mem_expr_addrs(&input[1], &mut addrs);
            }
            R::MaterializeGrandProductTermExpression { input, .. } => {
                collect_mem_expr_addrs(input, &mut addrs);
            }
            R::LookupWithDensAndSetupExpressions { input, setup, .. } => {
                addrs.insert(input.0);
                addrs.insert(setup.0);
                for addr in setup.1.iter() {
                    addrs.insert(*addr);
                }
                for col in &input.1.columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::LookupUnbalancedPairWithVectorInputs {
                input, remainder, ..
            } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                for col in &remainder.columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::LookupFromVectorInputWithSetup { input, setup, .. } => {
                addrs.insert(setup.0);
                for addr in setup.1.iter() {
                    addrs.insert(*addr);
                }
                for col in &input.columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                ..
            } => {
                addrs.insert(setup[0]);
                addrs.insert(setup[1]);
                use prover::cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;
                if let InitsOrTeardownsTimestampAndValue::Teardown {
                    lhs_timestamp,
                    lhs_value,
                    rhs_timestamp,
                    rhs_value,
                } = timestamp_and_value
                {
                    for ts in [lhs_timestamp, rhs_timestamp] {
                        addrs.insert(GKRAddress::BaseLayerMemory(ts[0]));
                        addrs.insert(GKRAddress::BaseLayerMemory(ts[1]));
                    }
                    for val in [lhs_value, rhs_value] {
                        addrs.insert(GKRAddress::BaseLayerMemory(val[0]));
                        addrs.insert(GKRAddress::BaseLayerMemory(val[1]));
                    }
                }
            }
        }
    }
    addrs.into_iter().collect()
}

pub fn collect_extra_addrs_from_cached_relations(
    layer: &GKRLayerDescription,
    input_sorted_addrs: &[GKRAddress],
) -> Vec<GKRAddress> {
    use std::collections::BTreeSet;
    let input_set: BTreeSet<GKRAddress> = input_sorted_addrs.iter().copied().collect();
    let mut extra = BTreeSet::new();
    for (_cached_addr, relation) in layer.cached_relations.iter() {
        for dep in relation.dependencies() {
            if !input_set.contains(&dep) {
                extra.insert(dep);
            }
        }
    }
    extra.into_iter().collect()
}

pub fn compute_max_pow(layer: &GKRLayerDescription) -> usize {
    use NoFieldGKRRelation as R;
    let mut max_pow = 0usize;
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        if let R::EnforceConstraintsMaxQuadratic { input } = &gate.enforced_relation {
            for (_, terms) in &input.quadratic_terms {
                for &(_, pow) in terms.iter() {
                    max_pow = max_pow.max(pow);
                }
            }
            for (_, terms) in &input.linear_terms {
                for &(_, pow) in terms.iter() {
                    max_pow = max_pow.max(pow);
                }
            }
            for &(_, pow) in input.constants.iter() {
                max_pow = max_pow.max(pow);
            }
        }
    }
    max_pow
}
