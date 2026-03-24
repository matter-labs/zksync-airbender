use proc_macro2::TokenStream;
use quote::quote;

use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation, OutputType};

pub mod sumcheck;
pub mod transcript;

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
        }
    }
    addrs.into_iter().collect()
}

pub fn collect_output_addrs(layer: &GKRLayerDescription) -> Vec<GKRAddress> {
    use std::collections::BTreeSet;
    let mut addrs = BTreeSet::new();

    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::EnforceConstraintsMaxQuadratic { .. } => {}
            R::LinearBaseFieldRelation { output, .. }
            | R::MaxQuadratic { output, .. }
            | R::Copy { output, .. }
            | R::InitialGrandProductFromCaches { output, .. }
            | R::UnbalancedGrandProductWithCache { output, .. }
            | R::TrivialProduct { output, .. }
            | R::MaskIntoIdentityProduct { output, .. }
            | R::MaterializeSingleLookupInput { output, .. }
            | R::MaterializedVectorLookupInput { output, .. } => {
                addrs.insert(*output);
            }
            R::LookupPairFromBaseInputs { output, .. }
            | R::LookupPairFromMaterializedBaseInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
            | R::LookupFromMaterializedBaseInputWithSetup { output, .. }
            | R::LookupPairFromVectorInputs { output, .. }
            | R::LookupPairFromMaterializedVectorInputs { output, .. }
            | R::LookupPairFromCachedVectorInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
            | R::LookupWithCachedDensAndSetup { output, .. }
            | R::AggregateLookupRationalPair { output, .. } => {
                addrs.insert(output[0]);
                addrs.insert(output[1]);
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
