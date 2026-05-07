use std::collections::BTreeSet;

use prover::cs::definitions::gkr::RamWordRepresentation;
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRLayerDescription, NoFieldGKRRelation, NoFieldSpecialMemoryContributionRelation,
};

pub mod sumcheck;
pub mod transcript;

pub use verifier_common::{
    BATCHING_CHALLENGE_EXTRA, DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS,
};

pub fn addr_to_idx(addr: &GKRAddress, sorted: &[GKRAddress]) -> usize {
    sorted
        .binary_search(addr)
        .unwrap_or_else(|_| panic!("address {:?} not found in sorted list", addr))
}

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
            R::EnforceConstraintsMaxQuadratic { .. } => {
                // TODO: remove once all circuits use individual EnforceSingleMaxQuadraticConstraint gates
                unimplemented!(
                    "EnforceConstraintsMaxQuadratic is not supported by the verifier generator"
                );
            }
            R::CopyInBaseField { input, .. } | R::CopyInExtensionField { input, .. } => {
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
