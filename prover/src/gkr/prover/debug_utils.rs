use std::collections::BTreeMap;

use crate::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use cs::definitions::gkr::{NoFieldLinearRelation, RamWordRepresentation};
use cs::definitions::{
    GKRAddress, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::CompiledMemoryTimestamp;
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, GKRCircuitArtifact,
    GKRLayerDescription, NoFieldGKRCacheRelation, NoFieldSpecialMemoryContributionRelation,
    OutputType,
};
use fft::batch_inverse_inplace_parallel;
use field::{Field, FieldExtension, PrimeField};

use super::GKRExternalChallenges;
use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::sumcheck::eq_poly::*;
use crate::worker::Worker;

pub(crate) fn check_logup_identity<F: PrimeField, E: FieldExtension<F> + Field>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    gkr_storage: &GKRStorage<F, E>,
    worker: &Worker,
) -> bool {
    for output_type in [
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        if let Some(addrs) = compiled_circuit.global_output_map.get(&output_type) {
            let num_addr = addrs[0];
            let den_addr = addrs[1];
            let layer_idx = match num_addr {
                GKRAddress::InnerLayer { layer, .. } => layer,
                _ => panic!("expected InnerLayer address for lookup output"),
            };
            let layer_source = &gkr_storage.layers[layer_idx];
            let num_poly = &layer_source.extension_field_inputs[&num_addr].values;
            let mut den_poly = layer_source.extension_field_inputs[&den_addr].values[..].to_vec();
            let mut buffer = vec![E::ZERO; den_poly.len()];
            batch_inverse_inplace_parallel(&mut den_poly, &mut buffer, worker);
            let mut sum = E::ZERO;
            for (n, d_inv) in num_poly.iter().zip(den_poly.iter()) {
                let mut term = *n;
                term.mul_assign(d_inv);
                sum.add_assign(&term);
            }
            if !sum.is_zero() {
                println!("LogUp relation diverged for lookup type {:?}", output_type);
                return false;
            }
        }
    }
    true
}

pub(crate) fn check_logup_identity_after_dimension_reduction<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    dim_reduction_description: &BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    gkr_storage: &GKRStorage<F, E>,
    worker: &Worker,
) -> bool {
    let (layer, out_layer) = dim_reduction_description.iter().rev().next().unwrap();
    println!("Self-checking lookup consistency after dimension reduction at layer {} with structure {:?}", layer, out_layer);
    for output_type in [
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        if let Some(addrs) = out_layer.get(&output_type) {
            let num_addr = addrs.output[0];
            let den_addr = addrs.output[1];
            let layer_idx = match num_addr {
                GKRAddress::InnerLayer { layer, .. } => layer,
                _ => panic!("expected InnerLayer address for lookup output"),
            };
            let layer_source = &gkr_storage.layers[layer_idx];
            let num_poly = &layer_source.extension_field_inputs[&num_addr].values;
            let mut den_poly = layer_source.extension_field_inputs[&den_addr].values[..].to_vec();
            let mut buffer = vec![E::ZERO; den_poly.len()];
            batch_inverse_inplace_parallel(&mut den_poly, &mut buffer, worker);
            let mut sum = E::ZERO;
            for (n, d_inv) in num_poly.iter().zip(den_poly.iter()) {
                let mut term = *n;
                term.mul_assign(d_inv);
                sum.add_assign(&term);
            }
            if !sum.is_zero() {
                return false;
            }
        }
    }
    true
}

/// Generate mock output claims by evaluating the global output polynomials at a fixed point.
/// Returns (readset, writeset, rangechecknum, rangecheckden, timechecknum, timecheckden, lookupnum, lookupden, evaluation_point).
pub(crate) fn mock_output_claims<F: PrimeField, E: FieldExtension<F> + Field>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    gkr_storage: &GKRStorage<F, E>,
    trace_len: usize,
    worker: &Worker,
) -> ((E, E, E, E, E, E, E, E), Vec<E>) {
    let challenges =
        vec![E::from_base(F::from_u32_unchecked(42)); trace_len.trailing_zeros() as usize];
    let eq_precomputed = make_eq_poly_in_full::<E>(&challenges, worker);
    let eq = eq_precomputed.last().unwrap();

    let mut evals = vec![];
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        let addresses = &compiled_circuit.global_output_map[&key];
        for address in addresses.iter() {
            let poly = gkr_storage.get_ext_poly(*address);
            let evaluation = evaluate_with_precomputed_eq_ext::<E>(poly, &eq[..]);
            evals.push(evaluation);
        }
    }

    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        evals.try_into().unwrap();

    (
        (
            claim_readset,
            claim_writeset,
            claim_rangechecknum,
            claim_rangecheckden,
            claim_timechecknum,
            claim_timecheckden,
            claim_lookupnum,
            claim_lookupden,
        ),
        challenges,
    )
}

pub(crate) fn compute_initial_sumcheck_claims<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &GKRStorage<F, E>,
    eval_point: &[E],
    output_layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    worker: &Worker,
) -> (E, E, E, E, E, E, E, E) {
    let eq_precomputed = make_eq_poly_in_full::<E>(&eval_point, worker);
    let eq = eq_precomputed.last().unwrap();

    let mut evals = vec![];
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        if let Some(addresses) = &output_layer.get(&key) {
            for address in addresses.output.iter() {
                let poly = gkr_storage.get_ext_poly(*address);
                let evaluation = evaluate_with_precomputed_eq_ext::<E>(poly, &eq[..]);
                evals.push(evaluation);
            }
        } else {
            evals.push(E::ZERO);
            evals.push(E::ZERO);
        }
    }

    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        evals.try_into().unwrap();

    (
        claim_readset,
        claim_writeset,
        claim_rangechecknum,
        claim_rangecheckden,
        claim_timechecknum,
        claim_timecheckden,
        claim_lookupnum,
        claim_lookupden,
    )
}

pub(crate) fn verify_cache_relations<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_desc: &GKRLayerDescription,
    claims: &BTreeMap<GKRAddress, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    lookup_multiplicative_constant: E,
) -> bool {
    for (cached_addr, relation) in layer_desc.cached_relations.iter() {
        match relation {
            NoFieldGKRCacheRelation::MemoryTuple(rel) => {
                let cached_claim = match claims.get(cached_addr) {
                    Some(v) => *v,
                    None => {
                        panic!(
                            "Missing claim for cached address {:?} for relation {:?}",
                            cached_addr, rel
                        );
                    }
                };

                let expected = evaluate_memory_tuple_from_claims(rel, claims, external_challenges);

                if expected != cached_claim {
                    println!(
                        "Memory tuple {:?} claim failure: expected {}, got {}",
                        rel, expected, cached_claim
                    );
                    return false;
                }
            }
            NoFieldGKRCacheRelation::SingleColumnLookup { relation, .. } => {
                let cached_claim = match claims.get(cached_addr) {
                    Some(v) => *v,
                    None => {
                        panic!(
                            "Missing claim for cached address {:?} for relation {:?}",
                            cached_addr, relation
                        );
                    }
                };

                let expected = evaluate_linear_relation(&relation.input, claims);

                if expected != cached_claim {
                    println!(
                        "Single column lookup {:?} claim failure: expected {}, got {}",
                        relation, expected, cached_claim
                    );
                    return false;
                }
            }
            NoFieldGKRCacheRelation::VectorizedLookup(no_field_vector_lookup_relation) => {
                let cached_claim = match claims.get(cached_addr) {
                    Some(v) => *v,
                    None => {
                        panic!(
                            "Missing claim for cached address {:?} for relation {:?}",
                            cached_addr, no_field_vector_lookup_relation
                        );
                    }
                };

                let mut expected =
                    evaluate_linear_relation(&no_field_vector_lookup_relation.columns[0], claims);
                let mut challenge = lookup_multiplicative_constant;
                for rel in no_field_vector_lookup_relation.columns[1..].iter() {
                    let mut t = evaluate_linear_relation(rel, claims);
                    t.mul_assign(&challenge);
                    expected.add_assign(&t);

                    challenge.mul_assign(&lookup_multiplicative_constant);
                }

                if expected != cached_claim {
                    println!(
                        "Vector lookup {:?} claim failure: expected {}, got {}",
                        relation, expected, cached_claim
                    );
                    return false;
                }
            }
            NoFieldGKRCacheRelation::VectorizedLookupSetup(items) => {
                let cached_claim = match claims.get(cached_addr) {
                    Some(v) => *v,
                    None => {
                        panic!(
                            "Missing claim for cached address {:?} for vectorized lookup setup",
                            cached_addr
                        );
                    }
                };

                let mut expected = claims[&items[0]];
                let mut challenge = lookup_multiplicative_constant;
                for address in items[1..].iter() {
                    let mut t = claims[address];
                    t.mul_assign(&challenge);
                    expected.add_assign(&t);

                    challenge.mul_assign(&lookup_multiplicative_constant);
                }

                if expected != cached_claim {
                    println!(
                        "Vector lookup setup claim failure: expected {}, got {}",
                        expected, cached_claim
                    );
                    return false;
                }
            }
        }
    }
    true
}

fn evaluate_memory_tuple_from_claims<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldSpecialMemoryContributionRelation,
    claims: &BTreeMap<GKRAddress, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
) -> E {
    let challenges = &external_challenges.permutation_argument_linearization_challenges;
    let mut result = external_challenges.permutation_argument_additive_part;

    // Address space contribution
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            result.add_assign_base(&F::from_u32_unchecked(c));
        }
        CompiledAddressSpaceRelationStrict::Is(offset) => {
            let claim = claims[&GKRAddress::BaseLayerMemory(offset)];
            result.add_assign(&claim);
        }
        CompiledAddressSpaceRelationStrict::Not(offset) => {
            let claim = claims[&GKRAddress::BaseLayerMemory(offset)];
            let mut t = E::from_base(F::ONE);
            t.sub_assign(&claim);
            result.add_assign(&t);
        }
    }

    // Address contribution
    match &rel.address {
        &CompiledAddressStrict::ConstantU16(c) => {
            let mut t = challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
            result.add_assign(&t);
        }
        &CompiledAddressStrict::Constant(c) => {
            let mut t = challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c));
            result.add_assign(&t);
        }
        &CompiledAddressStrict::U16Space(offset) => {
            let mut t = challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign(&claims[&GKRAddress::BaseLayerMemory(offset)]);
            result.add_assign(&t);
        }
        &CompiledAddressStrict::U32Space([low, high]) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, low),
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, high),
            ] {
                let mut t = challenges[idx];
                t.mul_assign(&claims[&GKRAddress::BaseLayerMemory(offset)]);
                result.add_assign(&t);
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            todo!();
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                let mut low = claims[&GKRAddress::BaseLayerMemory(*low_base)];
                low.add_assign_base(&F::from_u32_unchecked(*low_offset));
                if let Some((c, offset)) = *low_dynamic_offset {
                    let mut var_offset = claims[&GKRAddress::BaseLayerMemory(offset)];
                    var_offset.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
                    low.add_assign(&var_offset);
                }
                t.mul_assign(&low);
                result.add_assign(&t);
            }
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                let high = claims[&GKRAddress::BaseLayerMemory(*high)];
                t.mul_assign(&high);
                result.add_assign(&t);
            }
        }
    }
    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            {
                let mut t = challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                let mut ts_low = claims[&GKRAddress::BaseLayerMemory(ts[0])];
                ts_low.add_assign_base(&F::from_u32_unchecked(rel.timestamp_offset));
                t.mul_assign(&ts_low);
                result.add_assign(&t);
            }
            {
                let mut t = challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                t.mul_assign(&claims[&GKRAddress::BaseLayerMemory(ts[1])]);
                result.add_assign(&t);
            }
        }
    }

    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(read_value) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, read_value[0]),
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, read_value[1]),
            ] {
                let mut t = challenges[idx];
                t.mul_assign(&claims[&GKRAddress::BaseLayerMemory(offset)]);
                result.add_assign(&t);
            }
        }
        RamWordRepresentation::U8Limbs(read_value) => {
            for (idx, offset_low, offset_high) in [
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    read_value[0],
                    read_value[1],
                ),
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    read_value[2],
                    read_value[3],
                ),
            ] {
                let low = claims[&GKRAddress::BaseLayerMemory(offset_low)];
                let mut combined = claims[&GKRAddress::BaseLayerMemory(offset_high)];
                combined.mul_assign_by_base(&F::from_u32_unchecked(1 << 8));
                combined.add_assign(&low);
                let mut t = challenges[idx];
                t.mul_assign(&combined);
                result.add_assign(&t);
            }
        }
    }

    result
}

fn evaluate_linear_relation<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldLinearRelation,
    claims: &BTreeMap<GKRAddress, E>,
) -> E {
    let mut result = E::from_base(F::from_u32_unchecked(rel.constant));
    for (c, address) in rel.linear_terms.iter() {
        let mut t = claims[address];
        t.mul_assign_by_base(&F::from_u32_unchecked(*c));
        result.add_assign(&t);
    }

    result
}
