use core::mem::offset_of;

use super::*;
#[cfg(test)]
use prover::prover_stages::Proof;
use verifier_common::prover::nd_source_std::*;
use verifier_common::{
    cs::one_row_compiler::CompiledCircuitArtifact, DefaultLeafInclusionVerifier,
};

#[allow(dead_code)]
fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

#[cfg(test)]
use test_utils::skip_if_ci;

#[cfg(test)]
#[ignore = "manual unified/delegation verifier fixture test"]
#[test]
fn test_unified_cycle_or_delegation() {
    skip_if_ci!();
    // create an oracle to feed into verifier and look at the transcript values

    // let proof: Proof = deserialize_from_file("../../zksync-airbender/prover/delegation_proof");
    // let proof: Proof = deserialize_from_file("../../zksync-airbender/prover/blake2s_delegator_proof");
    let proof: Proof =
        deserialize_from_file("../../zksync-airbender/prover/keccak_delegator_proof");

    // let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
    //     deserialize_from_file("../../zksync-airbender/prover/full_machine_layout.json");
    // let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
    // deserialize_from_file("../../zksync-airbender/prover/blake2s_delegator_layout");
    let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
        deserialize_from_file("../prover/keccak_delegation_circuit_layout.json");

    // now form flattened iterator
    use verifier_common::proof_flattener::*;

    let mut oracle_data = vec![];
    oracle_data.extend(flatten_proof_for_skeleton(
        &proof,
        compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .len(),
    ));
    for query in proof.queries.iter() {
        oracle_data.extend(flatten_query(query));
    }

    // Spawn a new thread as it's large stack in debug builds
    let result = std::thread::Builder::new()
        .name("verifier thread".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let it = oracle_data.into_iter();

            set_iterator(it);

            #[allow(invalid_value)]
            unsafe {
                verify_with_configuration::<ThreadLocalBasedSource, DefaultLeafInclusionVerifier>(
                    &mut MaybeUninit::uninit().assume_init(),
                    &mut ProofPublicInputs::uninit(),
                )
            };
        })
        .map(|t| t.join());

    match result {
        Ok(..) => {}
        Err(err) => {
            panic!("Verifier thread fails with {}", err);
        }
    }
}

#[test]
fn test_unrolled_circuit() {
    // create an oracle to feed into verifier and look at the transcript values

    // let name = "add_sub_lui_auipc_mop";
    // let name = "jump_branch_slt";
    let name = "shift_binop_csrrw";
    // let name = "mul_div_unsigned";
    // let name = "word_only_load_store";
    // let name = "subword_only_load_store";
    // let name = "inits_and_teardowns";

    let proof: prover::prover_stages::unrolled_prover::UnrolledModeProof =
        deserialize_from_file(&format!("../prover/{}_unrolled_proof.json", name));
    let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
        deserialize_from_file(&format!("../cs/{}_preprocessed_layout.json", name));

    dbg!(&proof.public_inputs);
    dbg!(&proof.aux_boundary_values);
    dbg!(&proof.delegation_argument_accumulator);

    // now form flattened iterator
    use verifier_common::proof_flattener::*;

    let mut oracle_data = vec![];
    oracle_data.extend(flatten_unrolled_circuits_proof_for_skeleton(
        &proof,
        &compiled_circuit,
    ));
    for query in proof.queries.iter() {
        oracle_data.extend(flatten_query(query));
    }

    // Spawn a new thread as it's large stack in debug builds
    let result = std::thread::Builder::new()
        .name("verifier thread".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let it = oracle_data.into_iter();

            set_iterator(it);

            #[allow(invalid_value)]
            unsafe {
                verify_with_configuration::<ThreadLocalBasedSource, DefaultLeafInclusionVerifier>(
                    &mut MaybeUninit::uninit().assume_init(),
                    &mut ProofPublicInputs::uninit(),
                )
            };
        })
        .map(|t| t.join());

    match result {
        Ok(..) => {}
        Err(err) => {
            panic!("Verifier thread fails with {}", err);
        }
    }
}

#[test]
fn test_query_values_offsets() {
    // Create a dummy QueryValuesInstance to test pointer arithmetic
    let dummy = MaybeUninit::<QueryValuesInstance>::uninit();
    let base_ptr = dummy.as_ptr().cast::<u32>();

    for (i, &offset_increment) in BASE_CIRCUIT_QUERY_VALUES_OFFSETS.iter().enumerate() {
        let current_ptr = unsafe { base_ptr.add(offset_increment) };

        match i {
            0 => {
                // After first offset, we should be at setup_leaf
                let expected_ptr = unsafe {
                    base_ptr.add(
                        offset_of!(QueryValuesInstance, setup_leaf) / core::mem::size_of::<u32>(),
                    )
                };
                assert_eq!(current_ptr, expected_ptr, "setup_leaf pointer mismatch");
            }
            idx if idx == LEAF_SIZE_SETUP => {
                // After setup_leaf elements, we should be at witness_leaf
                let expected_ptr = unsafe {
                    base_ptr.add(
                        offset_of!(QueryValuesInstance, witness_leaf) / core::mem::size_of::<u32>(),
                    )
                };
                assert_eq!(current_ptr, expected_ptr, "witness_leaf pointer mismatch");
            }
            idx if idx == LEAF_SIZE_SETUP + LEAF_SIZE_WITNESS_TREE => {
                // After witness_leaf elements, we should be at memory_leaf
                let expected_ptr = unsafe {
                    base_ptr.add(
                        offset_of!(QueryValuesInstance, memory_leaf) / core::mem::size_of::<u32>(),
                    )
                };
                assert_eq!(current_ptr, expected_ptr, "memory_leaf pointer mismatch");
            }
            idx if idx == LEAF_SIZE_SETUP + LEAF_SIZE_WITNESS_TREE + LEAF_SIZE_MEMORY_TREE => {
                // After memory_leaf elements, we should be at stage_2_leaf
                let expected_ptr = unsafe {
                    base_ptr.add(
                        offset_of!(QueryValuesInstance, stage_2_leaf) / core::mem::size_of::<u32>(),
                    )
                };
                assert_eq!(current_ptr, expected_ptr, "stage_2_leaf pointer mismatch");
            }
            idx if idx
                == LEAF_SIZE_SETUP
                    + LEAF_SIZE_WITNESS_TREE
                    + LEAF_SIZE_MEMORY_TREE
                    + LEAF_SIZE_STAGE_2 =>
            {
                // After stage_2_leaf elements, we should be at quotient_leaf
                let expected_ptr = unsafe {
                    base_ptr.add(
                        offset_of!(QueryValuesInstance, quotient_leaf)
                            / core::mem::size_of::<u32>(),
                    )
                };
                assert_eq!(current_ptr, expected_ptr, "quotient_leaf pointer mismatch");
            }
            idx if idx
                == LEAF_SIZE_SETUP
                    + LEAF_SIZE_WITNESS_TREE
                    + LEAF_SIZE_MEMORY_TREE
                    + LEAF_SIZE_STAGE_2
                    + LEAF_SIZE_QUOTIENT =>
            {
                // After quotient_leaf elements, we should be at fri_oracles_leafs
                let expected_ptr = unsafe {
                    base_ptr.add(
                        offset_of!(QueryValuesInstance, fri_oracles_leafs)
                            / core::mem::size_of::<u32>(),
                    )
                };
                assert_eq!(
                    current_ptr, expected_ptr,
                    "fri_oracles_leafs pointer mismatch"
                );
            }
            _ => {}
        }
    }
}
