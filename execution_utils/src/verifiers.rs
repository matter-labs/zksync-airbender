// Code related to verifiers (creating oracles a.k.a input data etc).

use risc_v_simulator::cycle::{
    IMStandardIsaConfig, IWithoutByteAccessIsaConfigWithDelegation, MachineConfig,
};
use verifier_common::cs::utils::split_timestamp;

use crate::{ProofList, ProofMetadata};

/// Prefix byte for universal verifier, to distinguish between different payloads.
pub enum VerifierCircuitsIdentifiers {
    // This enum is used inside tools/verifier/main.rs
    BaseLayer = 0,
    RecursionLayer = 1,
    // Final layer is not used / supported anymore. We use Log23 layer instead.
    // FinalLayer = 2,
    RiscV = 3,
    /// Combine 2 proofs (from recursion layers) into one.
    // This is used in OhBender to combine previous block proof with current one.
    CombinedRecursionLayers = 4,
    RecursionLog23Layer = 5,
    /// Combine multiple proofs (from recursion layers) into one.
    /// Requires u32 to be passed as first word after this one,
    /// indicating how many proofs are combined.
    // Used to combine multiple FRIs into a single proof before SNARKing.
    CombinedMultipleRecursionLayers = 6,
}

/// Create oracle data for universal verifier.
// Universal verifier requires a prefix byte at the beginning to know what type of data this is.
pub fn generate_oracle_data_for_universal_verifier(
    metadata: &ProofMetadata,
    proofs: &ProofList,
) -> Vec<u32> {
    let mut oracle = generate_oracle_data_from_metadata_and_proof_list(metadata, proofs);

    if metadata.basic_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::BaseLayer as u32);
    } else if metadata.reduced_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::RecursionLayer as u32);
    } else if metadata.reduced_log_23_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::RecursionLog23Layer as u32);
    } else {
        panic!("Final proofs are no longer supported. Use log23 proofs instead.");
    };
    oracle
}

/// Create oracle data for a verifier from metadata and proof list.
pub fn generate_oracle_data_from_metadata_and_proof_list(
    metadata: &ProofMetadata,
    proofs: &ProofList,
) -> Vec<u32> {
    let mut oracle_data = vec![];
    // first - it reads all the register values.

    assert_eq!(32, metadata.register_values.len());
    for register in metadata.register_values.iter() {
        oracle_data.push(register.value);
        let (low, high) = split_timestamp(register.last_access_timestamp);
        oracle_data.push(low);
        oracle_data.push(high);
    }

    let delegations: Vec<u32> = if metadata.basic_proof_count > 0 {
        // Then it needs the number of circuits.
        oracle_data.push(metadata.basic_proof_count.try_into().unwrap());

        assert_eq!(metadata.reduced_proof_count, 0);

        // Then circuit proofs themselves.
        for i in 0..metadata.basic_proof_count {
            let proof = &proofs.basic_proofs[i];
            oracle_data
                .extend(verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, true));
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }

        full_machine_allowed_delegation_types()
    } else if metadata.reduced_proof_count > 0 {
        oracle_data.push(metadata.reduced_proof_count.try_into().unwrap());

        // Or reduced proofs
        for i in 0..metadata.reduced_proof_count {
            let proof = &proofs.reduced_proofs[i];
            oracle_data
                .extend(verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, true));
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }

        reduced_machine_allowed_delegation_types()
    } else if metadata.reduced_log_23_proof_count > 0 {
        oracle_data.push(metadata.reduced_log_23_proof_count.try_into().unwrap());

        // Or reduced log 23 proofs
        for i in 0..metadata.reduced_log_23_proof_count {
            let proof = &proofs.reduced_log_23_proofs[i];
            oracle_data
                .extend(verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, true));
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }

        reduced_machine_allowed_delegation_types()
    } else {
        panic!("No proofs");
    };

    for (k, _) in metadata.delegation_proof_count.iter() {
        assert!(delegations.contains(k), "No delegation circuit for {}", k);
    }

    for delegation_type in &delegations {
        let empty = vec![];
        let delegation_proofs = proofs
            .delegation_proofs
            .iter()
            .find(|(k, _)| k == delegation_type)
            .map(|(_, v)| v)
            .unwrap_or(&empty);
        oracle_data.push(delegation_proofs.len() as u32);

        for proof in delegation_proofs {
            // Notice, that apply_shuffle is assumed false for delegation proofs.
            oracle_data.extend(
                verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, false),
            );
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }
    }
    if let Some(prev_params) = metadata.prev_end_params_output {
        oracle_data.extend(prev_params);
    }
    oracle_data
}

fn reduced_machine_allowed_delegation_types() -> Vec<u32> {
    IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS.to_vec()
}

fn full_machine_allowed_delegation_types() -> Vec<u32> {
    IMStandardIsaConfig::ALLOWED_DELEGATION_CSRS.to_vec()
}
