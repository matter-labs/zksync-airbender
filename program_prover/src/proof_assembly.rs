//! `ProveResult` → `ProgramProof` assembly.

use std::collections::BTreeMap;

use execution_prover::{ProgramArtifacts, ProveResult};

use full_statement_verifier::host_utils::compute_end_params;
use full_statement_verifier::program_proof::ProgramProof;
use setups::{Setups, UnrolledCircuitSetupParams};

/// `ProveResult` carries proofs and final machine state; the `ProgramProof` the
/// verifiers consume also embeds the compiled circuits, and the `Setups` map
/// prefixes the ND streams. Both artifact sources come from
/// `ExecutionProver::program_artifacts`.
pub fn assemble_program_proof(
    artifacts: &ProgramArtifacts,
    result: ProveResult,
) -> (ProgramProof, Setups) {
    let mut setups: Setups = BTreeMap::new();
    for (family_idx, artifact) in artifacts.riscv_families.iter() {
        let trace_len = artifact.compiled_circuit.trace_len;
        setups.insert(
            *family_idx,
            UnrolledCircuitSetupParams::from_setup_tree_cap(
                *family_idx,
                trace_len as u32,
                artifact.setup_cap.clone(),
            ),
        );
    }

    let mut riscv_proofs: BTreeMap<u32, _> = result
        .circuit_families_proofs
        .into_iter()
        .map(|(family_idx, proofs)| (family_idx as u32, proofs))
        .collect();
    // The flattener emits a zero count for an absent family and an empty one
    // alike, so these entries change the representation, not the proof.
    for family_idx in artifacts.riscv_families.keys() {
        riscv_proofs.entry(*family_idx).or_default();
    }

    let compiled_riscv_circuits = artifacts
        .riscv_families
        .iter()
        .map(|(family_idx, artifact)| (*family_idx, (*artifact.compiled_circuit).clone()))
        .collect();
    let compiled_delegation_circuits = artifacts
        .delegations
        .iter()
        .map(|(delegation_type, artifact)| (*delegation_type, (**artifact).clone()))
        .collect();
    let inits_and_teardowns_circuit = artifacts
        .inits_and_teardowns
        .as_ref()
        .map(|artifact| (**artifact).clone());

    let end_params = compute_end_params(&setups, result.final_pc);

    let proof = ProgramProof {
        riscv_proofs,
        compiled_riscv_circuits,
        inits_and_teardown_proofs: result.inits_and_teardowns_proofs,
        inits_and_teardowns_circuit,
        delegation_proofs: result.delegation_proofs,
        compiled_delegation_circuits,
        register_final_values: result.register_final_values.to_vec(),
        final_pc: result.final_pc,
        final_timestamp: result.final_timestamp,
        end_params,
        recursion_chain_preimage: None,
        recursion_chain_hash: None,
        pow_challenge: result.pow_challenge,
        num_it_circuits: result.num_unified_it_circuits,
    };
    (proof, setups)
}
