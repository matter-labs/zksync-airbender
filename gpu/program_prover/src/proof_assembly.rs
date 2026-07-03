//! `ProveResult` → `ProgramProof` assembly.
//!
//! `ProveResult` carries only the proofs and final machine state; the
//! `ProgramProof` the verifiers consume additionally embeds the compiled
//! circuit artifacts and is accompanied by the per-family setup-cap map
//! (`Setups`) that prefixes the ND streams. Both come from
//! `ExecutionProver::program_artifacts`. Setup caps are recomputed on the CPU
//! via `GKRSetup::commit` — byte-identical to the caps the GPU prover
//! committed to (validated by the circuit_prover proof-parity suite), without
//! needing a GPU context here.

use std::alloc::Global;
use std::collections::{BTreeMap, HashMap};

use execution_prover::{ProgramArtifacts, ProveResult};
use gpu_core::primitives::field::BF;
use worker::Worker;

use crate::interim_upstream::{compute_end_params, Setups};
use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, ColumnMajorMerkleTreeConstructor,
    DefaultTreeConstructor, MerkleTreeCap, ProgramProof, SecurityLevel, Twiddles,
    UnrolledCircuitSetupParams,
};

/// Assemble a `ProgramProof` + its `Setups` map from a GPU prove result.
///
/// Mirrors the tail of `prover_examples::prove_unrolled_execution_with_replayer`:
/// every RISC-V family present in the artifacts gets a setup-params entry and
/// a (possibly empty) proof list; all delegation circuit artifacts are
/// embedded regardless of whether that delegation fired.
///
/// Handles both execution kinds: for `ExecutionKind::Unified` results,
/// `ProveResult::num_unified_it_circuits` carries the count of trailing
/// unified circuits with real inits-and-teardowns data, which becomes
/// `ProgramProof::num_it_circuits` (required by the unified flattener).
pub fn assemble_program_proof(
    artifacts: &ProgramArtifacts,
    result: ProveResult,
    security_level: SecurityLevel,
    worker: &Worker,
) -> (ProgramProof, Setups) {
    let mut twiddles: HashMap<usize, Twiddles<BF, Global>> = HashMap::new();
    let mut setups: Setups = BTreeMap::new();
    for (family_idx, artifact) in artifacts.riscv_families.iter() {
        let trace_len = artifact.compiled_circuit.trace_len;
        let prover_config = config_for_security_level_under_pessimistic_conjecture(
            trace_len.trailing_zeros() as usize,
            security_level,
        );
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let setup_commitment = artifact.cpu_setup.commit::<DefaultTreeConstructor>(
            &*twiddles_for_size,
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            worker,
        );
        setups.insert(
            *family_idx,
            UnrolledCircuitSetupParams {
                family_idx: *family_idx,
                capacity: trace_len as u32,
                setup_caps: MerkleTreeCap {
                    cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                        &setup_commitment.tree,
                    )
                    .cap
                    .try_into()
                    .unwrap(),
                },
            },
        );
    }

    let mut riscv_proofs: BTreeMap<u32, _> = result
        .circuit_families_proofs
        .into_iter()
        .map(|(family_idx, proofs)| (family_idx as u32, proofs))
        .collect();
    // The CPU reference inserts empty proof lists "for consistency" for
    // families that had no witness; mirror that so the flattener emits a
    // zero count for them.
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
        .map(|(delegation_type, artifact)| (*delegation_type, (*artifact.compiled_circuit).clone()))
        .collect();
    let inits_and_teardowns_circuit = artifacts
        .inits_and_teardowns
        .as_ref()
        .map(|artifact| (*artifact.compiled_circuit).clone());

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
