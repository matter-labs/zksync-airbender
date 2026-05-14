extern crate alloc;

use alloc::collections::BTreeMap;
use common_constants::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
};
use verifier_common::cs::definitions::TimestampScalar;
use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
use verifier_common::cs::utils::split_timestamp;
use verifier_common::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use verifier_common::field::PrimeField;
use verifier_common::prover::definitions::FinalRegisterValue;
use verifier_common::prover::{gkr::prover::GKRProof, merkle_trees::DefaultTreeConstructor};

/// This struct contains the proof data for a single program execution.
/// It has both metadata and proofs themselves.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ProgramProof {
    pub riscv_proofs:
        BTreeMap<u32, Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>>,
    pub compiled_riscv_circuits: BTreeMap<u32, GKRCircuitArtifact<BabyBearField>>,
    pub inits_and_teardown_proofs:
        Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    pub inits_and_teardowns_circuit: Option<GKRCircuitArtifact<BabyBearField>>,
    pub delegation_proofs:
        BTreeMap<u32, Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>>,
    pub compiled_delegation_circuits: BTreeMap<u32, GKRCircuitArtifact<BabyBearField>>,
    pub register_final_values: Vec<FinalRegisterValue>,
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub end_params: [u32; 8],
    pub recursion_chain_preimage: Option<[u32; 16]>,
    pub recursion_chain_hash: Option<[u32; 8]>,
    pub pow_challenge: u64,
}

impl ProgramProof {
    pub fn get_num_delegation_proofs_for_type(&self, delegation_type: u32) -> u32 {
        if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
            proofs.len() as u32
        } else {
            0
        }
    }

    pub fn flatten_for_verification(&self) -> Vec<u32> {
        let mut responses = Vec::with_capacity(32 + 32 * 2);

        assert_eq!(self.register_final_values.len(), 32);
        // registers
        for final_values in self.register_final_values.iter() {
            responses.push(final_values.value);
            let (low, high) = split_timestamp(final_values.last_access_timestamp);
            responses.push(low);
            responses.push(high);
        }

        {
            responses.push(self.final_pc);
            let (low, high) = split_timestamp(self.final_timestamp);
            responses.push(low);
            responses.push(high);
        }

        // then we need external challenges
        let mut ext_challenges = None;
        'outer: for (_, proofs) in self.riscv_proofs.iter() {
            for proof in proofs.iter() {
                ext_challenges = Some(proof.external_challenges);
                break 'outer;
            }
        }
        let ext_challenges = ext_challenges.expect("external challenges from one of the proofs");
        ext_challenges.flatten_into_buffer(&mut responses);

        dbg!(ext_challenges);
        dbg!(
            ext_challenges.permutation_argument_linearization_challenges[0]
                .c0
                .c0
                .as_u32_raw_repr_reduced()
        );

        // risc-v proofs
        for (k, proofs) in self.riscv_proofs.iter() {
            responses.push(proofs.len() as u32);
            let compiled_circuit = &self.compiled_riscv_circuits[k];
            for proof in proofs.iter() {
                let proof = ::verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
                    proof,
                    compiled_circuit,
                );
                dbg!((k, proof.first().unwrap(), proof.last().unwrap()));
                responses.extend(proof);
            }
        }

        if self.inits_and_teardown_proofs.len() > 0 {
            responses.push(1u32);
            let compiled_circuit = &self
                .inits_and_teardowns_circuit
                .as_ref()
                .expect("compiled inits and teardowns");
            for proof in self.inits_and_teardown_proofs.iter() {
                responses.extend(::verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
                    proof,
                    compiled_circuit,
                ));
            }
        } else {
            responses.push(0u32);
        }

        const DELEGATION_TYPES: &[u32] = &[
            BLAKE2S_DELEGATION_CSR_REGISTER,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
            KECCAK_SPECIAL5_CSR_REGISTER,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
        ];

        // delegation proofs
        for k in DELEGATION_TYPES.iter() {
            if let Some(proofs) = self.delegation_proofs.get(&k) {
                responses.push(proofs.len() as u32);
                let compiled_circuit = &self.compiled_delegation_circuits[&k];
                for proof in proofs.iter() {
                    responses.extend(::verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
                        proof,
                        compiled_circuit,
                    ));
                }
            } else {
                responses.push(0u32);
            }
        }

        responses.push(self.pow_challenge as u32);
        responses.push((self.pow_challenge >> 32) as u32);

        if let Some(preimage) = self.recursion_chain_preimage {
            responses.extend(preimage);
        }

        responses
    }
}
