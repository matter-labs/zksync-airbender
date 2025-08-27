use std::{collections::BTreeMap, path::Path};

use trace_and_split::FinalRegisterValue;
use verifier_common::{
    blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS, cs::utils::split_timestamp,
    prover::prover_stages::Proof,
};

// Structures to serialize / deserialize airbender proofs.
// ProgramProof = ProofMetadata + ProofList.
//
// For large programs, there can be 100s of proofs, so serialization via ProgramProof might be slow.
// That's why the alternative is to serialize ProofMetadata into one file, and put proofs into separate files.

/// This struct contains the proof data for a single program execution.
/// It has both metadata and proofs themselves.
#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProgramProof {
    pub base_layer_proofs: Vec<Proof>,
    pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
    pub register_final_values: Vec<FinalRegisterValue>,
    pub end_params: [u32; 8],
    pub recursion_chain_preimage: Option<[u32; 16]>,
    pub recursion_chain_hash: Option<[u32; 8]>,
}

/// This structs covers only the metadata of given set of proofs.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub struct ProofMetadata {
    pub basic_proof_count: usize,
    pub reduced_proof_count: usize,
    pub reduced_log_23_proof_count: usize,
    pub final_proof_count: usize,
    pub delegation_proof_count: Vec<(u32, usize)>,
    pub register_values: Vec<FinalRegisterValue>,
    // hash from current binary (from end pc and setup tree).
    pub end_params: [u32; 8],
    // blake hash of the prev_end_params_output (for debugging only).
    pub prev_end_params_output_hash: Option<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>,
    // parameters from the previous recursion level.
    pub prev_end_params_output: Option<[u32; 16]>,
}

/// This struct contains just the proofs.
pub struct ProofList {
    pub basic_proofs: Vec<Proof>,
    pub reduced_proofs: Vec<Proof>,
    pub reduced_log_23_proofs: Vec<Proof>,
    pub final_proofs: Vec<Proof>,
    pub delegation_proofs: Vec<(u32, Vec<Proof>)>,
}

impl ProgramProof {
    pub fn get_num_delegation_proofs_for_type(&self, delegation_type: u32) -> u32 {
        if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
            proofs.len() as u32
        } else {
            0
        }
    }

    pub fn flatten_for_delegation_circuits_set(
        &self,
        allowed_delegation_circuits: &[u32],
    ) -> Vec<u32> {
        let mut responses = Vec::with_capacity(32 + 32 * 2);

        assert_eq!(self.register_final_values.len(), 32);
        // registers
        for final_values in self.register_final_values.iter() {
            responses.push(final_values.value);
            let (low, high) = split_timestamp(final_values.last_access_timestamp);
            responses.push(low);
            responses.push(high);
        }

        // basic ones
        responses.push(self.base_layer_proofs.len() as u32);
        for proof in self.base_layer_proofs.iter() {
            let t = verifier_common::proof_flattener::flatten_full_proof(proof, true);
            responses.extend(t);
        }
        // then for every allowed delegation circuit
        for delegation_type in allowed_delegation_circuits.iter() {
            if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
                responses.push(proofs.len() as u32);
                for proof in proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_proof(proof, false);
                    responses.extend(t);
                }
            } else {
                responses.push(0);
            }
        }

        if let Some(preimage) = self.recursion_chain_preimage {
            responses.extend(preimage);
        }

        // check that we didn't have unexpected ones
        for t in self.delegation_proofs.keys() {
            assert!(
                allowed_delegation_circuits.contains(t),
                "allowed set of delegation circuits {:?} doesn't contain circuit type {}",
                allowed_delegation_circuits,
                t
            );
        }

        responses
    }

    pub fn from_proof_list_and_metadata(
        proof_list: &ProofList,
        proof_metadata: &ProofMetadata,
    ) -> ProgramProof {
        // program proof doesn't distinguish between final, reduced & basic proofs.
        let mut base_layer_proofs = proof_list.final_proofs.clone();
        base_layer_proofs.extend_from_slice(&proof_list.basic_proofs);
        base_layer_proofs.extend_from_slice(&proof_list.reduced_log_23_proofs);
        base_layer_proofs.extend_from_slice(&proof_list.reduced_proofs);

        ProgramProof {
            base_layer_proofs,
            delegation_proofs: proof_list.delegation_proofs.clone().into_iter().collect(),
            register_final_values: proof_metadata.register_values.clone(),
            end_params: proof_metadata.end_params,
            recursion_chain_preimage: proof_metadata.prev_end_params_output,
            recursion_chain_hash: proof_metadata.prev_end_params_output_hash,
        }
    }
    pub fn to_metadata_and_proof_list(self) -> (ProofMetadata, ProofList) {
        let reduced_proof_count = self.base_layer_proofs.len();
        let proof_list = ProofList {
            basic_proofs: vec![],
            // Here we're guessing - as ProgramProof doesn't distinguish between basic and reduced proofs.
            reduced_proofs: self.base_layer_proofs,
            reduced_log_23_proofs: vec![],
            final_proofs: vec![],
            delegation_proofs: self.delegation_proofs.clone().into_iter().collect(),
        };

        let proof_metadata = ProofMetadata {
            basic_proof_count: 0,
            reduced_proof_count,
            reduced_log_23_proof_count: 0,
            final_proof_count: 0,
            delegation_proof_count: vec![],
            register_values: self.register_final_values,
            end_params: self.end_params,
            prev_end_params_output_hash: self.recursion_chain_hash,
            prev_end_params_output: self.recursion_chain_preimage,
        };
        (proof_metadata, proof_list)
    }
}

impl ProofMetadata {
    pub fn total_proofs(&self) -> usize {
        self.basic_proof_count
            + self.reduced_proof_count
            + self.reduced_log_23_proof_count
            + self.final_proof_count
            + self
                .delegation_proof_count
                .iter()
                .map(|(_, v)| *v)
                .sum::<usize>()
    }
    pub fn create_prev_metadata(&self) -> ([u32; 8], Option<[u32; 16]>) {
        (self.end_params, self.prev_end_params_output)
    }
}

impl ProofList {
    pub fn write_to_directory(&self, output_dir: &Path) {
        println!("Writing proofs to {:?}", output_dir);

        for (i, proof) in self.basic_proofs.iter().enumerate() {
            serialize_to_file(
                proof,
                &Path::new(output_dir).join(&format!("proof_{}.json", i)),
            );
        }
        for (i, proof) in self.reduced_proofs.iter().enumerate() {
            serialize_to_file(
                proof,
                &Path::new(output_dir).join(&format!("reduced_proof_{}.json", i)),
            );
        }
        for (i, proof) in self.reduced_log_23_proofs.iter().enumerate() {
            serialize_to_file(
                proof,
                &Path::new(output_dir).join(&format!("reduced_log_23_proof_{}.json", i)),
            );
        }
        for (i, proof) in self.final_proofs.iter().enumerate() {
            serialize_to_file(
                proof,
                &Path::new(output_dir).join(&format!("final_proof_{}.json", i)),
            );
        }
        for (delegation_type, proofs) in self.delegation_proofs.iter() {
            for (i, proof) in proofs.iter().enumerate() {
                serialize_to_file(
                    proof,
                    &Path::new(output_dir)
                        .join(&format!("delegation_proof_{}_{}.json", delegation_type, i)),
                );
            }
        }
    }

    pub fn load_from_directory(input_dir: &String, metadata: &ProofMetadata) -> Self {
        let mut basic_proofs = vec![];
        for i in 0..metadata.basic_proof_count {
            let proof_path = Path::new(input_dir).join(format!("proof_{}.json", i));
            let proof: Proof = deserialize_from_file(proof_path.to_str().unwrap());
            basic_proofs.push(proof);
        }

        let mut reduced_proofs = vec![];
        for i in 0..metadata.reduced_proof_count {
            let proof_path = Path::new(input_dir).join(format!("reduced_proof_{}.json", i));
            let proof: Proof = deserialize_from_file(proof_path.to_str().unwrap());
            reduced_proofs.push(proof);
        }

        let mut reduced_log_23_proofs = vec![];
        for i in 0..metadata.reduced_log_23_proof_count {
            let proof_path = Path::new(input_dir).join(format!("reduced_log_23_proof_{}.json", i));
            let proof: Proof = deserialize_from_file(proof_path.to_str().unwrap());
            reduced_log_23_proofs.push(proof);
        }

        let mut final_proofs = vec![];
        for i in 0..metadata.final_proof_count {
            let proof_path = Path::new(input_dir).join(format!("final_proof_{}.json", i));
            let proof: Proof = deserialize_from_file(proof_path.to_str().unwrap());
            final_proofs.push(proof);
        }

        let mut delegation_proofs = vec![];
        for (delegation_type, count) in metadata.delegation_proof_count.iter() {
            let mut proofs = vec![];
            for i in 0..*count {
                let proof_path = Path::new(input_dir)
                    .join(format!("delegation_proof_{}_{}.json", delegation_type, i));
                let proof: Proof = deserialize_from_file(proof_path.to_str().unwrap());
                proofs.push(proof);
            }
            delegation_proofs.push((*delegation_type, proofs));
        }

        Self {
            basic_proofs,
            reduced_proofs,
            reduced_log_23_proofs,
            final_proofs,
            delegation_proofs,
        }
    }

    pub fn get_last_proof(&self) -> &Proof {
        self.final_proofs.last().unwrap_or_else(|| {
            self.basic_proofs.last().unwrap_or_else(|| {
                self.reduced_log_23_proofs.last().unwrap_or_else(|| {
                    self.reduced_proofs
                        .last()
                        .expect("Neither main proof nor reduced proof is present")
                })
            })
        })
    }
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(&format!("{filename}"));
    serde_json::from_reader(src).unwrap()
}
pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &Path) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}
