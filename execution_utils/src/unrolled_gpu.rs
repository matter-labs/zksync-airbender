use crate::get_padded_binary;
use crate::unrolled::{
    flatten_proof_into_responses_for_unrolled_recursion, UnrolledProgramProof, UnrolledProgramSetup,
};
use gpu_prover::{
    execution::prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration},
    machine_type::MachineType,
};
use setups::{pad_binary, read_and_pad_binary, CompiledCircuitsSet};

use ::prover::risc_v_simulator::{
    abstractions::non_determinism::QuasiUARTSource,
    cycle::{IMStandardIsaConfigWithUnsignedMulDiv, IWithoutByteAccessIsaConfigWithDelegation},
};
use std::{io::Read, path::Path};

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(&format!("{filename}"));
    serde_json::from_reader(src).unwrap()
}
pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &Path) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn load_binary_from_path(path: &String) -> Vec<u32> {
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    get_padded_binary(&buffer)
}

pub struct UnrolledProver {
    pub base_level: UnrolledProverLevel,
    pub recursion_over_base: UnrolledProverLevel,
    pub prover: ExecutionProver,
}

pub struct UnrolledProverLevel {
    pub binary: Vec<u8>,
    pub text: Vec<u8>,
    pub binary_u32: Vec<u32>,
    pub text_u32: Vec<u32>,
    pub setup: UnrolledProgramSetup,
    pub compiled_layouts: CompiledCircuitsSet,
}

pub const RECURSION_UNROLLED_BIN: &[u8] =
    include_bytes!("../../tools/verifier/recursion_in_unrolled_layer.bin");
pub const RECURSION_UNROLLED_TXT: &[u8] =
    include_bytes!("../../tools/verifier/recursion_in_unrolled_layer.text");

impl UnrolledProver {
    pub fn new(path_without_bin: &String, replay_worker_threads_count: usize) -> Self {
        let base_level = {
            let bin_path = format!("{}.bin", path_without_bin);
            let text_path = format!("{}.text", path_without_bin);

            let (binary, binary_u32) = read_and_pad_binary(Path::new(&bin_path));
            let (text, text_u32) = read_and_pad_binary(Path::new(&text_path));

            println!("Computing base setup");

            let base_layer_setup = crate::unrolled::compute_setup_for_machine_configuration::<
                IMStandardIsaConfigWithUnsignedMulDiv,
            >(&binary, &text);
            let base_layer_compiled_layouts =
                crate::setups::get_unrolled_circuits_artifacts_for_machine_type::<
                    IMStandardIsaConfigWithUnsignedMulDiv,
                >(&binary_u32);
            UnrolledProverLevel {
                binary,
                text,
                binary_u32,
                text_u32,
                setup: base_layer_setup,
                compiled_layouts: base_layer_compiled_layouts,
            }
        };

        let recursion_over_base = {
            let (binary, binary_u32) = pad_binary(RECURSION_UNROLLED_BIN.to_vec());
            let (text, text_u32) = pad_binary(RECURSION_UNROLLED_TXT.to_vec());

            println!("Computing recursion over base setup");

            let setup = crate::unrolled::compute_setup_for_machine_configuration::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&binary, &text);
            let compiled_layouts = crate::setups::get_unrolled_circuits_artifacts_for_machine_type::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&binary_u32);

            UnrolledProverLevel {
                binary,
                text,
                binary_u32,
                text_u32,
                setup,
                compiled_layouts,
            }
        };

        let mut configuration = ExecutionProverConfiguration::default();
        configuration.replay_worker_threads_count = replay_worker_threads_count;
        let mut prover = ExecutionProver::with_configuration(configuration);
        prover.add_binary(
            0,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            base_level.binary_u32.clone(),
            base_level.text_u32.clone(),
            None,
        );
        prover.add_binary(
            1,
            ExecutionKind::Unrolled,
            MachineType::Reduced,
            recursion_over_base.binary_u32.clone(),
            recursion_over_base.text_u32.clone(),
            None,
        );

        Self {
            base_level,
            prover,
            recursion_over_base,
        }
    }

    pub fn prove(
        &self,
        source: impl riscv_transpiler::vm::NonDeterminismCSRSource + Send + Sync + 'static,
    ) -> (UnrolledProgramProof, u64) {
        println!("Computing proof");

        let start_time = std::time::Instant::now();
        let result = self.prover.commit_memory_and_prove(0, 0, source);
        let base_proof = UnrolledProgramProof {
            final_pc: result.final_pc,
            final_timestamp: result.final_timestamp,
            circuit_families_proofs: result.circuit_families_proofs,
            inits_and_teardowns_proofs: result.inits_and_teardowns_proofs,
            delegation_proofs: result.delegation_proofs,
            register_final_values: result.register_final_values,
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
        };
        println!(
            "Basic proof done in {:.3}s {}",
            start_time.elapsed().as_secs_f64(),
            base_proof.debug_info()
        );

        let cycles = result.final_timestamp / 4;

        // Now recursion - first step.

        let proof = {
            let start_time = std::time::Instant::now();

            /*let mut witness = self.base_level.setup.flatten_for_recursion();
            witness.extend(base_proof.flatten_into_responses(
                &[1984, 1991, 1994, 1995],
                &self.base_level.compiled_layouts,
            ));*/
            let witness = flatten_proof_into_responses_for_unrolled_recursion(
                &base_proof,
                &self.base_level.setup,
                &self.base_level.compiled_layouts,
                true,
            );
            let source = QuasiUARTSource::new_with_reads(witness);
            let result = self.prover.commit_memory_and_prove(0, 1, source);
            let mut proof = UnrolledProgramProof {
                final_pc: result.final_pc,
                final_timestamp: result.final_timestamp,
                circuit_families_proofs: result.circuit_families_proofs,
                inits_and_teardowns_proofs: result.inits_and_teardowns_proofs,
                delegation_proofs: result.delegation_proofs,
                register_final_values: result.register_final_values,
                recursion_chain_preimage: None,
                recursion_chain_hash: None,
            };
            // make a hash chain
            let (hash_chain, preimage) =
                UnrolledProgramSetup::begin_recursion_chain(&self.base_level.setup.end_params);
            proof.recursion_chain_hash = Some(hash_chain);
            proof.recursion_chain_preimage = Some(preimage);
            println!(
                "Recursion over base proof done in {:.3}s {}",
                start_time.elapsed().as_secs_f64(),
                proof.debug_info()
            );
            proof
        };
        // Now real recursion.

        let previous_setup = self.recursion_over_base.setup.clone();
        let previous_compiled_layouts = self.recursion_over_base.compiled_layouts.clone();
        let mut proof = proof;

        for round in 0..6 {
            let start_time = std::time::Instant::now();
            //let mut witness = previous_setup.flatten_for_recursion();
            //witness.extend(proof.flatten_into_responses(&[1991], &previous_compiled_layouts));

            let witness = flatten_proof_into_responses_for_unrolled_recursion(
                &proof,
                &previous_setup,
                &previous_compiled_layouts,
                false,
            );

            let source = QuasiUARTSource::new_with_reads(witness);
            let result = self.prover.commit_memory_and_prove(0, 1, source);

            let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
                &previous_setup.end_params,
                &proof.recursion_chain_hash.expect("has recursion chain"),
                &proof
                    .recursion_chain_preimage
                    .expect("has recursion preimage"),
            );
            proof = UnrolledProgramProof {
                final_pc: result.final_pc,
                final_timestamp: result.final_timestamp,
                circuit_families_proofs: result.circuit_families_proofs,
                inits_and_teardowns_proofs: result.inits_and_teardowns_proofs,
                delegation_proofs: result.delegation_proofs,
                register_final_values: result.register_final_values,
                recursion_chain_preimage: Some(preimage),
                recursion_chain_hash: Some(hash_chain),
            };
            // make a hash chain
            println!(
                "Recursion round {} over recursion proof done in {:.3}s {}",
                round,
                start_time.elapsed().as_secs_f64(),
                proof.debug_info()
            );

            let (circuit_proofs, _) = proof.get_proof_counts();
            // For now, this is hardcoded.
            if circuit_proofs <= 4 {
                break;
            }
        }
        (proof, cycles)
    }
}
