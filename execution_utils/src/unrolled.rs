use riscv_transpiler::common_constants;
use sha3::Digest;
use std::collections::BTreeMap;
use trace_and_split::prover;
use trace_and_split::setups;

use super::*;
use prover::common_constants::TimestampScalar;
use prover::cs::utils::split_timestamp;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use setups::CompiledCircuitsSet;
use trace_and_split::FinalRegisterValue;

pub use setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type;

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProgramSetup {
    pub expected_final_pc: u32,
    pub binary_hash: [u8; 32],
    pub circuit_families_setups: BTreeMap<u8, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]>,
    pub inits_and_teardowns_setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub end_params: [u32; 8],
}

impl UnrolledProgramSetup {
    pub fn new_from_setups_and_binary(
        binary: &[u8],
        circuit_families_setups: &[(u8, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS])],
        inits_and_teardowns_setup: &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    ) -> Self {
        assert!(circuit_families_setups.is_sorted_by(|a, b| a.0 < b.0));
        let final_pc = find_binary_exit_point(binary);

        let setups: Vec<_> = circuit_families_setups.iter().map(|el| &el.1).collect();

        let end_params = if setups.len() > 1 {
            compute_end_parameters_for_unrolled_circuits(
                final_pc,
                &setups,
                inits_and_teardowns_setup,
            )
        } else {
            assert!(inits_and_teardowns_setup.iter().all(|el| el.cap.iter().all(|el| *el == [0u32; 8])), "single setup is for unified circuits, where inits and teardowns setup is conventional all zeroes here");
            compute_end_parameters_for_unified_circuit(final_pc, &setups[0])
        };

        // binary hash can be anything - it's just for bookkeeping
        let binary_hash = sha3::Keccak256::digest(binary).into();

        Self {
            expected_final_pc: final_pc,
            binary_hash,
            circuit_families_setups: BTreeMap::from_iter(
                circuit_families_setups.iter().map(|el| (el.0, el.1)),
            ),
            inits_and_teardowns_setup: *inits_and_teardowns_setup,
            end_params,
        }
    }

    pub fn flatten_for_recursion(&self) -> Vec<u32> {
        // we just need to dump merkle caps, without any circuit IDs
        let mut result = vec![];
        for (_, caps) in self.circuit_families_setups.iter() {
            result.extend_from_slice(MerkleTreeCap::flatten(caps));
        }
        result.extend_from_slice(MerkleTreeCap::flatten(&self.inits_and_teardowns_setup));

        result
    }

    pub fn flatten_unified_for_recursion(&self) -> Vec<u32> {
        assert_eq!(self.circuit_families_setups.len(), 1);
        // we just need to dump merkle caps, without any circuit IDs
        let mut result = vec![];
        for (_, caps) in self.circuit_families_setups.iter() {
            result.extend_from_slice(MerkleTreeCap::flatten(caps));
        }

        result
    }

    pub fn begin_recursion_chain(base_layer_end_params: &[u32; 8]) -> ([u32; 8], [u32; 16]) {
        let mut preimage = [0u32; 16];
        preimage[8..].copy_from_slice(base_layer_end_params);
        let mut result_hasher = Blake2sBufferingTranscript::new();
        result_hasher.absorb(&preimage);
        let hash_chain = result_hasher.finalize().0;
        (hash_chain, preimage)
    }

    pub fn continue_recursion_chain(
        end_params: &[u32; 8],
        previous_step_hash_chain: &[u32; 8],
        previous_step_chain_preimage: &[u32; 16],
    ) -> ([u32; 8], [u32; 16]) {
        {
            let mut result_hasher = Blake2sBufferingTranscript::new();
            result_hasher.absorb(previous_step_chain_preimage);
            let t = result_hasher.finalize().0;
            assert_eq!(&t, previous_step_hash_chain);
        }
        if &previous_step_hash_chain[8..] == &end_params[..] {
            // do not repeat
            assert!(&previous_step_hash_chain[..8] != &[0u32; 8]);
            (*previous_step_hash_chain, *previous_step_chain_preimage)
        } else {
            let mut preimage = [0u32; 16];
            preimage[..8].copy_from_slice(previous_step_hash_chain);
            preimage[8..].copy_from_slice(end_params);
            let mut result_hasher = Blake2sBufferingTranscript::new();
            result_hasher.absorb(&preimage);
            let hash_chain = result_hasher.finalize().0;
            (hash_chain, preimage)
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProgramProof {
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub circuit_families_proofs: BTreeMap<u8, Vec<UnrolledModeProof>>,
    pub inits_and_teardowns_proofs: Vec<UnrolledModeProof>,
    pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
    pub register_final_values: [FinalRegisterValue; 32],
    pub recursion_chain_preimage: Option<[u32; 16]>,
    pub recursion_chain_hash: Option<[u32; 8]>,
    pub pow_challenge: u64,
}

impl UnrolledProgramProof {
    pub fn get_proof_counts(&self) -> (usize, usize, usize) {
        let family_proofs: usize = self
            .circuit_families_proofs
            .iter()
            .map(|(_, v)| v.len())
            .sum();
        let inits_and_teardowns_proofs = self.inits_and_teardowns_proofs.len();
        let delegation_proofs: usize = self.delegation_proofs.iter().map(|(_, v)| v.len()).sum();
        (family_proofs, inits_and_teardowns_proofs, delegation_proofs)
    }

    pub fn debug_info(&self) -> String {
        let (family_proofs, inits_and_teardowns_proofs, delegation_proofs) =
            self.get_proof_counts();
        format!("Proofs: {family_proofs} circuit family proof(s), {inits_and_teardowns_proofs} inits and teardowns proof(s), {delegation_proofs} delegation proof(s)")
    }

    pub fn flatten_into_responses(
        &self,
        allowed_delegation_circuits: &[u32],
        compiled_layouts: &CompiledCircuitsSet,
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

        // final PC and timestamp
        {
            responses.push(self.final_pc);
            let (low, high) = split_timestamp(self.final_timestamp);
            responses.push(low);
            responses.push(high);
        }

        // families ones
        for (family, proofs) in self.circuit_families_proofs.iter() {
            responses.push(proofs.len() as u32);
            for proof in proofs.iter() {
                let Some(artifact) = &compiled_layouts.compiled_circuit_families.get(family) else {
                    panic!("Proofs file has a proof for circuit type {}, but there is no matching compiled circuit in the set", family);
                };
                let t =
                    verifier_common::proof_flattener::flatten_full_unrolled_proof(proof, artifact);
                responses.extend(t);
            }
        }

        // inits and teardowns
        {
            if let Some(compiled_inits_and_teardowns) =
                compiled_layouts.compiled_inits_and_teardowns.as_ref()
            {
                responses.push(self.inits_and_teardowns_proofs.len() as u32);
                for proof in self.inits_and_teardowns_proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                        proof,
                        &compiled_inits_and_teardowns,
                    );
                    responses.extend(t);
                }
            } else {
                responses.push(0u32);
            }
        }

        // then for every allowed delegation circuit
        for delegation_type in allowed_delegation_circuits.iter() {
            if *delegation_type == common_constants::NON_DETERMINISM_CSR {
                continue;
            }
            if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
                responses.push(proofs.len() as u32);
                for proof in proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_proof(proof, 0);
                    responses.extend(t);
                }
            } else {
                responses.push(0);
            }
        }

        let pow_challenge_low = self.pow_challenge as u32;
        let pow_challenge_high = (self.pow_challenge >> 32) as u32;
        responses.push(pow_challenge_low);
        responses.push(pow_challenge_high);

        if let Some(preimage) = self.recursion_chain_preimage {
            responses.extend(preimage);
        }

        responses
    }
}

pub fn compute_setup_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u8],
    text_section: &[u8],
) -> UnrolledProgramSetup {
    assert_eq!(binary_image.len() % 4, 0);
    assert_eq!(text_section.len() % 4, 0);

    let binary_image_u32: Vec<_> = binary_image
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let text_section_u32: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    assert_eq!(
        binary_image_u32.len(),
        riscv_transpiler::common_constants::ROM_WORD_SIZE
    );
    assert_eq!(
        text_section_u32.len(),
        riscv_transpiler::common_constants::ROM_WORD_SIZE
    );

    let families_setups = setups::compute_unrolled_circuits_params_for_machine_configuration::<C>(
        &binary_image_u32,
        &text_section_u32,
    );
    let inits_and_teardowns_setup =
        setups::compute_inits_and_teardowns_params(&binary_image_u32, &text_section_u32);

    UnrolledProgramSetup::new_from_setups_and_binary(
        binary_image,
        &families_setups
            .into_iter()
            .map(|el| (el.family_idx as u8, el.setup_caps))
            .collect::<Vec<_>>(),
        &inits_and_teardowns_setup,
    )
}

pub fn flatten_proof_into_responses_for_unrolled_recursion(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    is_base_layer: bool,
) -> Vec<u32> {
    let mut responses = vec![];
    let op = if is_base_layer {
        full_statement_verifier::definitions::OP_VERIFY_BASE_LAYER_IN_UNROLLED_CIRCUITS
    } else {
        full_statement_verifier::definitions::OP_VERIFY_RECURSIVE_LAYER_IN_UNROLLED_CIRCUITS
    };
    responses.push(op);
    responses.extend(setup.flatten_for_recursion());
    if is_base_layer {
        responses.extend(proof.flatten_into_responses(&[
            common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
            common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
            common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
        ], compiled_layouts));
    } else {
        responses.extend(proof.flatten_into_responses(&[
            common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        ], compiled_layouts));
    }

    responses
}

#[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
pub fn verify_unrolled_layer_proof(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    is_base_layer: bool,
) -> Result<[u32; 16], ()> {
    for (k, v) in proof.circuit_families_proofs.iter() {
        println!("{} proofs for family {}", v.len(), k);
    }

    let responses = flatten_proof_into_responses_for_unrolled_recursion(
        proof,
        setup,
        compiled_layouts,
        is_base_layer,
    );

    println!("Running the verifier");

    #[cfg(target_arch = "wasm32")]
    {
        let result = std::panic::catch_unwind(move || {
            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            let regs = full_statement_verifier::unrolled_proof_statement::verify_base_or_recursion_unrolled_circuits();

            regs
        }).map_err(|_| ());

        result
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        let result = std::thread::Builder::new()
            .name("verifier thread".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let it = responses.into_iter();
                prover::nd_source_std::set_iterator(it);

                let regs = full_statement_verifier::unrolled_proof_statement::verify_base_or_recursion_unrolled_circuits();

                regs
            })
            .expect("must spawn verifier thread")
            .join();

        result.map_err(|_| ())
    }
}

use common_constants::rom::ROM_SECOND_WORD_BITS;

#[cfg(feature = "prover")]
pub fn prove_unrolled_for_machine_configuration_into_program_proof<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &prover::worker::Worker,
) -> UnrolledProgramProof {
    use riscv_transpiler::common_constants::ROM_WORD_SIZE;

    assert_eq!(binary_image.len(), ROM_WORD_SIZE);
    assert_eq!(text_section.len(), ROM_WORD_SIZE);

    let proofs = prove_unrolled_with_replayer_for_machine_configuration::<C>(
        &binary_image,
        &text_section,
        cycles_bound,
        non_determinism,
        ram_bound,
        &worker,
    );

    let (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    ) = proofs;

    let program_proofs = UnrolledProgramProof {
        final_pc,
        final_timestamp,
        circuit_families_proofs: main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
        register_final_values: register_final_state,
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
        pow_challenge,
    };

    program_proofs
}

#[cfg(feature = "prover")]
pub fn prove_unrolled_with_replayer_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &prover::worker::Worker,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<UnrolledModeProof>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
    u64,
) {
    use std::alloc::Global;
    println!("Performing precomputations for circuit families");
    let families_precomps =
        setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<C, Global, Global>(
            binary_image,
            &text_section,
            &worker,
        );

    println!("Performing precomputations for inits and teardowns");
    let inits_and_teardowns_precomps = setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
        &binary_image,
        &text_section,
        worker,
    );

    println!("Performing precomputations for delegation circuits");
    let delegation_precomputations = setups::all_delegation_circuits_precomputations(worker);

    let (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    ) = prover_examples::unrolled::prove_unrolled_execution_with_replayer::<
        C,
        Global,
        ROM_SECOND_WORD_BITS,
    >(
        cycles_bound,
        &binary_image,
        &text_section,
        non_determinism,
        &families_precomps,
        &inits_and_teardowns_precomps,
        &delegation_precomputations,
        ram_bound,
        worker,
    );

    (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    )
}

#[cfg(all(any(feature = "verifier_80", feature = "verifier_100"), test))]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use std::path::Path;

    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
    use riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation;
    use riscv_transpiler::cycle::MachineConfig;

    struct TestProgram {
        binary_image: Vec<u8>,
        binary_image_u32: Vec<u32>,
        text_section: Vec<u8>,
        text_section_u32: Vec<u32>,
    }

    fn load_test_program(binary_path: &str, text_path: &str) -> TestProgram {
        let (binary_image, binary_image_u32) = setups::read_and_pad_binary(&Path::new(binary_path));
        let (text_section, text_section_u32) = setups::read_and_pad_binary(&Path::new(text_path));

        TestProgram {
            binary_image,
            binary_image_u32,
            text_section,
            text_section_u32,
        }
    }

    fn prepare_unrolled_program<C: MachineConfig>(
        program: &TestProgram,
    ) -> (UnrolledProgramSetup, CompiledCircuitsSet) {
        let program_setup = compute_setup_for_machine_configuration::<C>(
            &program.binary_image,
            &program.text_section,
        );
        let compiled_layouts =
            setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<C>(
                &program.binary_image_u32,
            );

        (program_setup, compiled_layouts)
    }

    fn prove_unrolled_test_program<C: MachineConfig>(
        program: &TestProgram,
        cycles_bound: usize,
        non_determinism_source: impl riscv_transpiler::vm::NonDeterminismCSRSource,
        ram_bound: usize,
        worker: &prover::worker::Worker,
    ) -> UnrolledProgramProof {
        prove_unrolled_for_machine_configuration_into_program_proof::<C>(
            &program.binary_image_u32,
            &program.text_section_u32,
            cycles_bound,
            non_determinism_source,
            ram_bound,
            worker,
        )
    }

    fn verify_unrolled_test_program(
        proof: &UnrolledProgramProof,
        program_setup: &UnrolledProgramSetup,
        compiled_layouts: &CompiledCircuitsSet,
        is_base_layer: bool,
    ) -> [u32; 16] {
        verify_unrolled_layer_proof(proof, program_setup, compiled_layouts, is_base_layer)
            .expect("proof should verify")
    }

    fn expected_base_layer_output(
        program_setup: &UnrolledProgramSetup,
        output_registers: [u32; 8],
    ) -> [u32; 16] {
        let (recursion_chain_hash, _) =
            UnrolledProgramSetup::begin_recursion_chain(&program_setup.end_params);
        let mut expected_output = [0u32; 16];
        expected_output[..8].copy_from_slice(&output_registers);
        expected_output[8..].copy_from_slice(&recursion_chain_hash);

        expected_output
    }

    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial]
    fn test_prove_unrolled_fibonacci() {
        skip_if_ci!();
        let program = load_test_program(
            "../examples/basic_fibonacci/app.bin",
            "../examples/basic_fibonacci/app.text",
        );

        let worker = prover::worker::Worker::new_with_num_threads(32);

        let cycles_bound = 1 << 24;
        let ram_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![]);
        let expected_output_registers = [144, 0, 0, 0, 0, 0, 0, 0];

        let (program_setup, compiled_layouts) =
            prepare_unrolled_program::<IMStandardIsaConfigWithUnsignedMulDiv>(&program);
        let program_proof = prove_unrolled_test_program::<IMStandardIsaConfigWithUnsignedMulDiv>(
            &program,
            cycles_bound,
            non_determinism_source,
            ram_bound,
            &worker,
        );
        let output =
            verify_unrolled_test_program(&program_proof, &program_setup, &compiled_layouts, true);

        assert_eq!(
            output,
            expected_base_layer_output(&program_setup, expected_output_registers)
        );
    }

    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial]
    fn test_prove_unrolled_hashed_fibonacci() {
        skip_if_ci!();
        let program = load_test_program(
            "../examples/hashed_fibonacci/app.bin",
            "../examples/hashed_fibonacci/app.text",
        );

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 24;
        let ram_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);
        let expected_output_registers = [1597, 15, 2_242_890_078, 0, 0, 0, 0, 0];

        let (program_setup, compiled_layouts) =
            prepare_unrolled_program::<IMStandardIsaConfigWithUnsignedMulDiv>(&program);
        let program_proof = prove_unrolled_test_program::<IMStandardIsaConfigWithUnsignedMulDiv>(
            &program,
            cycles_bound,
            non_determinism_source,
            ram_bound,
            &worker,
        );
        let output =
            verify_unrolled_test_program(&program_proof, &program_setup, &compiled_layouts, true);

        assert_eq!(
            output,
            expected_base_layer_output(&program_setup, expected_output_registers)
        );
    }

    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial]
    fn test_prove_unrolled_bigint_with_control() {
        skip_if_ci!();
        let program = load_test_program(
            "../examples/bigint_with_control/app.bin",
            "../examples/bigint_with_control/app.text",
        );

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 20;
        let ram_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![]);
        let expected_output_registers = [0, 0, 1, 0, 0, 0, 0, 0];

        let (program_setup, compiled_layouts) =
            prepare_unrolled_program::<IMStandardIsaConfigWithUnsignedMulDiv>(&program);
        let program_proof = prove_unrolled_test_program::<IMStandardIsaConfigWithUnsignedMulDiv>(
            &program,
            cycles_bound,
            non_determinism_source,
            ram_bound,
            &worker,
        );

        let bigint_proofs = program_proof
            .delegation_proofs
            .get(
                &common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
            )
            .expect("bigint example should emit bigint delegation proofs");
        assert!(!bigint_proofs.is_empty());

        let output =
            verify_unrolled_test_program(&program_proof, &program_setup, &compiled_layouts, true);
        assert_eq!(
            output,
            expected_base_layer_output(&program_setup, expected_output_registers)
        );
    }

    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial]
    fn test_prove_unrolled_keccak_f1600() {
        skip_if_ci!();
        let program = load_test_program(
            "../riscv_transpiler/examples/keccak_f1600/app.bin",
            "../riscv_transpiler/examples/keccak_f1600/app.text",
        );

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 21;
        let ram_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![]);
        let expected_output_registers = [1, 0, 0, 0, 0, 0, 0, 0];

        let (program_setup, compiled_layouts) =
            prepare_unrolled_program::<IMStandardIsaConfigWithUnsignedMulDiv>(&program);
        let program_proof = prove_unrolled_test_program::<IMStandardIsaConfigWithUnsignedMulDiv>(
            &program,
            cycles_bound,
            non_determinism_source,
            ram_bound,
            &worker,
        );
        let output =
            verify_unrolled_test_program(&program_proof, &program_setup, &compiled_layouts, true);

        assert_eq!(
            output,
            expected_base_layer_output(&program_setup, expected_output_registers)
        );
    }

    #[test]
    #[ignore = "manual heavy recursion proving test"]
    #[serial_test::serial]
    fn test_prove_unrolled_recursion_over_hashed_fibonacci() {
        skip_if_ci!();

        // First, prove a current base-layer program using the replayer path.
        let base_program = load_test_program(
            "../examples/hashed_fibonacci/app.bin",
            "../examples/hashed_fibonacci/app.text",
        );

        let worker = prover::worker::Worker::new_with_num_threads(8);
        let base_cycles_bound = 1 << 24;
        let base_ram_bound = 1 << 32;
        let base_non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let (base_program_setup, base_compiled_layouts) =
            prepare_unrolled_program::<IMStandardIsaConfigWithUnsignedMulDiv>(&base_program);
        let base_program_proof = prove_unrolled_test_program::<IMStandardIsaConfigWithUnsignedMulDiv>(
            &base_program,
            base_cycles_bound,
            base_non_determinism_source,
            base_ram_bound,
            &worker,
        );

        // Then feed that proof into the checked-in recursion verifier binary and prove
        // that program through the same replayer/transpiler path used by the current stack.
        let recursion_program = load_test_program(
            "../tools/verifier/recursion_in_unrolled_layer.bin",
            "../tools/verifier/recursion_in_unrolled_layer.text",
        );
        let recursion_cycles_bound = 1 << 26;
        let recursion_ram_bound = 1 << 30;
        let recursion_input = flatten_proof_into_responses_for_unrolled_recursion(
            &base_program_proof,
            &base_program_setup,
            &base_compiled_layouts,
            true,
        );
        let recursion_non_determinism_source = QuasiUARTSource::new_with_reads(recursion_input);
        let (recursion_program_setup, recursion_compiled_layouts) = prepare_unrolled_program::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&recursion_program);
        let expected_base_output = verify_unrolled_test_program(
            &base_program_proof,
            &base_program_setup,
            &base_compiled_layouts,
            true,
        );
        let (previous_chain_hash, previous_chain_preimage) =
            UnrolledProgramSetup::begin_recursion_chain(&base_program_setup.end_params);
        let (expected_chain_hash, _) = UnrolledProgramSetup::continue_recursion_chain(
            &recursion_program_setup.end_params,
            &previous_chain_hash,
            &previous_chain_preimage,
        );

        let mut recursion_program_proof =
            prove_unrolled_test_program::<IWithoutByteAccessIsaConfigWithDelegation>(
                &recursion_program,
                recursion_cycles_bound,
                recursion_non_determinism_source,
                recursion_ram_bound,
                &worker,
            );
        recursion_program_proof.recursion_chain_hash = Some(previous_chain_hash);
        recursion_program_proof.recursion_chain_preimage = Some(previous_chain_preimage);

        let result = verify_unrolled_test_program(
            &recursion_program_proof,
            &recursion_program_setup,
            &recursion_compiled_layouts,
            false,
        );

        let mut expected_result = expected_base_output;
        expected_result[8..].copy_from_slice(&expected_chain_hash);

        assert_eq!(result, expected_result);
    }
}
