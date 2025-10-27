use std::collections::BTreeMap;
use trace_and_split::prover;
use trace_and_split::setups;

use prover::common_constants::TimestampScalar;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::utils::split_timestamp;
use prover::field::*;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use prover::risc_v_simulator;
use trace_and_split::FinalRegisterValue;

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProgramProof {
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub compiled_circuit_families: BTreeMap<u8, CompiledCircuitArtifact<Mersenne31Field>>,
    pub circuit_families_proofs: BTreeMap<u8, Vec<UnrolledModeProof>>,
    pub compiled_inits_and_teardowns: CompiledCircuitArtifact<Mersenne31Field>,
    pub inits_and_teardowns_proofs: Vec<UnrolledModeProof>,
    pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
    pub register_final_values: [FinalRegisterValue; 32],
    pub end_params: [u32; 8],
    pub recursion_chain_preimage: Option<[u32; 16]>,
    pub recursion_chain_hash: Option<[u32; 8]>,
}

impl UnrolledProgramProof {
    pub fn flatten_into_responses(&self, allowed_delegation_circuits: &[u32]) -> Vec<u32> {
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
                let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                    proof,
                    &self.compiled_circuit_families[family],
                );
                responses.extend(t);
            }
        }

        // inits and teardowns
        {
            responses.push(self.inits_and_teardowns_proofs.len() as u32);
            for proof in self.inits_and_teardowns_proofs.iter() {
                let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                    proof,
                    &self.compiled_inits_and_teardowns,
                );
                responses.extend(t);
            }
        }

        // then for every allowed delegation circuit
        for delegation_type in allowed_delegation_circuits.iter() {
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

        if let Some(preimage) = self.recursion_chain_preimage {
            responses.extend(preimage);
        }

        responses
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::path::Path;

    use crate::unrolled::prover::VectorMemoryImplWithRom;
    use risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource;
    use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
    use risc_v_simulator::cycle::MachineConfig;
    use std::alloc::Global;

    #[test]
    fn test_prove_unrolled_fibonacci() {
        let (_, binary_image) =
            setups::read_binary(&Path::new("../examples/basic_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_binary(&Path::new("../examples/basic_fibonacci/app.text"));

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 24;
        let rom_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let proofs =
            prove_unrolled_for_machine_configuration::<IMStandardIsaConfigWithUnsignedMulDiv>(
                &binary_image,
                &text_section,
                cycles_bound,
                non_determinism_source,
                rom_bound,
                &worker,
            );

        println!("Proving completed, prepairing to verify");

        let is_valid = verify_unrolled_base_layer_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&binary_image, &text_section, proofs);

        assert!(is_valid);
    }

    #[test]
    fn test_prove_unrolled_hashed_fibonacci() {
        let (_, binary_image) =
            setups::read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 24;
        let rom_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let proofs = prove_unrolled_with_replayer_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(
            &binary_image,
            &text_section,
            cycles_bound,
            non_determinism_source,
            rom_bound,
            &worker,
        );

        println!("Proving completed, prepairing to verify");

        let is_valid = verify_unrolled_base_layer_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&binary_image, &text_section, proofs);

        assert!(is_valid);
    }

    pub fn prove_unrolled_for_machine_configuration<C: MachineConfig>(
        binary_image: &[u32],
        text_section: &[u32],
        cycles_bound: usize,
        non_determinism: impl NonDeterminismCSRSource<VectorMemoryImplWithRom>,
        ram_bound: usize,
        worker: &prover::worker::Worker,
    ) -> (
        BTreeMap<u8, Vec<UnrolledModeProof>>,
        Vec<UnrolledModeProof>,
        Vec<(u32, Vec<Proof>)>,
        [FinalRegisterValue; 32],
        (u32, TimestampScalar),
    ) {
        println!("Performing precomputations for circuit families");
        let families_precomps =
            setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<
                C,
                Global,
                Global,
            >(binary_image, &text_section, &worker);

        println!("Performing precomputations for inits and teardowns");
        let inits_and_teardowns_precomps =
            setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
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
        ) = prover_examples::unrolled::prove_unrolled_execution::<_, C, Global, 5>(
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
        )
    }

    pub fn prove_unrolled_with_replayer_for_machine_configuration<C: MachineConfig>(
        binary_image: &[u32],
        text_section: &[u32],
        cycles_bound: usize,
        non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource<
            riscv_transpiler::vm::RamWithRomRegion<5>,
        >,
        ram_bound: usize,
        worker: &prover::worker::Worker,
    ) -> (
        BTreeMap<u8, Vec<UnrolledModeProof>>,
        Vec<UnrolledModeProof>,
        Vec<(u32, Vec<Proof>)>,
        [FinalRegisterValue; 32],
        (u32, TimestampScalar),
    ) {
        println!("Performing precomputations for circuit families");
        let families_precomps =
            setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<
                C,
                Global,
                Global,
            >(binary_image, &text_section, &worker);

        println!("Performing precomputations for inits and teardowns");
        let inits_and_teardowns_precomps =
            setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
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
        ) = prover_examples::unrolled::prove_unrolled_execution_with_replayer::<C, Global, 5>(
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
        )
    }

    pub fn verify_unrolled_base_layer_for_machine_configuration<C: MachineConfig>(
        binary_image: &[u32],
        text_section: &[u32],
        proofs: (
            BTreeMap<u8, Vec<UnrolledModeProof>>,
            Vec<UnrolledModeProof>,
            Vec<(u32, Vec<Proof>)>,
            [FinalRegisterValue; 32],
            (u32, TimestampScalar),
        ),
    ) -> bool {
        let (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
        ) = proofs;
        let (families, inits_and_teardowns) =
            setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<C>(
                &binary_image,
            );

        // flatten and set iterator

        let program_proofs = UnrolledProgramProof {
            final_pc,
            final_timestamp,
            compiled_circuit_families: families,
            circuit_families_proofs: main_proofs,
            compiled_inits_and_teardowns: inits_and_teardowns,
            inits_and_teardowns_proofs,
            delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
            register_final_values: register_final_state,
            end_params: [0u32; 8],
            recursion_chain_hash: None,
            recursion_chain_preimage: None,
        };

        for (k, v) in program_proofs.circuit_families_proofs.iter() {
            println!("{} proofs for family {}", v.len(), k);
        }

        let responses = program_proofs.flatten_into_responses(C::ALLOWED_DELEGATION_CSRS);

        let families_setups = setups::compute_unrolled_circuits_params_for_machine_configuration::<C>(
            binary_image,
            text_section,
        );
        let inits_and_teardowns_setup =
            setups::compute_inits_and_teardowns_params(&binary_image, &text_section);

        let params = if setups::is_default_machine_configuration::<C>() {
            full_statement_verifier::unrolled_proof_statement::FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
        } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
            full_statement_verifier::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
        } else if setups::is_reduced_machine_configuration::<C>() {
            full_statement_verifier::unrolled_proof_statement::RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
        } else {
            panic!("Unknown configuration {:?}", std::any::type_name::<C>());
        };

        println!("Running the verifier");

        let result = std::thread::Builder::new()
                .name("verifier thread".to_string())
                .stack_size(1 << 27)
                .spawn(move || {

            let families_setups: Vec<_> = families_setups.iter().map(|el| &el.setup_caps).collect();

            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            #[allow(invalid_value)]
            let _ = unsafe {
                full_statement_verifier::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<true, { setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS }>(
                    &families_setups,
                    params,
                    (&inits_and_teardowns_setup, full_statement_verifier::unrolled_proof_statement::INITS_AND_TEARDOWNS_VERIFIER_PTR),
                    full_statement_verifier::BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
                )
            };
        })
        .expect("must spawn verifier thread").join();

        result.is_ok()
    }
}
