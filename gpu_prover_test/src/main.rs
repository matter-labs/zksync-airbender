#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

fn main() {}

#[cfg(test)]
mod tests {
    use execution_utils::setups::prover::prover_stages::unrolled_prover::UnrolledModeProof;
    use execution_utils::setups::prover::prover_stages::Proof;
    use execution_utils::setups::prover::worker::Worker;
    use execution_utils::setups::{read_and_pad_binary, CompiledCircuitsSet};
    use execution_utils::unified_circuit::{
        flatten_proof_into_responses_for_unified_recursion,
        prove_unified_for_machine_configuration_into_program_proof,
    };
    use execution_utils::unrolled::{
        flatten_proof_into_responses_for_unrolled_recursion, UnrolledProgramProof,
        UnrolledProgramSetup,
    };
    use execution_utils::unrolled_gpu::{UnrolledProver, UnrolledProverLevel};
    use gpu_prover::execution::prover::{
        ExecutionKind, ExecutionProver, ExecutionProverConfiguration,
    };
    use gpu_prover::machine_type::MachineType;
    use log::info;
    use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use risc_v_simulator::cycle::{
        IMStandardIsaConfigWithUnsignedMulDiv, IWithoutByteAccessIsaConfigWithDelegation,
    };
    use std::fs::File;
    use std::io::{Read, Write};
    use std::path::Path;

    #[test]
    fn prove_single_block() {
        init_logger();

        let block_number = 23620012;
        // let block_number = 23873944;

        let mut file = File::open(&format!("{}_witness", block_number)).expect("should open file");
        let mut witness = vec![];
        file.read_to_end(&mut witness)
            .expect("must read witness from file");
        let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
        assert_eq!(witness.len() % 4, 0);
        let witness: Vec<_> = witness
            .as_chunks::<4>()
            .0
            .iter()
            .map(|el| u32::from_be_bytes(*el))
            .collect();
        let source = QuasiUARTSource::new_with_reads(witness);
        let (binary, binary_u32) =
            read_binary(Path::new("../riscv_transpiler/examples/zksync_os/app.bin"));
        let (padded_binary, padded_binary_u32) =
            read_and_pad_binary(Path::new("../riscv_transpiler/examples/zksync_os/app.bin"));
        let (text, text_u32) =
            read_binary(Path::new("../riscv_transpiler/examples/zksync_os/app.text"));
        let (padded_text, padded_text_u32) =
            read_and_pad_binary(Path::new("../riscv_transpiler/examples/zksync_os/app.text"));
        info!("Computing setup");
        let setup = execution_utils::unrolled::compute_setup_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&padded_binary, &padded_text);
        serde_json::to_writer_pretty(File::create("setup.json").unwrap(), &setup).unwrap();
        let compiled_layouts =
            execution_utils::setups::get_unrolled_circuits_artifacts_for_machine_type::<
                IMStandardIsaConfigWithUnsignedMulDiv,
            >(&padded_binary_u32);
        serde_json::to_writer_pretty(File::create("layouts.json").unwrap(), &compiled_layouts)
            .unwrap();
        let configuration = ExecutionProverConfiguration {
            replay_worker_threads_count: 4,
            host_allocators_per_job_count: 64,
            host_allocators_per_device_count: 128,
            ..Default::default()
        };
        let mut prover = ExecutionProver::with_configuration(configuration);
        prover.add_binary(
            0,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            binary_u32,
            text_u32,
            None,
        );
        info!("warmup");
        let _result = prover.commit_memory_and_prove(0, 0, source.clone());
        info!("computing GPU proof");
        let result = prover.commit_memory_and_prove(0, 0, source);
        let proof = UnrolledProgramProof {
            final_pc: result.final_pc,
            final_timestamp: result.final_timestamp,
            circuit_families_proofs: result.circuit_families_proofs,
            inits_and_teardowns_proofs: result.inits_and_teardowns_proofs,
            delegation_proofs: result.delegation_proofs,
            register_final_values: result.register_final_values,
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
        };
        serde_json::to_writer_pretty(File::create("gpu_proof.json").unwrap(), &proof).unwrap();
    }

    #[test]
    fn prove_recursive_single_block_with_unrolled_prover() {
        init_logger();

        let block_number = 23620012;
        // let block_number = 23873944;

        let mut file = File::open(&format!("{}_witness", block_number)).expect("should open file");
        let mut witness = vec![];
        file.read_to_end(&mut witness)
            .expect("must read witness from file");
        let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
        assert_eq!(witness.len() % 4, 0);
        let witness: Vec<_> = witness
            .as_chunks::<4>()
            .0
            .iter()
            .map(|el| u32::from_be_bytes(*el))
            .collect();
        let app_path = "../riscv_transpiler/examples/zksync_os/app";
        let configuration = ExecutionProverConfiguration {
            replay_worker_threads_count: 4,
            host_allocators_per_job_count: 64,
            host_allocators_per_device_count: 128,
            ..Default::default()
        };
        let prover = UnrolledProver::new(
            &app_path.to_string(),
            configuration,
            UnrolledProverLevel::RecursionUnified,
        );
        let source = QuasiUARTSource::new_with_reads(witness);
        let (proof, _) = prover.prove(block_number, source);
        let encoded = bincode::serde::encode_to_vec(&proof, bincode::config::standard()).unwrap();
        File::create("gpu_proof_unrolled_prover.bin")
            .unwrap()
            .write_all(&encoded)
            .unwrap();
        // serde_json::to_writer_pretty(File::create("gpu_proof_unrolled_prover.json").unwrap(), &proof).unwrap();
    }

    #[test]
    fn prove_base_layer() {
        init_logger();
        let (padded_binary, padded_binary_u32) =
            read_and_pad_binary(Path::new("../examples/hashed_fibonacci/app.bin"));
        // read_and_pad_binary(Path::new("../riscv_transpiler/examples/keccak_f1600/app.bin"));
        let (binary, binary_u32) = read_binary(Path::new("../examples/hashed_fibonacci/app.bin"));
        // read_binary(Path::new("../riscv_transpiler/examples/keccak_f1600/app.bin"));
        let (padded_text, padded_text_u32) =
            read_and_pad_binary(Path::new("../examples/hashed_fibonacci/app.text"));
        // // read_and_pad_binary(Path::new("../riscv_transpiler/examples/keccak_f1600/app.text"));
        let (text, text_u32) = read_binary(Path::new("../examples/hashed_fibonacci/app.text"));
        // read_binary(Path::new(
        //     "../riscv_transpiler/examples/keccak_f1600/app.text",
        // ));
        // println!("Computing setup");
        // let setup = execution_utils::unrolled::compute_setup_for_machine_configuration::<
        //     IMStandardIsaConfigWithUnsignedMulDiv,
        // >(&padded_binary, &padded_text);
        // serde_json::to_writer_pretty(File::create("setup.json").unwrap(), &setup).unwrap();
        // let compiled_layouts =
        //     execution_utils::setups::get_unrolled_circuits_artifacts_for_machine_type::<
        //         IMStandardIsaConfigWithUnsignedMulDiv,
        //     >(&padded_binary_u32);
        // serde_json::to_writer_pretty(File::create("layouts.json").unwrap(), &compiled_layouts)
        //     .unwrap();
        println!("Computing proof");

        let mut prover = ExecutionProver::with_configuration(Default::default());
        prover.add_binary(
            0,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            binary_u32.clone(),
            text_u32.clone(),
            None,
        );
        let source = QuasiUARTSource::new_with_reads(vec![0, 0]);
        info!("warmup");
        let _result = prover.commit_memory_and_prove(0, 0, source.clone());
        info!("computing GPU proof");
        let result = prover.commit_memory_and_prove(0, 0, source.clone());
        let gpu_proof = UnrolledProgramProof {
            final_pc: result.final_pc,
            final_timestamp: result.final_timestamp,
            circuit_families_proofs: result.circuit_families_proofs,
            inits_and_teardowns_proofs: result.inits_and_teardowns_proofs,
            delegation_proofs: result.delegation_proofs,
            register_final_values: result.register_final_values,
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
        };
        serde_json::to_writer_pretty(File::create("gpu_proof.json").unwrap(), &gpu_proof).unwrap();

        // let worker = Worker::new();
        // let cpu_proof =
        //     execution_utils::unrolled::prove_unrolled_for_machine_configuration_into_program_proof::<
        //         IMStandardIsaConfigWithUnsignedMulDiv,
        //     >(&padded_binary_u32, &padded_text_u32, 1 << 31, source, 1 << 30, &worker);
        // serde_json::to_writer_pretty(File::create("cpu_proof.json").unwrap(), &cpu_proof).unwrap();
        //
        // compare_program_proofs(&cpu_proof, &gpu_proof);
    }

    #[cfg(feature = "verifier_80")]
    #[test]
    fn verify_base_proof() {
        let setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup.json").unwrap()).unwrap();
        let layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts.json").unwrap()).unwrap();
        // let cpu_proof: UnrolledProgramProof =
        //     serde_json::from_reader(&File::open("cpu_proof.json").unwrap()).unwrap();
        let gpu_proof: UnrolledProgramProof =
            serde_json::from_reader(&File::open("gpu_proof.json").unwrap()).unwrap();

        // println!("Verifying CPU proof...");
        // let result =
        //     execution_utils::unrolled::verify_unrolled_layer_proof(&cpu_proof, &setup, &layouts, true)
        //         .expect("is valid proof");
        // assert_eq!(result.iter().all(|el| *el == 0), false);

        for (id, proofs) in gpu_proof.delegation_proofs.iter() {
            println!("{} delegation proofs for delegation id {id}", proofs.len());
        }
        println!("Verifying GPU proof...");
        let result = execution_utils::unrolled::verify_unrolled_layer_proof(
            &gpu_proof, &setup, &layouts, true,
        )
        .expect("is valid proof");
        assert_eq!(result.iter().all(|el| *el == 0), false);
    }

    #[test]
    fn prove_recursion_over_base() {
        init_logger();
        let base_layer_setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup.json").unwrap()).unwrap();
        let base_layer_proof: UnrolledProgramProof =
            serde_json::from_reader(&File::open("gpu_proof.json").unwrap()).unwrap();
        let base_layer_layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts.json").unwrap()).unwrap();

        for (family, proofs) in base_layer_proof.circuit_families_proofs.iter() {
            println!("{} proofs for family {}", proofs.len(), family);
        }
        for (delegation_type, proofs) in base_layer_proof.delegation_proofs.iter() {
            println!("{} proofs for delegation {}", proofs.len(), delegation_type);
        }

        let witness = flatten_proof_into_responses_for_unrolled_recursion(
            &base_layer_proof,
            &base_layer_setup,
            &base_layer_layouts,
            true,
        );
        let source = QuasiUARTSource::new_with_reads(witness);

        let (binary, binary_u32) = read_binary(Path::new(
            "../tools/verifier/recursion_in_unrolled_layer.bin",
        ));
        let (padded_binary, padded_binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unrolled_layer.bin",
        ));
        let (text, text_u32) = read_binary(Path::new(
            "../tools/verifier/recursion_in_unrolled_layer.text",
        ));
        let (padded_text, padded_text_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unrolled_layer.text",
        ));

        info!("Computing setup");
        let setup = execution_utils::unrolled::compute_setup_for_machine_configuration::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&padded_binary, &padded_text);
        serde_json::to_writer_pretty(
            File::create("setup_recursion_over_base.json").unwrap(),
            &setup,
        )
        .unwrap();
        let layouts = execution_utils::setups::get_unrolled_circuits_artifacts_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&padded_binary_u32);
        serde_json::to_writer_pretty(
            File::create("layouts_recursion_over_base.json").unwrap(),
            &layouts,
        )
        .unwrap();

        let mut prover = ExecutionProver::with_configuration(Default::default());
        prover.add_binary(
            0,
            ExecutionKind::Unrolled,
            MachineType::Reduced,
            binary_u32.clone(),
            text_u32.clone(),
            None,
        );
        info!("warmup");
        let _ = prover.commit_memory_and_prove(0, 0, source.clone());
        info!("computing GPU proof");
        let result = prover.commit_memory_and_prove(0, 0, source.clone());
        let mut gpu_proof = UnrolledProgramProof {
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
            UnrolledProgramSetup::begin_recursion_chain(&base_layer_setup.end_params);
        gpu_proof.recursion_chain_hash = Some(hash_chain);
        gpu_proof.recursion_chain_preimage = Some(preimage);
        serde_json::to_writer_pretty(
            File::create("gpu_proof_recursion_over_base.json").unwrap(),
            &gpu_proof,
        )
        .unwrap();

        // let worker = Worker::new_with_num_threads(8);
        // println!("Computing proof");
        // let mut cpu_proof =
        //     execution_utils::unrolled::prove_unrolled_for_machine_configuration_into_program_proof::<
        //         IWithoutByteAccessIsaConfigWithDelegation,
        //     >(&binary_u32, &text_u32, 1 << 31, source, 1 << 30, &worker);
        // // make a hash chain
        // let (hash_chain, preimage) =
        //     UnrolledProgramSetup::begin_recursion_chain(&base_layer_setup.end_params);
        // cpu_proof.recursion_chain_hash = Some(hash_chain);
        // cpu_proof.recursion_chain_preimage = Some(preimage);
        // serde_json::to_writer_pretty(File::create("cpu_proof_recursion_over_base.json").unwrap(), &cpu_proof).unwrap();

        // compare_program_proofs(&cpu_proof, &gpu_proof);
    }

    #[cfg(feature = "verifier_80")]
    #[test]
    fn verify_recursion_over_base_proof() {
        let setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup_recursion_over_base.json").unwrap())
                .unwrap();
        let layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts_recursion_over_base.json").unwrap())
                .unwrap();
        // let cpu_proof: UnrolledProgramProof = serde_json::from_reader(&File::open("cpu_proof_recursion_over_base.json").unwrap()).unwrap();
        let gpu_proof: UnrolledProgramProof =
            serde_json::from_reader(&File::open("gpu_proof_recursion_over_base.json").unwrap())
                .unwrap();

        assert_eq!(setup.circuit_families_setups.len(), 4);

        // println!("Verifying CPU proof...");
        // let result = execution_utils::unrolled::verify_unrolled_layer_proof(&cpu_proof, &setup, &layouts, false).expect("is valid proof");
        // assert_eq!(result.iter().all(|el| *el == 0), false);

        println!("Verifying GPU proof...");
        let result = execution_utils::unrolled::verify_unrolled_layer_proof(
            &gpu_proof, &setup, &layouts, false,
        )
        .expect("is valid proof");
        assert_eq!(result.iter().all(|el| *el == 0), false);
    }

    #[test]
    fn prove_recursion_over_recursion() {
        init_logger();
        let previous_layer_setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup_recursion_over_base.json").unwrap())
                .unwrap();
        let previous_layer_proof: UnrolledProgramProof =
            serde_json::from_reader(&File::open("gpu_proof_recursion_over_base.json").unwrap())
                .unwrap();
        let previous_layer_layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts_recursion_over_base.json").unwrap())
                .unwrap();

        for (family, proofs) in previous_layer_proof.circuit_families_proofs.iter() {
            println!("{} proofs for family {}", proofs.len(), family);
        }
        for (delegation_type, proofs) in previous_layer_proof.delegation_proofs.iter() {
            println!("{} proofs for delegation {}", proofs.len(), delegation_type);
        }

        let witness = flatten_proof_into_responses_for_unified_recursion(
            &previous_layer_proof,
            &previous_layer_setup,
            &previous_layer_layouts,
            true,
        );
        let source = QuasiUARTSource::new_with_reads(witness);

        let (binary, binary_u32) = read_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));
        let (padded_binary, padded_binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));
        let (text, text_u32) = read_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.text",
        ));
        let (padded_text, padded_text_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.text",
        ));

        println!("Computing setup");
        let setup =
            execution_utils::unified_circuit::compute_unified_setup_for_machine_configuration::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&padded_binary, &padded_text);
        serde_json::to_writer_pretty(
            File::create("setup_recursion_over_recursion.json").unwrap(),
            &setup,
        )
        .unwrap();
        let layouts = execution_utils::setups::get_unified_circuit_artifact_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&padded_binary_u32);
        serde_json::to_writer_pretty(
            File::create("layouts_recursion_over_recursion.json").unwrap(),
            &layouts,
        )
        .unwrap();

        println!("Computing proof");

        let mut prover = ExecutionProver::with_configuration(Default::default());
        prover.add_binary(
            0,
            ExecutionKind::Unified,
            MachineType::Reduced,
            binary_u32.clone(),
            text_u32.clone(),
            None,
        );
        let result = prover.commit_memory_and_prove(0, 0, source.clone());
        let mut gpu_proof = UnrolledProgramProof {
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
        let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
            &previous_layer_setup.end_params,
            &previous_layer_proof.recursion_chain_hash.unwrap(),
            &previous_layer_proof.recursion_chain_preimage.unwrap(),
        );

        gpu_proof.recursion_chain_hash = Some(hash_chain);
        gpu_proof.recursion_chain_preimage = Some(preimage);
        serde_json::to_writer_pretty(
            File::create("gpu_proof_recursion_over_recursion.json").unwrap(),
            &gpu_proof,
        )
        .unwrap();

        let worker = Worker::new_with_num_threads(8);
        println!("Computing proof");
        let mut cpu_proof = prove_unified_for_machine_configuration_into_program_proof::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(
            &padded_binary_u32,
            &padded_text_u32,
            1 << 31,
            source,
            1 << 30,
            &worker,
        );

        cpu_proof.recursion_chain_hash = Some(hash_chain);
        cpu_proof.recursion_chain_preimage = Some(preimage);
        serde_json::to_writer_pretty(
            File::create("cpu_proof_recursion_over_recursion.json").unwrap(),
            &cpu_proof,
        )
        .unwrap();

        compare_program_proofs(&cpu_proof, &gpu_proof);
    }

    #[cfg(feature = "verifier_80")]
    #[test]
    fn verify_recursion_over_recursion_proof() {
        let setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup_recursion_over_recursion.json").unwrap())
                .unwrap();
        let layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts_recursion_over_recursion.json").unwrap())
                .unwrap();
        // let cpu_proof: UnrolledProgramProof = serde_json::from_reader(&File::open("cpu_proof_recursion_over_base.json").unwrap()).unwrap();
        let gpu_proof: UnrolledProgramProof = serde_json::from_reader(
            &File::open("gpu_proof_recursion_over_recursion.json").unwrap(),
        )
        .unwrap();

        // println!("Verifying CPU proof...");
        // let result = execution_utils::unrolled::verify_unrolled_layer_proof(&cpu_proof, &setup, &layouts, false).expect("is valid proof");
        // assert_eq!(result.iter().all(|el| *el == 0), false);

        println!("Verifying GPU proof...");
        let result = execution_utils::unified_circuit::verify_proof_in_unified_layer(
            &gpu_proof, &setup, &layouts, false,
        )
        .expect("is valid proof");
        assert_eq!(result.iter().all(|el| *el == 0), false);
    }

    #[test]
    fn prove_final_recursion() {
        init_logger();
        let previous_layer_setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup_recursion_over_recursion.json").unwrap())
                .unwrap();
        let previous_layer_proof: UnrolledProgramProof = serde_json::from_reader(
            &File::open("gpu_proof_recursion_over_recursion.json").unwrap(),
        )
        .unwrap();
        let previous_layer_layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts_recursion_over_recursion.json").unwrap())
                .unwrap();

        for (family, proofs) in previous_layer_proof.circuit_families_proofs.iter() {
            println!("{} proofs for family {}", proofs.len(), family);
        }
        for (delegation_type, proofs) in previous_layer_proof.delegation_proofs.iter() {
            println!("{} proofs for delegation {}", proofs.len(), delegation_type);
        }

        let witness = flatten_proof_into_responses_for_unified_recursion(
            &previous_layer_proof,
            &previous_layer_setup,
            &previous_layer_layouts,
            false,
        );
        let source = QuasiUARTSource::new_with_reads(witness);

        let (binary, binary_u32) = read_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));
        let (padded_binary, padded_binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));
        let (text, text_u32) = read_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.text",
        ));
        let (padded_text, padded_text_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.text",
        ));

        println!("Computing setup");
        let setup =
            execution_utils::unified_circuit::compute_unified_setup_for_machine_configuration::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&padded_binary, &padded_text);
        serde_json::to_writer_pretty(File::create("setup_final_recursion.json").unwrap(), &setup)
            .unwrap();
        let layouts = execution_utils::setups::get_unified_circuit_artifact_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&padded_binary_u32);
        serde_json::to_writer_pretty(
            File::create("layouts_final_recursion.json").unwrap(),
            &layouts,
        )
        .unwrap();

        println!("Computing proof");

        let mut prover = ExecutionProver::with_configuration(Default::default());
        prover.add_binary(
            0,
            ExecutionKind::Unified,
            MachineType::Reduced,
            binary_u32.clone(),
            text_u32.clone(),
            None,
        );
        let result = prover.commit_memory_and_prove(0, 0, source.clone());
        let mut gpu_proof = UnrolledProgramProof {
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
        let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
            &previous_layer_setup.end_params,
            &previous_layer_proof.recursion_chain_hash.unwrap(),
            &previous_layer_proof.recursion_chain_preimage.unwrap(),
        );

        gpu_proof.recursion_chain_hash = Some(hash_chain);
        gpu_proof.recursion_chain_preimage = Some(preimage);
        serde_json::to_writer_pretty(
            File::create("gpu_proof_final_recursion.json").unwrap(),
            &gpu_proof,
        )
        .unwrap();

        let worker = Worker::new_with_num_threads(8);
        println!("Computing proof");
        let mut cpu_proof = prove_unified_for_machine_configuration_into_program_proof::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(
            &padded_binary_u32,
            &padded_text_u32,
            1 << 31,
            source,
            1 << 30,
            &worker,
        );

        cpu_proof.recursion_chain_hash = Some(hash_chain);
        cpu_proof.recursion_chain_preimage = Some(preimage);
        serde_json::to_writer_pretty(
            File::create("cpu_proof_final_recursion.json").unwrap(),
            &cpu_proof,
        )
        .unwrap();

        compare_program_proofs(&cpu_proof, &gpu_proof);
    }

    #[cfg(feature = "verifier_80")]
    #[test]
    fn verify_final_recursion_proof() {
        let setup: UnrolledProgramSetup =
            serde_json::from_reader(&File::open("setup_final_recursion.json").unwrap()).unwrap();
        let layouts: CompiledCircuitsSet =
            serde_json::from_reader(&File::open("layouts_final_recursion.json").unwrap()).unwrap();
        // let cpu_proof: UnrolledProgramProof = serde_json::from_reader(&File::open("cpu_proof_recursion_over_base.json").unwrap()).unwrap();
        let gpu_proof: UnrolledProgramProof =
            serde_json::from_reader(&File::open("gpu_proof_final_recursion.json").unwrap())
                .unwrap();

        // println!("Verifying CPU proof...");
        // let result = execution_utils::unrolled::verify_unrolled_layer_proof(&cpu_proof, &setup, &layouts, false).expect("is valid proof");
        // assert_eq!(result.iter().all(|el| *el == 0), false);

        println!("Verifying GPU proof...");
        let result = execution_utils::unified_circuit::verify_proof_in_unified_layer(
            &gpu_proof, &setup, &layouts, false,
        )
        .expect("is valid proof");
        assert_eq!(result.iter().all(|el| *el == 0), false);
    }

    fn init_logger() {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("trace"))
            .target(env_logger::Target::Stdout)
            .format_timestamp_millis()
            .format_module_path(false)
            .format_target(false)
            .init();
    }

    fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
        use std::io::Read;
        let mut file = std::fs::File::open(path).expect("must open provided file");
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).expect("must read the file");
        assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
        let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
        for el in buffer.as_chunks::<4>().0 {
            binary.push(u32::from_le_bytes(*el));
        }

        (buffer, binary)
    }

    fn compare_program_proofs(a: &UnrolledProgramProof, b: &UnrolledProgramProof) {
        assert_eq!(a.final_pc, b.final_pc);
        assert_eq!(a.final_timestamp, b.final_timestamp);
        assert_eq!(a.register_final_values, b.register_final_values);
        assert_eq!(
            a.circuit_families_proofs.len(),
            b.circuit_families_proofs.len()
        );
        for (a, b) in a
            .circuit_families_proofs
            .iter()
            .zip(b.circuit_families_proofs.iter())
        {
            assert_eq!(a.0, b.0);
            assert_eq!(a.1.len(), b.1.len());
            for (proof_a, proof_b) in a.1.iter().zip(b.1.iter()) {
                compare_unrolled_proofs(proof_a, proof_b);
            }
        }
        assert_eq!(
            a.inits_and_teardowns_proofs.len(),
            b.inits_and_teardowns_proofs.len()
        );
        for (proof_a, proof_b) in a
            .inits_and_teardowns_proofs
            .iter()
            .zip(b.inits_and_teardowns_proofs.iter())
        {
            compare_unrolled_proofs(proof_a, proof_b);
        }
        assert_eq!(a.delegation_proofs.len(), b.delegation_proofs.len());
        for (a, b) in a.delegation_proofs.iter().zip(b.delegation_proofs.iter()) {
            assert_eq!(a.0, b.0);
            assert_eq!(a.1.len(), b.1.len());
            for (proof_a, proof_b) in a.1.iter().zip(b.1.iter()) {
                compare_delegation_proofs(proof_a, proof_b);
            }
        }
    }

    fn compare_unrolled_proofs(a: &UnrolledModeProof, b: &UnrolledModeProof) {
        let UnrolledModeProof {
            external_challenges,
            public_inputs,
            witness_tree_caps,
            memory_tree_caps,
            setup_tree_caps,
            stage_2_tree_caps,
            permutation_grand_product_accumulator,
            delegation_argument_accumulator,
            quotient_tree_caps,
            evaluations_at_random_points,
            deep_poly_caps,
            intermediate_fri_oracle_caps,
            last_fri_step_plain_leaf_values,
            final_monomial_form,
            queries,
            pow_nonce: _,
            delegation_type,
            aux_boundary_values,
        } = a;
        assert_eq!(
            external_challenges, &b.external_challenges,
            "external_challenges"
        );
        assert_eq!(public_inputs, &b.public_inputs, "public_inputs");
        assert_eq!(setup_tree_caps, &b.setup_tree_caps, "setup_tree_caps");
        assert_eq!(memory_tree_caps, &b.memory_tree_caps, "memory_tree_caps");
        assert_eq!(witness_tree_caps, &b.witness_tree_caps, "witness_tree_caps");
        assert_eq!(stage_2_tree_caps, &b.stage_2_tree_caps, "stage_2_tree_caps");
        assert_eq!(
            permutation_grand_product_accumulator, &b.permutation_grand_product_accumulator,
            "permutation_grand_product_accumulator"
        );
        assert_eq!(
            delegation_argument_accumulator, &b.delegation_argument_accumulator,
            "delegation_argument_accumulator"
        );
        assert_eq!(quotient_tree_caps, &b.quotient_tree_caps);
        assert_eq!(
            evaluations_at_random_points, &b.evaluations_at_random_points,
            "evaluations_at_random_points"
        );
        assert_eq!(deep_poly_caps, &b.deep_poly_caps, "deep_poly_caps");
        assert_eq!(
            intermediate_fri_oracle_caps, &b.intermediate_fri_oracle_caps,
            "intermediate_fri_oracle_caps"
        );
        assert_eq!(
            last_fri_step_plain_leaf_values, &b.last_fri_step_plain_leaf_values,
            "last_fri_step_plain_leaf_values"
        );
        assert_eq!(
            final_monomial_form, &b.final_monomial_form,
            "final_monomial_form"
        );
        assert_eq!(queries.len(), b.queries.len(), "queries length");
        assert_eq!(delegation_type, &b.delegation_type, "delegation_type");
        assert_eq!(
            aux_boundary_values, &b.aux_boundary_values,
            "aux_boundary_values"
        );
    }

    fn compare_delegation_proofs(a: &Proof, b: &Proof) {
        let Proof {
            external_values,
            public_inputs,
            witness_tree_caps,
            memory_tree_caps,
            setup_tree_caps,
            stage_2_tree_caps,
            memory_grand_product_accumulator,
            delegation_argument_accumulator,
            quotient_tree_caps,
            evaluations_at_random_points,
            deep_poly_caps,
            intermediate_fri_oracle_caps,
            last_fri_step_plain_leaf_values,
            final_monomial_form,
            queries,
            pow_nonce: _,
            circuit_sequence,
            delegation_type,
        } = a;
        assert_eq!(
            &external_values.challenges, &b.external_values.challenges,
            "challenges"
        );
        assert_eq!(
            &external_values.aux_boundary_values, &b.external_values.aux_boundary_values,
            "aux_boundary_values"
        );
        assert_eq!(public_inputs, &b.public_inputs, "public_inputs");
        assert_eq!(setup_tree_caps, &b.setup_tree_caps, "setup_tree_caps");
        assert_eq!(memory_tree_caps, &b.memory_tree_caps, "memory_tree_caps");
        assert_eq!(witness_tree_caps, &b.witness_tree_caps, "witness_tree_caps");
        assert_eq!(stage_2_tree_caps, &b.stage_2_tree_caps, "stage_2_tree_caps");
        assert_eq!(
            memory_grand_product_accumulator, &b.memory_grand_product_accumulator,
            "permutation_grand_product_accumulator"
        );
        assert_eq!(
            delegation_argument_accumulator, &b.delegation_argument_accumulator,
            "delegation_argument_accumulator"
        );
        assert_eq!(quotient_tree_caps, &b.quotient_tree_caps);
        assert_eq!(
            evaluations_at_random_points, &b.evaluations_at_random_points,
            "evaluations_at_random_points"
        );
        assert_eq!(deep_poly_caps, &b.deep_poly_caps, "deep_poly_caps");
        assert_eq!(
            intermediate_fri_oracle_caps, &b.intermediate_fri_oracle_caps,
            "intermediate_fri_oracle_caps"
        );
        assert_eq!(
            last_fri_step_plain_leaf_values, &b.last_fri_step_plain_leaf_values,
            "last_fri_step_plain_leaf_values"
        );
        assert_eq!(
            final_monomial_form, &b.final_monomial_form,
            "final_monomial_form"
        );
        assert_eq!(queries.len(), b.queries.len(), "queries length");
        assert_eq!(circuit_sequence, &b.circuit_sequence, "circuit_sequence");
        assert_eq!(delegation_type, &b.delegation_type, "delegation_type");
    }
}
