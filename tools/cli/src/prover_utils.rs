use clap::ValueEnum;
use execution_utils::Machine;
use execution_utils::{
    generate_oracle_data_for_universal_verifier, generate_oracle_data_from_metadata_and_proof_list,
    get_padded_binary, ProgramProof, ProofList, ProofMetadata, RecursionStrategy,
    UNIVERSAL_CIRCUIT_VERIFIER,
};
use verifier_common::parse_field_els_as_u32_from_u16_limbs_checked;

use prover::{
    prover_stages::Proof,
    risc_v_simulator::abstractions::non_determinism::QuasiUARTSource,
    transcript::{Blake2sBufferingTranscript, Seed},
};
use std::{alloc::Global, fs, io::Read, path::Path};

#[cfg(feature = "gpu")]
pub use gpu_prover::circuit_type::MainCircuitType;

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(&format!("{filename}"));
    serde_json::from_reader(src).unwrap()
}
pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &Path) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

/// Default amount of cycles, if no flag is set.
pub const DEFAULT_CYCLES: usize = 32_000_000;

// Determines when to stop proving.
#[derive(Clone, Debug, ValueEnum)]
pub enum ProvingLimit {
    /// Does base + 1st recursion layer.
    FinalRecursion,
    /// Does base + both recursion layers.
    FinalProof,
    /// Also creates a final snark (requires zkos_wrapper)
    Snark,
}

pub fn u32_from_hex_string(hex_string: &str) -> Vec<u32> {
    // Check the string length is a multiple of 8 (for valid u32 chunks)
    if hex_string.len() % 8 != 0 {
        panic!("Hex string length is not a multiple of 8");
    }
    // Parse the string in chunks of 8 characters
    let numbers: Vec<u32> = hex_string
        .as_bytes()
        .chunks(8)
        .map(|chunk| {
            let chunk_str = std::str::from_utf8(chunk).expect("Invalid UTF-8");
            u32::from_str_radix(chunk_str, 16).expect("Invalid hex number")
        })
        .collect();

    numbers
}

pub fn create_proofs(
    bin_path: &String,
    output_dir: &String,
    input_hex: &Option<String>,
    prev_metadata: &Option<String>,
    machine: &Machine,
    cycles: &Option<usize>,
    until: &Option<ProvingLimit>,
    recursion_mode: RecursionStrategy,
    tmp_dir: &Option<String>,
    use_gpu: bool,
) {
    let prev_metadata: Option<ProofMetadata> = prev_metadata
        .as_ref()
        .map(|prev_metadata| deserialize_from_file(&prev_metadata));

    let binary = load_binary_from_path(bin_path);

    let num_instances = (cycles.unwrap_or(DEFAULT_CYCLES) / risc_v_cycles::NUM_CYCLES) + 1;

    println!(
        "Will try proving now, with up to {} circuits.",
        num_instances
    );

    let non_determinism_data = if let Some(input_hex) = input_hex {
        u32_from_hex_string(input_hex)
    } else {
        vec![]
    };

    // Serialization and deserialization of artifacts
    // (as requested by user arguments) can take a lot of time,
    // and typically won't be needed in production.
    // total_proof_time accumulates the actual time spent on
    // the production critical path
    // (tracing, witness generation, proving, recursion).
    let (mut gpu_state, mut total_proof_time) = if use_gpu {
        // In this function we only use the GPU for the base and 1st recursion layer (reduced 2^22 machine).
        // In order to use it for the 2nd recursion layer, you should call `create_final_proofs_from_program_proof`
        #[cfg(feature = "gpu")]
        {
            let recursion_circuit_type = MainCircuitType::ReducedRiscVMachine;
            (
                Some(GpuSharedState::new(&binary, recursion_circuit_type)),
                Some(0f64),
            )
        }
        #[cfg(not(feature = "gpu"))]
        {
            panic!("Compiled without GPU support, but --use-gpu is set.");
        }
    } else {
        (None, None)
    };
    let mut gpu_state = gpu_state.as_mut();

    let (proof_list, proof_metadata) = create_proofs_internal(
        &binary,
        non_determinism_data,
        machine,
        num_instances,
        prev_metadata.map(|x| x.create_prev_metadata()),
        &mut gpu_state,
        &mut total_proof_time,
    );

    // Now we finished 'basic' proving - check if there is a need for recursion.
    if let Some(until) = until {
        assert_eq!(
            machine,
            &Machine::Standard,
            "Recursion is only supported after Standard machine"
        );

        if let Some(tmp_dir) = tmp_dir {
            let base_tmp_dir = Path::new(tmp_dir).join("base");
            if !base_tmp_dir.exists() {
                fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
            }
            proof_list.write_to_directory(&base_tmp_dir);
            serialize_to_file(&proof_metadata, &base_tmp_dir.join("metadata.json"))
        }
        let (recursion_proof_list, recursion_proof_metadata) = create_recursion_proofs(
            proof_list,
            proof_metadata,
            recursion_mode,
            tmp_dir,
            &mut gpu_state,
            &mut total_proof_time,
        );
        match until {
            ProvingLimit::FinalRecursion => {
                recursion_proof_list.write_to_directory(Path::new(output_dir));

                serialize_to_file(
                    &recursion_proof_metadata,
                    &Path::new(output_dir).join("metadata.json"),
                );
                let program_proof = ProgramProof::from_proof_list_and_metadata(
                    &recursion_proof_list,
                    &recursion_proof_metadata,
                );
                serialize_to_file(
                    &program_proof,
                    &Path::new(output_dir).join("recursion_program_proof.json"),
                );
            }
            ProvingLimit::FinalProof => {
                // Here we support only CPU proving, mostly for testing purposes.
                // In order to use GPU for 2nd recursion layer, please call `create_final_proofs_from_program_proof`
                let program_proof = create_final_proofs(
                    recursion_proof_list,
                    recursion_proof_metadata,
                    recursion_mode,
                    tmp_dir,
                    &mut None,
                    &mut None,
                );

                serialize_to_file(
                    &program_proof,
                    &Path::new(output_dir).join("final_program_proof.json"),
                );
            }
            ProvingLimit::Snark => todo!(),
        }
    } else {
        proof_list.write_to_directory(Path::new(output_dir));

        serialize_to_file(
            &proof_metadata,
            &Path::new(output_dir).join("metadata.json"),
        )
    }

    if gpu_state.is_some() {
        println!(
            "**** Total time on production critical path {:.3}s ****",
            total_proof_time.unwrap(),
        );
    }
}

pub fn load_binary_from_path(path: &String) -> Vec<u32> {
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    get_padded_binary(&buffer)
}

// For now, we share the setup cache, only for GPU (as we really care for performance there).
#[cfg(feature = "gpu")]
pub struct GpuSharedState {
    pub prover: gpu_prover::execution::prover::ExecutionProver<usize>,
}

#[cfg(feature = "gpu")]
impl GpuSharedState {
    const MAIN_BINARY_KEY: usize = 0;
    const RECURSION_BINARY_KEY: usize = 1;

    #[cfg(feature = "gpu")]
    pub fn new(binary: &Vec<u32>, recursion_circuit_type: MainCircuitType) -> Self {
        use gpu_prover::execution::prover::ExecutableBinary;
        use gpu_prover::execution::prover::ExecutionProver;

        // We don't support MainCircuitType::FinalReducedRiscVMachine on GPU for now
        // it's too big (2^25 rows).
        assert!(
            recursion_circuit_type == MainCircuitType::ReducedRiscVMachine
                || recursion_circuit_type == MainCircuitType::ReducedRiscVLog23Machine
        );

        let main_binary = ExecutableBinary {
            key: Self::MAIN_BINARY_KEY,
            circuit_type: MainCircuitType::RiscVCycles,
            bytecode: binary.clone(),
        };
        let recursion_binary = ExecutableBinary {
            key: Self::RECURSION_BINARY_KEY,
            circuit_type: recursion_circuit_type,
            bytecode: get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER),
        };
        let prover = ExecutionProver::new(1, vec![main_binary, recursion_binary]);
        Self { prover }
    }
}

#[cfg(not(feature = "gpu"))]
pub struct GpuSharedState<'a> {
    _phantom: std::marker::PhantomData<&'a ()>,
}

#[cfg(not(feature = "gpu"))]
impl<'a> GpuSharedState<'a> {
    pub fn new(_binary: &Vec<u32>) -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

pub fn create_proofs_internal(
    binary: &Vec<u32>,
    non_determinism_data: Vec<u32>,
    machine: &Machine,
    num_instances: usize,
    prev_end_params_output: Option<([u32; 8], Option<[u32; 16]>)>,
    gpu_shared_state: &mut Option<&mut GpuSharedState>,
    total_proof_time: &mut Option<f64>,
) -> (ProofList, ProofMetadata) {
    let worker = worker::Worker::new();

    let mut non_determinism_source = QuasiUARTSource::default();

    for entry in non_determinism_data {
        non_determinism_source.oracle.push_back(entry);
    }

    let (proof_list, register_values) = match machine {
        Machine::Standard => {
            if prev_end_params_output.is_some() {
                panic!("Are you sure that you want to pass --prev-metadata to basic proof?");
            }
            let (basic_proofs, delegation_proofs, register_values) =
                if let Some(gpu_shared_state) = gpu_shared_state {
                    #[cfg(feature = "gpu")]
                    {
                        println!("**** proving using GPU ****");
                        let timer = std::time::Instant::now();
                        let (final_register_values, basic_proofs, delegation_proofs) =
                            gpu_shared_state.prover.commit_memory_and_prove(
                                0,
                                &GpuSharedState::MAIN_BINARY_KEY,
                                num_instances,
                                non_determinism_source,
                            );
                        let elapsed = timer.elapsed().as_secs_f64();
                        *total_proof_time.as_mut().unwrap() += elapsed;
                        println!("**** proofs generated in {:.3}s ****", elapsed,);
                        (
                            basic_proofs,
                            delegation_proofs,
                            final_register_values.into(),
                        )
                    }
                    #[cfg(not(feature = "gpu"))]
                    {
                        let _ = gpu_shared_state;
                        let _ = total_proof_time;
                        panic!("GPU not enabled - please compile with --features gpu flag.")
                    }
                } else {
                    let main_circuit_precomputations =
                        setups::get_main_riscv_circuit_setup::<Global, Global>(&binary, &worker);
                    let delegation_precomputations =
                        setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

                    prover_examples::prove_image_execution(
                        num_instances,
                        &binary,
                        non_determinism_source,
                        &main_circuit_precomputations,
                        &delegation_precomputations,
                        &worker,
                    )
                };

            (
                ProofList {
                    basic_proofs,
                    reduced_proofs: vec![],
                    reduced_log_23_proofs: vec![],
                    final_proofs: vec![],
                    delegation_proofs,
                },
                register_values,
            )
        }
        Machine::Reduced => {
            let (reduced_proofs, delegation_proofs, register_values) =
                if let Some(gpu_shared_state) = gpu_shared_state {
                    #[cfg(feature = "gpu")]
                    {
                        println!("**** proving using GPU ****");
                        let timer = std::time::Instant::now();
                        let (final_register_values, basic_proofs, delegation_proofs) =
                            gpu_shared_state.prover.commit_memory_and_prove(
                                0,
                                &GpuSharedState::RECURSION_BINARY_KEY,
                                num_instances,
                                non_determinism_source,
                            );
                        let elapsed = timer.elapsed().as_secs_f64();
                        *total_proof_time.as_mut().unwrap() += elapsed;
                        println!("**** proofs generated in {:.3}s ****", elapsed);
                        (
                            basic_proofs,
                            delegation_proofs,
                            final_register_values.into(),
                        )
                    }
                    #[cfg(not(feature = "gpu"))]
                    {
                        let _ = gpu_shared_state;
                        let _ = total_proof_time;
                        panic!("GPU not enabled - please compile with --features gpu flag.")
                    }
                } else {
                    let main_circuit_precomputations =
                        setups::get_reduced_riscv_circuit_setup::<Global, Global>(&binary, &worker);
                    let delegation_precomputations =
                        setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

                    prover_examples::prove_image_execution_on_reduced_machine(
                        num_instances,
                        &binary,
                        non_determinism_source,
                        &main_circuit_precomputations,
                        &delegation_precomputations,
                        &worker,
                    )
                };

            (
                ProofList {
                    basic_proofs: vec![],
                    reduced_proofs,
                    reduced_log_23_proofs: vec![],
                    final_proofs: vec![],
                    delegation_proofs,
                },
                register_values,
            )
        }
        Machine::ReducedLog23 => {
            let (reduced_log_23_proofs, delegation_proofs, register_values) =
                if let Some(gpu_shared_state) = gpu_shared_state {
                    #[cfg(feature = "gpu")]
                    {
                        println!("**** proving using GPU ****");
                        let timer = std::time::Instant::now();
                        let (final_register_values, basic_proofs, delegation_proofs) =
                            gpu_shared_state.prover.commit_memory_and_prove(
                                0,
                                &GpuSharedState::RECURSION_BINARY_KEY,
                                num_instances,
                                non_determinism_source,
                            );
                        let elapsed = timer.elapsed().as_secs_f64();
                        *total_proof_time.as_mut().unwrap() += elapsed;
                        println!("**** proofs generated in {:.3}s ****", elapsed);
                        (
                            basic_proofs,
                            delegation_proofs,
                            final_register_values.into(),
                        )
                    }
                    #[cfg(not(feature = "gpu"))]
                    {
                        let _ = gpu_shared_state;
                        let _ = total_proof_time;
                        panic!("GPU not enabled - please compile with --features gpu flag.")
                    }
                } else {
                    let main_circuit_precomputations =
                        setups::get_reduced_riscv_log_23_circuit_setup::<Global, Global>(
                            &binary, &worker,
                        );

                    let delegation_precomputations =
                        setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

                    prover_examples::prove_image_execution_on_reduced_machine(
                        num_instances,
                        &binary,
                        non_determinism_source,
                        &main_circuit_precomputations,
                        &delegation_precomputations,
                        &worker,
                    )
                };

            (
                ProofList {
                    basic_proofs: vec![],
                    reduced_proofs: vec![],
                    reduced_log_23_proofs,
                    final_proofs: vec![],
                    delegation_proofs,
                },
                register_values,
            )
        }
        Machine::ReducedFinal => {
            let main_circuit_precomputations =
                setups::get_final_reduced_riscv_circuit_setup::<Global, Global>(&binary, &worker);

            let delegation_precomputations =
                setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

            let (final_proofs, delegation_proofs, register_values) =
                prover_examples::prove_image_execution_on_final_reduced_machine(
                    num_instances,
                    &binary,
                    non_determinism_source,
                    &main_circuit_precomputations,
                    &delegation_precomputations,
                    &worker,
                );
            if delegation_proofs.len() != 0 {
                panic!("Expected no delegation proofs for final reduced machine.");
            }

            (
                ProofList {
                    basic_proofs: vec![],
                    reduced_proofs: vec![],
                    reduced_log_23_proofs: vec![],
                    final_proofs,
                    delegation_proofs: vec![],
                },
                register_values,
            )
        }
    };

    let total_delegation_proofs: usize = proof_list
        .delegation_proofs
        .iter()
        .map(|(_, x)| x.len())
        .sum();

    println!(
        "Created {} basic proofs, {} reduced proofs, {} reduced (log23) proofs and {} delegation proofs. Final proofs: {}",
        proof_list.basic_proofs.len(),
        proof_list.reduced_proofs.len(),
        proof_list.reduced_log_23_proofs.len(),
        total_delegation_proofs,
        proof_list.final_proofs.len()
    );
    let last_proof = proof_list.get_last_proof();

    let (end_params, prev_end_params_output) =
        get_end_params_output(last_proof, prev_end_params_output);

    let prev_end_params_output_hash = prev_end_params_output.map(|data| {
        let mut tmp_hash = Blake2sBufferingTranscript::new();
        tmp_hash.absorb(&data);
        tmp_hash.finalize().0
    });

    let proof_metadata = ProofMetadata {
        basic_proof_count: proof_list.basic_proofs.len(),
        reduced_proof_count: proof_list.reduced_proofs.len(),
        reduced_log_23_proof_count: proof_list.reduced_log_23_proofs.len(),
        final_proof_count: proof_list.final_proofs.len(),
        delegation_proof_count: proof_list
            .delegation_proofs
            .iter()
            .map(|(i, x)| (i.clone() as u32, x.len()))
            .collect::<Vec<_>>(),
        register_values,
        end_params,
        prev_end_params_output_hash,
        prev_end_params_output,
    };

    (proof_list, proof_metadata)
}

pub fn create_recursion_proofs(
    proof_list: ProofList,
    proof_metadata: ProofMetadata,
    recursion_mode: RecursionStrategy,
    tmp_dir: &Option<String>,
    gpu_shared_state: &mut Option<&mut GpuSharedState>,
    total_proof_time: &mut Option<f64>,
) -> (ProofList, ProofMetadata) {
    assert!(
        proof_metadata.basic_proof_count > 0,
        "Recursion proofs can be created only for basic proofs.",
    );
    let binary = get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER);

    let mut recursion_level = 0;
    let mut current_proof_list = proof_list;
    let mut current_proof_metadata = proof_metadata.clone();

    loop {
        if recursion_mode.skip_first_layer() {
            println!("Skipping recursion.");
            break;
        }

        println!("*** Starting recursion level {} ***", recursion_level);
        let non_determinism_data = generate_oracle_data_for_universal_verifier(
            &current_proof_metadata,
            &current_proof_list,
        );

        (current_proof_list, current_proof_metadata) = create_proofs_internal(
            &binary,
            non_determinism_data,
            &Machine::Reduced,
            current_proof_metadata.total_proofs(),
            Some(current_proof_metadata.create_prev_metadata()),
            gpu_shared_state,
            total_proof_time,
        );

        if let Some(tmp_dir) = tmp_dir {
            let base_tmp_dir = Path::new(tmp_dir).join(format!("recursion_{}", recursion_level));
            if !base_tmp_dir.exists() {
                fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
            }
            current_proof_list.write_to_directory(&base_tmp_dir);
            serialize_to_file(&current_proof_metadata, &base_tmp_dir.join("metadata.json"))
        }

        recursion_level += 1;

        if recursion_mode.switch_to_second_recursion_layer(&current_proof_metadata) {
            println!("Stopping 1st recursion layer.");
            break;
        }
    }
    (current_proof_list, current_proof_metadata)
}

pub fn create_final_proofs_from_program_proof(
    input: ProgramProof,
    recursion_mode: RecursionStrategy,
    use_gpu: bool,
) -> ProgramProof {
    let (proof_metadata, proof_list) = input.to_metadata_and_proof_list();

    let (mut gpu_state, mut total_proof_time) = if use_gpu {
        assert!(
            recursion_mode != RecursionStrategy::UseFinalMachine,
            "GPU is not supported for final machine recursion."
        );

        #[cfg(feature = "gpu")]
        {
            // Here we use GPU for final recursion layer only.
            use gpu_prover::circuit_type::MainCircuitType;
            let recursion_circuit_type = MainCircuitType::ReducedRiscVLog23Machine;
            let binary = get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER);
            (
                Some(GpuSharedState::new(&binary, recursion_circuit_type)),
                Some(0f64),
            )
        }

        #[cfg(not(feature = "gpu"))]
        {
            panic!("GPU not enabled - please compile with --features gpu flag.")
        }
    } else {
        (None, None)
    };
    let mut gpu_state = gpu_state.as_mut();

    create_final_proofs(
        proof_list,
        proof_metadata,
        recursion_mode,
        &None,
        &mut gpu_state,
        &mut total_proof_time,
    )
}

pub fn create_final_proofs(
    proof_list: ProofList,
    proof_metadata: ProofMetadata,
    recursion_mode: RecursionStrategy,
    tmp_dir: &Option<String>,
    gpu_shared_state: &mut Option<&mut GpuSharedState>,
    total_proof_time: &mut Option<f64>,
) -> ProgramProof {
    let binary = recursion_mode.get_second_layer_binary();
    let machine = recursion_mode.get_second_layer_machine();

    let mut final_proof_level = 0;
    let mut current_proof_list = proof_list;
    let mut current_proof_metadata = proof_metadata.clone();

    loop {
        println!("*** Starting final_proofs level {} ***", final_proof_level);
        let non_determinism_data = generate_oracle_data_for_universal_verifier(
            &current_proof_metadata,
            &current_proof_list,
        );
        (current_proof_list, current_proof_metadata) = create_proofs_internal(
            &binary,
            non_determinism_data,
            &machine,
            current_proof_metadata.total_proofs(),
            Some(current_proof_metadata.create_prev_metadata()),
            gpu_shared_state,
            total_proof_time,
        );
        if let Some(tmp_dir) = tmp_dir {
            let base_tmp_dir = Path::new(tmp_dir).join(format!("final_{}", final_proof_level));
            if !base_tmp_dir.exists() {
                fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
            }
            current_proof_list.write_to_directory(&base_tmp_dir);
            serialize_to_file(&current_proof_metadata, &base_tmp_dir.join("metadata.json"))
        }

        if recursion_mode.finish_second_recursion_layer(&current_proof_metadata, final_proof_level)
        {
            println!("Stopping 2nd recursion layer.");
            break;
        }

        final_proof_level += 1;
    }

    ProgramProof::from_proof_list_and_metadata(&current_proof_list, &current_proof_metadata)
}

pub fn get_end_params_output_suffix_from_proof(last_proof: &Proof) -> Option<Seed> {
    if last_proof.public_inputs.len() != 4 {
        // We can compute this only for proofs with public inputs.
        return None;
    }

    let end_pc = parse_field_els_as_u32_from_u16_limbs_checked([
        last_proof.public_inputs[2],
        last_proof.public_inputs[3],
    ]);

    // We have to compute the the hash of the final program counter, and program binary (setup tree).
    let mut hasher = Blake2sBufferingTranscript::new();
    hasher.absorb(&[end_pc]);

    for cap in &last_proof.setup_tree_caps {
        for entry in cap.cap.iter() {
            hasher.absorb(entry);
        }
    }
    Some(hasher.finalize_reset())
}

/// Returns end_params, prev params
fn get_end_params_output(
    last_proof: &Proof,
    prev_end_params_output: Option<([u32; 8], Option<[u32; 16]>)>,
) -> ([u32; 8], Option<[u32; 16]>) {
    // we need PC from the last proof.
    let end_params_output_suffix = get_end_params_output_suffix_from_proof(last_proof).unwrap();
    // This describes the binary that we run.
    let end_params = end_params_output_suffix.0;

    let new_preimage = match prev_end_params_output {
        // This arm means, that we're in the recursion layer.
        Some((prev_bin, prev_params)) => match prev_params {
            // We know that this was the previous binary, and the parameters that it accepted.
            Some(prev_params) => {
                // Now there are 2 options - either the previous binary was proving its own code
                // (if we're in the second stage of recursion). Then let's not change the prev params.
                if prev_params[8..16] == prev_bin {
                    Some(prev_params)
                } else {
                    // Or previous binary could be different - then we should update the chain,
                    // by computing (hash(previous) || prev_bin).
                    let mut end_params_output = [0u32; 16];
                    let mut hasher = Blake2sBufferingTranscript::new();
                    hasher.absorb(&prev_params);
                    let prev_params_hash = hasher.finalize().0;

                    for i in 0..8 {
                        end_params_output[i] = prev_params_hash[i];
                    }
                    for i in 8..16 {
                        end_params_output[i] = prev_bin[i - 8];
                    }

                    Some(end_params_output)
                }
            }
            // This means that we're verifying the base layer.
            None => {
                let mut end_params_output = [0u32; 16];
                for i in 8..16 {
                    end_params_output[i] = prev_bin[i - 8];
                }
                Some(end_params_output)
            }
        },
        // For base layer.
        None => None,
    };

    return (end_params, new_preimage);
}

pub fn generate_oracle_data_from_metadata(metadata_path: &String) -> (ProofMetadata, Vec<u32>) {
    // This will handle all the verifictations - we just have to pass it the data in the right format.

    let metadata: ProofMetadata = deserialize_from_file(&metadata_path);
    let parent = Path::new(metadata_path).parent().unwrap();
    println!("Guessing parent to be {:?}", parent);

    let proof_list =
        ProofList::load_from_directory(&parent.to_str().unwrap().to_string(), &metadata);
    let oracle_data = generate_oracle_data_from_metadata_and_proof_list(&metadata, &proof_list);
    (metadata, oracle_data)
}
