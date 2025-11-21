use clap::ValueEnum;
pub use execution_utils::{
    generate_oracle_data_for_universal_verifier, generate_oracle_data_from_metadata_and_proof_list,
    get_padded_binary, Machine, ProgramProof, ProofList, ProofMetadata, RecursionStrategy,
};
use execution_utils::{
    unrolled::{
        flatten_proof_into_responses_for_unrolled_recursion, UnrolledProgramProof,
        UnrolledProgramSetup,
    },
    // verifier_binaries::UNIVERSAL_CIRCUIT_VERIFIER,
};
#[cfg(feature = "gpu")]
use gpu_prover::{
    execution::prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration},
    machine_type::MachineType,
};
use setups::{pad_binary, read_and_pad_binary, CompiledCircuitsSet};
use verifier_common::parse_field_els_as_u32_from_u16_limbs_checked;

use prover::{
    prover_stages::Proof,
    risc_v_simulator::{
        abstractions::non_determinism::QuasiUARTSource,
        cycle::{IMStandardIsaConfigWithUnsignedMulDiv, IWithoutByteAccessIsaConfigWithDelegation},
    },
    transcript::{Blake2sBufferingTranscript, Seed},
};
use std::{alloc::Global, fs, io::Read, path::Path};

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

#[cfg(feature = "gpu")]
pub fn multi_prove(bin_path: &String, input_files: Vec<Vec<u32>>) {
    todo!();
    /*
    let binary = load_binary_from_path(bin_path);

    // TODO: hardcoded for now.
    let num_instances = 500;
    // Let's use v23 circuits everywhere.
    let recursion_mode = RecursionStrategy::UseReducedLog23MachineInBothLayers;

    let recursion_circuit_type = MainCircuitType::ReducedRiscVLog23Machine;
    let mut gpu_state = Some(GpuSharedState::new(&binary, recursion_circuit_type));

    let mut gpu_state = gpu_state.as_mut();

    let mut final_results = vec![];

    for (i, non_determinism_data) in input_files.into_iter().enumerate() {
        let mut total_proof_time = Some(0f64);

        let (proof_list, proof_metadata) = create_proofs_internal(
            &binary,
            non_determinism_data,
            &Machine::Standard,
            num_instances,
            None,
            &mut gpu_state,
            &mut total_proof_time,
        );

        let (_recursion_proof_list, _recursion_proof_metadata) = create_recursion_proofs(
            proof_list,
            proof_metadata,
            recursion_mode,
            &None,
            &mut gpu_state,
            &mut total_proof_time,
        );
        // Currently we don't store the final proofs (as this is mostly for performance testing).
        println!(
            "**** {} Total time on production critical path {:.3}s ****",
            i,
            total_proof_time.unwrap(),
        );
        final_results.push(total_proof_time.unwrap());
    }

    println!("**** Multi-prove summary ****");
    for (i, time) in final_results.iter().enumerate() {
        println!("Input {}: total proof time {:.3}s", i, time);
    }
    */
}

// pub fn create_proofs(
//     bin_path: &String,
//     output_dir: &String,
//     input_data: Option<Vec<u32>>,
//     prev_metadata: &Option<String>,
//     machine: &Machine,
//     cycles: &Option<usize>,
//     until: &Option<ProvingLimit>,
//     recursion_mode: RecursionStrategy,
//     tmp_dir: &Option<String>,
//     use_gpu: bool,
// ) {
//     let prev_metadata: Option<ProofMetadata> = prev_metadata
//         .as_ref()
//         .map(|prev_metadata| deserialize_from_file(&prev_metadata));

//     let binary = load_binary_from_path(bin_path);

//     let num_instances = (cycles.unwrap_or(DEFAULT_CYCLES) / risc_v_cycles::NUM_CYCLES) + 1;

//     println!(
//         "Will try proving now, with up to {} circuits.",
//         num_instances
//     );

//     let non_determinism_data = input_data.unwrap_or_default();

//     // Serialization and deserialization of artifacts
//     // (as requested by user arguments) can take a lot of time,
//     // and typically won't be needed in production.
//     // total_proof_time accumulates the actual time spent on
//     // the production critical path
//     // (tracing, witness generation, proving, recursion).
//     let (mut gpu_state, mut total_proof_time) = if use_gpu {
//         // In this function we only use the GPU for the base and 1st recursion layer (reduced 2^22 machine).
//         // In order to use it for the 2nd recursion layer, you should call `create_final_proofs_from_program_proof`
//         #[cfg(feature = "gpu")]
//         {
//             (Some(GpuSharedState::new(&binary)), Some(0f64))
//         }
//         #[cfg(not(feature = "gpu"))]
//         {
//             panic!("Compiled without GPU support, but --use-gpu is set.");
//         }
//     } else {
//         (None, None)
//     };
//     let mut gpu_state = gpu_state.as_mut();

//     let (proof_list, proof_metadata) = create_proofs_internal(
//         &binary,
//         non_determinism_data,
//         machine,
//         num_instances,
//         prev_metadata.map(|x| x.create_prev_metadata()),
//         &mut gpu_state,
//         &mut total_proof_time,
//     );

//     // Now we finished 'basic' proving - check if there is a need for recursion.
//     if let Some(until) = until {
//         assert_eq!(
//             machine,
//             &Machine::Standard,
//             "Recursion is only supported after Standard machine"
//         );

//         if let Some(tmp_dir) = tmp_dir {
//             let base_tmp_dir = Path::new(tmp_dir).join("base");
//             if !base_tmp_dir.exists() {
//                 fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
//             }
//             proof_list.write_to_directory(&base_tmp_dir);
//             serialize_to_file(&proof_metadata, &base_tmp_dir.join("metadata.json"))
//         }
//         let (recursion_proof_list, recursion_proof_metadata) = create_recursion_proofs(
//             proof_list,
//             proof_metadata,
//             recursion_mode,
//             tmp_dir,
//             &mut gpu_state,
//             &mut total_proof_time,
//         );
//         match until {
//             ProvingLimit::FinalRecursion => {
//                 recursion_proof_list.write_to_directory(Path::new(output_dir));

//                 serialize_to_file(
//                     &recursion_proof_metadata,
//                     &Path::new(output_dir).join("metadata.json"),
//                 );
//                 let program_proof = ProgramProof::from_proof_list_and_metadata(
//                     &recursion_proof_list,
//                     &recursion_proof_metadata,
//                 );
//                 serialize_to_file(
//                     &program_proof,
//                     &Path::new(output_dir).join("recursion_program_proof.json"),
//                 );
//             }
//             ProvingLimit::FinalProof => {
//                 // Here we support only CPU proving, mostly for testing purposes.
//                 // In order to use GPU for 2nd recursion layer, please call `create_final_proofs_from_program_proof`
//                 let program_proof = create_final_proofs(
//                     recursion_proof_list,
//                     recursion_proof_metadata,
//                     recursion_mode,
//                     tmp_dir,
//                     &mut None,
//                     &mut None,
//                 );

//                 serialize_to_file(
//                     &program_proof,
//                     &Path::new(output_dir).join("final_program_proof.json"),
//                 );
//             }
//             ProvingLimit::Snark => todo!(),
//         }
//     } else {
//         proof_list.write_to_directory(Path::new(output_dir));

//         serialize_to_file(
//             &proof_metadata,
//             &Path::new(output_dir).join("metadata.json"),
//         )
//     }

//     if gpu_state.is_some() {
//         println!(
//             "**** Total time on production critical path {:.3}s ****",
//             total_proof_time.unwrap(),
//         );
//     }
// }

pub fn load_binary_from_path(path: &String) -> Vec<u32> {
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    get_padded_binary(&buffer)
}

// For now, we share the setup cache, only for GPU (as we really care for performance there).
#[cfg(feature = "gpu")]
pub struct GpuSharedState {
    pub prover: gpu_prover::execution::prover::ExecutionProver,
}

#[cfg(feature = "gpu")]
impl GpuSharedState {
    const MAIN_BINARY_KEY: usize = 0;
    const RECURSION_BINARY_KEY: usize = 1;

    #[cfg(feature = "gpu")]
    pub fn new(binary: &Vec<u32>) -> Self {
        use execution_utils::verifier_binaries::UNIVERSAL_CIRCUIT_VERIFIER;
        use gpu_prover::execution::prover::ExecutionProver;
        use gpu_prover::execution::prover::ExecutionProverConfiguration;

        /*let main_binary = ExecutableBinary {
            key: Self::MAIN_BINARY_KEY,
            circuit_type: MainCircuitType::RiscVCycles,
            bytecode: binary.clone(),
        };
        let recursion_binary = ExecutableBinary {
            key: Self::RECURSION_BINARY_KEY,
            circuit_type: recursion_circuit_type,
            bytecode: get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER),
        };*/
        let mut configuration = ExecutionProverConfiguration::default();
        configuration.replay_worker_threads_count = 8;
        let prover = ExecutionProver::with_configuration(configuration);

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

// pub fn create_proofs_internal(
//     binary: &Vec<u32>,
//     non_determinism_data: Vec<u32>,
//     machine: &Machine,
//     num_instances: usize,
//     prev_end_params_output: Option<([u32; 8], Option<[u32; 16]>)>,
//     gpu_shared_state: &mut Option<&mut GpuSharedState>,
//     total_proof_time: &mut Option<f64>,
// ) -> (ProofList, ProofMetadata) {
//     let worker = worker::Worker::new();

//     let mut non_determinism_source = QuasiUARTSource::default();

//     for entry in non_determinism_data {
//         non_determinism_source.oracle.push_back(entry);
//     }

//     let (proof_list, register_values) = match machine {
//         Machine::Standard => {
//             if prev_end_params_output.is_some() {
//                 panic!("Are you sure that you want to pass --prev-metadata to basic proof?");
//             }
//             let (basic_proofs, delegation_proofs, register_values) =
//                 if let Some(gpu_shared_state) = gpu_shared_state {
//                     #[cfg(feature = "gpu")]
//                     {
//                         println!("**** proving using GPU ****");
//                         let timer = std::time::Instant::now();
//                         /*let (final_register_values, basic_proofs, delegation_proofs) =
//                             gpu_shared_state.prover.commit_memory_and_prove(
//                                 0,
//                                 &GpuSharedState::MAIN_BINARY_KEY,
//                                 num_instances,
//                                 non_determinism_source,
//                             );
//                         let elapsed = timer.elapsed().as_secs_f64();
//                         *total_proof_time.as_mut().unwrap() += elapsed;
//                         println!("**** proofs generated in {:.3}s ****", elapsed,);
//                         (
//                             basic_proofs,
//                             delegation_proofs,
//                             final_register_values.into(),
//                         )*/
//                         todo!()
//                     }
//                     #[cfg(not(feature = "gpu"))]
//                     {
//                         let _ = gpu_shared_state;
//                         let _ = total_proof_time;
//                         panic!("GPU not enabled - please compile with --features gpu flag.")
//                     }
//                 } else {
//                     let main_circuit_precomputations =
//                         setups::get_main_riscv_circuit_setup::<Global, Global>(&binary, &worker);
//                     let delegation_precomputations =
//                         setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

//                     prover_examples::prove_image_execution(
//                         num_instances,
//                         &binary,
//                         non_determinism_source,
//                         &main_circuit_precomputations,
//                         &delegation_precomputations,
//                         &worker,
//                     )
//                 };

//             (
//                 ProofList {
//                     basic_proofs,
//                     reduced_proofs: vec![],
//                     reduced_log_23_proofs: vec![],
//                     delegation_proofs,
//                 },
//                 register_values,
//             )
//         }
//         Machine::Reduced => {
//             let (reduced_proofs, delegation_proofs, register_values) =
//                 if let Some(gpu_shared_state) = gpu_shared_state {
//                     #[cfg(feature = "gpu")]
//                     {
//                         println!("**** proving using GPU ****");
//                         let timer = std::time::Instant::now();
//                         /*let (final_register_values, basic_proofs, delegation_proofs) =
//                             gpu_shared_state.prover.commit_memory_and_prove(
//                                 0,
//                                 &GpuSharedState::RECURSION_BINARY_KEY,
//                                 num_instances,
//                                 non_determinism_source,
//                             );
//                         let elapsed = timer.elapsed().as_secs_f64();
//                         *total_proof_time.as_mut().unwrap() += elapsed;
//                         println!("**** proofs generated in {:.3}s ****", elapsed);
//                         (
//                             basic_proofs,
//                             delegation_proofs,
//                             final_register_values.into(),
//                         )*/
//                         todo!()
//                     }
//                     #[cfg(not(feature = "gpu"))]
//                     {
//                         let _ = gpu_shared_state;
//                         let _ = total_proof_time;
//                         panic!("GPU not enabled - please compile with --features gpu flag.")
//                     }
//                 } else {
//                     let main_circuit_precomputations =
//                         setups::get_reduced_riscv_circuit_setup::<Global, Global>(&binary, &worker);
//                     let delegation_precomputations =
//                         setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

//                     prover_examples::prove_image_execution_on_reduced_machine(
//                         num_instances,
//                         &binary,
//                         non_determinism_source,
//                         &main_circuit_precomputations,
//                         &delegation_precomputations,
//                         &worker,
//                     )
//                 };

//             (
//                 ProofList {
//                     basic_proofs: vec![],
//                     reduced_proofs,
//                     reduced_log_23_proofs: vec![],
//                     delegation_proofs,
//                 },
//                 register_values,
//             )
//         }
//         Machine::ReducedLog23 => {
//             let (reduced_log_23_proofs, delegation_proofs, register_values) =
//                 if let Some(gpu_shared_state) = gpu_shared_state {
//                     #[cfg(feature = "gpu")]
//                     {
//                         println!("**** proving using GPU ****");
//                         let timer = std::time::Instant::now();
//                         /*let (final_register_values, basic_proofs, delegation_proofs) =
//                             gpu_shared_state.prover.commit_memory_and_prove(
//                                 0,
//                                 &GpuSharedState::RECURSION_BINARY_KEY,
//                                 num_instances,
//                                 non_determinism_source,
//                             );
//                         let elapsed = timer.elapsed().as_secs_f64();
//                         *total_proof_time.as_mut().unwrap() += elapsed;
//                         println!("**** proofs generated in {:.3}s ****", elapsed);
//                         (
//                             basic_proofs,
//                             delegation_proofs,
//                             final_register_values.into(),
//                         )*/
//                         todo!()
//                     }
//                     #[cfg(not(feature = "gpu"))]
//                     {
//                         let _ = gpu_shared_state;
//                         let _ = total_proof_time;
//                         panic!("GPU not enabled - please compile with --features gpu flag.")
//                     }
//                 } else {
//                     let main_circuit_precomputations =
//                         setups::get_reduced_riscv_log_23_circuit_setup::<Global, Global>(
//                             &binary, &worker,
//                         );

//                     let delegation_precomputations =
//                         setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

//                     prover_examples::prove_image_execution_on_reduced_machine(
//                         num_instances,
//                         &binary,
//                         non_determinism_source,
//                         &main_circuit_precomputations,
//                         &delegation_precomputations,
//                         &worker,
//                     )
//                 };

//             (
//                 ProofList {
//                     basic_proofs: vec![],
//                     reduced_proofs: vec![],
//                     reduced_log_23_proofs,
//                     delegation_proofs,
//                 },
//                 register_values,
//             )
//         }
//     };

//     let total_delegation_proofs: usize = proof_list
//         .delegation_proofs
//         .iter()
//         .map(|(_, x)| x.len())
//         .sum();

//     println!(
//         "Created {} basic proofs, {} reduced proofs, {} reduced (log23) proofs and {} delegation proofs.",
//         proof_list.basic_proofs.len(),
//         proof_list.reduced_proofs.len(),
//         proof_list.reduced_log_23_proofs.len(),
//         total_delegation_proofs,
//     );
//     let last_proof = proof_list.get_last_proof();

//     let (end_params, prev_end_params_output) =
//         get_end_params_output(last_proof, prev_end_params_output);

//     let prev_end_params_output_hash = prev_end_params_output.map(|data| {
//         let mut tmp_hash = Blake2sBufferingTranscript::new();
//         tmp_hash.absorb(&data);
//         tmp_hash.finalize().0
//     });

//     let proof_metadata = ProofMetadata {
//         basic_proof_count: proof_list.basic_proofs.len(),
//         reduced_proof_count: proof_list.reduced_proofs.len(),
//         reduced_log_23_proof_count: proof_list.reduced_log_23_proofs.len(),
//         deprecated_final_proof_count: 0,
//         delegation_proof_count: proof_list
//             .delegation_proofs
//             .iter()
//             .map(|(i, x)| (i.clone() as u32, x.len()))
//             .collect::<Vec<_>>(),
//         register_values,
//         end_params,
//         prev_end_params_output_hash,
//         prev_end_params_output,
//     };

//     (proof_list, proof_metadata)
// }

// pub fn create_recursion_proofs(
//     proof_list: ProofList,
//     proof_metadata: ProofMetadata,
//     recursion_mode: RecursionStrategy,
//     tmp_dir: &Option<String>,
//     gpu_shared_state: &mut Option<&mut GpuSharedState>,
//     total_proof_time: &mut Option<f64>,
// ) -> (ProofList, ProofMetadata) {
//     assert!(
//         proof_metadata.basic_proof_count > 0,
//         "Recursion proofs can be created only for basic proofs.",
//     );
//     let binary = get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER);

//     let mut recursion_level = 0;
//     let mut current_proof_list = proof_list;
//     let mut current_proof_metadata = proof_metadata.clone();

//     let machine = if recursion_mode == RecursionStrategy::UseReducedLog23MachineInBothLayers {
//         &Machine::ReducedLog23
//     } else {
//         &Machine::Reduced
//     };

//     // Small sanity check, to make sure that GPU state matches the chosen machine.
//     #[cfg(feature = "gpu")]
//     if let Some(gpu_shared_state) = gpu_shared_state {}

//     loop {
//         if recursion_mode.skip_first_layer() {
//             println!("Skipping recursion.");
//             break;
//         }

//         println!("*** Starting recursion level {} ***", recursion_level);
//         let non_determinism_data = generate_oracle_data_for_universal_verifier(
//             &current_proof_metadata,
//             &current_proof_list,
//         );

//         (current_proof_list, current_proof_metadata) = create_proofs_internal(
//             &binary,
//             non_determinism_data,
//             machine,
//             current_proof_metadata.total_proofs(),
//             Some(current_proof_metadata.create_prev_metadata()),
//             gpu_shared_state,
//             total_proof_time,
//         );

//         if let Some(tmp_dir) = tmp_dir {
//             let base_tmp_dir = Path::new(tmp_dir).join(format!("recursion_{}", recursion_level));
//             if !base_tmp_dir.exists() {
//                 fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
//             }
//             current_proof_list.write_to_directory(&base_tmp_dir);
//             serialize_to_file(&current_proof_metadata, &base_tmp_dir.join("metadata.json"))
//         }

//         recursion_level += 1;

//         if recursion_mode.switch_to_second_recursion_layer(&current_proof_metadata) {
//             println!("Stopping 1st recursion layer.");
//             break;
//         }
//     }
//     (current_proof_list, current_proof_metadata)
// }

// pub fn create_final_proofs_from_program_proof(
//     input: ProgramProof,
//     recursion_mode: RecursionStrategy,
//     use_gpu: bool,
// ) -> ProgramProof {
//     let (proof_metadata, proof_list) = input.to_metadata_and_proof_list();

//     let (mut gpu_state, mut total_proof_time) = if use_gpu {
//         #[cfg(feature = "gpu")]
//         {
//             // Here we use GPU for final recursion layer only.
//             let binary = get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER);
//             (Some(GpuSharedState::new(&binary)), Some(0f64))
//         }

//         #[cfg(not(feature = "gpu"))]
//         {
//             panic!("GPU not enabled - please compile with --features gpu flag.")
//         }
//     } else {
//         (None, None)
//     };
//     let mut gpu_state = gpu_state.as_mut();

//     create_final_proofs(
//         proof_list,
//         proof_metadata,
//         recursion_mode,
//         &None,
//         &mut gpu_state,
//         &mut total_proof_time,
//     )
// }

// pub fn create_final_proofs(
//     proof_list: ProofList,
//     proof_metadata: ProofMetadata,
//     recursion_mode: RecursionStrategy,
//     tmp_dir: &Option<String>,
//     gpu_shared_state: &mut Option<&mut GpuSharedState>,
//     total_proof_time: &mut Option<f64>,
// ) -> ProgramProof {
//     let binary = recursion_mode.get_second_layer_binary();
//     let machine = recursion_mode.get_second_layer_machine();

//     let mut final_proof_level = 0;
//     let mut current_proof_list = proof_list;
//     let mut current_proof_metadata = proof_metadata.clone();

//     loop {
//         println!("*** Starting final_proofs level {} ***", final_proof_level);
//         let non_determinism_data = generate_oracle_data_for_universal_verifier(
//             &current_proof_metadata,
//             &current_proof_list,
//         );
//         (current_proof_list, current_proof_metadata) = create_proofs_internal(
//             &binary,
//             non_determinism_data,
//             &machine,
//             current_proof_metadata.total_proofs(),
//             Some(current_proof_metadata.create_prev_metadata()),
//             gpu_shared_state,
//             total_proof_time,
//         );
//         if let Some(tmp_dir) = tmp_dir {
//             let base_tmp_dir = Path::new(tmp_dir).join(format!("final_{}", final_proof_level));
//             if !base_tmp_dir.exists() {
//                 fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
//             }
//             current_proof_list.write_to_directory(&base_tmp_dir);
//             serialize_to_file(&current_proof_metadata, &base_tmp_dir.join("metadata.json"))
//         }

//         if recursion_mode.finish_second_recursion_layer(&current_proof_metadata, final_proof_level)
//         {
//             println!("Stopping 2nd recursion layer.");
//             break;
//         }

//         final_proof_level += 1;
//     }

//     ProgramProof::from_proof_list_and_metadata(&current_proof_list, &current_proof_metadata)
// }

// pub fn get_end_params_output_suffix_from_proof(last_proof: &Proof) -> Option<Seed> {
//     if last_proof.public_inputs.len() != 4 {
//         // We can compute this only for proofs with public inputs.
//         return None;
//     }

//     let end_pc = parse_field_els_as_u32_from_u16_limbs_checked([
//         last_proof.public_inputs[2],
//         last_proof.public_inputs[3],
//     ]);

//     // We have to compute the the hash of the final program counter, and program binary (setup tree).
//     let mut hasher = Blake2sBufferingTranscript::new();
//     hasher.absorb(&[end_pc]);

//     for cap in &last_proof.setup_tree_caps {
//         for entry in cap.cap.iter() {
//             hasher.absorb(entry);
//         }
//     }
//     Some(hasher.finalize_reset())
// }

// /// Returns end_params, prev params
// fn get_end_params_output(
//     last_proof: &Proof,
//     prev_end_params_output: Option<([u32; 8], Option<[u32; 16]>)>,
// ) -> ([u32; 8], Option<[u32; 16]>) {
//     // we need PC from the last proof.
//     let end_params_output_suffix = get_end_params_output_suffix_from_proof(last_proof).unwrap();
//     // This describes the binary that we run.
//     let end_params = end_params_output_suffix.0;

//     let new_preimage = match prev_end_params_output {
//         // This arm means, that we're in the recursion layer.
//         Some((prev_bin, prev_params)) => match prev_params {
//             // We know that this was the previous binary, and the parameters that it accepted.
//             Some(prev_params) => {
//                 // Now there are 2 options - either the previous binary was proving its own code
//                 // (if we're in the second stage of recursion). Then let's not change the prev params.
//                 if prev_params[8..16] == prev_bin {
//                     Some(prev_params)
//                 } else {
//                     // Or previous binary could be different - then we should update the chain,
//                     // by computing (hash(previous) || prev_bin).
//                     let mut end_params_output = [0u32; 16];
//                     let mut hasher = Blake2sBufferingTranscript::new();
//                     hasher.absorb(&prev_params);
//                     let prev_params_hash = hasher.finalize().0;

//                     for i in 0..8 {
//                         end_params_output[i] = prev_params_hash[i];
//                     }
//                     for i in 8..16 {
//                         end_params_output[i] = prev_bin[i - 8];
//                     }

//                     Some(end_params_output)
//                 }
//             }
//             // This means that we're verifying the base layer.
//             None => {
//                 let mut end_params_output = [0u32; 16];
//                 for i in 8..16 {
//                     end_params_output[i] = prev_bin[i - 8];
//                 }
//                 Some(end_params_output)
//             }
//         },
//         // For base layer.
//         None => None,
//     };

//     return (end_params, new_preimage);
// }

// pub fn generate_oracle_data_from_metadata(metadata_path: &String) -> (ProofMetadata, Vec<u32>) {
//     // This will handle all the verifictations - we just have to pass it the data in the right format.

//     let metadata: ProofMetadata = deserialize_from_file(&metadata_path);
//     let parent = Path::new(metadata_path).parent().unwrap();
//     println!("Guessing parent to be {:?}", parent);

//     let proof_list =
//         ProofList::load_from_directory(&parent.to_str().unwrap().to_string(), &metadata);
//     let oracle_data = generate_oracle_data_from_metadata_and_proof_list(&metadata, &proof_list);
//     (metadata, oracle_data)
// }

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
    include_bytes!("../../verifier/recursion_in_unrolled_layer.bin");
pub const RECURSION_UNROLLED_TXT: &[u8] =
    include_bytes!("../../verifier/recursion_in_unrolled_layer.text");

impl UnrolledProver {
    pub fn new(path_without_bin: &String, replay_worker_threads_count: usize) -> Self {
        let base_level = {
            let bin_path = format!("{}.bin", path_without_bin);
            let text_path = format!("{}.text", path_without_bin);

            let (binary, binary_u32) = read_and_pad_binary(Path::new(&bin_path));
            let (text, text_u32) = read_and_pad_binary(Path::new(&text_path));

            println!("Computing base setup");

            let base_layer_setup =
                execution_utils::unrolled::compute_setup_for_machine_configuration::<
                    IMStandardIsaConfigWithUnsignedMulDiv,
                >(&binary, &text);
            let base_layer_compiled_layouts =
                execution_utils::setups::get_unrolled_circuits_artifacts_for_machine_type::<
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

            let setup = execution_utils::unrolled::compute_setup_for_machine_configuration::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&binary, &text);
            let compiled_layouts =
                execution_utils::setups::get_unrolled_circuits_artifacts_for_machine_type::<
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
