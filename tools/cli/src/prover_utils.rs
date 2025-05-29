#[cfg(feature = "gpu")]
use crate::setup::SetupCache;
use crate::Machine;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use clap::ValueEnum;
use execution_utils::{
    get_padded_binary, ProgramProof, UNIVERSAL_CIRCUIT_NO_DELEGATION_VERIFIER,
    UNIVERSAL_CIRCUIT_VERIFIER,
};
use trace_and_split::FinalRegisterValue;
use verifier_common::parse_field_els_as_u32_checked;

use std::{alloc::Global, fs, io::Read, path::Path};

use prover::{
    cs::utils::split_timestamp,
    prover_stages::Proof,
    risc_v_simulator::{
        abstractions::non_determinism::QuasiUARTSource,
        cycle::{IMStandardIsaConfig, IWithoutByteAccessIsaConfigWithDelegation, MachineConfig},
    },
    transcript::{Blake2sBufferingTranscript, Seed},
};
fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}
fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &Path) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

/// Default amount of cycles, if no flag is set.
pub const DEFAULT_CYCLES: usize = 32_000_000;

// Determines when to stop proving.
#[derive(Clone, Debug, ValueEnum)]
pub enum ProvingLimit {
    /// Does base + recursion (reduced machine).
    FinalRecursion,
    /// Also does final proof (requires 128GB of RAM).
    FinalProof,
    /// Also creates a final snark (requires zkos_wrapper)
    Snark,
}

pub enum VerifierCircuitsIdentifiers {
    // This enum is used inside tools/verifier/main.rs
    BaseLayer = 0,
    RecursionLayer = 1,
    FinalLayer = 2,
    RiscV = 3,
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

fn reduced_machine_allowed_delegation_types() -> Vec<u32> {
    IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS.to_vec()
}

fn full_machine_allowed_delegation_types() -> Vec<u32> {
    IMStandardIsaConfig::ALLOWED_DELEGATION_CSRS.to_vec()
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ProofMetadata {
    pub basic_proof_count: usize,
    pub reduced_proof_count: usize,
    pub final_proof_count: usize,
    pub delegation_proof_count: Vec<(u32, usize)>,
    pub register_values: Vec<FinalRegisterValue>,
    // parameters used by the next recursion level.
    pub end_params_output: [u32; 16],
    // blake hash of the end_params_output (for debugging only).
    pub end_params_output_hash: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    // parameters from the previous recursion level.
    pub prev_end_params_output: Option<[u32; 16]>,
}

impl ProofMetadata {
    pub fn total_proofs(&self) -> usize {
        self.basic_proof_count
            + self.reduced_proof_count
            + self.final_proof_count
            + self
                .delegation_proof_count
                .iter()
                .map(|(_, v)| *v)
                .sum::<usize>()
    }
}

pub struct ProofList {
    pub basic_proofs: Vec<Proof>,
    pub reduced_proofs: Vec<Proof>,
    pub final_proofs: Vec<Proof>,
    pub delegation_proofs: Vec<(u32, Vec<Proof>)>,
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
            final_proofs,
            delegation_proofs,
        }
    }

    pub fn get_last_proof(&self) -> &Proof {
        self.final_proofs.last().unwrap_or_else(|| {
            self.basic_proofs.last().unwrap_or_else(|| {
                self.reduced_proofs
                    .last()
                    .expect("Neither main proof nor reduced proof is present")
            })
        })
    }
}

pub fn program_proof_from_proof_list_and_metadata(
    proof_list: &ProofList,
    proof_metadata: &ProofMetadata,
) -> ProgramProof {
    // program proof doesn't distinguish between final, reduced & basic proofs.
    let mut base_layer_proofs = proof_list.final_proofs.clone();
    base_layer_proofs.extend_from_slice(&proof_list.basic_proofs);
    base_layer_proofs.extend_from_slice(&proof_list.reduced_proofs);

    ProgramProof {
        base_layer_proofs,
        delegation_proofs: proof_list.delegation_proofs.clone().into_iter().collect(),
        register_final_values: proof_metadata.register_values.clone(),
        end_params: proof_metadata.end_params_output[8..16].try_into().unwrap(),
        recursion_chain_preimage: proof_metadata.prev_end_params_output,
        recursion_chain_hash: Some(proof_metadata.end_params_output[0..8].try_into().unwrap()),
    }
}
pub fn create_proofs(
    bin_path: &String,
    output_dir: &String,
    input_hex: &Option<String>,
    prev_metadata: &Option<String>,
    machine: &Machine,
    cycles: &Option<usize>,
    until: &Option<ProvingLimit>,
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

    let mut gpu_state = if use_gpu {
        Some(GpuSharedState::default())
    } else {
        None
    };
    let mut gpu_state = gpu_state.as_mut();

    let (proof_list, proof_metadata) = create_proofs_internal(
        &binary,
        non_determinism_data,
        machine,
        num_instances,
        prev_metadata,
        &mut gpu_state,
    );

    // Now we finished 'basic' proving - check if there is a need for recursion.
    if let Some(until) = until {
        if let Some(tmp_dir) = tmp_dir {
            let base_tmp_dir = Path::new(tmp_dir).join("base");
            if !base_tmp_dir.exists() {
                fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
            }
            proof_list.write_to_directory(&base_tmp_dir);
            serialize_to_file(&proof_metadata, &base_tmp_dir.join("metadata.json"))
        }
        let (recursion_proof_list, recursion_proof_metadata, recursion_prev_metadata) =
            create_recursion_proofs(proof_list, proof_metadata, tmp_dir, &mut gpu_state);
        match until {
            ProvingLimit::FinalRecursion => {
                recursion_proof_list.write_to_directory(Path::new(output_dir));

                serialize_to_file(
                    &recursion_proof_metadata,
                    &Path::new(output_dir).join("metadata.json"),
                )
            }
            ProvingLimit::FinalProof => {
                let program_proof = create_final_proofs(
                    recursion_proof_list,
                    recursion_proof_metadata,
                    recursion_prev_metadata,
                    tmp_dir,
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
}

pub fn load_binary_from_path(path: &String) -> Vec<u32> {
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    get_padded_binary(&buffer)
}

fn should_stop_recursion(proof_metadata: &ProofMetadata) -> bool {
    let max_delegation_proofs = proof_metadata
        .delegation_proof_count
        .iter()
        .map(|(_, x)| x)
        .max()
        .unwrap_or(&0);
    if proof_metadata.basic_proof_count > 2
        || proof_metadata.reduced_proof_count > 2
        || max_delegation_proofs > &1
    {
        return false;
    }
    true
}

// For now, we share the setup cache, only for GPU (as we really care for performance there).
#[derive(Default)]
pub struct GpuSharedState {
    #[cfg(feature = "gpu")]
    pub cache: SetupCache<Global, prover_examples::gpu::ConcurrentStaticHostAllocator>,
}

#[cfg(feature = "gpu")]
impl GpuSharedState {
    /// Create setups for given binary, and unviersal verifier.
    pub fn preheat_for_universal_verifier(&mut self, binary: &Vec<u32>) {
        let now = std::time::Instant::now();

        self.cache.get_or_create_main_circuit(binary);
        self.cache
            .get_or_create_reduced_circuit(&get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER));
        self.cache.get_or_create_delegations();
        println!("Creating setup took {:?}", now.elapsed());
    }
}

pub fn create_proofs_internal(
    binary: &Vec<u32>,
    non_determinism_data: Vec<u32>,
    machine: &Machine,
    num_instances: usize,
    prev_metadata: Option<ProofMetadata>,
    gpu_shared_state: &mut Option<&mut GpuSharedState>,
) -> (ProofList, ProofMetadata) {
    let worker = worker::Worker::new_with_num_threads(8);

    let mut non_determinism_source = QuasiUARTSource::default();

    for entry in non_determinism_data {
        non_determinism_source.oracle.push_back(entry);
    }

    let (proof_list, register_values) = match machine {
        Machine::Standard => {
            if prev_metadata.is_some() {
                panic!("Are you sure that you want to pass --prev-metadata to basic proof?");
            }
            let (basic_proofs, delegation_proofs, register_values) = if let Some(gpu_shared_state) =
                gpu_shared_state
            {
                #[cfg(feature = "gpu")]
                {
                    println!("**** proving using GPU ****");

                    let main_circuit_precomputations = gpu_shared_state
                        .cache
                        .get_or_create_main_circuit(&binary)
                        .clone();
                    let delegation_precomputations =
                        gpu_shared_state.cache.get_or_create_delegations();

                    let context = prover_examples::gpu::create_default_prover_context();
                    prover_examples::gpu::gpu_prove_image_execution_for_machine_with_gpu_tracers(
                        num_instances,
                        &binary,
                        non_determinism_source,
                        &main_circuit_precomputations,
                        &delegation_precomputations,
                        &context,
                        &worker,
                    )
                    .unwrap()
                }
                #[cfg(not(feature = "gpu"))]
                {
                    let _ = gpu_shared_state;
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
                    final_proofs: vec![],
                    delegation_proofs,
                },
                register_values,
            )
        }
        Machine::Reduced => {
            let (reduced_proofs, delegation_proofs, register_values) = if let Some(
                gpu_shared_state,
            ) = gpu_shared_state
            {
                #[cfg(feature = "gpu")]
                {
                    println!("**** proving using GPU ****");
                    let main_circuit_precomputations = gpu_shared_state
                        .cache
                        .get_or_create_reduced_circuit(&binary)
                        .clone();
                    //setups::get_reduced_riscv_circuit_setup(&binary, &worker);
                    let delegation_precomputations =
                        gpu_shared_state.cache.get_or_create_delegations();

                    //                        setups::all_delegation_circuits_precomputations(&worker);

                    let context = prover_examples::gpu::create_default_prover_context();
                    prover_examples::gpu::gpu_prove_image_execution_for_machine_with_gpu_tracers(
                        num_instances,
                        &binary,
                        non_determinism_source,
                        &main_circuit_precomputations,
                        &delegation_precomputations,
                        &context,
                        &worker,
                    )
                    .unwrap()
                }
                #[cfg(not(feature = "gpu"))]
                {
                    let _ = gpu_shared_state;
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
        "Created {} basic proofs, {} reduced proofs and {} delegation proofs. Final proofs: {}",
        proof_list.basic_proofs.len(),
        proof_list.reduced_proofs.len(),
        total_delegation_proofs,
        proof_list.final_proofs.len()
    );
    let last_proof = proof_list.get_last_proof();

    let (end_params_output, end_params_output_hash) =
        get_end_params_output(last_proof, &register_values);

    let proof_metadata = ProofMetadata {
        basic_proof_count: proof_list.basic_proofs.len(),
        reduced_proof_count: proof_list.reduced_proofs.len(),
        final_proof_count: proof_list.final_proofs.len(),
        delegation_proof_count: proof_list
            .delegation_proofs
            .iter()
            .map(|(i, x)| (i.clone() as u32, x.len()))
            .collect::<Vec<_>>(),
        register_values,
        end_params_output,
        end_params_output_hash,
        prev_end_params_output: prev_metadata.map(|prev_metadata| prev_metadata.end_params_output),
    };

    (proof_list, proof_metadata)
}

pub fn create_recursion_proofs(
    proof_list: ProofList,
    proof_metadata: ProofMetadata,
    tmp_dir: &Option<String>,
    gpu_shared_state: &mut Option<&mut GpuSharedState>,
) -> (ProofList, ProofMetadata, ProofMetadata) {
    assert!(
        proof_metadata.basic_proof_count > 0,
        "Recursion proofs can be created only for basic proofs.",
    );
    let binary = get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER);

    let mut recursion_level = 0;
    let mut current_proof_list = proof_list;
    let mut current_proof_metadata = proof_metadata.clone();
    let mut prev_metadata = proof_metadata.clone();

    loop {
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
            Some(prev_metadata.clone()),
            gpu_shared_state,
        );

        if let Some(tmp_dir) = tmp_dir {
            let base_tmp_dir = Path::new(tmp_dir).join(format!("recursion_{}", recursion_level));
            if !base_tmp_dir.exists() {
                fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
            }
            current_proof_list.write_to_directory(&base_tmp_dir);
            serialize_to_file(&current_proof_metadata, &base_tmp_dir.join("metadata.json"))
        }

        if recursion_level == 0 {
            // We have to update the 'prev' metadata only on level 0 & 1.
            prev_metadata = current_proof_metadata.clone();
        }
        recursion_level += 1;
        // TODO: check if we need to have 2 recursion levels.
        if recursion_level > 1 && should_stop_recursion(&current_proof_metadata) {
            println!("Stopping recursion.");
            break;
        }
    }
    (current_proof_list, current_proof_metadata, prev_metadata)
}

fn create_final_proofs(
    proof_list: ProofList,
    proof_metadata: ProofMetadata,
    prev_metadata: ProofMetadata,
    tmp_dir: &Option<String>,
) -> ProgramProof {
    let binary = get_padded_binary(UNIVERSAL_CIRCUIT_NO_DELEGATION_VERIFIER);

    let mut final_proof_level = 0;
    let mut current_proof_list = proof_list;
    let mut current_proof_metadata = proof_metadata.clone();
    let mut prev_metadata = prev_metadata;

    loop {
        println!("*** Starting final_proofs level {} ***", final_proof_level);
        let non_determinism_data = generate_oracle_data_for_universal_verifier(
            &current_proof_metadata,
            &current_proof_list,
        );

        (current_proof_list, current_proof_metadata) = create_proofs_internal(
            &binary,
            non_determinism_data,
            &Machine::ReducedFinal,
            current_proof_metadata.total_proofs(),
            Some(prev_metadata.clone()),
            &mut None,
        );
        if let Some(tmp_dir) = tmp_dir {
            let base_tmp_dir = Path::new(tmp_dir).join(format!("final_{}", final_proof_level));
            if !base_tmp_dir.exists() {
                fs::create_dir_all(&base_tmp_dir).expect("Failed to create tmp dir");
            }
            current_proof_list.write_to_directory(&base_tmp_dir);
            serialize_to_file(&current_proof_metadata, &base_tmp_dir.join("metadata.json"))
        }
        if final_proof_level == 0 {
            // We have to update the 'prev' metadata only on level 0 & 1.
            prev_metadata = current_proof_metadata.clone();
        }
        final_proof_level += 1;
        if current_proof_metadata.final_proof_count == 1 {
            break;
        }
    }

    program_proof_from_proof_list_and_metadata(&current_proof_list, &current_proof_metadata)
}

pub fn get_end_params_output_suffix_from_proof(last_proof: &Proof) -> Option<Seed> {
    if last_proof.public_inputs.len() != 4 {
        // We can compute this only for proofs with public inputs.
        return None;
    }

    let end_pc =
        parse_field_els_as_u32_checked([last_proof.public_inputs[2], last_proof.public_inputs[3]]);

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

fn get_end_params_output(
    last_proof: &Proof,
    register_values: &Vec<FinalRegisterValue>,
) -> ([u32; 16], [u32; 8]) {
    // we need PC from the last proof.
    let end_params_output_suffix = get_end_params_output_suffix_from_proof(last_proof).unwrap();

    let mut end_params_output = [0u32; 16];
    // First 8 entries should be from registers.
    for i in 0..8 {
        end_params_output[i] = register_values[18 + i].value;
    }
    for i in 8..16 {
        end_params_output[i] = end_params_output_suffix.0[i - 8];
    }

    let mut end_params_hash = Blake2sBufferingTranscript::new();
    end_params_hash.absorb(&end_params_output);
    (end_params_output, end_params_hash.finalize().0)
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

pub fn generate_oracle_data_for_universal_verifier(
    metadata: &ProofMetadata,
    proofs: &ProofList,
) -> Vec<u32> {
    let mut oracle = generate_oracle_data_from_metadata_and_proof_list(metadata, proofs);

    if metadata.basic_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::BaseLayer as u32);
    } else if metadata.reduced_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::RecursionLayer as u32);
    } else {
        oracle.insert(0, VerifierCircuitsIdentifiers::FinalLayer as u32);
    };
    oracle
}

pub fn generate_oracle_data_from_metadata_and_proof_list(
    metadata: &ProofMetadata,
    proofs: &ProofList,
) -> Vec<u32> {
    let mut oracle_data = vec![];
    // first - it reads all the register values.

    assert_eq!(32, metadata.register_values.len());
    for register in metadata.register_values.iter() {
        oracle_data.push(register.value);
        let (low, high) = split_timestamp(register.last_access_timestamp);
        oracle_data.push(low);
        oracle_data.push(high);
    }

    let delegations: Vec<u32> = if metadata.basic_proof_count > 0 {
        // Then it needs the number of circuits.
        oracle_data.push(metadata.basic_proof_count.try_into().unwrap());

        assert_eq!(metadata.reduced_proof_count, 0);

        // Then circuit proofs themselves.
        for i in 0..metadata.basic_proof_count {
            let proof = &proofs.basic_proofs[i];
            oracle_data
                .extend(verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, true));
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }

        full_machine_allowed_delegation_types()
    } else if metadata.reduced_proof_count > 0 {
        oracle_data.push(metadata.reduced_proof_count.try_into().unwrap());

        // Or reduced proofs
        for i in 0..metadata.reduced_proof_count {
            let proof = &proofs.reduced_proofs[i];
            oracle_data
                .extend(verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, true));
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }

        reduced_machine_allowed_delegation_types()
    } else {
        oracle_data.push(metadata.final_proof_count.try_into().unwrap());

        for i in 0..metadata.final_proof_count {
            let proof = &proofs.final_proofs[i];
            oracle_data
                .extend(verifier_common::proof_flattener::flatten_proof_for_skeleton(proof, true));
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }

        // For final proof - empty vec.
        vec![]
    };

    for (k, _) in metadata.delegation_proof_count.iter() {
        assert!(delegations.contains(k), "No delegation circuit for {}", k);
    }

    for delegation_type in &delegations {
        let empty = vec![];
        let delegation_proofs = proofs
            .delegation_proofs
            .iter()
            .find(|(k, _)| k == delegation_type)
            .map(|(_, v)| v)
            .unwrap_or(&empty);
        oracle_data.push(delegation_proofs.len() as u32);

        for proof in delegation_proofs {
            // Notice, that apply_shuffle is assumed false for delegation proofs.
            oracle_data.extend(
                verifier_common::proof_flattener::flatten_proof_for_skeleton(&proof, false),
            );
            for query in proof.queries.iter() {
                oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
            }
        }
    }
    if let Some(prev_params) = metadata.prev_end_params_output {
        oracle_data.extend(prev_params);
    }
    oracle_data
}
