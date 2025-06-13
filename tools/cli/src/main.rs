#![feature(array_chunks)]
#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use blake2s_u32::Blake2sState;
use clap::{Parser, Subcommand};
use cli_lib::generate_constants::generate_constants_for_binary;
use cli_lib::prover_utils::{
    create_final_proofs_from_program_proof, create_proofs, generate_oracle_data_from_metadata,
    serialize_to_file, u32_from_hex_string, ProvingLimit, VerifierCircuitsIdentifiers,
    DEFAULT_CYCLES,
};
use cli_lib::Machine;

use cli_lib::vk::generate_vk;
use execution_utils::ProgramProof;
use reqwest::blocking::Client;
use serde_json::Value;
use std::path::Path;
use std::{fs, io::Write, iter};

use prover::{
    merkle_trees::{MerkleTreeCapVarLength, MerkleTreeConstructor},
    prover_stages::Proof,
    risc_v_simulator::{
        abstractions::non_determinism::QuasiUARTSource,
        cycle::{
            IMStandardIsaConfig, IWithoutByteAccessIsaConfig,
            IWithoutByteAccessIsaConfigWithDelegation,
        },
        runner::run_simple_with_entry_point_and_non_determimism_source_for_config,
        sim::SimulatorConfig,
    },
};

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Clone, Debug, Parser, Default)]
struct InputConfig {
    // Either load data from the input file
    #[arg(long)]
    input_file: Option<String>,

    // Loads data from the RPC - if set, you also have to set input_batch
    #[arg(long)]
    input_rpc: Option<String>,
    #[arg(long)]
    input_batch: Option<u64>,
}

#[derive(Subcommand)]
enum Commands {
    Prove {
        /// Path to binary
        #[arg(short, long)]
        bin: String,
        // Either load data from the input file or from RPC
        #[clap(flatten)]
        input: InputConfig,
        #[arg(long, default_value = "output")]
        output_dir: String,
        #[arg(long, value_enum, default_value = "standard")]
        machine: Machine,
        // If proving for recursion - you must also pass the previous metadata info.
        #[arg(long)]
        prev_metadata: Option<String>,
        /// Number of riscV cycles to run. 32_000_000 if not set.
        #[arg(long)]
        cycles: Option<usize>,

        /// If set, run the recursion, until a given moment.
        #[arg(long)]
        until: Option<ProvingLimit>,

        /// If set, the temporary data (e.g. intermediate proofs) will be stored in the given directory.
        #[arg(long)]
        tmp_dir: Option<String>,
        /// If true, use GPU for proving.
        #[arg(long)]
        gpu: bool,
    },
    /// Run the 'final' step of proving (for example on the output from ZKSmith)
    ProveFinal {
        // Either load data from the input file or from RPC
        #[clap(flatten)]
        input: InputConfig,
        #[arg(long, default_value = "output")]
        output_dir: String,
    },
    /// Verifies a single proof.
    Verify {
        /// Path to proof file.
        #[arg(short, long)]
        proof: String,
    },
    /// Verifies whole run (potentially multiple proofs)
    VerifyAll {
        #[arg(short, long)]
        metadata: Option<String>,

        #[arg(short, long)]
        program_proof: Option<String>,
    },
    Run {
        #[arg(short, long)]
        bin: String,
        // Either load data from the input file or from RPC
        #[clap(flatten)]
        input: InputConfig,
        /// Number of riscV cycles to run. 32_000_000 if not set.
        #[arg(long)]
        cycles: Option<usize>,
        /// If present - compare the register values with results.
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        expected_results: Option<Vec<u32>>,

        #[arg(long, value_enum, default_value = "standard")]
        machine: Machine,
    },

    /// Generates verification key hash, for a given binary.
    /// This way you can compare it with the one inside the proof, to make sure that
    /// the proof is really checking the execution of a given code.
    GenerateVk {
        #[arg(short, long)]
        bin: String,
        #[arg(long)]
        machine: Option<Machine>,
        #[arg(long)]
        output: Option<String>,
    },

    Flatten {
        #[arg(long)]
        input_file: String,
        #[arg(long)]
        output_file: String,
    },
    FlattenAll {
        #[arg(long)]
        input_metadata: String,
        #[arg(long)]
        output_file: String,
    },
    /// Combines two proofs into a single one.
    /// This is used to combine the proof from the previous block with the current one.
    /// Both proofs must have the same recursion chain hash.
    FlattenTwo {
        #[arg(long)]
        first_metadata: String,
        #[arg(long)]
        second_metadata: String,
        #[arg(long)]
        output_file: String,
    },
    /// Generate End params and AUX values for a given binary and verification path.
    // These can be considered quasi 'verification' keys - as they tie the final proof
    // to the original bytecode (and verifications).
    GenerateConstants {
        bin: String,
        /// If true, use the universal verifier (used by the cli tool).
        /// If false, use separate verifiers.
        #[arg(long)]
        universal_verifier: bool,
        /// If true recompute all the verification keys.
        /// If false, use the ones from the vk.json files.
        #[arg(long)]
        recompute: bool,
    },
}

fn fetch_data_from_json_rpc(
    url: &str,
    batch_number: u64,
) -> Result<Option<String>, reqwest::Error> {
    let client = Client::new();
    let request_body = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "anvil_zks_getBoojumWitness",
        "params": [batch_number],
        "id": 1,
    });

    let response = client
        .post(url)
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()?
        .json::<Value>()?;

    match &response["result"] {
        Value::String(data) => {
            let tmp_data = data.strip_prefix("0x").unwrap_or(&data);
            Ok(Some(tmp_data.to_string()))
        }
        _ => Ok(None),
    }
}

fn fetch_data_from_url(url: &str) -> Result<Option<String>, reqwest::Error> {
    let client = Client::new();
    let response = client.get(url).send()?.text()?;
    Ok(Some(response))
}

fn fetch_input_hex_string(input: &InputConfig) -> Result<Option<String>, reqwest::Error> {
    if let Some(input_file) = &input.input_file {
        Ok(Some(
            fs::read_to_string(input_file).unwrap().trim().to_string(),
        ))
    } else if let Some(url) = &input.input_rpc {
        let batch = input
            .input_batch
            .expect("input_batch must be set if input_rpc is set");
        fetch_data_from_json_rpc(&url, batch)
    } else {
        Ok(None)
    }
}

fn fetch_final_input_json(input: &InputConfig) -> Result<Option<String>, reqwest::Error> {
    if let Some(input_file) = &input.input_file {
        Ok(Some(
            fs::read_to_string(input_file).unwrap().trim().to_string(),
        ))
    } else if let Some(url) = &input.input_rpc {
        let batch = input
            .input_batch
            .expect("input_batch must be set if input_rpc is set");
        fetch_data_from_url(format!("{}/downloads/{}", url, batch).as_str())
    } else {
        Ok(None)
    }
}

fn main() {
    let cli = Cli::parse();
    match &cli.command {
        Commands::Prove {
            bin,
            input,
            output_dir,
            machine,
            prev_metadata,
            cycles,
            until,
            tmp_dir,
            gpu,
        } => {
            let input_hex = fetch_input_hex_string(input).expect("Failed to fetch");
            create_proofs(
                bin,
                output_dir,
                &input_hex,
                prev_metadata,
                machine,
                cycles,
                until,
                tmp_dir,
                gpu.clone(),
            );
        }
        Commands::ProveFinal { input, output_dir } => {
            let input = fetch_final_input_json(input).expect("Failed to fetch");

            let input_program_proof: ProgramProof = serde_json::from_str(&input.unwrap())
                .expect("Failed to parse input_hex into ProgramProof");

            let program_proof = create_final_proofs_from_program_proof(input_program_proof);

            serialize_to_file(
                &program_proof,
                &Path::new(output_dir).join("final_program_proof.json"),
            );
        }
        Commands::Verify { proof } => {
            #[cfg(feature = "include_verifiers")]
            verify_proof(proof);
            #[cfg(not(feature = "include_verifiers"))]
            {
                let _ = proof;
                panic!("Not enabled - please compile with `include_verifiers` feature.")
            }
        }
        Commands::VerifyAll {
            metadata,
            program_proof,
        } => {
            #[cfg(feature = "include_verifiers")]
            {
                if let Some(metadata) = metadata {
                    verify_all(metadata);
                } else if let Some(program_proof) = program_proof {
                    verify_all_program_proof(program_proof);
                } else {
                    panic!("Please either provide --metadata or --program_proof");
                }
            }
            #[cfg(not(feature = "include_verifiers"))]
            {
                let _ = metadata;
                let _ = program_proof;
                panic!("Not enabled - please compile with `include_verifiers` feature.")
            }
        }
        Commands::Run {
            bin,
            cycles,
            input,
            expected_results,
            machine,
        } => {
            let input_hex = fetch_input_hex_string(input).expect("Failed to fetch");

            run_binary(bin, cycles, &input_hex, expected_results, machine);
        }
        Commands::GenerateVk {
            bin,
            machine,
            output,
        } => generate_vk(bin, machine, output),
        Commands::Flatten {
            input_file,
            output_file,
        } => flatten_file(input_file, output_file),
        Commands::FlattenAll {
            input_metadata,
            output_file,
        } => flatten_all(input_metadata, output_file),
        Commands::FlattenTwo {
            first_metadata,
            second_metadata,
            output_file,
        } => flatten_two(first_metadata, second_metadata, output_file),
        Commands::GenerateConstants {
            bin,
            universal_verifier,
            recompute,
        } => generate_constants_for_binary(bin, universal_verifier, recompute),
    }
}

/// Computes a single hash for multiple trees.
pub fn merkle_trees_to_hash<T: MerkleTreeConstructor>(trees: &Vec<T>) -> String {
    let caps = trees.iter().map(|x| x.get_cap()).collect::<Vec<_>>();
    merkle_caps_to_hash(&caps)
}

/// Computes a single hash for multiple tree caps.
pub fn merkle_caps_to_hash(caps: &Vec<MerkleTreeCapVarLength>) -> String {
    let mut all_leaves = vec![];
    for cap in caps {
        all_leaves.append(&mut cap.cap.clone());
    }
    let mut hasher = Blake2sState::new();
    for entry in all_leaves {
        let mut result = [0u32; 16];
        // yes, this is very lazy - as we just copy 8 uint32, and the remaining 8 are zero.
        result[..8].copy_from_slice(&entry);
        hasher.absorb::<true>(&result);
    }
    let empty = [0u32; 16];
    let mut dst = [0u32; 8];
    hasher.absorb_final_block::<true>(&empty, 0, &mut dst);

    dst.iter()
        .map(|value| format!("{:08x}", value))
        .collect::<Vec<_>>()
        .join("")
}

#[derive(Debug)]
pub enum CircuitType {
    RiscV,
    RiscVReduced,
    DelegatedExtendedBlake,
}

pub fn proof_name_to_circuit_type(file_name: &str) -> CircuitType {
    if file_name.starts_with("delegation_proof_1991_") {
        CircuitType::DelegatedExtendedBlake
    } else if file_name.starts_with("proof_") {
        CircuitType::RiscV
    } else if file_name.starts_with("reduced_proof_") {
        CircuitType::RiscVReduced
    } else {
        panic!("Failed to map file {} to a proof type.", file_name);
    }
}

#[cfg(feature = "include_verifiers")]
fn verify_proof(proof_path: &String) {
    use cli_lib::prover_utils::get_end_params_output_suffix_from_proof;

    println!("Verifying proof from {}", proof_path);
    let proof: Proof = deserialize_from_file(proof_path);

    let end_params_output = get_end_params_output_suffix_from_proof(&proof);
    println!("Final params hash: {:?}", end_params_output);

    let verification_key = merkle_caps_to_hash(&proof.setup_tree_caps);
    println!("Proof verification key is {}", verification_key);

    let circuit_type = proof_name_to_circuit_type(
        std::path::Path::new(proof_path)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap(),
    );

    println!("Circuit type detected as {:?}", circuit_type);

    let shuffle_ram_inits_and_teardowns: bool = match circuit_type {
        CircuitType::RiscV => true,
        CircuitType::RiscVReduced => true,
        CircuitType::DelegatedExtendedBlake => false,
    };

    let mut oracle_data = vec![];

    oracle_data.extend(
        verifier_common::proof_flattener::flatten_proof_for_skeleton(
            &proof,
            shuffle_ram_inits_and_teardowns,
        ),
    );
    for query in proof.queries.iter() {
        oracle_data.extend(verifier_common::proof_flattener::flatten_query(query));
    }

    let it = oracle_data.into_iter();

    verifier_common::prover::nd_source_std::set_iterator(it);

    match circuit_type {
        CircuitType::RiscV => unsafe {
            risc_v_cycles_verifier::verify(
                std::mem::MaybeUninit::uninit().assume_init_mut(),
                &mut verifier_common::ProofPublicInputs::uninit(),
            )
        },
        CircuitType::RiscVReduced => unsafe {
            reduced_risc_v_machine_verifier::verify(
                std::mem::MaybeUninit::uninit().assume_init_mut(),
                &mut verifier_common::ProofPublicInputs::uninit(),
            )
        },
        CircuitType::DelegatedExtendedBlake => {
            unsafe {
                blake2_with_compression_verifier::verify(
                    std::mem::MaybeUninit::uninit().assume_init_mut(),
                    &mut verifier_common::ProofPublicInputs::uninit(),
                )
            };
        }
    }
    println!("PROOF IS VALID");
}

fn flatten_file(input_file: &String, output_file: &String) {
    let proof: Proof = deserialize_from_file(input_file);
    //let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
    //        deserialize_from_file("../../prover/delegation_layout");
    let shuffle_ram_inits_and_teardowns = true;

    let mut data = vec![VerifierCircuitsIdentifiers::RiscV as u32];
    // FIXME: this should detect the type of the proof.
    data.extend(
        verifier_common::proof_flattener::flatten_proof_for_skeleton(
            &proof,
            shuffle_ram_inits_and_teardowns,
        ),
    );

    for query in proof.queries.iter() {
        data.extend(verifier_common::proof_flattener::flatten_query(query));
    }

    u32_to_file(output_file, &data);

    let foo = u32_from_file(output_file);
    assert_eq!(foo, data);
}

fn flatten_all(input_metadata: &String, output_file: &String) {
    let (metadata, mut oracle) = generate_oracle_data_from_metadata(input_metadata);

    if metadata.basic_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::BaseLayer as u32);
    } else if metadata.reduced_proof_count > 0 {
        oracle.insert(0, VerifierCircuitsIdentifiers::RecursionLayer as u32);
    } else {
        oracle.insert(0, VerifierCircuitsIdentifiers::FinalLayer as u32);
    };

    u32_to_file(output_file, &oracle);
}

fn flatten_two(first_metadata: &String, second_metadata: &String, output_file: &String) {
    let (metadata, mut oracle) = generate_oracle_data_from_metadata(first_metadata);
    let (metadata2, oracle2) = generate_oracle_data_from_metadata(second_metadata);

    oracle.extend(oracle2);
    assert!(metadata.reduced_proof_count > 0);
    assert!(metadata2.reduced_proof_count > 0);

    oracle.insert(
        0,
        VerifierCircuitsIdentifiers::CombinedRecursionLayers as u32,
    );

    u32_to_file(output_file, &oracle);
}

#[cfg(feature = "include_verifiers")]
fn verify_all(metadata_path: &String) {
    let (metadata, oracle_data) = generate_oracle_data_from_metadata(metadata_path);
    let it = oracle_data.into_iter();

    verifier_common::prover::nd_source_std::set_iterator(it);

    if metadata.basic_proof_count > 0 {
        assert_eq!(metadata.reduced_proof_count, 0);
        let output = full_statement_verifier::verify_base_layer();
        println!("Output is: {:?}", output);
    } else if metadata.reduced_proof_count > 0 {
        println!("Running continue recursive");
        assert!(metadata.reduced_proof_count > 0);
        let output = full_statement_verifier::verify_recursion_layer();
        println!("Output is: {:?}", output);
    } else {
        println!("Running final recursive");
        assert!(metadata.final_proof_count > 0);
        let output = full_statement_verifier::verify_final_recursion_layer();
        println!("Output is: {:?}", output);
    };
    assert!(
        verifier_common::prover::nd_source_std::try_read_word().is_none(),
        "Expected that all words from CSR were consumed"
    );
}

#[cfg(feature = "include_verifiers")]
fn verify_all_program_proof(program_proof_path: &String) {
    use cli_lib::prover_utils::{
        generate_oracle_data_from_metadata_and_proof_list,
        proof_list_and_metadata_from_program_proof,
    };

    let input_program_proof: ProgramProof = deserialize_from_file(&program_proof_path);
    //serde_json::from_str(&input.unwrap()).expect("Failed to parse input_hex into ProgramProof");
    let (metadata, proof_list) = proof_list_and_metadata_from_program_proof(input_program_proof);

    let oracle_data = generate_oracle_data_from_metadata_and_proof_list(&metadata, &proof_list);
    let it = oracle_data.into_iter();

    verifier_common::prover::nd_source_std::set_iterator(it);

    // Assume that program proof has only recursion proofs.
    println!("Running continue recursive");
    assert!(metadata.reduced_proof_count > 0);
    let output = full_statement_verifier::verify_recursion_layer();
    println!("Output is: {:?}", output);

    assert!(
        verifier_common::prover::nd_source_std::try_read_word().is_none(),
        "Expected that all words from CSR were consumed"
    );
}

fn u32_from_file(input_file: &String) -> Vec<u32> {
    let hex_string = fs::read_to_string(input_file).unwrap().trim().to_string();

    u32_from_hex_string(&hex_string)
}

fn u32_to_file(output_file: &String, numbers: &[u32]) {
    // Open the file for writing
    let mut file = fs::File::create(output_file).expect("Failed to create file");

    // Write each u32 as an 8-character hexadecimal string without newlines
    for &num in numbers {
        write!(file, "{:08X}", num).expect("Failed to write to file");
    }

    println!("Successfully wrote to file: {}", output_file);
}

fn run_binary(
    bin_path: &String,
    cycles: &Option<usize>,
    input_hex: &Option<String>,
    expected_results: &Option<Vec<u32>>,
    machine: &Machine,
) {
    let config = SimulatorConfig {
        bin_path: bin_path.into(),
        cycles: cycles.unwrap_or(DEFAULT_CYCLES),
        entry_point: 0,
        diagnostics: None,
    };
    let mut non_determinism_source = QuasiUARTSource::default();
    if let Some(input_hex) = input_hex {
        let data = u32_from_hex_string(input_hex);
        for entry in data {
            non_determinism_source.oracle.push_back(entry);
        }
    }

    let registers = match machine {
        Machine::Standard => {
            let (_, final_state) =
                run_simple_with_entry_point_and_non_determimism_source_for_config::<
                    _,
                    IMStandardIsaConfig,
                >(config, non_determinism_source);

            final_state.registers
        }
        Machine::Reduced => {
            let (_, final_state) =
                run_simple_with_entry_point_and_non_determimism_source_for_config::<
                    _,
                    IWithoutByteAccessIsaConfigWithDelegation,
                >(config, non_determinism_source);

            final_state.registers
        }
        Machine::ReducedFinal => {
            let (_, final_state) =
                run_simple_with_entry_point_and_non_determimism_source_for_config::<
                    _,
                    IWithoutByteAccessIsaConfig,
                >(config, non_determinism_source);

            final_state.registers
        }
    };

    // our convention is to return 32 bytes placed into registers x10-x17

    let result = registers[10..26]
        .iter()
        .map(|x| format!("{}", x))
        .collect::<Vec<_>>()
        .join(", ");
    println!("Result: {}", result);
    if let Some(expected_results) = expected_results {
        // let's compare registers to expected results.
        // expected results can be shorter - so pad with zeros.
        for (i, (a, b)) in registers[10..18]
            .iter()
            .zip(expected_results.iter().chain(iter::repeat(&0)))
            .enumerate()
        {
            if a != b {
                panic!(
                    "Expected results differ on {}: register: {} expected: {}",
                    i, a, b
                );
            }
        }
    }
}
