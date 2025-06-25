#![feature(generic_const_exprs)]
#![feature(array_chunks)]
#![feature(allocator_api)]

// DONE: Generate files for proving
// DONE: Generate proofs
// DONE: Generate verifiers
// TODO: Compile verifiers
// TODO: Test verifiers in RISC-V simulator

use proc_macro2::TokenStream;
use quote::quote;

// use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
// use prover::witness_evaluator::SimpleWitnessProxy;
use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
use prover::witness_proxy::WitnessProxy;
use prover::SimpleWitnessProxy;
// use ::cs::cs::placeholder::Placeholder;
// use ::cs::cs::witness_placer::WitnessTypeSet;
// use ::field::Mersenne31Field;
// use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use risc_v_simulator::cycle::IMStandardIsaConfig;

use cs::cs::oracle::Oracle;
use cs::cs::placeholder::Placeholder;
use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use cs::cs::witness_placer::{
    WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
    WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
    WitnessComputationalU8, WitnessMask, WitnessTypeSet,
};
use cs::default_compile_machine;
use cs::machine::machine_configurations::create_csr_table_for_delegation;
use cs::machine::machine_configurations::create_table_for_rom_image;
use cs::machine::machine_configurations::dump_ssa_witness_eval_form;
use cs::machine::machine_configurations::full_isa_with_delegation_no_exceptions::FullIsaMachineWithDelegationNoExceptionHandling;
use cs::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
use cs::tables::TableType;
use field::Mersenne31Field;
use std::io::Write;
use witness_eval_generator::derive_from_ssa::derive_from_ssa;

pub mod circuit_files;
pub mod profiling;
pub mod testing_prover;
pub mod witness_generation_functions;

const CIRCUIT_DIR: &str = "circuit_files";
const PROOFS_DIR: &str = "proofs";
const VERIFIERS_DIR: &str = "verifiers";
const COMPILED_VERIFIERS_DIR: &str = "binaries";
const FLAMEGRAPH_DIR: &str = "flamegraphs";

#[test]
fn generate_circuit_files_test() {
    let proof_configs = deserialize_from_file::<Vec<ProfilingConfig>>("profiling_configs.json");

    for config in proof_configs {
        println!(
            "Generating circuit files for: trace_len_log={}, second_word_bits={}, reduced_machine={}",
            config.trace_len_log, config.second_word_bits, config.reduced_machine
        );
        circuit_files::generate_circuit_files(&config, &CIRCUIT_DIR);
    }
}

#[test]
fn include_witness_generator_function_test() {
    let proof_configs = deserialize_from_file::<Vec<ProfilingConfig>>("profiling_configs.json");

    let mut full_stream = TokenStream::new();
    let mut stream = TokenStream::new();

    for config in proof_configs {
        let mod_name = format!(
            "witness_gen_{}_{}_{}",
            config.trace_len_log,
            config.second_word_bits,
            if config.reduced_machine {
                "reduced"
            } else {
                "full"
            }
        );

        use proc_macro2::Ident;
        use proc_macro2::Span;

        let mod_name = Ident::new(&mod_name, Span::call_site());

        let path = format!("../{}/{}", CIRCUIT_DIR, config.witness_gen_file_name());

        let ProfilingConfig {
            trace_len_log,
            second_word_bits,
            reduced_machine,
        } = config;

        let t = quote! {
            if config.trace_len_log == #trace_len_log &&
               config.second_word_bits == #second_word_bits &&
               config.reduced_machine == #reduced_machine
            {
               return #mod_name::witness_eval_fn;
            }
        };

        stream.extend(t);

        let t = quote! {
            mod #mod_name {
                use super::*;

                include!(#path);

                pub fn witness_eval_fn<'a, 'b>(
                    proxy: &'_ mut SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
                ) {
                    let fn_ptr = evaluate_witness_fn::<
                        ScalarWitnessTypeSet<Mersenne31Field, true>,
                        SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
                    >;
                    (fn_ptr)(proxy);
                }
            }
        };

        full_stream.extend(t);
    }

    let full_stream = quote! {
        use super::*;
        #full_stream
        pub fn get_witness_function_from_config(
            config: &ProfilingConfig,
        ) -> fn(&mut SimpleWitnessProxy<'_, MainRiscVOracle<'_, IMStandardIsaConfig>>) {
            #stream

            panic!("No witness generation function found for the given configuration");
        }
    };

    let generated_filename = &"src/witness_generation_functions.rs";

    std::fs::File::create(&generated_filename)
        .unwrap()
        .write_all(
            &format_rust_code(&full_stream.to_string())
                .unwrap()
                .as_bytes(),
        )
        .unwrap();
}

#[test]
fn generate_testing_proofs() {
    let proof_configs = deserialize_from_file::<Vec<ProfilingConfig>>("profiling_configs.json");

    for config in proof_configs {
        println!(
            "Generating testing proof for: trace_len_log={}, second_word_bits={}, reduced_machine={}",
            config.trace_len_log, config.second_word_bits, config.reduced_machine
        );

        let proof = testing_prover::generate_testing_proof(&config);

        serialize_to_file(
            &proof,
            &format!("{}/{}", PROOFS_DIR, config.proof_file_name()),
        );
    }
}

#[test]
fn generate_script_for_creating_verifiers() {
    let proof_configs = deserialize_from_file::<Vec<ProfilingConfig>>("profiling_configs.json");

    let mut script_string = "#!/bin/bash\n\n".to_string();
    script_string.push_str("circuit_names=(\n");
    for config in proof_configs {
        script_string.push_str(&format!("    \"{}\"\n", config.circuit_name()));
    }
    script_string.push_str(")\n\n");

    script_string.push_str(CREATING_VERIFIERS_SCRIPT);

    let mut file = std::fs::File::create("create_testing_verifiers.sh").unwrap();
    file.write_all(script_string.as_bytes()).unwrap();
}

const CREATING_VERIFIERS_SCRIPT: &str = "for CIRCUIT_NAME in \"${circuit_names[@]}\"; do
    echo $CIRCUIT_NAME

    CIRCUIT_DIR=\"verifiers/$CIRCUIT_NAME\"
    DST_DIR=\"$CIRCUIT_DIR/verifier\"

    rm -r $CIRCUIT_DIR

    mkdir $CIRCUIT_DIR

    cp -r ../verifier $DST_DIR

    rm $DST_DIR/src/generated/*

    cp circuit_files/${CIRCUIT_NAME}_layout.json $DST_DIR/src/generated/layout
    cp circuit_files/${CIRCUIT_NAME}_circuit_layout.rs $DST_DIR/src/generated/circuit_layout.rs
    cp circuit_files/${CIRCUIT_NAME}_quotient.rs $DST_DIR/src/generated/quotient.rs

    rm $DST_DIR/README.md
    rm $DST_DIR/expand.sh
    rm $DST_DIR/flamegraph.svg

    DST_DIR=\"$CIRCUIT_DIR/verifier_for_compilation\"
    cp -r verifier_for_compilation $DST_DIR

done";

#[test]
fn generate_script_for_compiling_verifiers() {
    let proof_configs = deserialize_from_file::<Vec<ProfilingConfig>>("profiling_configs.json");

    let mut script_string = "#!/bin/bash\n\n".to_string();
    script_string.push_str("circuit_names=(\n");
    for config in proof_configs {
        script_string.push_str(&format!("    \"{}\"\n", config.circuit_name()));
    }
    script_string.push_str(")\n\n");

    script_string.push_str(COMPILING_VERIFIERS_SCRIPT);

    let mut file = std::fs::File::create("compile_testing_verifiers.sh").unwrap();
    file.write_all(script_string.as_bytes()).unwrap();
}

const COMPILING_VERIFIERS_SCRIPT: &str = "for CIRCUIT_NAME in \"${circuit_names[@]}\"; do
    echo $CIRCUIT_NAME

    VER_DIR=\"verifiers/$CIRCUIT_NAME/verifier_for_compilation\"

    cd $VER_DIR
    ./build_for_testing.sh
    cd -

    cp $VER_DIR/tester.bin binaries/${CIRCUIT_NAME}_compiled_verifier.bin
    cp $VER_DIR/tester.elf binaries/${CIRCUIT_NAME}_compiled_verifier.elf
    cp $VER_DIR/tester.text binaries/${CIRCUIT_NAME}_compiled_verifier.text

done";

#[test]
fn profile_verifiers() {
    let proof_configs = deserialize_from_file::<Vec<ProfilingConfig>>("profiling_configs.json");

    for config in proof_configs {
        profiling::profile_inner(
            &config,
            CIRCUIT_DIR,
            PROOFS_DIR,
            COMPILED_VERIFIERS_DIR,
            FLAMEGRAPH_DIR,
        );
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct ProfilingConfig {
    trace_len_log: usize,
    second_word_bits: usize,
    reduced_machine: bool,
}

impl ProfilingConfig {
    pub fn circuit_name(&self) -> String {
        format!(
            "{}_machine_2^{}_{}_2nd_word_bits",
            if self.reduced_machine {
                "reduced"
            } else {
                "full"
            },
            self.trace_len_log,
            self.second_word_bits
        )
    }
    pub fn layout_file_name(&self) -> String {
        self.circuit_name() + &"_layout.json"
    }
    pub fn ssa_file_name(&self) -> String {
        self.circuit_name() + &"_ssa.json"
    }
    pub fn witness_gen_file_name(&self) -> String {
        self.circuit_name() + &"_generated.rs"
    }
    pub fn circuit_layout_file_name(&self) -> String {
        self.circuit_name() + &"_circuit_layout.rs"
    }
    pub fn quotient_file_name(&self) -> String {
        self.circuit_name() + &"_quotient.rs"
    }
    pub fn proof_file_name(&self) -> String {
        self.circuit_name() + &"_proof.json"
    }
    pub fn bin_file_name(&self) -> String {
        self.circuit_name() + &"_compiled_verifier.bin"
    }
    pub fn elf_file_name(&self) -> String {
        self.circuit_name() + &"_compiled_verifier.elf"
    }
    pub fn flamegraph_file_name(&self) -> String {
        self.circuit_name() + &"_flamegraph.svg"
    }
}

const PROVING_CONFIGS: [ProfilingConfig; 4] = [
    ProfilingConfig {
        trace_len_log: 20,
        second_word_bits: 4,
        reduced_machine: false,
    },
    ProfilingConfig {
        trace_len_log: 21,
        second_word_bits: 4,
        reduced_machine: false,
    },
    ProfilingConfig {
        trace_len_log: 22,
        second_word_bits: 4,
        reduced_machine: false,
    },
    ProfilingConfig {
        trace_len_log: 23,
        second_word_bits: 4,
        reduced_machine: false,
    },
];

fn main() {
    serialize_to_file(&PROVING_CONFIGS, "profiling_configs.json");
}

/// Runs rustfmt to format the code.
pub fn format_rust_code(code: &str) -> Result<String, String> {
    // Spawn the `rustfmt` process
    let mut rustfmt = std::process::Command::new("rustfmt")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn rustfmt: {}", e))?;

    // Write the Rust code to `rustfmt`'s stdin
    if let Some(mut stdin) = rustfmt.stdin.take() {
        stdin
            .write_all(code.as_bytes())
            .map_err(|e| format!("Failed to write to rustfmt stdin: {}", e))?;
    }

    // Wait for `rustfmt` to complete and collect the formatted code
    let output = rustfmt
        .wait_with_output()
        .map_err(|e| format!("Failed to read rustfmt output: {}", e))?;

    if !output.status.success() {
        return Err(format!(
            "rustfmt failed with status {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    // Convert the output to a String
    String::from_utf8(output.stdout).map_err(|e| format!("Invalid UTF-8 in rustfmt output: {}", e))
}

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(&format!("{}", filename));
    serde_json::from_reader(src).unwrap()
}
