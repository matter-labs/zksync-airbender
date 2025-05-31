#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use clap::Parser;
use std::{
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

mod all_layouts;

use prover::{
    cs::{
        cs::witness_placer::graph_description::RawExpression,
        one_row_compiler::CompiledCircuitArtifact,
    },
    field::Mersenne31Field,
};
use verifier_generator::{generate_from_parts, generate_inlined};

pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst =
        std::fs::File::create(filename).expect(&format!("Cannot create file: {}", filename));
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

/// Runs rustfmt to format the code.
fn format_rust_code(code: &str) -> Result<String, String> {
    // Spawn the `rustfmt` process
    let mut rustfmt = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
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

/// Returns formatted rust code with verifier and inline verifier files.
pub fn generate_verifier_files(
    circuit: &CompiledCircuitArtifact<Mersenne31Field>,
) -> (String, String) {
    let verifier = format_rust_code(&generate_from_parts(&circuit).to_string()).unwrap();

    let inlined_verifier =
        format_rust_code(&generate_inlined(circuit.clone()).to_string()).unwrap();

    (verifier, inlined_verifier)
}

pub fn generate_witness_evaluation_function(
    circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    ssa: &[Vec<RawExpression<Mersenne31Field>>],
) -> String {
    let witness_fn = format_rust_code(
        &witness_eval_generator::derive_from_ssa::derive_from_ssa(ssa, circuit, false).to_string(),
    )
    .unwrap();

    witness_fn
}

pub fn generate_gpu_witness_evaluation_function(
    circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    ssa: &[Vec<RawExpression<Mersenne31Field>>],
) -> String {
    gpu_witness_eval_generator::Generator::generate(ssa, circuit, false)
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[arg(long, default_value = "output")]
    output_dir: String,
}

fn create_all(
    gen_fn: fn() -> (
        CompiledCircuitArtifact<Mersenne31Field>,
        Vec<Vec<RawExpression<Mersenne31Field>>>,
    ),
    prefix: &str,
    output_dir: &str,
) {
    let (circuit, ssa) = (gen_fn)();
    serialize_to_file(
        &circuit,
        Path::new(&output_dir)
            .join(format!("{}_layout.json", prefix))
            .to_str()
            .unwrap(),
    );
    let (verifier, inline_verifier) = generate_verifier_files(&circuit);
    std::fs::write(
        Path::new(&output_dir).join(format!("{}_circuit_layout.rs", prefix)),
        verifier,
    )
    .expect(&format!("Failed to write to {}", output_dir));
    std::fs::write(
        Path::new(&output_dir).join(format!("{}_quotient.rs", prefix)),
        inline_verifier,
    )
    .expect(&format!("Failed to write to {}", output_dir));

    let witness_fn = generate_witness_evaluation_function(&circuit, &ssa);
    std::fs::write(
        Path::new(&output_dir).join(format!("{}_witness_generation_fn.rs", prefix)),
        witness_fn,
    )
    .expect(&format!("Failed to write to {}", output_dir));

    let witness_fn = generate_gpu_witness_evaluation_function(&circuit, &ssa);
    std::fs::write(
        Path::new(&output_dir).join(format!("{}_witness_generation_fn.cuh", prefix)),
        witness_fn,
    )
    .expect(&format!("Failed to write to {}", output_dir));
}

use all_layouts::*;

const ALL_LAYOUTS: &[(
    fn() -> (
        CompiledCircuitArtifact<Mersenne31Field>,
        Vec<Vec<RawExpression<Mersenne31Field>>>,
    ),
    &str,
)] = &[
    (create_main_machine_layout_with_delegation, "risc_v_cycles"),
    (
        create_reduced_machine_layout_with_delegation,
        "reduced_risc_v_machine",
    ),
    (
        create_final_reduced_machine_layout_with_delegation,
        "final_reduced_risc_v_machine",
    ),
    (
        create_machine_without_signed_mul_div_layout_with_delegation,
        "machine_without_signed_mul_div",
    ),
    (
        create_blake_with_compression_delegation_layout,
        "blake2_with_compression",
    ),
    (
        create_bigint_with_control_delegation_layout,
        "bigint_with_control",
    ),
];

fn main() {
    let cli = Cli::parse();

    let output_dir = cli.output_dir;

    for (gen_fn, prefix) in ALL_LAYOUTS.iter() {
        create_all(*gen_fn, prefix, &output_dir);
    }

    println!("Layout, quotient and witness eval fns were generated");

    // All delegations circuit params
    let description = format_rust_code(&setups::generate_artifacts()).unwrap();

    std::fs::write(
        Path::new(&output_dir).join("all_delegation_circuits_params.rs"),
        description,
    )
    .expect(&format!("Failed to write to {}", output_dir));
}

#[allow(dead_code)]
fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

#[test]
fn generate_verifier() {
    let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
        deserialize_from_file("../../prover/full_machine_layout.json");

    let (verifier, inline_verifier) = generate_verifier_files(&compiled_circuit);
    std::fs::write(
        Path::new(&"../../verifier/src/generated/circuit_layout.rs"),
        verifier,
    )
    .expect(&format!("Failed to write to"));
    std::fs::write(
        Path::new("../../verifier/src/generated/quotient.rs"),
        inline_verifier,
    )
    .expect(&format!("Failed to write to"));
}
