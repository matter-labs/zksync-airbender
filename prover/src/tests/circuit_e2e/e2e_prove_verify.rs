//! True end-to-end prove+verify tests for individual RISC-V opcodes.
//!
//! Each test:
//!   1. Assembles a single instruction from its mnemonic string (e.g. "div x3, x1, x2")
//!   2. Builds a minimal RISC-V program (instruction + exit sequence, padded to ROM size)
//!   3. Transpiles & executes the program through the VM
//!   4. Generates a full STARK proof via the prover
//!   5. Verifies the proof via the verifier


use std::collections::HashMap;
use std::path::Path;

use test_utils::skip_if_ci;

use execution_utils::setups;
use execution_utils::unrolled::{
    compute_setup_for_machine_configuration,
    prove_unrolled_for_machine_configuration_into_program_proof,
    verify_unrolled_layer_proof,
    UnrolledProgramProof, UnrolledProgramSetup,
};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
use riscv_transpiler::cycle::MachineConfig;
use setups::CompiledCircuitsSet;
use worker::Worker;

/// Build a padded ROM text section from assembly instructions.
/// Appends the standard EXIT_SEQUENCE so the VM halts and outputs register state.
fn assemble_program(instructions: &[&str]) -> Vec<u32> {
    let mut labels = HashMap::new();
    let mut text = Vec::new();
    for (i, instr) in instructions.iter().enumerate() {
        let pc = (i as u32) * 4;
        let encoding = lib_rv32_asm::assemble_ir(instr, &mut labels, pc)
            .unwrap_or_else(|e| panic!("failed to assemble '{}': {:?}", instr, e))
            .unwrap_or_else(|| panic!("no instruction produced for '{}'", instr));
        text.push(encoding);
    }
    text.extend_from_slice(execution_utils::EXIT_SEQUENCE);
    // Pad to ROM_WORD_SIZE
    text.resize(riscv_transpiler::common_constants::ROM_WORD_SIZE, 0);
    text
}

/// Run the full prove+verify pipeline for a program and return output registers [x10..x25].
fn prove_and_verify(text_section: &[u32], label: &str) -> [u32; 16] {
    // Empty binary image (no data section), padded to ROM size
    let binary_image = vec![0u32; riscv_transpiler::common_constants::ROM_WORD_SIZE];

    let worker = Worker::new_with_num_threads(8);
    let cycles_bound = 1 << 21;
    let ram_bound = 1 << 32;
    let non_determinism = QuasiUARTSource::new_with_reads(vec![]);

    println!("[prove] {}", label);
    let now = std::time::Instant::now();

    let program_proof =
        prove_unrolled_for_machine_configuration_into_program_proof::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&binary_image, text_section, cycles_bound, non_determinism, ram_bound, &worker);

    println!("[prove] done in {:?}", now.elapsed());

    // Build setup for verification
    let binary_image_u8: Vec<u8> = binary_image.iter().flat_map(|w| w.to_le_bytes()).collect();
    let text_section_u8: Vec<u8> = text_section.iter().flat_map(|w| w.to_le_bytes()).collect();

    let program_setup = compute_setup_for_machine_configuration::<
        IMStandardIsaConfigWithUnsignedMulDiv,
    >(&binary_image_u8, &text_section_u8);

    let compiled_layouts =
        setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&binary_image);

    println!("[verify] {}", label);
    let now = std::time::Instant::now();

    let output = verify_unrolled_layer_proof(
        &program_proof,
        &program_setup,
        &compiled_layouts,
        true,
    )
    .expect("proof verification failed");

    println!("[verify] done in {:?}", now.elapsed());
    println!("[PASS] {}", label);

    output
}

// ==================== ADD ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_add() {
    skip_if_ci!();
    // addi x1, x0, 10  -> x1 = 10
    // addi x2, x0, 20  -> x2 = 20
    // add x10, x1, x2  -> x10 = 30
    let text = assemble_program(&[
        "addi x1, x0, 10",
        "addi x2, x0, 20",
        "add x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "add x10, x1, x2: 10 + 20 = 30");
    // x10 is the first output register
    assert_eq!(output[0], 30, "x10 should be 30");
}

// ==================== SUB ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_sub() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 50",
        "addi x2, x0, 20",
        "sub x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "sub x10, x1, x2: 50 - 20 = 30");
    assert_eq!(output[0], 30, "x10 should be 30");
}

// ==================== MUL ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_mul() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 6",
        "addi x2, x0, 7",
        "mul x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "mul x10, x1, x2: 6 * 7 = 42");
    assert_eq!(output[0], 42, "x10 should be 42");
}

// ==================== DIV ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_div() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 42",
        "addi x2, x0, 7",
        "div x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "div x10, x1, x2: 42 / 7 = 6");
    assert_eq!(output[0], 6, "x10 should be 6");
}

// ==================== DIV signed overflow ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_div_overflow() {
    skip_if_ci!();
    // INT_MIN / -1 = INT_MIN (RISC-V spec: overflow returns dividend)
    // We need to load INT_MIN (0x80000000) and -1 (0xFFFFFFFF) into registers.
    // lui x1, 0x80000  -> x1 = 0x80000000 = INT_MIN
    // addi x2, x0, -1  -> x2 = 0xFFFFFFFF = -1
    // div x10, x1, x2  -> x10 = 0x80000000 = INT_MIN
    let text = assemble_program(&[
        "lui x1, 0x80000",
        "addi x2, x0, -1",
        "div x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "div x10, x1, x2: INT_MIN / -1 = INT_MIN");
    assert_eq!(output[0], 0x80000000, "x10 should be INT_MIN");
}

// ==================== SLL (shift left logical) ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_sll() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 1",
        "addi x2, x0, 4",
        "sll x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "sll x10, x1, x2: 1 << 4 = 16");
    assert_eq!(output[0], 16, "x10 should be 16");
}

// ==================== XOR ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_xor() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 255",
        "addi x2, x0, 15",
        "xor x10, x1, x2",
    ]);
    let output = prove_and_verify(&text, "xor x10, x1, x2: 0xFF ^ 0x0F = 0xF0");
    assert_eq!(output[0], 0xF0, "x10 should be 0xF0");
}

// ==================== LUI ====================

#[test]
#[ignore = "heavy proving test"]
#[serial_test::serial]
fn test_e2e_lui() {
    skip_if_ci!();
    let text = assemble_program(&["lui x10, 0x12345"]);
    let output = prove_and_verify(&text, "lui x10, 0x12345: x10 = 0x12345000");
    assert_eq!(output[0], 0x12345000, "x10 should be 0x12345000");
}
