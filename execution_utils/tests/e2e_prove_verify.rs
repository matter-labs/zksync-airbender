//! Prove+verify integration tests for every legal RISC-V opcode in
//! airbender.
//!
//! Each test:
//!   1. Assembles a minimal program from string-form RV32IM instructions
//!   2. Builds a padded ROM (program + EXIT_SEQUENCE)
//!   3. Transpiles & executes the program through the VM
//!   4. Generates a full STARK proof via the prover
//!   5. Verifies the proof, returning [x10..x25]
//!   6. Asserts the expected register state for that opcode
//!

use std::collections::HashMap;

use test_utils::skip_if_ci;

use execution_utils::unrolled::{
    compute_setup_for_machine_configuration,
    prove_unrolled_for_machine_configuration_into_program_proof, verify_unrolled_layer_proof,
};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
use worker::Worker;

// ==================== Helpers ====================

/// Build a padded ROM text section from assembly instructions.
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
    text.resize(riscv_transpiler::common_constants::ROM_WORD_SIZE, 0);
    text
}

/// Run prove+verify with no non-determinism inputs.
fn prove_and_verify(text_section: &[u32], label: &str) -> [u32; 16] {
    prove_and_verify_with_uart(text_section, label, vec![])
}

fn prove_and_verify_with_uart(
    text_section: &[u32],
    label: &str,
    uart_reads: Vec<u32>,
) -> [u32; 16] {
    let worker = Worker::new_with_num_threads(8);
    let cycles_bound = 1 << 21;
    let ram_bound = 1 << 32;
    let non_determinism = QuasiUARTSource::new_with_reads(uart_reads);

    println!("[prove] {}", label);
    let now = std::time::Instant::now();

    let program_proof = prove_unrolled_for_machine_configuration_into_program_proof::<
        IMStandardIsaConfigWithUnsignedMulDiv,
    >(
        text_section,
        text_section,
        cycles_bound,
        non_determinism,
        ram_bound,
        &worker,
        verifier_common::SecurityModel::Security80,
    );

    println!("[prove] done in {:?}", now.elapsed());

    let text_section_u8: Vec<u8> = text_section.iter().flat_map(|w| w.to_le_bytes()).collect();

    let program_setup = compute_setup_for_machine_configuration::<
        IMStandardIsaConfigWithUnsignedMulDiv,
    >(&text_section_u8, &text_section_u8);

    let compiled_layouts =
        setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(text_section);

    println!("[verify] {}", label);
    let now = std::time::Instant::now();

    let output = verify_unrolled_layer_proof(
        &program_proof,
        &program_setup,
        &compiled_layouts,
        true,
        verifier_common::SecurityModel::Security80,
    )
    .expect("proof verification failed");

    println!("[verify] done in {:?}", now.elapsed());
    println!("[PASS] {}", label);

    output
}

// ==================== Family 1: AddSub / LUI / AUIPC ====================

#[test]
#[serial_test::serial]
fn test_prover_pipeline_add() {
    skip_if_ci!();
    // Compute the result into x3 (a "scratch" register outside x10..x25),
    // point x26 at the start of RAM (0x00400000), and store the result so
    // the trailing EXIT_SEQUENCE loads x10 = result and x11..x25 = 0
    // (RAM is zero-initialised).
    let text = assemble_program(&[
        "addi x1, x0, 10",
        "addi x2, x0, 20",
        "add x3, x1, x2",
        "lui x26, 0x400",
        "sw x3, 0(x26)",
    ]);
    let output = prove_and_verify(&text, "ADD: 10 + 20 = 30");
    assert_eq!(output[0], 30, "x10 should be 30");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sub() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 50", "addi x2, x0, 20", "sub x10, x1, x2"]);
    let output = prove_and_verify(&text, "SUB: 50 - 20 = 30");
    assert_eq!(output[0], 30, "x10 should be 30");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_addi() {
    skip_if_ci!();
    let text = assemble_program(&["addi x10, x0, 42"]);
    let output = prove_and_verify(&text, "ADDI: 0 + 42 = 42");
    assert_eq!(output[0], 42, "x10 should be 42");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_lui() {
    skip_if_ci!();
    let text = assemble_program(&["lui x10, 0x12345"]);
    let output = prove_and_verify(&text, "LUI: 0x12345 << 12 = 0x12345000");
    assert_eq!(output[0], 0x12345000, "x10 should be 0x12345000");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_auipc() {
    skip_if_ci!();
    // AUIPC at pc=0 collapses to LUI semantics, so place a filler at pc=0 and
    // put the AUIPC at pc=4. Expected: x10 = 4 + (0x12345 << 12) = 0x12345004.
    let text = assemble_program(&["addi x1, x0, 0", "auipc x10, 0x12345"]);
    let output = prove_and_verify(&text, "AUIPC at pc=4: 0x4 + 0x12345000 = 0x12345004");
    assert_eq!(output[0], 0x12345004, "x10 should be 0x12345004");
}

// ==================== Family 2: SLT / Branches / Jumps ====================

#[test]
#[serial_test::serial]
fn test_prover_pipeline_slt() {
    skip_if_ci!();
    // SLT (signed): -1 < 1 -> 1
    let text = assemble_program(&["addi x1, x0, -1", "addi x2, x0, 1", "slt x10, x1, x2"]);
    let output = prove_and_verify(&text, "SLT: (-1) < 1 = 1");
    assert_eq!(output[0], 1, "x10 should be 1");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sltu() {
    skip_if_ci!();
    // SLTU (unsigned): 1 <u 2 -> 1
    let text = assemble_program(&["addi x1, x0, 1", "addi x2, x0, 2", "sltu x10, x1, x2"]);
    let output = prove_and_verify(&text, "SLTU: 1 <u 2 = 1");
    assert_eq!(output[0], 1, "x10 should be 1");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_slti() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 3", "slti x10, x1, 5"]);
    let output = prove_and_verify(&text, "SLTI: 3 < 5 = 1");
    assert_eq!(output[0], 1, "x10 should be 1");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sltiu() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 3", "sltiu x10, x1, 5"]);
    let output = prove_and_verify(&text, "SLTIU: 3 <u 5 = 1");
    assert_eq!(output[0], 1, "x10 should be 1");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_beq() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 5",
        "addi x2, x0, 5",
        "beq x1, x2, 12",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
    ]);
    let output = prove_and_verify(&text, "BEQ taken: x10 = 42");
    assert_eq!(output[0], 42, "x10 should be 42 (branch taken)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_bne() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 5",
        "addi x2, x0, 7",
        "bne x1, x2, 12",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
    ]);
    let output = prove_and_verify(&text, "BNE taken: x10 = 42");
    assert_eq!(output[0], 42, "x10 should be 42 (branch taken)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_blt() {
    skip_if_ci!();
    // BLT (signed): -1 < 1 -> branch taken
    let text = assemble_program(&[
        "addi x1, x0, -1",
        "addi x2, x0, 1",
        "blt x1, x2, 12",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
    ]);
    let output = prove_and_verify(&text, "BLT taken: x10 = 42");
    assert_eq!(output[0], 42, "x10 should be 42 (branch taken)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_bge() {
    skip_if_ci!();
    // BGE (signed): 5 >= 5 -> branch taken
    let text = assemble_program(&[
        "addi x1, x0, 5",
        "addi x2, x0, 5",
        "bge x1, x2, 12",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
    ]);
    let output = prove_and_verify(&text, "BGE taken: x10 = 42");
    assert_eq!(output[0], 42, "x10 should be 42 (branch taken)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_bltu() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 1",
        "addi x2, x0, 2",
        "bltu x1, x2, 12",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
    ]);
    let output = prove_and_verify(&text, "BLTU taken: x10 = 42");
    assert_eq!(output[0], 42, "x10 should be 42 (branch taken)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_bgeu() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 7",
        "addi x2, x0, 5",
        "bgeu x1, x2, 12",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
    ]);
    let output = prove_and_verify(&text, "BGEU taken: x10 = 42");
    assert_eq!(output[0], 42, "x10 should be 42 (branch taken)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_jal() {
    skip_if_ci!();

    let text = assemble_program(&[
        "addi x0, x0, 0",
        "jal x1, 16",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 77",
        "addi x10, x0, 42",
        "addi x11, x1, 0",
    ]);
    let output = prove_and_verify(&text, "JAL at pc=4: jump + link");
    assert_eq!(output[0], 42, "x10 should be 42 (jumped to target)");
    assert_eq!(output[1], 8, "x11 should be 8 (link = pc+4 with pc=4)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_jalr() {
    skip_if_ci!();
    let text = assemble_program(&[
        "addi x1, x0, 16",
        "jalr x2, 0(x1)",
        "addi x10, x0, 99",
        "addi x10, x0, 88",
        "addi x10, x0, 42",
        "addi x11, x2, 0",
    ]);
    let output = prove_and_verify(&text, "JALR: indirect jump + link");
    assert_eq!(output[0], 42, "x10 should be 42 (jumped to target)");
    assert_eq!(output[1], 8, "x11 should be 8 (link register)");
}

// ==================== Family 3: Shift / Binop / CSR ====================

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sll() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 1", "addi x2, x0, 4", "sll x10, x1, x2"]);
    let output = prove_and_verify(&text, "SLL: 1 << 4 = 16");
    assert_eq!(output[0], 16, "x10 should be 16");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_srl() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 64", "addi x2, x0, 4", "srl x10, x1, x2"]);
    let output = prove_and_verify(&text, "SRL: 64 >> 4 = 4");
    assert_eq!(output[0], 4, "x10 should be 4");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sra() {
    skip_if_ci!();
    // SRA arithmetic: -16 >> 1 = -8 = 0xFFFFFFF8
    let text = assemble_program(&["addi x1, x0, -16", "addi x2, x0, 1", "sra x10, x1, x2"]);
    let output = prove_and_verify(&text, "SRA: (-16) >> 1 = -8");
    assert_eq!(output[0], 0xFFFFFFF8, "x10 should be 0xFFFFFFF8 (-8)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_xor() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 255", "addi x2, x0, 15", "xor x10, x1, x2"]);
    let output = prove_and_verify(&text, "XOR: 0xFF ^ 0x0F = 0xF0");
    assert_eq!(output[0], 0xF0, "x10 should be 0xF0");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_and() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 240", "addi x2, x0, 85", "and x10, x1, x2"]);
    let output = prove_and_verify(&text, "AND: 0xF0 & 0x55 = 0x50");
    assert_eq!(output[0], 0x50, "x10 should be 0x50");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_or() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 240", "addi x2, x0, 15", "or x10, x1, x2"]);
    let output = prove_and_verify(&text, "OR: 0xF0 | 0x0F = 0xFF");
    assert_eq!(output[0], 0xFF, "x10 should be 0xFF");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_slli() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 1", "slli x10, x1, 4"]);
    let output = prove_and_verify(&text, "SLLI: 1 << 4 = 16");
    assert_eq!(output[0], 16, "x10 should be 16");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_srli() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 64", "srli x10, x1, 3"]);
    let output = prove_and_verify(&text, "SRLI: 64 >> 3 = 8");
    assert_eq!(output[0], 8, "x10 should be 8");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_srai() {
    skip_if_ci!();
    // x1 = 0xFFFFF000 (= -4096 signed); SRAI by 12 -> 0xFFFFFFFF (-1)
    let text = assemble_program(&["lui x1, 0xFFFFF", "srai x10, x1, 12"]);
    let output = prove_and_verify(&text, "SRAI: (-4096) >> 12 = -1");
    assert_eq!(output[0], 0xFFFFFFFF, "x10 should be 0xFFFFFFFF (-1)");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_xori() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 255", "xori x10, x1, 15"]);
    let output = prove_and_verify(&text, "XORI: 0xFF ^ 0x0F = 0xF0");
    assert_eq!(output[0], 0xF0, "x10 should be 0xF0");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_andi() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 240", "andi x10, x1, 15"]);
    let output = prove_and_verify(&text, "ANDI: 0xF0 & 0x0F = 0x00");
    assert_eq!(output[0], 0x00, "x10 should be 0x00");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_ori() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 240", "ori x10, x1, 15"]);
    let output = prove_and_verify(&text, "ORI: 0xF0 | 0x0F = 0xFF");
    assert_eq!(output[0], 0xFF, "x10 should be 0xFF");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_csrrw() {
    skip_if_ci!();
    // csrrw rd, csr, rs1: rd = csr_old; csr = rs1.
    // For NON_DETERMINISM_CSR (0x7c0) the read pulls one value from the
    // QuasiUART input list; the write is a no-op.
    let text = assemble_program(&["csrrw x10, 0x7c0, x0"]);
    let output =
        prove_and_verify_with_uart(&text, "CSRRW: read non-determinism input", vec![0x12345678]);
    assert_eq!(output[0], 0x12345678, "x10 should be the non-det input");
}

// ==================== Family 4: MUL / DIV ====================

#[test]
#[serial_test::serial]
fn test_prover_pipeline_mul() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 6", "addi x2, x0, 7", "mul x10, x1, x2"]);
    let output = prove_and_verify(&text, "MUL: 6 * 7 = 42");
    assert_eq!(output[0], 42, "x10 should be 42");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_mulh() {
    skip_if_ci!();
    // MULH (signed * signed, high 32): -2 * 3 = -6 in 64-bit signed.
    // Low 32 = 0xFFFF_FFFA, high 32 = 0xFFFF_FFFF (-1).
    let text = assemble_program(&["addi x1, x0, -2", "addi x2, x0, 3", "mulh x10, x1, x2"]);
    let output = prove_and_verify(&text, "MULH: high32 of (-2)*3 = 0xFFFFFFFF");
    assert_eq!(output[0], 0xFFFFFFFF, "x10 should be 0xFFFFFFFF");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_mulhsu() {
    skip_if_ci!();
    // MULHSU (signed * unsigned, high 32): -2 (signed) * 3 (unsigned) = -6 in
    // 64-bit signed. High 32 = 0xFFFF_FFFF.
    let text = assemble_program(&["addi x1, x0, -2", "addi x2, x0, 3", "mulhsu x10, x1, x2"]);
    let output = prove_and_verify(&text, "MULHSU: high32 of (-2)*3u = 0xFFFFFFFF");
    assert_eq!(output[0], 0xFFFFFFFF, "x10 should be 0xFFFFFFFF");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_mulhu() {
    skip_if_ci!();
    // MULHU: 2^30 * 2^30 = 2^60. High 32 = 2^28 = 0x10000000.
    let text = assemble_program(&["lui x1, 0x40000", "lui x2, 0x40000", "mulhu x10, x1, x2"]);
    let output = prove_and_verify(&text, "MULHU: high32 of 2^30 * 2^30 = 0x10000000");
    assert_eq!(output[0], 0x10000000, "x10 should be 0x10000000");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_div() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 42", "addi x2, x0, 7", "div x10, x1, x2"]);
    let output = prove_and_verify(&text, "DIV: 42 / 7 = 6");
    assert_eq!(output[0], 6, "x10 should be 6");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_div_overflow() {
    skip_if_ci!();
    // RISC-V spec: signed INT_MIN / -1 returns INT_MIN (no trap).
    let text = assemble_program(&["lui x1, 0x80000", "addi x2, x0, -1", "div x10, x1, x2"]);
    let output = prove_and_verify(&text, "DIV signed overflow: INT_MIN / -1 = INT_MIN");
    assert_eq!(output[0], 0x80000000, "x10 should be INT_MIN");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_divu() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 42", "addi x2, x0, 7", "divu x10, x1, x2"]);
    let output = prove_and_verify(&text, "DIVU: 42 /u 7 = 6");
    assert_eq!(output[0], 6, "x10 should be 6");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_rem() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 42", "addi x2, x0, 5", "rem x10, x1, x2"]);
    let output = prove_and_verify(&text, "REM: 42 % 5 = 2");
    assert_eq!(output[0], 2, "x10 should be 2");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_remu() {
    skip_if_ci!();
    let text = assemble_program(&["addi x1, x0, 42", "addi x2, x0, 5", "remu x10, x1, x2"]);
    let output = prove_and_verify(&text, "REMU: 42 %u 5 = 2");
    assert_eq!(output[0], 2, "x10 should be 2");
}

// ==================== Family 5: Word load / store ====================
//
// RAM layout: ROM occupies the first ROM_BYTE_SIZE = 4 MiB, so 0x00400000 is
// the first valid RAM address. `lui x1, 0x400` loads x1 = 0x00400000.

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sw() {
    skip_if_ci!();
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, 42",
        "sw x2, 0(x1)",
        "lw x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "SW + LW roundtrip word: 42");
    assert_eq!(output[0], 42, "x10 should be 42 after SW/LW");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_lw() {
    skip_if_ci!();
    // Same program as SW; the assertion is on LW behavior.
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, 1234",
        "sw x2, 0(x1)",
        "lw x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "LW: load back word 1234");
    assert_eq!(output[0], 1234, "x10 should be 1234 after LW");
}

// ==================== Family 6: Subword load / store ====================

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sb() {
    skip_if_ci!();
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, 127",
        "sb x2, 0(x1)",
        "lb x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "SB + LB roundtrip byte: 127");
    assert_eq!(output[0], 127, "x10 should be 127");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_lb() {
    skip_if_ci!();
    // Store -1 (low byte = 0xFF), load with sign-extension -> 0xFFFFFFFF.
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, -1",
        "sb x2, 0(x1)",
        "lb x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "LB: sign-extends 0xFF to 0xFFFFFFFF");
    assert_eq!(output[0], 0xFFFFFFFF, "LB should sign-extend");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_lbu() {
    skip_if_ci!();
    // Store -1 (low byte = 0xFF), load unsigned (zero-extend) -> 0x000000FF.
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, -1",
        "sb x2, 0(x1)",
        "lbu x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "LBU: zero-extends 0xFF to 0x000000FF");
    assert_eq!(output[0], 0xFF, "LBU should zero-extend");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_sh() {
    skip_if_ci!();
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, 1234",
        "sh x2, 0(x1)",
        "lh x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "SH + LH roundtrip halfword: 1234");
    assert_eq!(output[0], 1234, "x10 should be 1234");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_lh() {
    skip_if_ci!();
    // Store -1 (low halfword = 0xFFFF), load with sign-extension -> 0xFFFFFFFF.
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, -1",
        "sh x2, 0(x1)",
        "lh x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "LH: sign-extends 0xFFFF to 0xFFFFFFFF");
    assert_eq!(output[0], 0xFFFFFFFF, "LH should sign-extend");
}

#[test]
#[serial_test::serial]
fn test_prover_pipeline_lhu() {
    skip_if_ci!();
    // Store -1 (low halfword = 0xFFFF), load unsigned (zero-extend) -> 0x0000FFFF.
    let text = assemble_program(&[
        "lui x1, 0x400",
        "addi x2, x0, -1",
        "sh x2, 0(x1)",
        "lhu x10, 0(x1)",
    ]);
    let output = prove_and_verify(&text, "LHU: zero-extends 0xFFFF to 0x0000FFFF");
    assert_eq!(output[0], 0xFFFF, "LHU should zero-extend");
}
