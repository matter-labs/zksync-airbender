fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(&format!("{} doesn't exist", filename));
    serde_json::from_reader(src).unwrap()
}

#[cfg(feature = "gkr_verify")]
#[path = "generated/add_sub_lui_auipc_mop/mod.rs"]
mod generated_add_sub_lui_auipc_mop;

#[cfg(feature = "gkr_verify")]
#[path = "generated/jump_branch_slt/mod.rs"]
mod generated_jump_branch_slt;

#[cfg(feature = "gkr_verify")]
#[path = "generated/shift_binop/mod.rs"]
mod generated_shift_binop;

#[cfg(feature = "gkr_verify")]
fn run_gkr_verify_for_circuit(name: &str, proof_path: &str, circuit_path: &str, verify_fn: fn()) {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::gkr::prover::GKRProof;
    use prover::merkle_trees::DefaultTreeConstructor;
    use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
    use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
    use verifier_common::prover::nd_source_std::*;

    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file(proof_path);
    let compiled_circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(circuit_path);

    let oracle_data = flatten_gkr_proof_for_nds::<
        BabyBearField,
        BabyBearExt4,
        DefaultTreeConstructor,
    >(&proof, &compiled_circuit);

    let circuit_name = name.to_string();
    let result = std::thread::Builder::new()
        .name(format!("gkr verifier {}", name))
        .stack_size(1 << 27)
        .spawn(move || {
            set_iterator(oracle_data.into_iter());
            verify_fn();
        })
        .map(|t| t.join());

    match result {
        Ok(Ok(())) => println!("{}: verification passed", circuit_name),
        Ok(Err(e)) => std::panic::resume_unwind(e),
        Err(err) => panic!("Failed to spawn verifier thread: {}", err),
    }
}

#[cfg(feature = "gkr_verify")]
fn verify_add_sub() {
    use verifier_common::prover::nd_source_std::ThreadLocalBasedSource;
    generated_add_sub_lui_auipc_mop::verify_gkr_sumcheck::<ThreadLocalBasedSource>()
        .unwrap_or_else(|e| panic!("GKR verification failed: {:?}", e));
}

#[cfg(feature = "gkr_verify")]
fn verify_jump_branch_slt() {
    use verifier_common::prover::nd_source_std::ThreadLocalBasedSource;
    generated_jump_branch_slt::verify_gkr_sumcheck::<ThreadLocalBasedSource>()
        .unwrap_or_else(|e| panic!("GKR verification failed: {:?}", e));
}

#[cfg(feature = "gkr_verify")]
fn verify_shift_binop() {
    use verifier_common::prover::nd_source_std::ThreadLocalBasedSource;
    generated_shift_binop::verify_gkr_sumcheck::<ThreadLocalBasedSource>()
        .unwrap_or_else(|e| panic!("GKR verification failed: {:?}", e));
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_gkr_sumcheck_verify_inlined() {
    let circuits: &[(&str, &str, &str, fn())] = &[
        (
            "add_sub_lui_auipc_mop",
            "../prover/test_proofs/add_sub_lui_auipc_mop_gkr_proof.json",
            "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_gkr.json",
            verify_add_sub,
        ),
        (
            "jump_branch_slt",
            "../prover/test_proofs/jump_branch_slt_gkr_proof.json",
            "../cs/compiled_circuits/jump_branch_slt_preprocessed_layout_gkr.json",
            verify_jump_branch_slt,
        ),
        (
            "shift_binop",
            "../prover/test_proofs/shift_binop_gkr_proof.json",
            "../cs/compiled_circuits/shift_binop_preprocessed_layout_gkr.json",
            verify_shift_binop,
        ),
    ];

    for &(name, proof_path, circuit_path, verify_fn) in circuits {
        run_gkr_verify_for_circuit(name, proof_path, circuit_path, verify_fn);
    }
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_gkr_sumcheck_verify_inlined_rejects_corrupted_proof() {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::gkr::prover::GKRProof;
    use prover::merkle_trees::DefaultTreeConstructor;
    use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
    use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
    use verifier_common::prover::nd_source_std::*;

    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file("../prover/test_proofs/add_sub_lui_auipc_mop_gkr_proof.json");
    let compiled_circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_gkr.json",
    );

    let mut oracle_data = flatten_gkr_proof_for_nds::<
        BabyBearField,
        BabyBearExt4,
        DefaultTreeConstructor,
    >(&proof, &compiled_circuit);

    // Corrupt a word in the sumcheck coefficient region (past the transcript preamble and evaluations)
    let corrupt_idx = oracle_data.len() / 2;
    oracle_data[corrupt_idx] ^= 1;

    let result = std::thread::Builder::new()
        .name("gkr verifier corrupted".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            set_iterator(oracle_data.into_iter());
            generated_add_sub_lui_auipc_mop::verify_gkr_sumcheck::<ThreadLocalBasedSource>()
        })
        .expect("failed to spawn thread")
        .join()
        .expect("verifier thread panicked");

    assert!(
        result.is_err(),
        "verifier should reject corrupted proof data"
    );
}

#[cfg(feature = "gkr_verify")]
fn run_gkr_verifier_in_transpiler(
    name: &str,
    proof_path: &str,
    circuit_path: &str,
    binary_suffix: &str,
) {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::gkr::prover::GKRProof;
    use prover::merkle_trees::DefaultTreeConstructor;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::simple_instruction_set::*;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;
    use riscv_transpiler::vm::*;
    use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
    use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;

    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file(proof_path);
    let compiled_circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(circuit_path);

    let oracle_data = flatten_gkr_proof_for_nds::<
        BabyBearField,
        BabyBearExt4,
        DefaultTreeConstructor,
    >(&proof, &compiled_circuit);

    println!(
        "{}: oracle data length: {} u32 words",
        name,
        oracle_data.len()
    );

    let bin_path = format!("../tools/gkr_verifier/{}.bin", binary_suffix);
    let text_path = format!("../tools/gkr_verifier/{}.text", binary_suffix);
    let elf_path = format!("../tools/gkr_verifier/{}.elf", binary_suffix);

    let binary_bytes = std::fs::read(&bin_path).expect(&format!(
        "Missing {} — run `cd tools/gkr_verifier && ./dump_bin.sh` first",
        bin_path
    ));
    assert!(binary_bytes.len() % 4 == 0);
    let binary: Vec<u32> = binary_bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();

    let text_bytes = std::fs::read(&text_path).expect(&format!(
        "Missing {} — run `cd tools/gkr_verifier && ./dump_bin.sh` first",
        text_path
    ));
    assert!(text_bytes.len() % 4 == 0);
    let text_section: Vec<u32> = text_bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let cycles_bound = 1 << 24;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(oracle_data);

    let symbols_path = std::path::PathBuf::from(&elf_path);
    let output_path = std::env::current_dir()
        .unwrap()
        .join(format!("gkr_flamegraph_{}.svg", binary_suffix));
    let mut fg_config =
        riscv_transpiler::vm::FlamegraphConfig::new(symbols_path, output_path.clone());
    fg_config.frequency_recip = 1; // sample every cycle for accuracy
    let mut profiler = riscv_transpiler::vm::VmFlamegraphProfiler::new(fg_config).unwrap();

    let is_program_finished =
        VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled_with_flamegraph::<
            _,
            _,
            _,
            field::baby_bear::base::BabyBearField,
        >(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut non_determinism,
            &mut profiler,
        )
        .expect("flamegraph profiler IO error");

    assert!(
        is_program_finished,
        "{}: GKR verifier program did not finish (PC stuck or cycle bound reached)",
        name
    );

    let exact_cycles =
        (state.timestamp - common_constants::INITIAL_TIMESTAMP) / common_constants::TIMESTAMP_STEP;
    println!("{}: GKR verifier finished in {} cycles", name, exact_cycles);

    println!("  PC = 0x{:08x}", state.pc);
    for (i, reg) in state.registers[10..18].iter().enumerate() {
        println!("  a{} = 0x{:08x} ({})", i, reg.value, reg.value);
    }

    let a0 = state.registers[10].value;
    if a0 == 0xDEAD {
        let error_code = state.registers[11].value;
        let layer = state.registers[12].value;
        let round = state.registers[13].value;
        match error_code {
            1 => panic!(
                "{}: GKR SumcheckRoundFailed at layer={}, round={}",
                name, layer, round
            ),
            2 => panic!("{}: GKR FinalStepCheckFailed at layer={}", name, layer),
            _ => panic!("{}: GKR unknown error code={}", name, error_code),
        }
    }
    assert_eq!(
        a0, 1,
        "{}: GKR verifier failed: a0 = {} (expected 1 for success)",
        name, a0
    );

    println!(
        "{}: GKR verifier completed successfully in transpiler",
        name
    );
    println!("Flamegraph written to {}", output_path.display());
}

#[test]
#[cfg(feature = "gkr_verify")]
#[ignore = "requires RISC-V binaries from tools/gkr_verifier"]
fn test_gkr_verifier_in_transpiler() {
    let circuits: &[(&str, &str, &str, &str)] = &[
        (
            "add_sub_lui_auipc_mop",
            "../prover/test_proofs/add_sub_lui_auipc_mop_gkr_proof.json",
            "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_gkr.json",
            "add_sub",
        ),
        (
            "jump_branch_slt",
            "../prover/test_proofs/jump_branch_slt_gkr_proof.json",
            "../cs/compiled_circuits/jump_branch_slt_preprocessed_layout_gkr.json",
            "jump_branch_slt",
        ),
        (
            "shift_binop",
            "../prover/test_proofs/shift_binop_gkr_proof.json",
            "../cs/compiled_circuits/shift_binop_preprocessed_layout_gkr.json",
            "shift_binop",
        ),
    ];

    for &(name, proof_path, circuit_path, binary_suffix) in circuits {
        run_gkr_verifier_in_transpiler(name, proof_path, circuit_path, binary_suffix);
    }
}
