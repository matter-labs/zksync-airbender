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

#[cfg(feature = "gkr_verify")]
fn flatten_ext4(el: field::baby_bear::ext4::BabyBearExt4) -> [u32; 4] {
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use field::{FieldExtension, FixedArrayConvertible, PrimeField};

    let coeffs = <BabyBearExt4 as FieldExtension<BabyBearField>>::into_coeffs(el);
    let arr: [BabyBearField; 4] = coeffs.into_array();
    arr.map(|f| f.as_u32_raw_repr_reduced())
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_whir_sumcheck_step_valid() {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use verifier_common::prover::nd_source_std::*;

    let c0 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(42),
    );
    let c1 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(7),
    );
    let c2 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(13),
    );
    let coeffs = [c0, c1, c2];

    let mut p1 = c0;
    p1.add_assign(&c1);
    p1.add_assign(&c2);
    let mut claim = c0;
    claim.add_assign(&p1);

    let mut nds_words = Vec::new();
    for &c in &coeffs {
        nds_words.extend(flatten_ext4(c));
    }

    let result = std::thread::Builder::new()
        .name("whir_sumcheck_step".into())
        .stack_size(1 << 24)
        .spawn(move || {
            set_iterator(nds_words.into_iter());

            use verifier_common::blake2s_u32::DelegatedBlake2sState;
            use verifier_common::transcript::Seed;

            let mut seed = Seed::default();
            let mut hasher = DelegatedBlake2sState::new();

            let result = generated_add_sub_lui_auipc_mop::common::verify_whir_sumcheck_step::<
                ThreadLocalBasedSource,
            >(&mut hasher, &mut seed, claim, 0);

            let (new_claim, alpha) = result.expect("valid sumcheck step should pass");

            let mut expected = c2;
            expected.mul_assign(&alpha);
            expected.add_assign(&c1);
            expected.mul_assign(&alpha);
            expected.add_assign(&c0);
            assert_eq!(new_claim, expected,);
        })
        .unwrap()
        .join();

    match result {
        Ok(()) => println!("whir sumcheck step: valid test passed"),
        Err(e) => std::panic::resume_unwind(e),
    }
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_whir_sumcheck_step_rejects_invalid() {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use verifier_common::prover::nd_source_std::*;

    let c0 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(42),
    );
    let c1 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(7),
    );
    let c2 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(13),
    );

    let mut p1 = c0;
    p1.add_assign(&c1);
    p1.add_assign(&c2);
    let mut claim = c0;
    claim.add_assign(&p1);
    claim.add_assign(&BabyBearExt4::ONE); // corrupt the claim

    let mut nds_words = Vec::new();
    for &c in &[c0, c1, c2] {
        nds_words.extend(flatten_ext4(c));
    }

    let result = std::thread::Builder::new()
        .name("whir_sumcheck_step_invalid".into())
        .stack_size(1 << 24)
        .spawn(move || {
            set_iterator(nds_words.into_iter());

            use verifier_common::blake2s_u32::DelegatedBlake2sState;
            use verifier_common::transcript::Seed;

            let mut seed = Seed::default();
            let mut hasher = DelegatedBlake2sState::new();

            generated_add_sub_lui_auipc_mop::common::verify_whir_sumcheck_step::<
                ThreadLocalBasedSource,
            >(&mut hasher, &mut seed, claim, 0)
        })
        .unwrap()
        .join()
        .expect("thread should not panic");

    assert!(result.is_err(), "verifier should reject mismatched claim");
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_batch_claims() {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use verifier_common::gkr::LazyVec;

    let sigma0 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(5),
    );
    let sigma1 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(11),
    );
    let sigma2 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(17),
    );

    let gamma = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
        BabyBearField::from_u32_unchecked(3),
    );

    let mut claims: LazyVec<BabyBearExt4, 8> = LazyVec::new();
    claims.push(sigma0);
    claims.push(sigma1);
    claims.push(sigma2);

    let gamma_powers =
        generated_add_sub_lui_auipc_mop::common::materialize_gamma_powers::<3>(gamma);

    assert_eq!(gamma_powers[0], BabyBearExt4::ONE);
    assert_eq!(gamma_powers[1], gamma);
    let mut gamma_sq = gamma;
    gamma_sq.mul_assign(&gamma);
    assert_eq!(gamma_powers[2], gamma_sq);

    let batched =
        generated_add_sub_lui_auipc_mop::common::batch_claims::<3, 8>(&claims, &gamma_powers);

    let mut expected = sigma0;
    let mut term = gamma_powers[1];
    term.mul_assign(&sigma1);
    expected.add_assign(&term);
    let mut term = gamma_powers[2];
    term.mul_assign(&sigma2);
    expected.add_assign(&term);

    assert_eq!(batched, expected);

    // Test with non-trivial extension field elements (all 4 limbs nonzero)
    let ext = |a: u32, b: u32, c: u32, d: u32| -> BabyBearExt4 {
        <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs([
            BabyBearField::from_u32_unchecked(a),
            BabyBearField::from_u32_unchecked(b),
            BabyBearField::from_u32_unchecked(c),
            BabyBearField::from_u32_unchecked(d),
        ])
    };

    let s0 = ext(1, 2, 3, 4);
    let s1 = ext(5, 6, 7, 8);
    let g = ext(9, 10, 11, 12);

    let mut claims2: LazyVec<BabyBearExt4, 4> = LazyVec::new();
    claims2.push(s0);
    claims2.push(s1);

    let gp = generated_add_sub_lui_auipc_mop::common::materialize_gamma_powers::<2>(g);
    let batched2 = generated_add_sub_lui_auipc_mop::common::batch_claims::<2, 4>(&claims2, &gp);

    let mut expected2 = s0;
    let mut t = gp[1];
    t.mul_assign(&s1);
    expected2.add_assign(&t);
    assert_eq!(batched2, expected2, "batch with full ext4 elements");
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_verify_merkle_path() {
    use verifier_common::blake2s_u32::{
        Blake2sState, DelegatedBlake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS,
        BLAKE2S_DIGEST_SIZE_U32_WORDS,
    };
    use verifier_common::prover::nd_source_std::*;

    let leaves: [[u32; 8]; 4] = [
        [1, 2, 3, 4, 5, 6, 7, 8],
        [9, 10, 11, 12, 13, 14, 15, 16],
        [17, 18, 19, 20, 21, 22, 23, 24],
        [25, 26, 27, 28, 29, 30, 31, 32],
    ];

    let mut node_01 = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    block[..8].copy_from_slice(&leaves[0]);
    block[8..].copy_from_slice(&leaves[1]);
    Blake2sState::compress_two_to_one::<true>(&block, &mut node_01);

    let mut node_23 = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    block[..8].copy_from_slice(&leaves[2]);
    block[8..].copy_from_slice(&leaves[3]);
    Blake2sState::compress_two_to_one::<true>(&block, &mut node_23);

    let mut root = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    block[..8].copy_from_slice(&node_01);
    block[8..].copy_from_slice(&node_23);
    Blake2sState::compress_two_to_one::<true>(&block, &mut root);

    {
        let mut nds_words = Vec::new();
        nds_words.extend_from_slice(&leaves[1]);
        nds_words.extend_from_slice(&node_23);

        let result = std::thread::Builder::new()
            .name("merkle_valid".into())
            .stack_size(1 << 24)
            .spawn(move || {
                set_iterator(nds_words.into_iter());
                let mut hasher = DelegatedBlake2sState::new();
                hasher.state = leaves[0];

                verifier_common::whir::verify_merkle_path::<ThreadLocalBasedSource>(
                    &mut hasher,
                    0,
                    2,
                    &root,
                )
            })
            .unwrap()
            .join()
            .expect("thread should not panic");

        assert!(result, "valid Merkle path should verify");
    }

    {
        let mut nds_words = Vec::new();
        nds_words.extend_from_slice(&leaves[2]);
        nds_words.extend_from_slice(&node_01);

        let result = std::thread::Builder::new()
            .name("merkle_valid_leaf3".into())
            .stack_size(1 << 24)
            .spawn(move || {
                set_iterator(nds_words.into_iter());
                let mut hasher = DelegatedBlake2sState::new();
                hasher.state = leaves[3];

                verifier_common::whir::verify_merkle_path::<ThreadLocalBasedSource>(
                    &mut hasher,
                    3,
                    2,
                    &root,
                )
            })
            .unwrap()
            .join()
            .expect("thread should not panic");

        assert!(result, "valid Merkle path for leaf 3 should verify");
    }

    {
        let mut bad_sibling = leaves[1];
        bad_sibling[0] ^= 0xDEADBEEF;

        let mut nds_words = Vec::new();
        nds_words.extend_from_slice(&bad_sibling);
        nds_words.extend_from_slice(&node_23);

        let result = std::thread::Builder::new()
            .name("merkle_invalid".into())
            .stack_size(1 << 24)
            .spawn(move || {
                set_iterator(nds_words.into_iter());
                let mut hasher = DelegatedBlake2sState::new();
                hasher.state = leaves[0];

                verifier_common::whir::verify_merkle_path::<ThreadLocalBasedSource>(
                    &mut hasher,
                    0,
                    2,
                    &root,
                )
            })
            .unwrap()
            .join()
            .expect("thread should not panic");

        assert!(!result, "corrupted sibling should fail verification");
    }
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_fold_coset() {
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};

    let from_base = |v: u32| -> BabyBearExt4 {
        <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
            BabyBearField::from_u32_unchecked(v),
        )
    };

    let two_inv = BabyBearField::from_u32_unchecked(2).inverse().unwrap();

    {
        let evals = [from_base(10), from_base(20)];
        let challenge = from_base(7);
        let root_inv = BabyBearField::from_u32_unchecked(5);
        let offsets = [BabyBearField::ONE]; // single pair

        let mut buf_a = [BabyBearExt4::ZERO; 1];
        let mut buf_b = [BabyBearExt4::ZERO; 1];

        let result = generated_add_sub_lui_auipc_mop::common::fold_coset(
            &evals,
            1,
            &[challenge],
            root_inv,
            &offsets,
            two_inv,
            &mut buf_a,
            &mut buf_b,
        );

        let a = evals[0];
        let b = evals[1];
        let mut expected = a;
        expected.sub_assign(&b);
        expected.mul_assign(&challenge);
        let mut root = root_inv;
        root.mul_assign(&offsets[0]);
        expected.mul_assign_by_base(&root);
        expected.add_assign(&a);
        expected.add_assign(&b);
        expected.mul_assign_by_base(&two_inv);

        assert_eq!(result, expected, "K=1 fold_coset");
    }

    {
        let evals = [from_base(3), from_base(7), from_base(11), from_base(13)];
        let challenges = [from_base(2), from_base(5)];
        let root_inv = BabyBearField::from_u32_unchecked(3);
        let offsets = [BabyBearField::ONE, BabyBearField::from_u32_unchecked(9)];

        let mut buf_a = [BabyBearExt4::ZERO; 2];
        let mut buf_b = [BabyBearExt4::ZERO; 2];

        let result = generated_add_sub_lui_auipc_mop::common::fold_coset(
            &evals,
            2,
            &challenges,
            root_inv,
            &offsets,
            two_inv,
            &mut buf_a,
            &mut buf_b,
        );

        let fold_pair = |a: BabyBearExt4,
                         b: BabyBearExt4,
                         ch: BabyBearExt4,
                         ri: BabyBearField,
                         off: BabyBearField,
                         ti: BabyBearField|
         -> BabyBearExt4 {
            let mut t = a;
            t.sub_assign(&b);
            t.mul_assign(&ch);
            let mut r = ri;
            r.mul_assign(&off);
            t.mul_assign_by_base(&r);
            t.add_assign(&a);
            t.add_assign(&b);
            t.mul_assign_by_base(&ti);
            t
        };

        let t0 = fold_pair(
            evals[0],
            evals[1],
            challenges[0],
            root_inv,
            offsets[0],
            two_inv,
        );
        let t1 = fold_pair(
            evals[2],
            evals[3],
            challenges[0],
            root_inv,
            offsets[1],
            two_inv,
        );

        let mut root_inv_sq = root_inv;
        root_inv_sq.square();
        let expected = fold_pair(t0, t1, challenges[1], root_inv_sq, offsets[0], two_inv);

        assert_eq!(result, expected, "K=2 fold_coset");
    }
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_read_and_verify_pow_valid_nonce() {
    use prover::worker::Worker;
    use verifier_common::prover::nd_source_std::*;
    use verifier_common::transcript::Blake2sTranscript;
    use verifier_common::whir::read_and_verify_pow;

    let seed = Blake2sTranscript::commit_initial(&[1, 2, 3, 4, 5, 6, 7, 8]);
    let pow_bits = 8u32;

    let worker = Worker::new_with_num_threads(1);
    let (post_pow_seed, nonce) = Blake2sTranscript::search_pow(&seed, pow_bits, &worker);

    std::thread::Builder::new()
        .stack_size(1 << 24)
        .spawn(move || {
            let nonce_lo = nonce as u32;
            let nonce_hi = (nonce >> 32) as u32;
            set_iterator(vec![nonce_lo, nonce_hi].into_iter());

            let mut seed_copy = seed;
            read_and_verify_pow::<ThreadLocalBasedSource>(&mut seed_copy, pow_bits);
            assert_eq!(seed_copy, post_pow_seed);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_read_and_verify_pow_invalid_nonce_panics() {
    use prover::worker::Worker;
    use verifier_common::prover::nd_source_std::*;
    use verifier_common::transcript::Blake2sTranscript;
    use verifier_common::whir::read_and_verify_pow;

    let seed = Blake2sTranscript::commit_initial(&[1, 2, 3, 4, 5, 6, 7, 8]);
    let pow_bits = 8u32;

    let worker = Worker::new_with_num_threads(1);
    let (_, nonce) = Blake2sTranscript::search_pow(&seed, pow_bits, &worker);

    let bad_nonce = nonce.wrapping_add(1);
    let result = std::thread::Builder::new()
        .stack_size(1 << 24)
        .spawn(move || {
            let nonce_lo = bad_nonce as u32;
            let nonce_hi = (bad_nonce >> 32) as u32;
            set_iterator(vec![nonce_lo, nonce_hi].into_iter());

            let mut seed_copy = seed;
            read_and_verify_pow::<ThreadLocalBasedSource>(&mut seed_copy, pow_bits);
        })
        .unwrap()
        .join();

    assert!(
        result.is_err(),
        "Off-by-one nonce should cause verify_pow to panic"
    );
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_draw_query_indices_deterministic() {
    use verifier_common::blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
    use verifier_common::transcript::Blake2sTranscript;
    use verifier_common::whir::draw_query_indices_vec;

    let seed = Blake2sTranscript::commit_initial(&[10, 20, 30, 40, 50, 60, 70, 80]);
    let num_queries = 16usize;
    let query_index_bits = 18usize;
    let num_required_words = (query_index_bits * num_queries).next_multiple_of(32) / 32;
    let draw_words = (num_required_words + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);

    let mut seed1 = seed;
    let mut hasher1 = DelegatedBlake2sState::new();
    let indices1 = draw_query_indices_vec(
        &mut hasher1,
        &mut seed1,
        num_queries,
        query_index_bits,
        draw_words,
    );

    let mut seed2 = seed;
    let mut hasher2 = DelegatedBlake2sState::new();
    let indices2 = draw_query_indices_vec(
        &mut hasher2,
        &mut seed2,
        num_queries,
        query_index_bits,
        draw_words,
    );

    assert_eq!(
        indices1, indices2,
        "Same seed should produce same query indices"
    );
    assert_eq!(seed1, seed2, "Seeds should match after drawing");
}

#[test]
#[cfg(feature = "gkr_verify")]
fn test_draw_query_indices_in_range() {
    use verifier_common::blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
    use verifier_common::transcript::Blake2sTranscript;
    use verifier_common::whir::draw_query_indices_vec;

    let seed = Blake2sTranscript::commit_initial(&[99, 98, 97, 96, 95, 94, 93, 92]);
    let num_queries = 32usize;
    let query_index_bits = 12usize;
    let max_index = 1usize << query_index_bits;
    let num_required_words = (query_index_bits * num_queries).next_multiple_of(32) / 32;
    let draw_words = (num_required_words + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);

    let mut seed_copy = seed;
    let mut hasher = DelegatedBlake2sState::new();
    let indices = draw_query_indices_vec(
        &mut hasher,
        &mut seed_copy,
        num_queries,
        query_index_bits,
        draw_words,
    );

    assert_eq!(indices.len(), num_queries);
    for (i, &idx) in indices.iter().enumerate() {
        assert!(
            idx < max_index,
            "Query index {i} = {idx} exceeds max {max_index}"
        );
    }
}
