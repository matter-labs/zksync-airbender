//! End-to-end recursive proving pipeline, expressed as a series of tests.
//!
//! Flow (each stage proves a RISC-V program and feeds its proof into the next
//! stage's verifier program as non-determinism):
//!
//! 1. Prove the `zksync_os` app+witness as a **base layer** program (unrolled
//!    machine mode, IM ISA + delegations). Verify natively.
//! 2. Feed that proof into `fsv_unrolled_base_layer_sec_80` and prove it
//!    (unrolled machine mode, reduced ISA + delegations). Verify natively.
//! 3. Feed into `fsv_unrolled_recursion_layer_sec_80`, prove (unrolled, reduced).
//!    Repeat this step while a single verifier invocation still needs >= 64M
//!    cycles to run.
//! 4. Once a verifier invocation would take < 64M cycles, **bridge** to the
//!    unified machine: re-prove `fsv_unrolled_recursion_layer_sec_80` in
//!    **unified** machine mode (this re-proves the same verifier over the last
//!    unrolled proof, but emits a *unified* single-circuit proof).
//! 5. Feed the unified proof into `fsv_unified_recursion_layer_sec_80` and prove
//!    it in unified machine mode. Verify natively.
//!
//! The whole pipeline is a single `#[ignore]`d heavy test; the pure helpers
//! (hash-chain math, hex witness parsing) are covered by cheap unit tests.

#[cfg(all(test, feature = "verifiers"))]
mod tests {
    use crate::serialize_to_file;
use crate::unified::prove_unified_execution_with_replayer;
    use crate::unrolled::prove_unrolled_execution_with_replayer;
    use common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
    use full_statement_verifier::program_proof::ProgramProof;
    use full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer;
    use full_statement_verifier::unrolled_proof_statement::{
        verify_unrolled_base_layer, verify_unrolled_recursion_layer,
    };
    use prover::definitions::{MerkleTreeCap, SecurityLevel};
    use prover::worker::Worker;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::cycle::{
        IMStandardIsaConfigUnsignedMulDivOnly, ReducedMachineWithDelegation,
    };
    use setups::UnrolledCircuitSetupParams;
    use std::alloc::Global;
    use std::collections::BTreeMap;
    use std::path::Path;
    use test_utils::skip_if_ci;
    use verifier_common::errors::DebugErrorCreator;
    use verifier_common::transcript::Blake2sBufferingTranscript;

    /// REDUCED_ROUNDS variant the sec-80 verifier binaries are compiled with.
    const REDUCED_ROUNDS: bool = true;

    /// Once a single full-statement-verifier invocation would run in fewer than
    /// this many cycles, the unified machine (a few 1<<24 instances) can prove
    /// it, so we stop unrolled recursion and bridge to unified.
    const UNIFIED_SWITCH_CYCLES: u64 = 64 * 1024 * 1024;

    // Per-stage cycle/RAM bounds (generous; the prover chunks into as many
    // circuit instances as the actual run needs).
    const BASE_CYCLES_BOUND: usize = 1 << 31;
    const UNROLLED_RECURSION_CYCLES_BOUND: usize = 1 << 27;
    const UNIFIED_CYCLES_BOUND: usize = 1 << 26;
    const RAM_BOUND: usize = 1 << 30;

    type Setups = BTreeMap<u32, UnrolledCircuitSetupParams>;

    // ---- pure helpers -------------------------------------------------------

    /// Parse a hex-text witness dump (`23620012_witness`): one contiguous string
    /// of 8-hex-char big-endian u32 words. Mirrors `cli::u32_from_hex_string`.
    fn read_hex_witness(path: &Path) -> Vec<u32> {
        let raw = std::fs::read_to_string(path).expect("read witness file");
        let raw = raw.trim();
        assert!(
            raw.len() % 8 == 0,
            "witness hex length {} is not a multiple of 8",
            raw.len()
        );
        raw.as_bytes()
            .chunks(8)
            .map(|c| {
                u32::from_str_radix(std::str::from_utf8(c).unwrap(), 16).expect("invalid hex word")
            })
            .collect()
    }

    /// `end_params` of a program: blake(final_pc_buffer || each setup cap).
    /// Mirrors the `end_params_output` hashing inside the full-statement verifier.
    fn compute_end_params(setups: &Setups, final_pc: u32) -> [u32; 8] {
        let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
        let mut buffer = [0u32; 16];
        buffer[0] = final_pc;
        hasher.absorb(&buffer);
        for params in setups.values() {
            hasher.absorb(MerkleTreeCap::flatten_single(&params.setup_caps));
        }
        hasher.finalize_reset().0
    }

    /// Start a recursion chain from the base-layer `end_params`.
    fn begin_chain(base_end_params: &[u32; 8]) -> ([u32; 8], [u32; 16]) {
        let mut preimage = [0u32; 16];
        preimage[8..].copy_from_slice(base_end_params);
        let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
        hasher.absorb(&preimage);
        let hash = hasher.finalize_reset().0;
        (hash, preimage)
    }

    /// Extend the recursion chain by one verifier step's `end_params`.
    fn continue_chain(
        prev_hash: &[u32; 8],
        prev_preimage: &[u32; 16],
        end_params: &[u32; 8],
    ) -> ([u32; 8], [u32; 16]) {
        if &prev_preimage[8..] == &end_params[..] {
            // chaining the same program again: nothing new to commit.
            (*prev_hash, *prev_preimage)
        } else {
            let mut preimage = [0u32; 16];
            preimage[..8].copy_from_slice(prev_hash);
            preimage[8..].copy_from_slice(end_params);
            let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
            hasher.absorb(&preimage);
            let hash = hasher.finalize_reset().0;
            (hash, preimage)
        }
    }

    /// nd stream for an unrolled (multi-circuit) proof: setup caps then the
    /// flattened proof (which already carries the recursion preimage, if any).
    fn build_unrolled_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
        let mut stream: Vec<u32> = setups
            .values()
            .flat_map(|p| MerkleTreeCap::flatten_single(&p.setup_caps).to_vec())
            .collect();
        stream.extend(proof.flatten_for_verification());
        stream
    }

    /// nd stream for a unified (single-circuit) proof.
    fn build_unified_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
        let mut stream: Vec<u32> = setups
            .values()
            .flat_map(|p| MerkleTreeCap::flatten_single(&p.setup_caps).to_vec())
            .collect();
        stream.extend(proof.flatten_unified_for_verification());
        stream
    }

    /// Executed cycle count implied by a proof's final timestamp.
    fn proof_cycles(proof: &ProgramProof) -> u64 {
        (proof.final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
    }

    // ---- native verification (sanity-check each proof before recursing) -----

    fn native_verify_unrolled(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
        std::thread::Builder::new()
            .name("unrolled verifier".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let mut it = stream.into_iter();
                let result = if is_base {
                    verify_unrolled_base_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut it)
                } else {
                    verify_unrolled_recursion_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut it)
                };
                result.expect("unrolled proof must verify")
            })
            .expect("spawn verifier thread")
            .join()
            .expect("verifier thread must not panic")
    }

    fn native_verify_unified(stream: Vec<u32>) -> [u32; 16] {
        std::thread::Builder::new()
            .name("unified verifier".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let mut it = stream.into_iter();
                verify_unified_circuit_recursion_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(
                    &mut it,
                )
                .expect("unified proof must verify")
            })
            .expect("spawn verifier thread")
            .join()
            .expect("verifier thread must not panic")
    }

    // ---- program loading ----------------------------------------------------

    fn load_program(bin: &str, text: &str) -> (Vec<u32>, Vec<u32>) {
        let (_, binary_image) = setups::read_and_pad_binary(Path::new(bin));
        let (_, text_section) = setups::read_and_pad_binary(Path::new(text));
        // let (_, text_section) = read_binary(Path::new(text));
        (binary_image, text_section)
    }

    fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
        use std::io::Read;
        let mut file = std::fs::File::open(path).expect("must open provided file");
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).expect("must read the file");
        assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
        let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
        for el in buffer.as_chunks::<4>().0 {
            binary.push(u32::from_le_bytes(*el));
        }

        (buffer, binary)
    }

    const FSV_DIR: &str = "../../tools/gkr_verifier";

    fn fsv_program(name: &str) -> (Vec<u32>, Vec<u32>) {
        load_program(
            &format!("{FSV_DIR}/{name}.bin"),
            &format!("{FSV_DIR}/{name}.text"),
        )
    }

    // ---- pure-helper unit tests (cheap) -------------------------------------

    #[test]
    fn hex_witness_parses() {
        // "00000002" -> 2, "00000288" -> 0x288.
        let tmp = std::env::temp_dir().join("recursion_hex_witness_test.txt");
        std::fs::write(&tmp, "0000000200000288").unwrap();
        let words = read_hex_witness(&tmp);
        assert_eq!(words, vec![2, 0x288]);
        let _ = std::fs::remove_file(&tmp);
    }

    #[test]
    fn recursion_chain_is_consistent() {
        // begin then continue with a different program extends the chain;
        // continuing with the same end_params is idempotent.
        let ep_base = [1u32, 2, 3, 4, 5, 6, 7, 8];
        let (h0, p0) = begin_chain(&ep_base);
        assert_eq!(&p0[8..], &ep_base);

        let ep_step = [9u32, 10, 11, 12, 13, 14, 15, 16];
        let (h1, p1) = continue_chain(&h0, &p0, &ep_step);
        assert_ne!(h1, h0, "a new program must advance the chain");
        assert_eq!(&p1[..8], &h0);
        assert_eq!(&p1[8..], &ep_step);

        // re-chaining the same program is a no-op.
        let (h2, p2) = continue_chain(&h1, &p1, &ep_step);
        assert_eq!(h2, h1);
        assert_eq!(p2, p1);
    }

    // ---- the full pipeline (heavy) ------------------------------------------

    #[test]
    #[ignore = "manual heavy recursive-proving pipeline (hours, large RAM)"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_recursive_proving_pipeline_zksync_os() {
        skip_if_ci!();

        let use_caches = true;
        let worker = Worker::new_with_num_threads(8);

        // === Stage 1: base layer — prove zksync_os app + witness (IM ISA). ===
        let (zksync_bin, zksync_text) = load_program(
            "../../riscv_transpiler/examples/zksync_os/app.bin",
            "../../riscv_transpiler/examples/zksync_os/app.text",
        );
        let zksync_witness = read_hex_witness(Path::new(
            "../../riscv_transpiler/examples/zksync_os/23620012_witness",
        ));

        let pc = 30238;
        println!("PC[{} * 4] = 0x{:08x}", pc, zksync_text[pc]);

        println!("=== Stage 1: proving zksync_os base layer ===");
        let (base_proof, base_setups) = prove_unrolled_execution_with_replayer::<
            IMStandardIsaConfigUnsignedMulDivOnly,
            Global,
        >(
            BASE_CYCLES_BOUND,
            &zksync_bin,
            &zksync_text,
            use_caches,
            QuasiUARTSource::new_with_reads(zksync_witness),
            RAM_BOUND,
            &worker,
            SecurityLevel::Sec80,
            0,
        );
        println!("Base proofs are done");
        serialize_to_file(&base_proof, "base_proofs.bin");
        serialize_to_file(&base_setups, "base_setups.bin");

        // sanity: base proof verifies on the native machine.
        native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);

        let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
        let (mut chain_hash, mut chain_preimage) = begin_chain(&base_end_params);

        let mut total_cycles = proof_cycles(&base_proof);
        println!("zksync_os base layer ran {total_cycles} cycles");

        // === Stages 2-3: unrolled recursion (reduced ISA) until a verifier
        //                 invocation drops below the unified-switch threshold. ===
        let (unrolled_base_bin, unrolled_base_text) = fsv_program("fsv_unrolled_base_layer_sec_80");
        let (unrolled_rec_bin, unrolled_rec_text) =
            fsv_program("fsv_unrolled_recursion_layer_sec_80");

        let mut proof = base_proof;
        let mut setups = base_setups;
        let mut input_is_base = true;

        loop {
            let (bin, text) = if input_is_base {
                (&unrolled_base_bin, &unrolled_base_text)
            } else {
                (&unrolled_rec_bin, &unrolled_rec_text)
            };
            let stream = build_unrolled_stream(&setups, &proof);

            println!(
                "=== unrolled recursion over a {} proof ===",
                if input_is_base { "base" } else { "recursion" }
            );
            let (mut new_proof, new_setups) =
                prove_unrolled_execution_with_replayer::<ReducedMachineWithDelegation, Global>(
                    UNROLLED_RECURSION_CYCLES_BOUND,
                    bin,
                    text,
                    use_caches,
                    QuasiUARTSource::new_with_reads(stream),
                    RAM_BOUND,
                    &worker,
                    SecurityLevel::Sec80,
                    0,
                );
            new_proof.recursion_chain_hash = Some(chain_hash);
            new_proof.recursion_chain_preimage = Some(chain_preimage);

            let round_cycles = proof_cycles(&new_proof);
            total_cycles += round_cycles;
            println!("unrolled recursion round ran {round_cycles} cycles (total {total_cycles})");

            // sanity verify (this proof carries a recursion preimage).
            native_verify_unrolled(build_unrolled_stream(&new_setups, &new_proof), false);

            let end_params = compute_end_params(&new_setups, new_proof.final_pc);
            let (h, p) = continue_chain(&chain_hash, &chain_preimage, &end_params);
            chain_hash = h;
            chain_preimage = p;

            proof = new_proof;
            setups = new_setups;
            input_is_base = false;

            if round_cycles < UNIFIED_SWITCH_CYCLES {
                println!("verifier invocation now < 64M cycles — switching to unified machine");
                break;
            }
        }

        // === Stage 4: bridge — re-prove the unrolled-recursion verifier over
        //              the last unrolled proof, but in UNIFIED machine mode, so
        //              its proof is a single unified circuit. ===
        println!("=== bridge: proving fsv_unrolled_recursion_layer in unified mode ===");
        let bridge_stream = build_unrolled_stream(&setups, &proof);
        let (mut bridge_proof, bridge_setups) = prove_unified_execution_with_replayer::<Global>(
            UNIFIED_CYCLES_BOUND,
            &unrolled_rec_bin,
            &unrolled_rec_text,
            use_caches,
            QuasiUARTSource::new_with_reads(bridge_stream),
            RAM_BOUND,
            &worker,
            SecurityLevel::Sec80,
            0,
        );
        bridge_proof.recursion_chain_hash = Some(chain_hash);
        bridge_proof.recursion_chain_preimage = Some(chain_preimage);
        total_cycles += proof_cycles(&bridge_proof);

        native_verify_unified(build_unified_stream(&bridge_setups, &bridge_proof));

        let bridge_end_params = compute_end_params(&bridge_setups, bridge_proof.final_pc);
        let (h, p) = continue_chain(&chain_hash, &chain_preimage, &bridge_end_params);
        chain_hash = h;
        chain_preimage = p;
        proof = bridge_proof;
        setups = bridge_setups;

        // === Stage 5: final — prove fsv_unified_recursion_layer over the
        //              unified bridge proof, in unified machine mode. ===
        println!("=== final: proving fsv_unified_recursion_layer in unified mode ===");
        let (unified_rec_bin, unified_rec_text) = fsv_program("fsv_unified_recursion_layer_sec_80");
        let final_stream = build_unified_stream(&setups, &proof);
        let (mut final_proof, final_setups) = prove_unified_execution_with_replayer::<Global>(
            UNIFIED_CYCLES_BOUND,
            &unified_rec_bin,
            &unified_rec_text,
            use_caches,
            QuasiUARTSource::new_with_reads(final_stream),
            RAM_BOUND,
            &worker,
            SecurityLevel::Sec80,
            0,
        );
        final_proof.recursion_chain_hash = Some(chain_hash);
        final_proof.recursion_chain_preimage = Some(chain_preimage);
        total_cycles += proof_cycles(&final_proof);

        let final_output = native_verify_unified(build_unified_stream(&final_setups, &final_proof));

        println!("=== pipeline complete: {total_cycles} total cycles proven ===");
        println!("final recursion-chain output registers: {final_output:?}");
    }

    #[test]
    #[serial_test::serial]
    fn load_binary() {
        use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
        use riscv_transpiler::ir::simple_instruction_set::*;

        let (zksync_bin, zksync_text) = load_program(
            "../../riscv_transpiler/examples/zksync_os/app.bin",
            "../../riscv_transpiler/examples/zksync_os/app.text",
        );

        println!("0x{:08x}", zksync_text[0x0013ce00 / 4]);

        let instructions: Vec<Instruction> =
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&zksync_text);
    }
}
