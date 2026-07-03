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
//!    Before each round we *measure* how many cycles running the verifier over
//!    the current proof would take; we keep recursing on the unrolled machine
//!    while that stays at/above a configurable threshold.
//! 4. Once the measured verifier run drops below the threshold
//!    (`RECURSION_UNIFIED_SWITCH_CYCLES`, default 64M), **bridge** to the unified
//!    machine: re-prove the unrolled verifier over the last unrolled proof in
//!    **unified** machine mode, emitting a *unified* single-circuit proof.
//! 5. Feed the unified proof into `fsv_unified_recursion_layer_sec_80` and prove
//!    it in unified machine mode. Verify natively.
//!
//! Blake variants of the recursive verifiers are selected at runtime, per stage:
//! `RECURSION_UNROLLED_BLAKE` / `RECURSION_BRIDGE_BLAKE` / `RECURSION_FINAL_BLAKE`
//! (see `full_statement_verifier::host_utils` for the selection rules). Build
//! the matching binaries with `tools/gkr_verifier/dump_recursive_verifiers.sh`.
//! Intermediate proofs/setups are cached to disk, keyed by the active blake
//! variants so different options don't overwrite each other.
//!
//! The protocol pieces (recursion hash chain, `end_params` hashing, nd-stream
//! layout, binary registry) live in `full_statement_verifier::recursion_chain`,
//! `full_statement_verifier::host_utils` and `verifier_common::fsv_binaries`;
//! this pipeline consumes only the exported API

#[cfg(all(test, feature = "verifiers"))]
mod tests {
    use super::scripts::*;
    use crate::unified::prove_unified_execution_with_replayer;
    use crate::unrolled::prove_unrolled_execution_with_replayer;
    use crate::unrolled::run_unrolled_machine_in_full;
    use crate::*;
    use common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
    use full_statement_verifier::host_utils::{
        bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
        final_blake_mode, load_fsv_program, load_program, native_verify_unified,
        native_verify_unrolled, unified_switch_cycles, unrolled_blake_mode, FsvRecursionChain,
    };
    use full_statement_verifier::program_proof::ProgramProof;
    use prover::definitions::SecurityLevel;
    use prover::worker::Worker;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::cycle::{
        IMStandardIsaConfigUnsignedMulDivOnly, ReducedMachineWithDelegation,
    };
    use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
    use setups::Setups;
    use std::alloc::Global;
    use std::path::Path;
    use test_utils::skip_if_ci;
    use verifier_common::fsv_binaries::FsvProgram;

    // Per-stage cycle/RAM bounds (generous; the prover chunks into as many
    // circuit instances as the actual run needs).
    const BASE_CYCLES_BOUND: usize = 1 << 31;
    const UNROLLED_RECURSION_CYCLES_BOUND: usize = 1 << 28;
    const UNIFIED_CYCLES_BOUND: usize = 1 << 27;
    const RAM_BOUND: usize = 1 << 30;

    const FSV_DIR: &str = "../../tools/gkr_verifier";

    // ---- pure helpers -------------------------------------------------------

    /// Parse a hex-text witness dump (`23620012_witness`): one contiguous string
    /// of 8-hex-char big-endian u32 words. Mirrors `cli::u32_from_hex_string`.
    fn read_hex_witness(path: &Path) -> Vec<u32> {
        let raw = std::fs::read_to_string(path).expect("read witness file");
        let raw = raw.trim();
        assert!(
            raw.len().is_multiple_of(8),
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

    /// Run (without proving) the verifier program over `stream` and return the
    /// number of cycles it executes — i.e. how big a circuit proving it needs.
    fn measure_verifier_cycles(
        binary_image: &[u32],
        text_section: &[u32],
        stream: Vec<u32>,
    ) -> u64 {
        let (
            (_final_pc, final_timestamp),
            _snapshotter,
            _counters,
            _ram,
            _registers,
            _tape,
            _state,
        ) = run_unrolled_machine_in_full::<
            ReducedMachineWithDelegation,
            DelegationsAndUnifiedCounters,
        >(
            UNROLLED_RECURSION_CYCLES_BOUND,
            binary_image,
            text_section,
            RAM_BOUND,
            DelegationsAndUnifiedCounters::default(),
            QuasiUARTSource::new_with_reads(stream),
        );
        (final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
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
            Path::new("../../riscv_transpiler/examples/zksync_os/app.bin"),
            Path::new("../../riscv_transpiler/examples/zksync_os/app.text"),
        );
        let zksync_witness = read_hex_witness(Path::new(
            "../../riscv_transpiler/examples/zksync_os/23620012_witness",
        ));

        println!("=== Stage 1: proving zksync_os base layer ===");
        let (base_proof, base_setups) =
            if let Ok(base_proof) = try_deserialize_compressed_from_file("base_proofs.bin") {
                println!("Using existing files for base layer");
                (
                    base_proof,
                    try_deserialize_compressed_from_file("base_setups.bin").unwrap(),
                )
            } else {
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
                serialize_compressed_to_file(&base_proof, "base_proofs.bin");
                serialize_compressed_to_file(&base_setups, "base_setups.bin");

                (base_proof, base_setups)
            };

        // sanity: base proof verifies on the native machine.
        native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
        println!("Base layer proofs pass the verification on native arch");

        let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
        let mut chain = FsvRecursionChain::begin(&base_end_params);

        let mut total_cycles = base_proof.executed_cycles();
        println!("zksync_os base layer ran {total_cycles} cycles");

        // === Stages 2-3: unrolled recursion (reduced ISA). Each round we first
        //                 MEASURE how many cycles running the next verifier would
        //                 take; once that drops below the configurable threshold
        //                 we stop and switch to the unified machine. ===
        let unrolled_blake = unrolled_blake_mode();
        let bridge_blake = bridge_blake_mode();
        let final_blake = final_blake_mode();
        let u_tag = unrolled_blake.tag();
        let bridge_tag = bridge_blake.tag();
        let final_tag = final_blake.tag();
        let switch_cycles = unified_switch_cycles();
        println!(
            "blake modes: unrolled={u_tag}, bridge={bridge_tag}, final={final_tag}; \
             unified-switch threshold {switch_cycles} cycles"
        );

        let (unrolled_base_bin, unrolled_base_text) =
            load_fsv_program(FSV_DIR, FsvProgram::UnrolledBaseLayer, unrolled_blake);
        let (unrolled_rec_bin, unrolled_rec_text) =
            load_fsv_program(FSV_DIR, FsvProgram::UnrolledRecursionLayer, unrolled_blake);

        let mut proof = base_proof;
        let mut setups = base_setups;
        let mut input_is_base = true;
        let mut layer = 0;

        loop {
            let (bin, text) = if input_is_base {
                (&unrolled_base_bin, &unrolled_base_text)
            } else {
                (&unrolled_rec_bin, &unrolled_rec_text)
            };

            // Resume from a previously-proven unrolled layer if present.
            if let Ok(cached_proof) = try_deserialize_compressed_from_file::<ProgramProof>(
                &format!("recursion_layer_{}_proof_{}.bin", layer, u_tag),
            ) {
                println!("Using existing files for unrolled layer {layer}");
                let cached_setups: Setups = try_deserialize_compressed_from_file(&format!(
                    "recursion_layer_{layer}_setups_{u_tag}.bin"
                ))
                .unwrap();
                total_cycles += cached_proof.executed_cycles();
                native_verify_unrolled(build_unrolled_stream(&cached_setups, &cached_proof), false);
                let end_params = compute_end_params(&cached_setups, cached_proof.final_pc);
                chain.extend(&end_params);
                proof = cached_proof;
                setups = cached_setups;
                input_is_base = false;
                layer += 1;
                continue;
            }

            // Measure the next verifier invocation BEFORE proving it.
            let measured =
                measure_verifier_cycles(bin, text, build_unrolled_stream(&setups, &proof));
            println!("running the layer-{layer} verifier would take {measured} cycles");
            if measured < switch_cycles {
                println!("... below {switch_cycles} — switching to the unified machine");
                break;
            }

            println!(
                "=== unrolled recursion over a {} proof (layer {layer}) ===",
                if input_is_base { "base" } else { "recursion" }
            );
            let (mut new_proof, new_setups) =
                prove_unrolled_execution_with_replayer::<ReducedMachineWithDelegation, Global>(
                    UNROLLED_RECURSION_CYCLES_BOUND,
                    bin,
                    text,
                    use_caches,
                    QuasiUARTSource::new_with_reads(build_unrolled_stream(&setups, &proof)),
                    RAM_BOUND,
                    &worker,
                    SecurityLevel::Sec80,
                    0,
                );
            new_proof.set_recursion_chain(&chain);
            serialize_compressed_to_file(
                &new_proof,
                &format!("recursion_layer_{layer}_proof_{u_tag}.bin"),
            );
            serialize_compressed_to_file(
                &new_setups,
                &format!("recursion_layer_{layer}_setups_{u_tag}.bin"),
            );

            let round_cycles = new_proof.executed_cycles();
            total_cycles += round_cycles;
            println!("unrolled recursion round ran {round_cycles} cycles (total {total_cycles})");

            // sanity verify (this proof carries a recursion preimage).
            native_verify_unrolled(build_unrolled_stream(&new_setups, &new_proof), false);

            let end_params = compute_end_params(&new_setups, new_proof.final_pc);
            chain.extend(&end_params);

            proof = new_proof;
            setups = new_setups;
            input_is_base = false;
            layer += 1;
        }

        // === Stage 4: bridge — re-prove the verifier we just measured (the one
        //              that verifies the last unrolled proof) but in UNIFIED
        //              machine mode, so its proof is a single unified circuit.
        //              The bridge binary is an unrolled verifier in its own
        //              (bridge-selected) blake variant; only the *proving
        //              machine* changes. ===
        let bridge_program = if input_is_base {
            FsvProgram::UnrolledBaseLayer
        } else {
            FsvProgram::UnrolledRecursionLayer
        };
        let (bridge_bin, bridge_text) = load_fsv_program(FSV_DIR, bridge_program, bridge_blake);
        println!(
            "=== bridge: proving the unrolled verifier in unified mode (blake {bridge_tag}) ==="
        );
        let (bridge_proof, bridge_setups) = if let Ok(bridge_proof) =
            try_deserialize_compressed_from_file::<ProgramProof>(&format!(
                "bridge_proof_{u_tag}_{bridge_tag}.bin"
            )) {
            println!("Using existing files for bridge layer");
            (
                bridge_proof,
                try_deserialize_compressed_from_file(&format!(
                    "bridge_setups_{u_tag}_{bridge_tag}.bin"
                ))
                .unwrap(),
            )
        } else {
            let (mut bridge_proof, bridge_setups) = prove_unified_execution_with_replayer::<Global>(
                UNIFIED_CYCLES_BOUND,
                &bridge_bin,
                &bridge_text,
                use_caches,
                QuasiUARTSource::new_with_reads(build_unrolled_stream(&setups, &proof)),
                RAM_BOUND,
                &worker,
                SecurityLevel::Sec80,
                0,
            );
            bridge_proof.set_recursion_chain(&chain);

            serialize_compressed_to_file(
                &bridge_proof,
                &format!("bridge_proof_{u_tag}_{bridge_tag}.bin"),
            );
            serialize_compressed_to_file(
                &bridge_setups,
                &format!("bridge_setups_{u_tag}_{bridge_tag}.bin"),
            );

            (bridge_proof, bridge_setups)
        };
        let bridge_proof_cycles = bridge_proof.executed_cycles();
        total_cycles += bridge_proof_cycles;
        println!("bridge unified proof ran {bridge_proof_cycles} cycles (total {total_cycles})");

        native_verify_unified(build_unified_stream(&bridge_setups, &bridge_proof), false);

        let bridge_end_params = compute_end_params(&bridge_setups, bridge_proof.final_pc);
        chain.extend(&bridge_end_params);
        proof = bridge_proof;
        setups = bridge_setups;

        // === Stage 5: final — prove fsv_unified_recursion_layer (final-blake
        //              variant) over the unified bridge proof, in unified mode. ===
        println!("=== final: proving fsv_unified_recursion_layer in unified mode (blake {final_tag}) ===");
        let (unified_rec_bin, unified_rec_text) =
            load_fsv_program(FSV_DIR, FsvProgram::UnifiedRecursionLayer, final_blake);
        let (final_proof, final_setups) = if let Ok(final_proof) =
            try_deserialize_compressed_from_file::<ProgramProof>(&format!(
                "final_proof_{u_tag}_{bridge_tag}_{final_tag}.bin"
            )) {
            println!("Using existing files for final layer");
            (
                final_proof,
                try_deserialize_compressed_from_file(&format!(
                    "final_setups_{u_tag}_{bridge_tag}_{final_tag}.bin"
                ))
                .unwrap(),
            )
        } else {
            let (mut final_proof, final_setups) = prove_unified_execution_with_replayer::<Global>(
                UNIFIED_CYCLES_BOUND,
                &unified_rec_bin,
                &unified_rec_text,
                use_caches,
                QuasiUARTSource::new_with_reads(build_unified_stream(&setups, &proof)),
                RAM_BOUND,
                &worker,
                SecurityLevel::Sec80,
                0,
            );
            final_proof.set_recursion_chain(&chain);

            serialize_compressed_to_file(
                &final_proof,
                &format!("final_proof_{u_tag}_{bridge_tag}_{final_tag}.bin"),
            );
            serialize_compressed_to_file(
                &final_setups,
                &format!("final_setups_{u_tag}_{bridge_tag}_{final_tag}.bin"),
            );

            (final_proof, final_setups)
        };
        let final_proof_cycles = final_proof.executed_cycles();
        total_cycles += final_proof_cycles;
        println!("final unified proof ran {final_proof_cycles} cycles (total {total_cycles})");

        let final_output =
            native_verify_unified(build_unified_stream(&final_setups, &final_proof), false);

        println!("=== pipeline complete: {total_cycles} total cycles proven ===");
        println!("final recursion-chain output registers: {final_output:?}");

        // Informational: how big a further unified-recursion step would be.
        let next_cycles = measure_verifier_cycles(
            &unified_rec_bin,
            &unified_rec_text,
            build_unified_stream(&final_setups, &final_proof),
        );
        println!("verifying the final proof would take {next_cycles} cycles");
    }

    #[test]
    #[serial_test::serial]
    fn load_binary() {
        use riscv_transpiler::ir::simple_instruction_set::*;
        use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;

        let (_zksync_bin, zksync_text) = load_program(
            Path::new("../../riscv_transpiler/examples/zksync_os/app.bin"),
            Path::new("../../riscv_transpiler/examples/zksync_os/app.text"),
        );

        println!("0x{:08x}", zksync_text[0x0013_ce00 / 4]);

        let _instructions: Vec<Instruction> =
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&zksync_text);
    }
}

#[cfg(test)]
mod scripts {
    use std::io::Read;
    use std::io::Write;

    #[allow(dead_code)]
    pub(super) fn try_deserialize_compressed_from_file<T: serde::de::DeserializeOwned>(
        filename: &str,
    ) -> Result<T, ()> {
        use flate2::read::ZlibDecoder;

        let mut src = std::fs::File::open(filename).map_err(|_| ())?;
        let mut buffer = vec![];
        src.read_to_end(&mut buffer).map_err(|_| ())?;

        let mut decoder = ZlibDecoder::new(&buffer[..]);
        let mut unpacked: Vec<u8> = vec![];
        decoder.read_to_end(&mut unpacked).map_err(|_| ())?;

        Ok(bincode::deserialize_from(&unpacked[..]).unwrap())
    }

    #[allow(dead_code)]
    pub(super) fn serialize_compressed_to_file<T: serde::Serialize>(el: &T, filename: &str) {
        use flate2::write::ZlibEncoder;
        use flate2::Compression;
        let mut buffer = vec![];
        bincode::serialize_into(&mut buffer, el).unwrap();

        let dst = std::fs::File::create(filename).unwrap();
        let mut e = ZlibEncoder::new(dst, Compression::default());
        e.write_all(&buffer).expect("must compress");
        let _ = e.finish();
    }

    #[test]
    fn convert_file() {
        // type T = full_statement_verifier::program_proof::ProgramProof;
        type T = setups::Setups;

        let file_name = "recursion_layer_0_setups";
        let data: T = crate::deserialize_from_file(&format!("{file_name}.json"));
        serialize_compressed_to_file(&data, &format!("{file_name}.bin"));
    }
}
