//! End-to-end recursive proving pipeline, expressed as a series of tests.
//!
//! Flow (each stage proves a RISC-V program and feeds its proof into the next
//! stage's verifier program as non-determinism):
//!
//! 1. Prove the `zksync_os` app+witness as a **base layer** program (unrolled
//!    machine mode, IM ISA + delegations). Verify natively.
//! 2. Feed that proof into `fsv_unrolled_base_layer_sec_100` and prove it
//!    (unrolled machine mode, reduced ISA + delegations). Verify natively.
//! 3. Feed into `fsv_unrolled_recursion_layer_sec_100`, prove (unrolled, reduced).
//!    Before each round we *measure* how many cycles running the verifier over
//!    the current proof would take; we keep recursing on the unrolled machine
//!    while that stays at/above a configurable threshold.
//! 4. Once the estimated verifier cost drops below the threshold
//!    (`RECURSION_UNIFIED_SWITCH_CYCLES`, default 64M), **bridge** to the unified
//!    machine: re-prove the unrolled verifier over the last unrolled proof in
//!    **unified** machine mode, emitting a *unified* single-circuit proof.
//! 5. Feed the unified proof into `fsv_unified_recursion_layer_sec_100` and prove
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
    use crate::*;
    use full_statement_verifier::host_utils::{
        bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
        final_blake_mode, load_fsv_program, load_program, native_verify_unified,
        native_verify_unrolled, unified_switch_cycles, unrolled_blake_mode, FsvRecursionChain,
    };
    use full_statement_verifier::program_proof::ProgramProof;
    use program_prover::unified::prove_unified_execution_with_replayer;
    use program_prover::unrolled::prove_unrolled_execution_with_replayer;
    use prover::definitions::SecurityLevel;
    use prover::gkr::prover::{DefaultBabyBearBackend, DefaultBabyBearGKRBackend};
    use prover::worker::Worker;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::cycle::{
        IMStandardIsaConfigUnsignedMulDivOnly, ReducedMachineWithDelegation,
    };
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
        // 12 = this machine's P-core count; E-cores regress proving (measured).
        let worker = Worker::new_with_num_threads(12);

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
                    _,
                    _,
                >(
                    BASE_CYCLES_BOUND,
                    &zksync_bin,
                    &zksync_text,
                    use_caches,
                    QuasiUARTSource::new_with_reads(zksync_witness),
                    RAM_BOUND,
                    &worker,
                    SecurityLevel::Sec100,
                    verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                    &DefaultBabyBearBackend::default(),
                    &DefaultBabyBearGKRBackend::default(),
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

        // === Stages 2-3: unrolled recursion (reduced ISA). ===
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

            let program = if input_is_base {
                FsvProgram::UnrolledBaseLayer
            } else {
                FsvProgram::UnrolledRecursionLayer
            };
            let estimated =
                full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles(
                    &proof,
                    program,
                    unrolled_blake,
                )
                .expect("cannot estimate verifier cycles");
            println!("running the layer-{layer} verifier would take ~{estimated} cycles");
            if estimated < switch_cycles {
                println!("... below {switch_cycles} — switching to the unified machine");
                break;
            }

            println!(
                "=== unrolled recursion over a {} proof (layer {layer}) ===",
                if input_is_base { "base" } else { "recursion" }
            );
            let (mut new_proof, new_setups) = prove_unrolled_execution_with_replayer::<
                ReducedMachineWithDelegation,
                Global,
                _,
                _,
            >(
                UNROLLED_RECURSION_CYCLES_BOUND,
                bin,
                text,
                use_caches,
                QuasiUARTSource::new_with_reads(build_unrolled_stream(&setups, &proof)),
                RAM_BOUND,
                &worker,
                SecurityLevel::Sec100,
                verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                &DefaultBabyBearBackend::default(),
                &DefaultBabyBearGKRBackend::default(),
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
            let (mut bridge_proof, bridge_setups) =
                prove_unified_execution_with_replayer::<Global, _, _>(
                    UNIFIED_CYCLES_BOUND,
                    &bridge_bin,
                    &bridge_text,
                    use_caches,
                    QuasiUARTSource::new_with_reads(build_unrolled_stream(&setups, &proof)),
                    RAM_BOUND,
                    &worker,
                    SecurityLevel::Sec100,
                    verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                    &DefaultBabyBearBackend::default(),
                    &DefaultBabyBearGKRBackend::default(),
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
        //              variant) over the unified bridge proof, in unified mode,
        //              REPEATED until the proof shape reaches its fixed point:
        //              exactly ONE unified circuit chunk (2^23 cycles) and ONE
        //              blake2-with-compression delegation proof. Each layer is
        //              cached to disk under its index, so an interrupted run
        //              resumes at the first unproven layer. ===
        let (unified_rec_bin, unified_rec_text) =
            load_fsv_program(FSV_DIR, FsvProgram::UnifiedRecursionLayer, final_blake);

        // (total unified chunks, per-delegation-type proof counts)
        fn proof_shape(p: &ProgramProof) -> (usize, Vec<(u32, usize)>) {
            let unified_chunks = p.riscv_proofs.values().map(|v| v.len()).sum::<usize>();
            let delegations: Vec<(u32, usize)> = p
                .delegation_proofs
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .filter(|(_, n)| *n > 0)
                .collect();
            (unified_chunks, delegations)
        }
        let blake_delegation_type =
            <setups::Blake2sWithCompressionDelegationCircuit as circuit_common::DelegationCircuit<
                prover::field::baby_bear::base::BabyBearField,
            >>::DELEGATION_TYPE_ID as u32;
        let converged = |p: &ProgramProof| proof_shape(p) == (1, vec![(blake_delegation_type, 1)]);

        const MAX_FINAL_LAYERS: usize = 8;
        let mut final_layer = 0usize;
        while !converged(&proof) {
            assert!(
                final_layer < MAX_FINAL_LAYERS,
                "unified recursion did not converge to (1 unified chunk, 1 blake proof) \
                 within {MAX_FINAL_LAYERS} layers"
            );
            let (chunks, delegations) = proof_shape(&proof);
            let measured = measure_verifier_cycles(
                &unified_rec_bin,
                &unified_rec_text,
                build_unified_stream(&setups, &proof),
            );
            println!(
                "=== final layer {final_layer}: proving fsv_unified_recursion_layer in unified \
                 mode (blake {final_tag}) over a proof with {chunks} unified chunk(s) + \
                 delegations {delegations:?}; measured {measured} verifier cycles -> {} chunk(s) ===",
                measured.div_ceil(1 << 23)
            );

            let proof_file =
                format!("final_layer_{final_layer}_proof_{u_tag}_{bridge_tag}_{final_tag}.bin");
            let setups_file =
                format!("final_layer_{final_layer}_setups_{u_tag}_{bridge_tag}_{final_tag}.bin");
            let (new_proof, new_setups) = if let Ok(cached_proof) =
                try_deserialize_compressed_from_file::<ProgramProof>(&proof_file)
            {
                println!("Using existing files for final layer {final_layer}");
                (
                    cached_proof,
                    try_deserialize_compressed_from_file(&setups_file).unwrap(),
                )
            } else {
                let (mut new_proof, new_setups) =
                    prove_unified_execution_with_replayer::<Global, _, _>(
                        UNIFIED_CYCLES_BOUND,
                        &unified_rec_bin,
                        &unified_rec_text,
                        use_caches,
                        QuasiUARTSource::new_with_reads(build_unified_stream(&setups, &proof)),
                        RAM_BOUND,
                        &worker,
                        SecurityLevel::Sec100,
                        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                        &DefaultBabyBearBackend::default(),
                        &DefaultBabyBearGKRBackend::default(),
                    );
                new_proof.set_recursion_chain(&chain);
                serialize_compressed_to_file(&new_proof, &proof_file);
                serialize_compressed_to_file(&new_setups, &setups_file);
                (new_proof, new_setups)
            };

            let layer_cycles = new_proof.executed_cycles();
            total_cycles += layer_cycles;
            let (new_chunks, new_delegations) = proof_shape(&new_proof);
            println!(
                "final layer {final_layer} unified proof ran {layer_cycles} cycles \
                 (total {total_cycles}); shape: {new_chunks} unified chunk(s), \
                 delegations {new_delegations:?}"
            );

            native_verify_unified(build_unified_stream(&new_setups, &new_proof), false);

            let end_params = compute_end_params(&new_setups, new_proof.final_pc);
            chain.extend(&end_params);
            proof = new_proof;
            setups = new_setups;
            final_layer += 1;
        }

        let (chunks, delegations) = proof_shape(&proof);
        let final_output = native_verify_unified(build_unified_stream(&setups, &proof), false);

        println!("=== pipeline complete: {total_cycles} total cycles proven ===");
        println!(
            "converged after {final_layer} final layer(s): {chunks} unified chunk(s), \
             delegations {delegations:?}"
        );
        println!("final recursion-chain output registers: {final_output:?}");

        // Informational: how big a further unified-recursion step would be —
        // this is the number that must fit the L1 (Proth120) wrapper circuit.
        let next_cycles = measure_verifier_cycles(
            &unified_rec_bin,
            &unified_rec_text,
            build_unified_stream(&setups, &proof),
        );
        println!(
            "verifying the final proof would take {next_cycles} cycles ({} unified chunk(s))",
            next_cycles.div_ceil(1 << 23)
        );
    }

    /// Cheap follow-up to the converged pipeline (needs its cached
    /// `final_layer_0_proof_*` files): measure, for every unified-recursion
    /// verifier blake variant, how many cycles verifying the CONVERGED
    /// (1 unified chunk + 1 blake proof) takes. This is the cycle count the
    /// L1 (Proth120) wrapper circuit must fit; the special-opcodes variant
    /// additionally does blake inline, so its proof would carry NO delegation
    /// circuit — the shape the single-proof EVM verifier consumes.
    #[test]
    #[ignore = "needs the cached artifacts of test_recursive_proving_pipeline_zksync_os"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn measure_final_proof_verifier_variants() {
        use verifier_common::fsv_binaries::BlakeMode;
        skip_if_ci!();

        let u_tag = unrolled_blake_mode().tag();
        let bridge_tag = bridge_blake_mode().tag();
        let final_tag = final_blake_mode().tag();
        let proof: ProgramProof = try_deserialize_compressed_from_file(&format!(
            "final_layer_0_proof_{u_tag}_{bridge_tag}_{final_tag}.bin"
        ))
        .expect("run test_recursive_proving_pipeline_zksync_os first");
        let setups: Setups = try_deserialize_compressed_from_file(&format!(
            "final_layer_0_setups_{u_tag}_{bridge_tag}_{final_tag}.bin"
        ))
        .unwrap();

        for mode in [
            BlakeMode::Compression,
            BlakeMode::GFunction,
            BlakeMode::BlakeSpecialOpcodes,
        ] {
            let (bin, text) = load_fsv_program(FSV_DIR, FsvProgram::UnifiedRecursionLayer, mode);
            let cycles =
                measure_verifier_cycles(&bin, &text, build_unified_stream(&setups, &proof));
            println!(
                "verifying the converged proof with fsv_unified_recursion_layer[{}] takes {cycles} cycles ({} x 2^22, {} x 2^23 chunks)",
                mode.tag(),
                cycles.div_ceil(1 << 22),
                cycles.div_ceil(1 << 23),
            );
        }
    }

    /// Stage-A research for the L1 (Proth120) feed: the L1 verifier accepts
    /// exactly ONE unified-circuit proof at 2^22 cycles, so the chain must end
    /// delegation-free. Starting from the converged pipeline proof (1 unified
    /// chunk + 1 blake proof), keep proving `fsv_unified_recursion_layer` in
    /// its SPECIAL-OPCODES blake variant (hashing inline via the reduced
    /// machine's tri-add/xor-rotate opcodes — no delegation circuits at all)
    /// until the fixed point: a delegation-free proof whose own verification
    /// needs exactly as many 2^23 chunks as the proof has. Prints the verifier
    /// cycle count at every stage. Needs the cached artifacts of
    /// `test_recursive_proving_pipeline_zksync_os`; caches its own layers as
    /// `spec_layer_{k}_*` so interrupted runs resume.
    #[test]
    #[ignore = "manual research run (needs the converged pipeline caches)"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_special_opcodes_convergence_research() {
        use verifier_common::fsv_binaries::BlakeMode;
        skip_if_ci!();

        let use_caches = true;
        let worker = Worker::new_with_num_threads(12);
        let u_tag = unrolled_blake_mode().tag();
        let bridge_tag = bridge_blake_mode().tag();
        let final_tag = final_blake_mode().tag();

        fn shape(p: &ProgramProof) -> (usize, Vec<(u32, usize)>) {
            let unified_chunks = p.riscv_proofs.values().map(|v| v.len()).sum::<usize>();
            let delegations: Vec<(u32, usize)> = p
                .delegation_proofs
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .filter(|(_, n)| *n > 0)
                .collect();
            (unified_chunks, delegations)
        }

        // Converged pipeline artifacts.
        let mut proof: ProgramProof = try_deserialize_compressed_from_file(&format!(
            "final_layer_0_proof_{u_tag}_{bridge_tag}_{final_tag}.bin"
        ))
        .expect("run test_recursive_proving_pipeline_zksync_os first");
        let mut setups: Setups = try_deserialize_compressed_from_file(&format!(
            "final_layer_0_setups_{u_tag}_{bridge_tag}_{final_tag}.bin"
        ))
        .unwrap();

        // Reconstruct the recursion chain exactly as the pipeline left it:
        // begin at the base layer, extend through every cached stage.
        let base_proof: ProgramProof =
            try_deserialize_compressed_from_file("base_proofs.bin").unwrap();
        let base_setups: Setups = try_deserialize_compressed_from_file("base_setups.bin").unwrap();
        let mut chain =
            FsvRecursionChain::begin(&compute_end_params(&base_setups, base_proof.final_pc));
        for (p_file, s_file) in [
            (
                format!("recursion_layer_0_proof_{u_tag}.bin"),
                format!("recursion_layer_0_setups_{u_tag}.bin"),
            ),
            (
                format!("bridge_proof_{u_tag}_{bridge_tag}.bin"),
                format!("bridge_setups_{u_tag}_{bridge_tag}.bin"),
            ),
            (
                format!("final_layer_0_proof_{u_tag}_{bridge_tag}_{final_tag}.bin"),
                format!("final_layer_0_setups_{u_tag}_{bridge_tag}_{final_tag}.bin"),
            ),
        ] {
            let p: ProgramProof = try_deserialize_compressed_from_file(&p_file).unwrap();
            let s: Setups = try_deserialize_compressed_from_file(&s_file).unwrap();
            chain.extend(&compute_end_params(&s, p.final_pc));
        }

        let (spec_bin, spec_text) = load_fsv_program(
            FSV_DIR,
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        );

        const MAX_LAYERS: usize = 6;
        for k in 0..MAX_LAYERS {
            let measured = measure_verifier_cycles(
                &spec_bin,
                &spec_text,
                build_unified_stream(&setups, &proof),
            );
            let need = measured.div_ceil(1 << 23) as usize;
            let (cur_chunks, cur_delegations) = shape(&proof);
            println!(
                "[spec-opcodes] stage {k}: current proof = {cur_chunks} unified chunk(s), \
                 delegations {cur_delegations:?}; verifying it (special-opcodes fsv) takes \
                 {measured} cycles -> {need} x 2^23 chunk(s) ({} x 2^22)",
                measured.div_ceil(1 << 22)
            );
            if cur_delegations.is_empty() && need == cur_chunks {
                println!(
                    "[spec-opcodes] CONVERGED: {cur_chunks} chunk(s), delegation-free, \
                     self-reproducing at lde 2"
                );
                return;
            }

            let p_file = format!("spec_layer_{k}_proof_{u_tag}_{bridge_tag}_{final_tag}.bin");
            let s_file = format!("spec_layer_{k}_setups_{u_tag}_{bridge_tag}_{final_tag}.bin");
            let (new_proof, new_setups) =
                if let Ok(cached) = try_deserialize_compressed_from_file::<ProgramProof>(&p_file) {
                    println!("Using existing files for spec layer {k}");
                    (
                        cached,
                        try_deserialize_compressed_from_file(&s_file).unwrap(),
                    )
                } else {
                    let (mut np, ns) = prove_unified_execution_with_replayer::<Global, _, _>(
                        UNIFIED_CYCLES_BOUND,
                        &spec_bin,
                        &spec_text,
                        use_caches,
                        QuasiUARTSource::new_with_reads(build_unified_stream(&setups, &proof)),
                        RAM_BOUND,
                        &worker,
                        SecurityLevel::Sec100,
                        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                        &DefaultBabyBearBackend::default(),
                        &DefaultBabyBearGKRBackend::default(),
                    );
                    np.set_recursion_chain(&chain);
                    serialize_compressed_to_file(&np, &p_file);
                    serialize_compressed_to_file(&ns, &s_file);
                    (np, ns)
                };

            let (chunks, delegations) = shape(&new_proof);
            println!(
                "[spec-opcodes] layer {k} proof: {chunks} unified chunk(s), \
                 delegations {delegations:?} ({} cycles proven)",
                new_proof.executed_cycles()
            );
            assert!(
                delegations.is_empty(),
                "special-opcodes verifier run must make no delegation calls"
            );
            native_verify_unified(build_unified_stream(&new_setups, &new_proof), false);
            chain.extend(&compute_end_params(&new_setups, new_proof.final_pc));
            proof = new_proof;
            setups = new_setups;
        }
        panic!("no fixed point within {MAX_LAYERS} special-opcodes layers");
    }

    /// Stage-B research for the L1 feed: prove the final recursion layers as
    /// DELEGATION-FREE unified circuits committed in MERGED memory+witness
    /// mode under the high-LDE "L1 feeder" config (every oracle domain at
    /// BabyBear's 2^27 two-adicity cap, plain-text 2^3 tail, pow-tuned
    /// queries), so their verification gets cheap enough for the L1 (Proth120)
    /// wrapper's 2^22-cycle unified circuit. Layer 0 proves the STANDARD
    /// special-opcodes verifier run over the converged pipeline proof
    /// (1 unified + 1 blake — the feeder input); every later layer proves the
    /// MERGED-mode feeder verifier run over the previous feeder proof. Each
    /// iteration measures how many cycles verifying the result takes (the
    /// measurement IS a full VM run of the feeder verifier, so it doubles as
    /// the verification check). Stops on success (fits 2^22) or on a
    /// non-contracting fixed point. Prints cycles + chunk grids at every
    /// stage. Needs the caches of `test_recursive_proving_pipeline_zksync_os`
    /// and the MERGED-mode feeder fsv binary
    /// (`dump_bin.sh --blake special_opcodes_extension
    /// fsv_unified_recursion_layer_sec_100_l1_feeder`). Run once with
    /// `--features gkr_self_checks` for the full self-checked validation of
    /// the merged+feeder proving mode (layer caches then let a fast rerun
    /// finish the convergence).
    #[test]
    #[ignore = "manual research run (needs the converged pipeline caches)"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_l1_feeder_high_lde_research() {
        use crate::unified_transition::prove_unified_transition_with_replayer;
        use verifier_common::fsv_binaries::BlakeMode;
        skip_if_ci!();

        let use_caches = true;
        let worker = Worker::new_with_num_threads(12);
        let u_tag = unrolled_blake_mode().tag();
        let bridge_tag = bridge_blake_mode().tag();
        let final_tag = final_blake_mode().tag();
        let tags = format!("{u_tag}_{bridge_tag}_{final_tag}");

        fn shape(p: &ProgramProof) -> (usize, Vec<(u32, usize)>) {
            let unified_chunks = p.riscv_proofs.values().map(|v| v.len()).sum::<usize>();
            let delegations: Vec<(u32, usize)> = p
                .delegation_proofs
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .filter(|(_, n)| *n > 0)
                .collect();
            (unified_chunks, delegations)
        }

        // Input: the converged pipeline proof (1 unified chunk + 1 blake
        // proof, standard schedule, separate commitment).
        let mut proof: ProgramProof =
            try_deserialize_compressed_from_file(&format!("final_layer_0_proof_{tags}.bin"))
                .expect("run test_recursive_proving_pipeline_zksync_os first");
        let mut setups: Setups =
            try_deserialize_compressed_from_file(&format!("final_layer_0_setups_{tags}.bin"))
                .unwrap();

        // Reconstruct the recursion chain through every cached stage.
        let base_proof: ProgramProof =
            try_deserialize_compressed_from_file("base_proofs.bin").unwrap();
        let base_setups: Setups = try_deserialize_compressed_from_file("base_setups.bin").unwrap();
        let mut chain =
            FsvRecursionChain::begin(&compute_end_params(&base_setups, base_proof.final_pc));
        for (p_file, s_file) in [
            (
                format!("recursion_layer_0_proof_{u_tag}.bin"),
                format!("recursion_layer_0_setups_{u_tag}.bin"),
            ),
            (
                format!("bridge_proof_{u_tag}_{bridge_tag}.bin"),
                format!("bridge_setups_{u_tag}_{bridge_tag}.bin"),
            ),
            (
                format!("final_layer_0_proof_{tags}.bin"),
                format!("final_layer_0_setups_{tags}.bin"),
            ),
        ] {
            let p: ProgramProof = try_deserialize_compressed_from_file(&p_file).unwrap();
            let s: Setups = try_deserialize_compressed_from_file(&s_file).unwrap();
            chain.extend(&compute_end_params(&s, p.final_pc));
        }

        // Layer-0 run verifies the STANDARD separate-mode proof (standard
        // special-opcodes fsv); all later runs verify MERGED feeder proofs
        // (merged-mode feeder special-opcodes fsv).
        let (std_bin, std_text) = load_fsv_program(
            FSV_DIR,
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        );
        let (feeder_bin, feeder_text) = load_program(
            Path::new(&format!(
                "{FSV_DIR}/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.bin"
            )),
            Path::new(&format!(
                "{FSV_DIR}/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.text"
            )),
        );

        let feeder_config =
            prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_23();
        println!(
            "[l1-feeder] config: base lde {}, whir steps {:?}, queries {:?}, pow {:?}, \
             intermediate lde factors {:?}",
            feeder_config.lde_factor,
            feeder_config.whir_schedule.whir_steps_schedule,
            feeder_config.whir_schedule.whir_queries_schedule,
            feeder_config.whir_schedule.whir_pow_schedule,
            feeder_config.whir_schedule.whir_steps_lde_factors,
        );

        const MAX_LAYERS: usize = 5;
        for k in 0..MAX_LAYERS {
            let (run_bin, run_text) = if k == 0 {
                (&std_bin, &std_text)
            } else {
                (&feeder_bin, &feeder_text)
            };

            let p_file = format!("feeder_layer_{k}_proof_{tags}.bin");
            let s_file = format!("feeder_layer_{k}_setups_{tags}.bin");
            let (new_proof, new_setups) =
                if let Ok(cached) = try_deserialize_compressed_from_file::<ProgramProof>(&p_file) {
                    println!("Using existing files for feeder layer {k}");
                    (
                        cached,
                        try_deserialize_compressed_from_file(&s_file).unwrap(),
                    )
                } else {
                    let (mut np, ns) = prove_unified_transition_with_replayer::<_, _>(
                        UNIFIED_CYCLES_BOUND,
                        run_bin,
                        run_text,
                        use_caches,
                        QuasiUARTSource::new_with_reads(build_unified_stream(&setups, &proof)),
                        RAM_BOUND,
                        &worker,
                        SecurityLevel::Sec100,
                        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                        &feeder_config,
                        &DefaultBabyBearBackend::default(),
                        &DefaultBabyBearGKRBackend::default(),
                    );
                    np.set_recursion_chain(&chain);
                    serialize_compressed_to_file(&np, &p_file);
                    serialize_compressed_to_file(&ns, &s_file);
                    (np, ns)
                };

            let (chunks, delegations) = shape(&new_proof);
            assert!(delegations.is_empty());
            chain.extend(&compute_end_params(&new_setups, new_proof.final_pc));
            proof = new_proof;
            setups = new_setups;

            // Measuring = running the actual feeder RISC-V verifier over the
            // new proof to completion (it only reaches the success exit if the
            // proof verifies), so this doubles as the verification check.
            let measured = measure_verifier_cycles(
                &feeder_bin,
                &feeder_text,
                build_unified_stream(&setups, &proof),
            );
            let need = measured.div_ceil(1 << 23) as usize;
            println!(
                "[l1-feeder] layer {k}: proof = {chunks} chunk(s) at lde 16 \
                 ({} cycles proven); verifying it takes {measured} cycles \
                 -> {} x 2^22 / {need} x 2^23",
                proof.executed_cycles(),
                measured.div_ceil(1 << 22),
            );

            if measured <= 1 << 22 {
                println!(
                    "[l1-feeder] TARGET REACHED: verifying the layer-{k} feeder proof takes \
                     {measured} <= 2^22 = {} cycles — fits the L1 (Proth120) unified circuit",
                    1u64 << 22
                );
                return;
            }
            if need >= chunks {
                println!(
                    "[l1-feeder] NO FURTHER CONTRACTION: {chunks}-chunk feeder proof needs \
                     {need} chunk(s) to re-verify at {measured} cycles (> 2^22) — the schedule \
                     must get more aggressive (higher base LDE / larger intermediate rates)"
                );
                return;
            }
        }
        panic!("no verdict within {MAX_LAYERS} feeder layers");
    }

    /// The FINAL L1 step: prove the merged-mode feeder verifier's execution
    /// over the converged single-chunk feeder proof (`feeder_layer_1`, ~2.8M
    /// cycles <= 2^22) as ONE Proth120 packed unified-circuit proof with the
    /// EVM-production parameters, writing the proof + commitment-mode aux
    /// fixtures into `prover/` — exactly where the verifier_evm generation and
    /// the two-transaction test (`generated_contracts/two_tx/run_two_tx.sh`)
    /// pick them up. Requires `--features l1` and the caches of
    /// `test_l1_feeder_high_lde_research`; the packed setup commitment is
    /// served by coset recomputation (program-specific, nothing cached).
    #[cfg(feature = "l1")]
    #[test]
    #[ignore = "manual heavy proving run (Proth120 packed 2^26 commitment)"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_l1_wrap_proth120() {
        use prover::tests::gkr::orchestration::common::ProgramConfig;
        skip_if_ci!();

        let worker = Worker::new_with_num_threads(12);
        let u_tag = unrolled_blake_mode().tag();
        let bridge_tag = bridge_blake_mode().tag();
        let final_tag = final_blake_mode().tag();
        let tags = format!("{u_tag}_{bridge_tag}_{final_tag}");

        let proof: ProgramProof =
            try_deserialize_compressed_from_file(&format!("feeder_layer_1_proof_{tags}.bin"))
                .expect("run test_l1_feeder_high_lde_research first");
        let setups: Setups =
            try_deserialize_compressed_from_file(&format!("feeder_layer_1_setups_{tags}.bin"))
                .unwrap();
        let stream = build_unified_stream(&setups, &proof);

        let program = ProgramConfig {
            binary_path: format!(
                "{FSV_DIR}/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.bin"
            ),
            text_section_path: format!(
                "{FSV_DIR}/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.text"
            ),
            non_determinism_reads: stream,
            cycles_bound: 1 << 22,
            ram_bound_bytes: 1 << 30,
        };

        let _l1_proof = crate::l1::prove_l1_wrap_in_recompute_mode(
            &program,
            Path::new(
                "../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
            ),
            Path::new("../../prover/unified_circuit_proof_proth120.json"),
            Path::new("../../prover/unified_circuit_proof_proth120_commitment_mod_aux_data.json"),
            &worker,
        );
        println!(
            "L1 wrap complete: run the two-transaction cross-check with \
             verifier_evm/generated_contracts/two_tx/run_two_tx.sh"
        );
    }

    /// Debug helper: host-side verification of the cached feeder-layer-0
    /// proof with the L1-feeder statement + DebugErrorCreator, so a rejection
    /// names the failing check instead of an opaque VM trap.
    #[test]
    #[ignore = "debug helper for the L1-feeder research caches"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn debug_native_verify_feeder_layer_0() {
        use verifier_common::errors::DebugErrorCreator;
        skip_if_ci!();

        let u_tag = unrolled_blake_mode().tag();
        let bridge_tag = bridge_blake_mode().tag();
        let final_tag = final_blake_mode().tag();
        let tags = format!("{u_tag}_{bridge_tag}_{final_tag}");
        let proof: ProgramProof =
            try_deserialize_compressed_from_file(&format!("feeder_layer_0_proof_{tags}.bin"))
                .expect("run test_l1_feeder_high_lde_research first");
        let setups: Setups =
            try_deserialize_compressed_from_file(&format!("feeder_layer_0_setups_{tags}.bin"))
                .unwrap();
        let stream = build_unified_stream(&setups, &proof);
        let result = std::thread::Builder::new()
            .name("feeder verifier".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let mut it = stream.into_iter();
                full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100_l1_feeder::<
                    _,
                    DebugErrorCreator,
                    { full_statement_verifier::verifier_common::USE_REDUCED_BLAKE2_ROUNDS },
                >(&mut it)
            })
            .expect("spawn verifier thread")
            .join()
            .expect("verifier thread must not panic");
        println!("feeder layer 0 native verification result: {result:?}");
        assert!(result.is_ok());
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
        let data: T = program_prover::deserialize_from_file(&format!("{file_name}.json"));
        serialize_compressed_to_file(&data, &format!("{file_name}.bin"));
    }
}
