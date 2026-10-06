use super::orchestration::common::ProgramConfig;
use super::orchestration::unified::{prove_unified, DelegationCallCounts, DelegationEvalFns};
use crate::definitions::SecurityLevel;
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use worker::Worker;

#[test]
fn gkr_run_unified_test_sec_100() {
    run_unified_test(SecurityLevel::Sec100);
}

fn run_unified_test(level: SecurityLevel) {
    let proof_suffix = level.dir_suffix();
    let worker = Worker::new_with_num_threads(8);

    // Blake variant selection. Both variants run the same `multi_family_smoke`
    // program shape but with a different Blake delegation CSR baked in. Default
    // is `g_function` to match the cascading default of `gkr_test.sh --blake`.
    let blake_variant = std::env::var("GKR_BLAKE").ok();
    let config = match blake_variant.as_deref() {
        Some("compression") | Some("blake2_with_compression") => {
            ProgramConfig::multi_family_smoke_blake_compression()
        }
        _ => ProgramConfig::multi_family_smoke_blake_g_function(),
    };

    let delegation_eval_fns = DelegationEvalFns {
        blake: Some(super::blake2_with_extended_control::witness_eval_fn),
        bigint: Some(super::bigint_with_extended_control::witness_eval_fn),
        keccak: Some(super::keccak_special5::witness_eval_fn),
        blake_g_function: Some(super::blake2_g_function::witness_eval_fn),
    };

    let vm = super::orchestration::common::run_vm_and_capture::<
        DelegationsAndUnifiedCounters,
        riscv_transpiler::ir::ReducedMachineDecoderConfig,
    >(&config, &worker);
    let delegation_call_counts = DelegationCallCounts {
        blake: vm.counters.blake_calls,
        bigint: vm.counters.bigint_calls,
        keccak: vm.counters.keccak_calls,
        blake_g_function: vm.counters.blake_g_function_calls,
    };

    let output = prove_unified::<DelegationsAndUnifiedCounters>(
        vm,
        level,
        &proof_suffix,
        &worker,
        super::unified_reduced_machine::witness_eval_fn,
        &delegation_eval_fns,
        &delegation_call_counts,
        false,
    );

    let circuits_filter = super::orchestration::common::parse_circuits_filter();
    if circuits_filter.is_none() {
        use field::baby_bear::ext4::BabyBearExt4;
        use field::Field;
        assert_eq!(
            output.permutation_argument_accumulator,
            BabyBearExt4::ONE,
            "unified grand-product accumulator should be ONE"
        );

        write_fsv_unified_fixture(&output, proof_suffix);
    }
}

/// Same small program, with no forged delegation row.
#[test]
#[ignore = "expensive end-to-end zero-timestamp delegation control"]
fn gkr_run_unified_zero_ts_control_sec_100() {
    run_zero_ts_program(false);
}

/// Confirm whether a zero-timestamp Keccak row changes an exported register
/// without any Keccak call in the same program.
#[test]
#[ignore = "expensive end-to-end zero-timestamp delegation PoC"]
fn gkr_run_unified_zero_ts_phantom_sec_100() {
    run_zero_ts_program(true);
}

fn run_zero_ts_program(inject_zero_ts_keccak: bool) {
    use field::baby_bear::ext4::BabyBearExt4;
    use field::Field;

    let worker = Worker::new_with_num_threads(8);
    let case = if inject_zero_ts_keccak {
        "phantom"
    } else {
        "control"
    };
    let path = std::env::temp_dir().join(format!(
        "airbender-zero-ts-{case}-{}.bin",
        std::process::id()
    ));
    // addi x1, x0, 1; lw x2, 256(x0); jal x0, 0. No instruction touches x10 or x11.
    // The load also gives the newer unified harness a touched RAM chunk to close.
    let binary: Vec<u8> = [0x0010_0093u32, 0x1000_2103, 0x0000_006f]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    std::fs::write(&path, binary).expect("write PoC program");
    let program_path = path.to_string_lossy().into_owned();
    let config = ProgramConfig {
        binary_path: program_path.clone(),
        text_section_path: program_path,
        non_determinism_reads: vec![],
        cycles_bound: 16,
        ram_bound_bytes: super::orchestration::common::RAM_BOUND_BYTES,
    };
    let mut vm = super::orchestration::common::run_vm_and_capture::<
        DelegationsAndUnifiedCounters,
        riscv_transpiler::ir::ReducedMachineDecoderConfig,
    >(&config, &worker);
    std::fs::remove_file(&path).expect("remove PoC program");
    assert_eq!(vm.counters.keccak_calls, 0);

    if inject_zero_ts_keccak {
        // The witness starts after the phantom row's writes at timestamp 2.
        // The main program never accesses these registers, so its replay is
        // otherwise identical; the register boundary exposes x10 = 8.
        for (register, value) in [(10usize, 8u32), (11, 0)] {
            assert_eq!(
                vm.snapshotter.initial_snapshot.state.registers[register].value,
                0
            );
            assert_eq!(vm.final_state.registers[register].value, 0);
            vm.snapshotter.initial_snapshot.state.registers[register].value = value;
            vm.snapshotter.initial_snapshot.state.registers[register].timestamp = 2;
            for snapshot in &mut vm.snapshotter.snapshots {
                snapshot.state.registers[register].value = value;
                snapshot.state.registers[register].timestamp = 2;
            }
            vm.final_state.registers[register].value = value;
            vm.final_state.registers[register].timestamp = 2;
        }
    }

    let delegation_eval_fns = DelegationEvalFns {
        blake: Some(super::blake2_with_extended_control::witness_eval_fn),
        bigint: Some(super::bigint_with_extended_control::witness_eval_fn),
        keccak: Some(super::keccak_special5::witness_eval_fn),
        blake_g_function: Some(super::blake2_g_function::witness_eval_fn),
    };
    let proof_suffix = if inject_zero_ts_keccak {
        "zero_ts_phantom_sec_100"
    } else {
        "zero_ts_control_sec_100"
    };
    let output = prove_unified::<DelegationsAndUnifiedCounters>(
        vm,
        SecurityLevel::Sec100,
        proof_suffix,
        &worker,
        super::unified_reduced_machine::witness_eval_fn,
        &delegation_eval_fns,
        &DelegationCallCounts::default(),
        inject_zero_ts_keccak,
    );
    let (expected_x10, expected_timestamp) = if inject_zero_ts_keccak {
        (8, 2)
    } else {
        (0, 0)
    };
    assert_eq!(output.register_final_state[10].current_value, expected_x10);
    assert_eq!(
        output.register_final_state[10].last_access_timestamp,
        expected_timestamp
    );
    assert_eq!(
        output.register_final_state[11].last_access_timestamp,
        expected_timestamp
    );
    assert_eq!(
        output.permutation_argument_accumulator,
        BabyBearExt4::ONE,
        "zero-timestamp grand product did not close"
    );
    write_fsv_unified_fixture(&output, proof_suffix);
}

/// Serialize the component bundle (Option B) for the full statement verifier's unified
/// base-layer test. The FSV crate (where `ProgramProof` lives) sits above the prover in the
/// crate graph, so the prover can't build a `ProgramProof` directly — it emits these
/// ingredients via the shared [`UnifiedBaseLayerComponents`] struct and the FSV test reassembles
/// the `ProgramProof`. The struct is the single source of truth for the layout (no positional
/// tuple to keep in sync).
fn write_fsv_unified_fixture(
    output: &super::orchestration::unified::UnifiedProverOutput,
    proof_suffix: &str,
) {
    use crate::definitions::FinalRegisterValue;
    use crate::fsv_fixture::{DelegationComponents, UnifiedBaseLayerComponents};

    let (Some(unified_proof), Some(unified_setup_cap)) = (
        output.unified_proof.as_ref(),
        output.unified_setup_cap.as_ref(),
    ) else {
        // Only emit the fixture when a full unified proof was produced.
        return;
    };

    let delegations: Vec<DelegationComponents> = output
        .delegation_outputs
        .iter()
        .filter_map(|d| {
            d.proof.as_ref().map(|p| DelegationComponents {
                delegation_csr: d.delegation_type as u32,
                proof: p.clone(),
            })
        })
        .collect();

    let register_final_values: Vec<FinalRegisterValue> = output
        .register_final_state
        .iter()
        .map(|el| FinalRegisterValue {
            value: el.current_value,
            last_access_timestamp: el.last_access_timestamp,
        })
        .collect();

    let bundle = UnifiedBaseLayerComponents {
        unified_proof: unified_proof.clone(),
        delegations,
        register_final_values,
        final_pc: output.final_pc,
        final_timestamp: output.final_timestamp,
        unified_setup_cap: *unified_setup_cap,
        pow_bits: output.pow_bits,
        pow_challenge: output.pow_challenge,
    };

    let dir = "../full_statement_verifier/tests/fixtures";
    std::fs::create_dir_all(dir).expect("create FSV fixtures dir");
    let path = format!("{dir}/unified_base_layer_fixture_{proof_suffix}.json");
    let file = std::fs::File::create(&path).expect("create FSV fixture file");
    serde_json::to_writer(std::io::BufWriter::new(file), &bundle)
        .expect("serialize FSV unified fixture");
    println!("Wrote FSV unified base-layer fixture to {path}");
}
