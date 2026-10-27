//! End-to-end proof of the unified extended machine (`cs::gkr_circuits::unified_extended_machine`)
//! on `examples/extended_machine_smoke`: VM run, witness trace through the generated
//! witness-eval fn, GKR + WHIR proof with the circuit definition's prover config, grand-product
//! closure, and the proof fixture the generated Rust verifier is tested against
//! (`verifier/tests/unified_extended_machine.rs`).
//!
//! The machine has no ROM range, and the memory argument's inits of the ROM-range addresses
//! stay zero-valued, so a program must not load from that range. Two programs are proved:
//! the hand-assembled smoke program (RAM above the ROM only), and `extended_machine_linking`,
//! a Rust program linked with the execute-only-text layout (`riscv_common` feature
//! `execute_only_text`): its `.rodata`/`.data` start in RAM and are materialised by the
//! `init_from_text` code the strict ELF post-processing splices in, and the VM runs it with an
//! execute-only ROM (`RamWithRomRegion<_, true>`), so any load from the ROM range would panic.
use super::orchestration::common::{run_vm_and_capture_with_rom_mode, ProgramConfig};
use super::orchestration::unified::{
    build_full_trace_for_unified_machine, prove_built_trace_for_unified_machine,
};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::{produce_initial_permutation_product_contribution, SecurityLevel};
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use common_constants::circuit_families::EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::INITIAL_PC;
use cs::definitions::INITIAL_TIMESTAMP;
use cs::gkr_circuits::unified_extended_machine::{
    unified_extended_machine_table_driver_fn, UnifiedExtendedMachineDecoder,
};
use cs::tables::TableDriver;
use cs::utils::split_timestamp;
use field::Field;
use riscv_transpiler::ir::ExtendedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters};
use worker::Worker;

const CIRCUIT_NAME: &str = "unified_extended_machine";

fn smoke_program() -> ProgramConfig {
    ProgramConfig {
        program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
            "../examples/extended_machine_smoke/app.bin",
            "../examples/extended_machine_smoke/app.text",
        ),
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

fn linking_program() -> ProgramConfig {
    ProgramConfig {
        program: riscv_transpiler::elf::ProgramSource::strict_elf(
            "../examples/extended_machine_linking/app.elf",
        ),
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

/// The smoke program; writes the proof fixture the generated verifier is tested against.
#[test]
fn gkr_run_unified_extended_test_sec_100() {
    run_unified_extended_test::<false>(SecurityLevel::Sec100, smoke_program(), true);
}

/// The execute-only-text Rust program on an execute-only ROM.
#[test]
fn gkr_run_unified_extended_linking_test_sec_100() {
    run_unified_extended_test::<true>(SecurityLevel::Sec100, linking_program(), false);
}

fn run_unified_extended_test<const EXEC_ONLY_ROM: bool>(
    level: SecurityLevel,
    config: ProgramConfig,
    write_fixture: bool,
) {
    let proof_suffix = super::orchestration::common::proof_suffix(level);
    let worker = Worker::new_with_num_threads(8);

    let vm = run_vm_and_capture_with_rom_mode::<
        DelegationsAndUnifiedCounters,
        ExtendedMachineDecoderConfig,
        EXEC_ONLY_ROM,
    >(&config, &worker);
    assert_eq!(vm.counters.blake_calls, 0);
    assert_eq!(vm.counters.bigint_calls, 0);
    assert_eq!(vm.counters.keccak_calls, 0);
    assert_eq!(vm.counters.blake_g_function_calls, 0);

    let use_caches = cfg!(not(feature = "no_caches"));
    let circuit: GKRCircuitArtifact<BabyBearField> =
        super::orchestration::delegations::deserialize_from_file(&if use_caches {
            format!("../cs/compiled_circuits/{CIRCUIT_NAME}_layout_gkr.json")
        } else {
            format!("../cs/compiled_circuits/{CIRCUIT_NAME}_layout_no_caches_gkr.json")
        });

    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls < circuit.trace_len);

    let mut table_driver = TableDriver::<BabyBearField>::new();
    unified_extended_machine_table_driver_fn(&mut table_driver);

    let (full_trace, table_driver, decoder_table, inits_and_teardowns_top_bits) =
        build_full_trace_for_unified_machine::<_, ExtendedMachineDecoderConfig, EXEC_ONLY_ROM>(
            &vm,
            &circuit,
            num_calls,
            EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX,
            Box::new(UnifiedExtendedMachineDecoder),
            table_driver,
            super::unified_extended_machine::witness_eval_fn,
            true,
            &worker,
        );

    #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
    {
        println!("Checking constraint satisfiability (unified extended)");
        assert!(
            super::check_satisfied(&circuit, &full_trace),
            "unified extended circuit constraint not satisfied"
        );
    }

    // No delegations, so the grand product closes with any challenges; the hardcoded ones keep
    // the fixture deterministic (the generated verifier takes the challenges from the proof).
    let external_challenges = super::orchestration::common::hardcoded_external_challenges();

    let (proof, _setup_cap) = prove_built_trace_for_unified_machine(
        CIRCUIT_NAME,
        &circuit,
        full_trace,
        &table_driver,
        &decoder_table,
        inits_and_teardowns_top_bits,
        &external_challenges,
        level,
        &worker,
    );

    let register_final_state_raw = vm
        .register_final_state()
        .map(|el| (el.current_value, split_timestamp(el.last_access_timestamp)));
    let mut accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            vm.final_pc(),
            split_timestamp(vm.final_timestamp()),
            &external_challenges,
        );
    accumulator.mul_assign(&proof.grand_product_accumulator_computed);
    assert_eq!(
        accumulator,
        BabyBearExt4::ONE,
        "unified extended grand-product accumulator should be ONE"
    );

    if write_fixture {
        super::orchestration::delegations::serialize_to_file(
            &proof,
            &format!("test_proofs/{CIRCUIT_NAME}_{proof_suffix}_gkr_proof.json"),
        );
    }
}
