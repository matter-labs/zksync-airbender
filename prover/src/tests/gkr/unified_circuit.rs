use crate::definitions::SecurityLevel;
use super::orchestration::common::ProgramConfig;
use super::orchestration::unified::{
    prove_unified, DelegationCallCounts, DelegationEvalFns,
};
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use worker::Worker;

#[test]
fn gkr_run_unified_test_sec_80() {
    run_unified_test(SecurityLevel::Sec80);
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
    }
}
