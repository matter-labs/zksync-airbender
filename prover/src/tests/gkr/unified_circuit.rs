use super::orchestration::common::ProgramConfig;
use super::orchestration::unified::{prove_unified, DelegationCallCounts, DelegationEvalFns};
use crate::definitions::SecurityLevel;
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
    };

    let dir = "../full_statement_verifier/tests/fixtures";
    std::fs::create_dir_all(dir).expect("create FSV fixtures dir");
    let path = format!("{dir}/unified_base_layer_fixture_{proof_suffix}.json");
    let file = std::fs::File::create(&path).expect("create FSV fixture file");
    serde_json::to_writer(std::io::BufWriter::new(file), &bundle)
        .expect("serialize FSV unified fixture");
    println!("Wrote FSV unified base-layer fixture to {path}");
}
