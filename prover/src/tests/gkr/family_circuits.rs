use super::*;
use crate::definitions::SecurityLevel;
use ::field::baby_bear::base::BabyBearField;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::tables::TableDriver;
use riscv_transpiler::ir::*;
use riscv_transpiler::vm::Counters;
use std::alloc::Global;
use worker::Worker;
const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

/// Single-family CPU experiment: prove ONLY
/// the add/sub/lui/auipc/mop family circuit, but prove it twice under different
/// RS-codeword storage policies ([`RsCodewordSource::InMemory`] vs
/// [`RsCodewordSource::Recompute`]) and assert the two proofs are byte-identical.
/// The storage policy is orthogonal to the (fixed) prover config, so it must not
/// change the proof.
#[test]
#[ignore = "production-scale 2^24 RS storage parity; run explicitly"]
fn add_sub_family_rs_codeword_source_parity() {
    use crate::gkr::prover::WhirOracleStorage;
    use riscv_transpiler::vm::DelegationsAndFamiliesCounters;

    type CountersT = DelegationsAndFamiliesCounters;
    const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

    let worker = Worker::new_with_num_threads(8);

    let config = super::orchestration::common::ProgramConfig::mop_smoke();
    let vm = super::orchestration::common::run_vm_and_capture::<
        CountersT,
        FullUnsignedMachineDecoderConfig,
    >(&config, &worker);

    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(num_calls > 0);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("add_sub_lui_auipc_mop"),
    );
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);

    let full_trace =
        super::orchestration::per_family::build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            num_calls,
            &circuit,
            &table_driver,
            decoder_table_data,
            add_sub_lui_auipc_mop::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            false,
            &worker,
        )
        .full_trace;

    assert!(check_satisfied(&circuit, &full_trace));

    let trace_len = 1usize << TRACE_LEN_LOG2;
    let external_challenges = super::orchestration::common::hardcoded_external_challenges();

    // Prove the SAME trace under each WHIR oracle storage policy, including the
    // mixed one (recompute-based base oracles + materialized intermediates).
    let prove = |storage: WhirOracleStorage| {
        super::orchestration::per_family::prove_built_family_trace_with_rs_source(
            &circuit,
            &table_driver,
            decoder_table_data,
            full_trace.clone(),
            trace_len,
            &external_challenges,
            SecurityLevel::Sec100,
            storage,
            &worker,
        )
    };

    let proof_in_memory = prove(WhirOracleStorage::fully_in_memory());
    let proof_recompute = prove(WhirOracleStorage::fully_recompute());
    let proof_mixed = prove(WhirOracleStorage::recompute_base_materialized_intermediates());

    // The storage policy must not change the proof: compare the full serialized form.
    let bytes_in_memory =
        serde_json::to_vec(&proof_in_memory).expect("proof serializes (InMemory)");
    let bytes_recompute =
        serde_json::to_vec(&proof_recompute).expect("proof serializes (Recompute)");
    let bytes_mixed = serde_json::to_vec(&proof_mixed).expect("proof serializes (mixed)");
    assert_eq!(
        bytes_in_memory, bytes_recompute,
        "InMemory and Recompute RS-codeword sources must produce byte-identical proofs"
    );
    assert_eq!(
        bytes_in_memory, bytes_mixed,
        "recompute base + materialized intermediates must produce a byte-identical proof"
    );
}

/// Prove the add/sub/lui/auipc/mop family circuit with the SETUP commitment served
/// from disk (`SetupCommitment::OnDisk`): the setup is committed in memory the usual
/// way, its RS codewords + Merkle tree are written to disk, then it is proved reading
/// them back from disk. The proof must equal the equivalent in-memory-setup proof.
///
/// NOTE: this writes the full setup RS codewords to disk (~all LDE cosets of the
/// setup columns) and runs two 2^24 proofs; keep it a deliberately-run test.
#[test]
#[ignore = "production-scale 2^24 on-disk setup parity; run explicitly"]
fn add_sub_family_on_disk_setup() {
    use riscv_transpiler::vm::DelegationsAndFamiliesCounters;

    type CountersT = DelegationsAndFamiliesCounters;
    const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

    let worker = Worker::new_with_num_threads(8);

    let config = super::orchestration::common::ProgramConfig::mop_smoke();
    let vm = super::orchestration::common::run_vm_and_capture::<
        CountersT,
        FullUnsignedMachineDecoderConfig,
    >(&config, &worker);

    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(num_calls > 0);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("add_sub_lui_auipc_mop"),
    );
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);

    let full_trace =
        super::orchestration::per_family::build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            num_calls,
            &circuit,
            &table_driver,
            decoder_table_data,
            add_sub_lui_auipc_mop::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            false,
            &worker,
        )
        .full_trace;

    assert!(check_satisfied(&circuit, &full_trace));

    let trace_len = 1usize << TRACE_LEN_LOG2;
    let external_challenges = super::orchestration::common::hardcoded_external_challenges();

    // Prove with the setup served from disk.
    let disk_prefix = format!(
        "{}/gkr_on_disk_setup_add_sub",
        std::env::temp_dir().display()
    );
    let proof_on_disk = super::orchestration::per_family::prove_built_family_trace_on_disk_setup(
        &circuit,
        &table_driver,
        decoder_table_data,
        full_trace.clone(),
        trace_len,
        &external_challenges,
        SecurityLevel::Sec100,
        &disk_prefix,
        &worker,
    );

    // Reference: the same circuit with the setup kept in memory (the standard path).
    // Uses the same (unclamped, standard cap) config as the on-disk path above.
    let proof_in_memory = super::orchestration::per_family::prove_built_family_trace(
        &circuit,
        &table_driver,
        decoder_table_data,
        full_trace,
        trace_len,
        &external_challenges,
        SecurityLevel::Sec100,
        &worker,
    );

    let bytes_on_disk = serde_json::to_vec(&proof_on_disk).expect("proof serializes (on-disk)");
    let bytes_in_memory =
        serde_json::to_vec(&proof_in_memory).expect("proof serializes (in-memory)");
    assert_eq!(
        bytes_on_disk, bytes_in_memory,
        "on-disk setup must produce the same proof as the in-memory setup"
    );
}
