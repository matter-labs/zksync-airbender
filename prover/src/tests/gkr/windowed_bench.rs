//! Benchmark harness for the windowed sumcheck variants on the real add/sub
//! family circuit. The VM run + replay (the slow, single-threaded part) is done
//! once and the `NonMemoryCircuitOracle` internals are cached to disk with
//! bincode; subsequent runs rebuild the witness trace from the cache and go
//! straight to the storage setup + benchmarks.
//!
//! Run with:
//! `cargo test -p prover --release windowed_sumcheck_bench_add_sub -- --nocapture --ignored`

use super::*;
use crate::gkr::prover::forward_loop;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::sumcheck_loop::windowed_mode::bench::run_windowed_sumcheck_benchmarks;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRStorage};
use crate::gkr::virtual_polys::range_check::materialize_virtual_range_check_setup_poly;
use crate::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::definitions::VirtualSetupPoly;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::TableDriver;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::NonMemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::NonMemDestinationHolder;
use std::alloc::Global;
use worker::Worker;

use common_constants::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
    NON_DETERMINISM_CSR,
};
use cs::definitions::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

const WITNESS_CACHE_PATH: &str = "test_proofs/add_sub_windowed_bench_witness.bin";

/// The internals of `NonMemoryCircuitOracle` for one add/sub circuit instance,
/// cached to disk so benchmark re-runs skip the VM run + replay + decoder-table
/// preprocessing.
#[derive(serde::Serialize, serde::Deserialize)]
struct AddSubOracleData {
    tracing_data: Vec<NonMemoryOpcodeTracingDataWithTimestamp>,
    decoder_table: Vec<Option<ExecutorFamilyDecoderData>>,
}

fn build_or_load_add_sub_oracle_data(worker: &Worker) -> AddSubOracleData {
    if std::path::Path::new(WITNESS_CACHE_PATH).exists() {
        println!("loading cached oracle data from {WITNESS_CACHE_PATH}");
        return bincode_deserialize_from_file(WITNESS_CACHE_PATH);
    }

    println!("no witness cache found: running the VM to build it");
    type CountersT = DelegationsAndFamiliesCounters;

    let config = super::orchestration::common::ProgramConfig::mop_smoke();
    let vm = super::orchestration::common::run_vm_and_capture::<
        CountersT,
        FullUnsignedMachineDecoderConfig,
    >(&config, worker);

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
    let decoder_table = preprocessing_data[&CIRCUIT_TYPE].clone();

    // replay the run, capturing the add/sub family tracing data
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<CIRCUIT_TYPE> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state(), state);

    let data = AddSubOracleData {
        tracing_data: buffer,
        decoder_table,
    };
    bincode_serialize_to_file(&data, WITNESS_CACHE_PATH);
    println!(
        "cached oracle data ({} calls) to {WITNESS_CACHE_PATH}",
        data.tracing_data.len()
    );
    data
}

#[test]
#[ignore = "benchmark; run explicitly with --ignored --nocapture in release mode"]
fn windowed_sumcheck_bench_add_sub() {
    let worker = Worker::new_with_num_threads(8);
    let trace_len = 1usize << TRACE_LEN_LOG2;

    let data = build_or_load_add_sub_oracle_data(&worker);

    let circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("add_sub_lui_auipc_mop"),
    );
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);

    let oracle = NonMemoryCircuitOracle {
        inner: &data.tracing_data,
        decoder_table: &data.decoder_table,
        default_pc_value_in_padding: 4,
    };

    println!("computing full witness trace");
    let now = std::time::Instant::now();
    let mut full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        &circuit,
        add_sub_lui_auipc_mop::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &table_driver,
        &worker,
        None,
        Global,
        Global,
    );
    println!("full witness trace took {:?}", now.elapsed());

    // storage setup, mirroring the prover up to (but excluding) commitments:
    // setup columns + preprocessed lookups, virtual polys, forward pass
    let external_challenges: GKRExternalChallenges<BabyBearField, BabyBearExt4> =
        super::orchestration::common::hardcoded_external_challenges();
    let lookup_alpha = BabyBearExt4::from_array_of_base([
        BabyBearField::new(7),
        BabyBearField::new(31),
        BabyBearField::new(111),
        BabyBearField::new(255),
    ]);
    let lookup_additive_part = BabyBearExt4::from_array_of_base([
        BabyBearField::new(17),
        BabyBearField::new(3),
        BabyBearField::new(77),
        BabyBearField::new(217),
    ]);

    println!("constructing setup + storage");
    let now = std::time::Instant::now();
    let setup = GKRSetup::construct(&table_driver, &data.decoder_table, trace_len, &circuit);
    let mut gkr_storage = GKRStorage::<BabyBearField, BabyBearExt4>::default();
    let (preprocessed_generic_lookup, decoder_lookup_fill_value) = setup
        .preprocess_generic_lookups(
            &circuit,
            lookup_alpha,
            trace_len,
            &mut gkr_storage,
            &worker,
        );
    gkr_storage.insert_base_field_at_layer(
        0,
        cs::definitions::GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
        BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<
            BabyBearField,
            Global,
            16,
        >(trace_len.trailing_zeros())),
    );
    gkr_storage.insert_base_field_at_layer(
        0,
        cs::definitions::GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
        BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<
            BabyBearField,
            Global,
            TIMESTAMP_COLUMNS_NUM_BITS,
        >(trace_len.trailing_zeros())),
    );
    println!("setup + preprocess took {:?}", now.elapsed());

    println!("running forward pass");
    let now = std::time::Instant::now();
    for (layer_idx, layer) in circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &circuit,
            &external_challenges,
            &mut full_trace,
            &[],
            trace_len,
            &preprocessed_generic_lookup,
            lookup_alpha,
            lookup_additive_part,
            decoder_lookup_fill_value,
            &worker,
        );
    }
    println!("forward pass took {:?}", now.elapsed());

    run_windowed_sumcheck_benchmarks(
        &circuit.layers[0],
        0,
        &mut gkr_storage,
        &external_challenges,
        lookup_alpha,
        lookup_additive_part,
        trace_len,
        3,
        &worker,
    );
}
