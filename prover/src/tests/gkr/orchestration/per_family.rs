use super::common::{circuit_in_filter, ensure_memory_trace_consistency, log_prove_decision};
use super::delegations::{deserialize_from_file, serialize_to_file};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::cs::tables::TableDriver;
use crate::definitions::SecurityLevel;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::{prove_configured_with_gkr, CommitmentMode};
use crate::gkr::prover::{GKRExternalChallenges, GKRProof};
use crate::gkr::prover_config::example_configs;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::family_circuits::{
    evaluate_gkr_memory_witness_for_executor_family, evaluate_gkr_witness_for_executor_family,
    evaluate_init_and_teardown_memory_witness, GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
use crate::gkr::witness_gen::oracles::{MemoryCircuitOracle, NonMemoryCircuitOracle};
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, ReplayBuffer, SimpleSnapshotter, SimpleTape, State};
use riscv_transpiler::witness::data_structs::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::witness::{MemDestinationHolder, NonMemDestinationHolder};
use std::alloc::Global;
use transcript::Blake2sTranscript;
use worker::Worker;

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

/// Output of [`prove_non_mem_family`] / [`prove_mem_family`] /
/// [`prove_inits_and_teardowns`].
///
/// `memory_trace` is always populated; the caller threads it into the
/// state/shuffle-ram permutation parsers. `proof` is `None` when the
/// circuit had no calls AND `prove_empty == false`, when the circuits
/// filter excluded this family, or when `compute_only == true`.
pub struct FamilyProveOutput {
    pub memory_trace: GKRMemoryOnlyWitnessTrace<BabyBearField, Global, Global>,
    pub compiled_circuit: GKRCircuitArtifact<BabyBearField>,
    pub proof: Option<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
}

/// Output of [`build_nonmem_family_full_trace`] / [`build_mem_family_full_trace`]:
/// the full witness trace (always populated), the memory-only trace (populated
/// only when the caller requested the memory-consistency check), and whether the
/// built oracle was empty (no calls to this family). The honest
/// `prove_*_family` helpers thread `memory_trace` into the state/shuffle-ram
/// permutation parsers and derive their `should_prove` decision from
/// `oracle_is_empty`; the malicious-proof generators take only `full_trace`.
pub struct BuiltFamilyTrace {
    pub full_trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
    pub memory_trace: Option<GKRMemoryOnlyWitnessTrace<BabyBearField, Global, Global>>,
    pub oracle_is_empty: bool,
}

/// Prove a *pre-built* family witness trace: build the prover config + twiddles,
/// construct & commit the setup, and run the GKR prover. Split out of the family
/// helpers so callers that build the trace another way — the
/// `add_sub_mop_real_program_check_satisfied` smoke test and the malicious-proof
/// generator (which mutates the trace before proving) — share the exact same
/// prove path. The caller owns `check_satisfied`, the empty grand-product
/// assertion, and serialization.
#[allow(clippy::too_many_arguments)]
pub fn prove_built_family_trace(
    circuit: &GKRCircuitArtifact<BabyBearField>,
    table_driver: &TableDriver<BabyBearField>,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    full_trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    worker: &Worker,
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len.trailing_zeros() as usize,
        level,
    );
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, worker);
    let setup = GKRSetup::construct(table_driver, decoder_table_data, trace_len, circuit);
    let setup_commitment = setup.commit(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        worker,
    );

    println!("Trying to prove");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<
        BabyBearField,
        BabyBearExt4,
        DefaultTreeConstructor,
        Blake2sTranscript,
    >(
        circuit,
        external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        CommitmentMode::SeparateMemoryAndWitness,
        Vec::new(),
        trace_len,
        worker,
    );
    println!("Proving time is {:?}", now.elapsed());

    proof
}

/// Per-variant compiled-circuit JSON path
pub fn circuit_path(stem: &str) -> String {
    if USE_GKR_WITH_CACHES {
        format!("../cs/compiled_circuits/{stem}_layout_gkr.json")
    } else {
        format!("../cs/compiled_circuits/{stem}_layout_no_caches_gkr.json")
    }
}

/// Prove one of the four non-mem per-family circuits
/// (add_sub_lui_auipc_mop, jump_branch_slt, shift_binop, unsigned_mul_div).
/// Caller passes the const-generic family index via `CIRCUIT_TYPE`,
/// the compiled-circuit stem (e.g. "add_sub_lui_auipc_mop"), and the
/// preprocessing data slice.
#[expect(
    clippy::too_many_arguments,
    reason = "prover/witness-gen stage plumbing; grouping these into a struct would just move the fan-out"
)]
pub fn prove_non_mem_family<const CIRCUIT_TYPE: u8, C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    table_driver_setup: impl FnOnce(&mut TableDriver<BabyBearField>),
    trace_len: usize,
    num_cycles_per_chunk: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    prove_empty: bool,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    circuit_stem: &str,
    proof_suffix: &str,
    worker: &Worker,
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
) -> FamilyProveOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path(circuit_stem));
    let mut table_driver = TableDriver::<BabyBearField>::new();
    table_driver_setup(&mut table_driver);

    let built = build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
        snapshotter,
        tape,
        expected_final_state,
        cycles_bound,
        num_calls,
        &circuit,
        &table_driver,
        decoder_table_data,
        eval_fn,
        num_cycles_per_chunk,
        true,
        worker,
    );

    let should_prove = !compute_only
        && circuit_in_filter(circuits_filter, circuit_stem)
        && (prove_empty || !built.oracle_is_empty);
    log_prove_decision(circuit_stem, should_prove, compute_only);

    let proof = if should_prove {
        #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
        {
            println!("Checking constraint satisfiability");
            assert!(
                crate::tests::gkr::check_satisfied(&circuit, &built.full_trace),
                "family circuit constraint not satisfied"
            );
        }

        let proof = prove_built_family_trace(
            &circuit,
            &table_driver,
            decoder_table_data,
            built.full_trace,
            trace_len,
            external_challenges,
            level,
            worker,
        );

        if built.oracle_is_empty {
            assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
        }

        serialize_to_file(
            &proof,
            &format!("test_proofs/{circuit_stem}_{proof_suffix}_gkr_proof.json"),
        );

        Some(proof)
    } else {
        None
    };

    FamilyProveOutput {
        memory_trace: built.memory_trace.expect("consistency check was requested"),
        compiled_circuit: circuit,
        proof,
    }
}

/// Prove one of the two mem per-family circuits (mem_word_only,
/// mem_subword_only). The `mem_word_only` family also needs a
/// binary-derived extra-tables setup; the caller drives that via
/// `table_driver_setup`.
#[expect(
    clippy::too_many_arguments,
    reason = "prover/witness-gen stage plumbing; grouping these into a struct would just move the fan-out"
)]
pub fn prove_mem_family<const CIRCUIT_TYPE: u8, C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    table_driver_setup: impl FnOnce(&mut TableDriver<BabyBearField>),
    trace_len: usize,
    num_cycles_per_chunk: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    prove_empty: bool,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    circuit_stem: &str,
    proof_suffix: &str,
    worker: &Worker,
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
) -> FamilyProveOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path(circuit_stem));
    let mut table_driver = TableDriver::<BabyBearField>::new();
    table_driver_setup(&mut table_driver);

    let built = build_mem_family_full_trace::<CIRCUIT_TYPE, _>(
        snapshotter,
        tape,
        expected_final_state,
        cycles_bound,
        num_calls,
        &circuit,
        &table_driver,
        decoder_table_data,
        eval_fn,
        num_cycles_per_chunk,
        true,
        worker,
    );

    let should_prove = !compute_only
        && circuit_in_filter(circuits_filter, circuit_stem)
        && (prove_empty || !built.oracle_is_empty);
    log_prove_decision(circuit_stem, should_prove, compute_only);

    let proof = if should_prove {
        #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
        {
            println!("Checking constraint satisfiability");
            assert!(
                crate::tests::gkr::check_satisfied(&circuit, &built.full_trace),
                "family circuit constraint not satisfied"
            );
        }

        let proof = prove_built_family_trace(
            &circuit,
            &table_driver,
            decoder_table_data,
            built.full_trace,
            trace_len,
            external_challenges,
            level,
            worker,
        );

        if built.oracle_is_empty {
            assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
        }

        serialize_to_file(
            &proof,
            &format!("test_proofs/{circuit_stem}_{proof_suffix}_gkr_proof.json"),
        );

        Some(proof)
    } else {
        None
    };

    FamilyProveOutput {
        memory_trace: built.memory_trace.expect("consistency check was requested"),
        compiled_circuit: circuit,
        proof,
    }
}

/// Prove the standalone inits-and-teardowns circuit. Structurally
/// different from the executor family helpers above — there's no
/// snapshotter replay; the witness is built directly from the dumped
/// inits/teardowns columns the VM produced.
#[expect(
    clippy::too_many_arguments,
    reason = "prover/witness-gen stage plumbing; grouping these into a struct would just move the fan-out"
)]
#[expect(
    clippy::type_complexity,
    reason = "generic over field + allocator; a bound-free type alias would drop those bounds"
)]
pub fn prove_inits_and_teardowns(
    inits_and_teardowns: Vec<(
        [Vec<BabyBearField, Global>; 2],
        [Vec<BabyBearField, Global>; 2],
    )>,
    total_unique_teardowns: usize,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    proof_suffix: &str,
    worker: &Worker,
) -> FamilyProveOutput {
    // i/t has historically always read the `no_caches` layout in this
    // test path. Preserving that here — see the original family_circuits.rs.
    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        "../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json",
    );

    let table_driver = TableDriver::<BabyBearField>::new();

    let witness_inner =
        evaluate_init_and_teardown_memory_witness(inits_and_teardowns, &circuit, Global, Global);

    let memory_trace = GKRMemoryOnlyWitnessTrace {
        column_major_trace: witness_inner.clone(),
    };

    let should_prove = !compute_only && circuit_in_filter(circuits_filter, "inits_and_teardowns");
    log_prove_decision("inits_and_teardowns", should_prove, compute_only);

    if !should_prove {
        return FamilyProveOutput {
            memory_trace,
            compiled_circuit: circuit,
            proof: None,
        };
    }

    let full_trace = GKRFullWitnessTrace {
        column_major_memory_trace: witness_inner,
        column_major_witness_trace: Vec::new(),
        column_major_scratch_space_trace: Vec::new(),
        generic_lookup_mapping: Vec::new(),
        range_check_16_lookup_mapping: Vec::new(),
        timestamp_range_check_lookup_mapping: Vec::new(),
    };

    #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
    {
        println!("Checking constraint satisfiability");
        assert!(
            crate::tests::gkr::check_satisfied(&circuit, &full_trace),
            "inits_and_teardowns constraint not satisfied"
        );
    }

    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len.trailing_zeros() as usize,
        level,
    );
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, worker);
    let setup = GKRSetup::construct(&table_driver, &[], trace_len, &circuit);
    let setup_commitment = setup.commit(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        worker,
    );

    let inits_and_teardowns_top_bits: Vec<u32> = (0..circuit.memory_layout.teardown_sets.len())
        .map(|el| el as u32)
        .collect();

    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<
        BabyBearField,
        BabyBearExt4,
        DefaultTreeConstructor,
        Blake2sTranscript,
    >(
        &circuit,
        external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        CommitmentMode::SeparateMemoryAndWitness,
        inits_and_teardowns_top_bits,
        trace_len,
        worker,
    );
    println!("Proving time is {:?}", now.elapsed());

    if total_unique_teardowns == 0 {
        assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
    }

    serialize_to_file(
        &proof,
        &format!("test_proofs/inits_and_teardowns_{proof_suffix}_gkr_proof.json"),
    );

    FamilyProveOutput {
        memory_trace,
        compiled_circuit: circuit,
        proof: Some(proof),
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "prover/witness-gen stage plumbing; grouping these into a struct would just move the fan-out"
)]
pub fn build_nonmem_family_full_trace<const CIRCUIT_TYPE: u8, C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    circuit: &GKRCircuitArtifact<BabyBearField>,
    table_driver: &TableDriver<BabyBearField>,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
    num_cycles_per_chunk: usize,
    run_memory_consistency_check: bool,
    worker: &Worker,
) -> BuiltFamilyTrace
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<CIRCUIT_TYPE> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: decoder_table_data,
        default_pc_value_in_padding: 4,
    };
    let oracle_is_empty = oracle.inner.is_empty();

    let memory_trace = if run_memory_consistency_check {
        println!("Computing memory trace");
        Some(evaluate_gkr_memory_witness_for_executor_family::<
            BabyBearField,
            _,
            _,
            _,
        >(
            circuit,
            num_cycles_per_chunk,
            &oracle,
            worker,
            None,
            Global,
            Global,
        ))
    } else {
        None
    };

    println!("Computing full trace");
    let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        circuit,
        eval_fn,
        num_cycles_per_chunk,
        &oracle,
        table_driver,
        worker,
        None,
        Global,
        Global,
    );

    if let Some(memory_trace) = &memory_trace {
        ensure_memory_trace_consistency(memory_trace, &full_trace);
    }

    BuiltFamilyTrace {
        full_trace,
        memory_trace,
        oracle_is_empty,
    }
}

/// Memory-family counterpart of [`build_nonmem_family_full_trace`]: replay into
/// a `MemDestinationHolder`, build a `MemoryCircuitOracle`, compute the full
/// witness trace, and (optionally) run the memory-trace consistency check.
/// Used by the malicious-proof generator to obtain a mem-family trace it can
/// mutate before proving.
#[allow(clippy::too_many_arguments)]
pub fn build_mem_family_full_trace<const CIRCUIT_TYPE: u8, C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    circuit: &GKRCircuitArtifact<BabyBearField>,
    table_driver: &TableDriver<BabyBearField>,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
    num_cycles_per_chunk: usize,
    run_memory_consistency_check: bool,
    worker: &Worker,
) -> BuiltFamilyTrace
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
    let mut tracer = MemDestinationHolder::<CIRCUIT_TYPE> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);

    let oracle = MemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: decoder_table_data,
    };
    let oracle_is_empty = oracle.inner.is_empty();

    let memory_trace = if run_memory_consistency_check {
        println!("Computing memory trace");
        Some(evaluate_gkr_memory_witness_for_executor_family::<
            BabyBearField,
            _,
            _,
            _,
        >(
            circuit,
            num_cycles_per_chunk,
            &oracle,
            worker,
            None,
            Global,
            Global,
        ))
    } else {
        None
    };

    println!("Computing full trace");
    let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        circuit,
        eval_fn,
        num_cycles_per_chunk,
        &oracle,
        table_driver,
        worker,
        None,
        Global,
        Global,
    );

    if let Some(memory_trace) = &memory_trace {
        ensure_memory_trace_consistency(memory_trace, &full_trace);
    }

    BuiltFamilyTrace {
        full_trace,
        memory_trace,
        oracle_is_empty,
    }
}
