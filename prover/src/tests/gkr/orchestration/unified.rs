//! Unified-circuit prove orchestration.
//!
//! Proves a program with the single unified reduced-machine circuit
//! (subsumes the 6 per-family circuits + inline i/t) plus per-CSR
//! delegations. Used by the recursion layer.
//!
//! See `unified_orchestration_extraction.md` for architectural decisions.

use super::common::*;
use super::delegations::{
    deserialize_from_file as delegations_deserialize, prove_delegation_bigint,
    prove_delegation_blake, prove_delegation_blake_g_function, prove_delegation_keccak,
    serialize_to_file as delegations_serialize, DelegationProveOutput,
};
use crate::cs::definitions::TimestampScalar;
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::{produce_initial_permutation_product_contribution, SecurityLevel};
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::{GKRExternalChallenges, GKRProof};
use crate::gkr::prover_config::example_configs;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_memory_witness_for_executor_family,
    evaluate_gkr_witness_for_executor_family,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use crate::gkr::witness_gen::trace_structs::RamShuffleMemStateRecord;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::INITIAL_PC;
use cs::definitions::INITIAL_TIMESTAMP;
use cs::utils::split_timestamp;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use worker::Worker;

/// Unified-mode prove output. `unified_proof` is `None` only when the
/// circuits filter explicitly excludes `unified_reduced_machine`.
pub struct UnifiedProverOutput {
    pub unified_proof: Option<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    pub compiled_unified_circuit: GKRCircuitArtifact<BabyBearField>,
    pub delegation_outputs: Vec<DelegationProveOutput>,
    pub register_final_state: [RamShuffleMemStateRecord; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub external_challenges: GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    /// Closes to ONE when the full applicable set was proved (no filter,
    /// machine state + unified proof + all relevant delegations).
    pub permutation_argument_accumulator: BabyBearExt4,
}

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

/// Per-delegation cycle counts. Provided by the caller because the
/// `Counters` trait doesn't expose them via a generic accessor (per-family
/// and unified counter types each have these as plain fields). The test
/// reads the right field for its counter type and passes the count.
#[derive(Clone, Copy, Debug, Default)]
pub struct DelegationCallCounts {
    pub blake: usize,
    pub bigint: usize,
    pub keccak: usize,
    pub blake_g_function: usize,
}

/// Per-delegation witness-eval fn pointers, supplied by the caller (they
/// live in the test module today). Each is `Some` for delegations the
/// active blake-variant build wires up; the orchestration uses `None` to
/// short-circuit that delegation.
pub struct DelegationEvalFns {
    pub blake: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::Blake2sDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
    pub bigint: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
    pub keccak: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::KeccakDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
    pub blake_g_function: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::Blake2sGFunctionDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
}

/// Unified-mode entry point. Takes a pre-captured `VmRunOutput<C>` from
/// [`run_vm_and_capture`] (so the caller stays in charge of when the VM
/// runs — symmetric with how `family_circuits.rs` drives the per-family
/// helpers), proves the unified circuit plus each active delegation,
/// asserts the grand-product accumulator closes to ONE (unless a circuits
/// filter is active, in which case the assert is skipped because partial
/// proving can't close).
///
/// `unified_eval_fn` is the unified-circuit witness eval fn, supplied by
/// the caller from the test module. Same for the delegation eval fns.
pub fn prove_unified<C>(
    vm: VmRunOutput<C>,
    level: SecurityLevel,
    proof_suffix: &str,
    worker: &Worker,
    unified_eval_fn: fn(
        &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            UnifiedRiscvCircuitOracle<'_>,
            BabyBearField,
        >,
    ),
    delegation_eval_fns: &DelegationEvalFns,
    delegation_call_counts: &DelegationCallCounts,
) -> UnifiedProverOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let prove_empty = parse_prove_empty();
    let circuits_filter = parse_circuits_filter();

    let external_challenges = hardcoded_external_challenges();

    // Load the unified circuit and sanity-check its i/t coverage.
    let unified_circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
        delegations_deserialize("../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json")
    } else {
        delegations_deserialize(
            "../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        )
    };
    let num_unified_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();
    let unified_ram_coverage_bytes: usize =
        (num_unified_teardown_sets << TRACE_LEN_LOG2) << (WORD_BITS as usize);
    assert!(
        unified_ram_coverage_bytes <= vm.cycles_bound * 4 * 4
            || unified_ram_coverage_bytes <= vm.ram_bound_bytes,
        "unified circuit i/t coverage ({unified_ram_coverage_bytes} bytes) doesn't fit the run; \
         recompile unified with a larger num_inits_and_teardowns_pairs"
    );

    let _ = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX; // touch import

    // --- Prove delegations first so we can read their memory_traces into
    //     the unified accumulator before computing its own contributions. ---

    let mut delegation_outputs: Vec<DelegationProveOutput> = Vec::new();
    if let Some(eval_fn) = delegation_eval_fns.blake {
        delegation_outputs.push(prove_delegation_blake::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state,
            vm.cycles_bound,
            delegation_call_counts.blake,
            &external_challenges,
            level,
            prove_empty,
            /* compute_only */ false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }
    if let Some(eval_fn) = delegation_eval_fns.bigint {
        delegation_outputs.push(prove_delegation_bigint::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state,
            vm.cycles_bound,
            delegation_call_counts.bigint,
            &external_challenges,
            level,
            prove_empty,
            /* compute_only */ false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }
    if let Some(eval_fn) = delegation_eval_fns.keccak {
        delegation_outputs.push(prove_delegation_keccak::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state,
            vm.cycles_bound,
            delegation_call_counts.keccak,
            &external_challenges,
            level,
            prove_empty,
            /* compute_only */ false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }
    if let Some(eval_fn) = delegation_eval_fns.blake_g_function {
        delegation_outputs.push(prove_delegation_blake_g_function::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state,
            vm.cycles_bound,
            delegation_call_counts.blake_g_function,
            &external_challenges,
            level,
            prove_empty,
            /* compute_only */ false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }

    // --- Prove the unified circuit. ---

    let prove_unified = circuit_in_filter(&circuits_filter, "unified_reduced_machine");

    let num_unified_calls = sum_executor_family_calls(&vm.counters);
    assert!(num_unified_calls < NUM_CYCLES_PER_CHUNK);

    let unified_proof = if prove_unified {
        Some(prove_unified_inner::<C>(
            &vm,
            &unified_circuit,
            num_unified_teardown_sets,
            num_unified_calls,
            unified_eval_fn,
            &external_challenges,
            level,
            proof_suffix,
            worker,
        ))
    } else {
        None
    };

    // --- Accumulator close-check. ---

    let register_final_state_raw = vm
        .register_final_state
        .map(|el| (el.current_value, split_timestamp(el.last_access_timestamp)));
    let mut permutation_argument_accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            vm.final_pc,
            split_timestamp(vm.final_timestamp),
            &external_challenges,
        );
    if let Some(ref p) = unified_proof {
        permutation_argument_accumulator.mul_assign(&p.grand_product_accumulator_computed);
    }
    for d in &delegation_outputs {
        permutation_argument_accumulator.mul_assign(&d.grand_product_factor());
    }

    UnifiedProverOutput {
        unified_proof,
        compiled_unified_circuit: unified_circuit,
        delegation_outputs,
        register_final_state: vm.register_final_state,
        final_pc: vm.final_pc,
        final_timestamp: vm.final_timestamp,
        external_challenges,
        permutation_argument_accumulator,
    }
}

fn prove_unified_inner<C>(
    vm: &VmRunOutput<C>,
    unified_circuit: &GKRCircuitArtifact<BabyBearField>,
    num_unified_teardown_sets: usize,
    num_calls: usize,
    eval_fn: fn(
        &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            UnifiedRiscvCircuitOracle<'_>,
            BabyBearField,
        >,
    ),
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    proof_suffix: &str,
    worker: &Worker,
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let trace_len: usize = 1 << TRACE_LEN_LOG2;

    // Replay the captured trace into the unified destination holder.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut replay_ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state, state);

    let oracle = UnifiedRiscvCircuitOracle::new::<BabyBearField>(
        &buffer[..],
        &vm.text_section,
        common_constants::ROM_WORD_SIZE,
    );
    let unified_table_driver = build_unified_table_driver::<BabyBearField>(&vm.binary);

    // Collect i/t columns sized to the unified circuit's set count.
    let mut unified_inits_and_teardowns = Vec::with_capacity(num_unified_teardown_sets);
    for _ in 0..num_unified_teardown_sets {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        unified_inits_and_teardowns.push(([a, b], [c, d]));
    }
    vm.ram
        .collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
            worker,
            TRACE_LEN_LOG2,
            0,
            &mut unified_inits_and_teardowns,
        );

    println!("Computing memory trace (unified)");
    let unified_memory_trace =
        evaluate_gkr_memory_witness_for_executor_family::<BabyBearField, _, _, _>(
            unified_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            worker,
            Some(unified_inits_and_teardowns.clone()),
            Global,
            Global,
        );

    println!("Computing full trace (unified)");
    let unified_full_trace =
        evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
            unified_circuit,
            eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &unified_table_driver,
            worker,
            Some(unified_inits_and_teardowns),
            Global,
            Global,
        );

    super::common::ensure_memory_trace_consistency(&unified_memory_trace, &unified_full_trace);

    #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
    {
        println!("Checking constraint satisfiability (unified)");
        assert!(
            crate::tests::gkr::check_satisfied(unified_circuit, &unified_full_trace),
            "unified circuit constraint not satisfied"
        );
    }

    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len.trailing_zeros() as usize,
        level,
    );
    let unified_twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, worker);
    let unified_setup = GKRSetup::construct(
        &unified_table_driver,
        oracle.decoder_table_with_options(),
        trace_len,
        unified_circuit,
    );
    let unified_setup_commitment = unified_setup.commit(
        &unified_twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        worker,
    );

    let unified_top_bits: Vec<u32> = (0..num_unified_teardown_sets)
        .map(|i| i as u32)
        .collect();

    println!("Trying to prove (unified)");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        unified_circuit,
        external_challenges,
        unified_full_trace,
        &unified_setup,
        &unified_setup_commitment,
        &unified_twiddles,
        &prover_config,
        unified_top_bits,
        trace_len,
        worker,
    );
    println!("Unified proving time is {:?}", now.elapsed());

    delegations_serialize(
        &proof,
        &format!(
            "test_proofs/unified_reduced_machine_{}_gkr_proof.json",
            proof_suffix
        ),
    );

    proof
}

/// Total executor cycle count. The unified counter (`DelegationsAndUnifiedCounters`)
/// exposes this directly under `REDUCED_MACHINE_CIRCUIT_FAMILY_IDX` (sum of all
/// per-family cycles); the per-family counter would need a 6-way sum, but the
/// unified mode is always driven by the unified counter type, so we just go
/// through the one canonical accessor.
fn sum_executor_family_calls<C: Counters + Copy + std::fmt::Debug>(counters: &C) -> usize {
    counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>()
}
