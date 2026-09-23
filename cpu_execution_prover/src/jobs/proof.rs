use super::{rows, teardown_sets, CpuJobs};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    bigint_witness_eval_fn, blake2_g_function_witness_eval_fn,
    blake2_with_compression_witness_eval_fn, evaluate_gkr_witness_for_delegation_circuit,
    evaluate_gkr_witness_for_executor_family, evaluate_init_and_teardown_memory_witness,
    keccak_special5_witness_eval_fn, prove_configured_with_gkr_with_backends, Blake2sTranscript,
    ColumnMajorWitnessProxy, CommitmentMode, DefaultTreeConstructor, DelegationAbiDescription,
    DelegationOracle, DelegationWitness, GKRFullWitnessTrace, MemoryCircuitOracle,
    NonMemoryCircuitOracle, UnifiedRiscvCircuitOracle, UnrolledCircuitWitnessEvalFn, BF, E4,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::messages::{ProofRequest, ProofResult};
use execution_prover::prover_config;
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::caps::join_memory_caps;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType,
};
use execution_prover_model::trace::{
    ChunkedTraceHolder, DelegationTracingDataHost, InitsAndTeardownsTraceHost, TracingDataHost,
    UnrolledTracingDataHost,
};
use std::alloc::Global;
use worker::Worker;

type Witness = GKRFullWitnessTrace<BF, Global, Global>;

pub(super) fn run<A: HostTraceAllocator>(
    jobs: &mut CpuJobs,
    request: ProofRequest<A, CpuCircuitPrecomputations>,
    worker: &Worker,
) -> ProofResult<A> {
    let ProofRequest {
        batch_id,
        circuit_type,
        sequence_id,
        precomputations,
        inits_and_teardowns,
        tracing_data,
        external_challenges,
        memory_caps,
        security_level,
    } = request;
    let config = prover_config(circuit_type, security_level);
    let twiddles = jobs.twiddles(precomputations.trace_len, worker);
    let setup_commitment = precomputations
        .setup_commitment
        .get()
        .unwrap_or_else(|| panic!("setup initialization has not run for {circuit_type:?}"));
    let (witness, top_bits) = build_witness(
        &precomputations,
        circuit_type,
        inits_and_teardowns.as_ref(),
        tracing_data.as_ref(),
        worker,
    );
    let proof = prove_configured_with_gkr_with_backends::<
        BF,
        E4,
        DefaultTreeConstructor,
        Blake2sTranscript,
        _,
        _,
    >(
        precomputations.compiled_circuit(),
        &external_challenges,
        witness,
        &precomputations.setup,
        setup_commitment,
        &*twiddles,
        &config,
        CommitmentMode::SeparateMemoryAndWitness,
        top_bits,
        precomputations.trace_len,
        &jobs.backend,
        &jobs.gkr_backend,
        worker,
    );

    // `SeparateMemoryAndWitness` re-commits memory while proving, and that
    // second commitment is the one the verifier checks: it must equal the cap
    // published in the memory pass, or the two passes proved different traces.
    let committed = join_memory_caps(&memory_caps, config.lde_factor, config.cap_size);
    assert!(
        proof.whir_proof.memory_commitment.commitment.cap.cap == committed.cap,
        "memory commitment produced while proving {circuit_type:?}[{sequence_id}] \
         disagrees with the cap committed in its memory pass"
    );

    ProofResult {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns,
        tracing_data,
        proof,
    }
}

/// The full witness and the top-bits vector the proof carries: empty for
/// families and delegations, the instance's windows for inits-and-teardowns
/// and unified.
fn build_witness<A: HostTraceAllocator>(
    precomputations: &CpuCircuitPrecomputations,
    circuit_type: CircuitType,
    inits_and_teardowns: Option<&InitsAndTeardownsTraceHost<A>>,
    tracing_data: Option<&TracingDataHost<A>>,
    worker: &Worker,
) -> (Witness, Vec<u32>) {
    match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(_)) => {
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace))) =
                tracing_data
            else {
                panic!("proof for {circuit_type:?} received a trace of a different shape");
            };
            let Some(UnrolledCircuitWitnessEvalFn::NonMemory {
                witness_fn,
                decoder_table,
                default_pc_value_in_padding,
            }) = precomputations.witness_eval_fn.as_ref()
            else {
                panic!("{circuit_type:?} carries no matching witness evaluator");
            };
            let rows = rows(trace);
            let oracle = NonMemoryCircuitOracle {
                inner: &rows,
                decoder_table,
                default_pc_value_in_padding: *default_pc_value_in_padding,
            };
            let witness = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
                precomputations.compiled_circuit(),
                *witness_fn,
                precomputations.trace_len,
                &oracle,
                &precomputations.table_driver,
                worker,
                None,
                Global,
                Global,
            );
            (witness, Vec::new())
        }
        CircuitType::Unrolled(UnrolledCircuitType::Memory(_)) => {
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace))) =
                tracing_data
            else {
                panic!("proof for {circuit_type:?} received a trace of a different shape");
            };
            let Some(UnrolledCircuitWitnessEvalFn::Memory {
                witness_fn,
                decoder_table,
            }) = precomputations.witness_eval_fn.as_ref()
            else {
                panic!("{circuit_type:?} carries no matching witness evaluator");
            };
            let rows = rows(trace);
            let oracle = MemoryCircuitOracle {
                inner: &rows,
                decoder_table,
            };
            let witness = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
                precomputations.compiled_circuit(),
                *witness_fn,
                precomputations.trace_len,
                &oracle,
                &precomputations.table_driver,
                worker,
                None,
                Global,
                Global,
            );
            (witness, Vec::new())
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(trace))) =
                tracing_data
            else {
                panic!("proof for {circuit_type:?} received a trace of a different shape");
            };
            let Some(UnrolledCircuitWitnessEvalFn::Unified {
                witness_fn,
                decoder_table,
            }) = precomputations.witness_eval_fn.as_ref()
            else {
                panic!("{circuit_type:?} carries no matching witness evaluator");
            };
            let sets = teardown_sets(precomputations, inits_and_teardowns);
            // A unified instance without inits-and-teardowns is a leading
            // dummy: its rows cancel, and its windows only have to keep the
            // concatenated sequence ordered.
            let top_bits = inits_and_teardowns
                .map_or_else(|| vec![0u32; sets.len()], |trace| trace.top_bits.clone());
            let rows = rows(trace);
            let oracle = UnifiedRiscvCircuitOracle {
                inner: &rows,
                decoder_table,
            };
            let witness = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
                precomputations.compiled_circuit(),
                *witness_fn,
                precomputations.trace_len,
                &oracle,
                &precomputations.table_driver,
                worker,
                Some(sets),
                Global,
                Global,
            );
            (witness, top_bits)
        }
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            let Some(trace) = inits_and_teardowns else {
                panic!("proof for {circuit_type:?} received a trace of a different shape");
            };
            let sets = teardown_sets(precomputations, Some(trace));
            // The memory columns are the whole witness: a standalone
            // inits-and-teardowns circuit has no execution rows.
            let witness = GKRFullWitnessTrace {
                column_major_memory_trace: evaluate_init_and_teardown_memory_witness(
                    sets,
                    precomputations.compiled_circuit(),
                    Global,
                    Global,
                ),
                column_major_witness_trace: Vec::new(),
                column_major_scratch_space_trace: Vec::new(),
                generic_lookup_mapping: Vec::new(),
                range_check_16_lookup_mapping: Vec::new(),
                timestamp_range_check_lookup_mapping: Vec::new(),
            };
            (witness, trace.top_bits.clone())
        }
        CircuitType::Delegation(delegation_type) => {
            let Some(TracingDataHost::Delegation(trace)) = tracing_data else {
                panic!("proof for {circuit_type:?} received a trace of a different shape");
            };
            let witness = match (delegation_type, trace) {
                (
                    DelegationCircuitType::BigIntWithControl,
                    DelegationTracingDataHost::BigIntWithControl(trace),
                ) => delegation_witness(precomputations, trace, bigint_witness_eval_fn, worker),
                (
                    DelegationCircuitType::Blake2WithCompression,
                    DelegationTracingDataHost::Blake2WithCompression(trace),
                ) => delegation_witness(
                    precomputations,
                    trace,
                    blake2_with_compression_witness_eval_fn,
                    worker,
                ),
                (
                    DelegationCircuitType::Blake2GFunction,
                    DelegationTracingDataHost::Blake2GFunction(trace),
                ) => delegation_witness(
                    precomputations,
                    trace,
                    blake2_g_function_witness_eval_fn,
                    worker,
                ),
                (
                    DelegationCircuitType::KeccakSpecial5,
                    DelegationTracingDataHost::KeccakSpecial5(trace),
                ) => delegation_witness(
                    precomputations,
                    trace,
                    keccak_special5_witness_eval_fn,
                    worker,
                ),
                _ => panic!("proof for {circuit_type:?} received a trace of a different shape"),
            };
            (witness, Vec::new())
        }
    }
}

fn delegation_witness<
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
    A: HostTraceAllocator,
>(
    precomputations: &CpuCircuitPrecomputations,
    trace: &ChunkedTraceHolder<
        DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>,
        A,
    >,
    witness_eval_fn: fn(
        &mut ColumnMajorWitnessProxy<
            '_,
            DelegationOracle<
                '_,
                D,
                REG_ACCESSES,
                INDIRECT_READS,
                INDIRECT_WRITES,
                VARIABLE_OFFSETS,
            >,
            BF,
        >,
    ),
    worker: &Worker,
) -> Witness {
    let rows = rows(trace);
    let oracle = DelegationOracle::<D, _, _, _, _> {
        cycle_data: &rows,
        marker: core::marker::PhantomData,
    };
    evaluate_gkr_witness_for_delegation_circuit::<BF, _, _, _>(
        precomputations.compiled_circuit(),
        witness_eval_fn,
        precomputations.trace_len,
        &oracle,
        &precomputations.table_driver,
        worker,
        Global,
        Global,
    )
}
