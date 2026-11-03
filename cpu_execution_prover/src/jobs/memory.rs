use super::caps::split_memory_cap;
use super::{rows, teardown_sets, CpuJobs, CpuTwiddles};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    commit_memory_tree_for_delegation_circuit, commit_memory_tree_for_inits_and_teardowns,
    commit_memory_tree_for_unified_circuits, commit_memory_tree_for_unrolled_mem_circuits,
    commit_memory_tree_for_unrolled_nonmem_circuits, BigintAbiDescription,
    Blake2sGFunctionAbiDescription, Blake2sRoundFunctionAbiDescription, DefaultBabyBearBackend,
    DefaultTreeConstructor, DelegationAbiDescription, DelegationWitness, KeccakChi5AbiDescription,
    KeccakColumnParityAbiDescription, KeccakSpecial5AbiDescription, KeccakThetaRhoAbiDescription,
    MerkleTreeCapVarLength, ProverConfig, UnrolledCircuitWitnessEvalFn, BF, E4,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::messages::{MemoryCommitmentRequest, MemoryCommitmentResult};
use execution_prover::prover_config;
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType,
};
use execution_prover_model::trace::{
    ChunkedTraceHolder, DelegationTracingDataHost, TracingDataHost, UnrolledTracingDataHost,
};
use std::alloc::Global;
use worker::Worker;

/// `commit_memory_tree_for_unified_circuits` takes the text section but does
/// not read it: the binary is already baked into the compiled artifact.
const UNUSED_TEXT_SECTION: &[u32] = &[];

pub(super) fn run<A: HostTraceAllocator>(
    jobs: &mut CpuJobs,
    request: MemoryCommitmentRequest<A, CpuCircuitPrecomputations>,
    worker: &Worker,
) -> MemoryCommitmentResult<A> {
    let MemoryCommitmentRequest {
        batch_id,
        circuit_type,
        sequence_id,
        precomputations,
        inits_and_teardowns,
        tracing_data,
        security_level,
    } = request;
    let config = prover_config(circuit_type, security_level);
    let twiddles = jobs.twiddles(precomputations.trace_len, worker);
    let flat_cap = match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(_)) => {
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace))) =
                tracing_data.as_ref()
            else {
                panic!(
                    "memory commitment for {circuit_type:?} received a trace of a different shape"
                );
            };
            let Some(UnrolledCircuitWitnessEvalFn::NonMemory {
                decoder_table,
                default_pc_value_in_padding,
                ..
            }) = precomputations.witness_eval_fn.as_ref()
            else {
                panic!("{circuit_type:?} carries no matching witness evaluator");
            };
            let rows = rows(trace);
            commit_memory_tree_for_unrolled_nonmem_circuits::<
                BF,
                E4,
                DefaultTreeConstructor,
                Global,
                Global,
                _,
            >(
                &jobs.backend,
                precomputations.compiled_circuit(),
                &rows,
                &*twiddles,
                &config,
                *default_pc_value_in_padding,
                decoder_table,
                worker,
            )
        }
        CircuitType::Unrolled(UnrolledCircuitType::Memory(_)) => {
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace))) =
                tracing_data.as_ref()
            else {
                panic!(
                    "memory commitment for {circuit_type:?} received a trace of a different shape"
                );
            };
            let Some(UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. }) =
                precomputations.witness_eval_fn.as_ref()
            else {
                panic!("{circuit_type:?} carries no matching witness evaluator");
            };
            let rows = rows(trace);
            commit_memory_tree_for_unrolled_mem_circuits::<
                BF,
                E4,
                DefaultTreeConstructor,
                Global,
                Global,
                _,
            >(
                &jobs.backend,
                precomputations.compiled_circuit(),
                &rows,
                &*twiddles,
                &config,
                decoder_table,
                worker,
            )
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(trace))) =
                tracing_data.as_ref()
            else {
                panic!(
                    "memory commitment for {circuit_type:?} received a trace of a different shape"
                );
            };
            let Some(UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. }) =
                precomputations.witness_eval_fn.as_ref()
            else {
                panic!("{circuit_type:?} carries no matching witness evaluator");
            };
            let rows = rows(trace);
            let sets = teardown_sets(&precomputations, inits_and_teardowns.as_ref());
            commit_memory_tree_for_unified_circuits::<
                BF,
                E4,
                DefaultTreeConstructor,
                Global,
                Global,
                _,
            >(
                &jobs.backend,
                precomputations.compiled_circuit(),
                &rows,
                sets,
                UNUSED_TEXT_SECTION,
                &*twiddles,
                &config,
                decoder_table,
                worker,
            )
        }
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            assert!(
                inits_and_teardowns.is_some(),
                "memory commitment for {circuit_type:?} received no inits-and-teardowns trace"
            );
            let sets = teardown_sets(&precomputations, inits_and_teardowns.as_ref());
            commit_memory_tree_for_inits_and_teardowns::<
                BF,
                E4,
                DefaultTreeConstructor,
                Global,
                Global,
                _,
            >(
                &jobs.backend,
                precomputations.compiled_circuit(),
                sets,
                &*twiddles,
                &config,
                worker,
            )
        }
        CircuitType::Delegation(delegation_type) => {
            let Some(TracingDataHost::Delegation(trace)) = tracing_data.as_ref() else {
                panic!(
                    "memory commitment for {circuit_type:?} received a trace of a different shape"
                );
            };
            match (delegation_type, trace) {
                (
                    DelegationCircuitType::BigIntWithControl,
                    DelegationTracingDataHost::BigIntWithControl(trace),
                ) => commit_delegation::<BigintAbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                (
                    DelegationCircuitType::Blake2WithCompression,
                    DelegationTracingDataHost::Blake2WithCompression(trace),
                ) => commit_delegation::<Blake2sRoundFunctionAbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                (
                    DelegationCircuitType::Blake2GFunction,
                    DelegationTracingDataHost::Blake2GFunction(trace),
                ) => commit_delegation::<Blake2sGFunctionAbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                (
                    DelegationCircuitType::KeccakSpecial5,
                    DelegationTracingDataHost::KeccakSpecial5(trace),
                ) => commit_delegation::<KeccakSpecial5AbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                (
                    DelegationCircuitType::KeccakThetaRho,
                    DelegationTracingDataHost::KeccakThetaRho(trace),
                ) => commit_delegation::<KeccakThetaRhoAbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                (
                    DelegationCircuitType::KeccakColumnParity,
                    DelegationTracingDataHost::KeccakColumnParity(trace),
                ) => commit_delegation::<KeccakColumnParityAbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                (
                    DelegationCircuitType::KeccakChi5,
                    DelegationTracingDataHost::KeccakChi5(trace),
                ) => commit_delegation::<KeccakChi5AbiDescription, _, _, _, _, _>(
                    &jobs.backend,
                    &precomputations,
                    trace,
                    &config,
                    &twiddles,
                    worker,
                ),
                _ => panic!(
                    "memory commitment for {circuit_type:?} received a trace of a different shape"
                ),
            }
        }
    };
    let merkle_tree_caps = split_memory_cap(&flat_cap, config.lde_factor, config.cap_size);
    MemoryCommitmentResult {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns,
        tracing_data,
        merkle_tree_caps,
    }
}

fn commit_delegation<
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
    A: HostTraceAllocator,
>(
    backend: &DefaultBabyBearBackend,
    precomputations: &CpuCircuitPrecomputations,
    trace: &ChunkedTraceHolder<
        DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>,
        A,
    >,
    config: &ProverConfig,
    twiddles: &CpuTwiddles,
    worker: &Worker,
) -> MerkleTreeCapVarLength {
    let rows = rows(trace);
    commit_memory_tree_for_delegation_circuit::<
        BF,
        E4,
        DefaultTreeConstructor,
        Global,
        Global,
        D,
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
        _,
    >(
        backend,
        precomputations.compiled_circuit(),
        &rows,
        twiddles,
        config,
        worker,
    )
}
