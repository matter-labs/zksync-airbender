use super::*;

pub(super) fn make_delegation_tracing_host_for_test<W>(
    circuit_type: DelegationCircuitType,
    buffer: Vec<W>,
) -> TracingDataHost<Global>
where
    W: gpu_trace::trace::tracing_data::DelegationTracingDataHostSource,
{
    let trace = gpu_trace::witness::trace_delegation::DelegationTraceHost::<W, Global> {
        chunks: vec![Arc::new(buffer)],
    };
    TracingDataHost::Delegation(W::get(circuit_type, trace))
}

pub(super) fn prepare_unified_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_unified_proof_fixture_in_mode(circuit_common::SoundnessMode::DEFAULT)
}

pub(super) fn prepare_unified_proof_fixture_in_mode(
    mode: circuit_common::SoundnessMode,
) -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(CanonicalCircuit::UnifiedReducedMachine, mode)
}

pub(super) fn prepare_unified_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unified_proof_fixture().base
}
