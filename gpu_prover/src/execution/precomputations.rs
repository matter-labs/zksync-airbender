use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::circuit_type::{DelegationCircuitType, MainCircuitType};
use crate::prover::setup::SetupTreesAndCaps;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use fft::LdePrecomputations;
use field::Mersenne31Field;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::prover_stages::SetupPrecomputations;
use prover::risc_v_simulator::cycle::{
    IMStandardIsaConfig, IMWithoutSignedMulDivIsaConfig, IWithoutByteAccessIsaConfig,
    IWithoutByteAccessIsaConfigWithDelegation, MachineConfig,
};
use prover::trace_holder::RowMajorTrace;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use setups::{
    bigint_with_control, blake2_with_compression, final_reduced_risc_v_machine,
    machine_without_signed_mul_div, reduced_risc_v_log_23_machine, reduced_risc_v_machine,
    risc_v_cycles,
};
use std::alloc::Global;
use std::sync::{Arc, OnceLock};
use worker::Worker;

type BF = Mersenne31Field;

#[derive(Clone)]
pub struct CircuitPrecomputations {
    pub compiled_circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub lde_precomputations: Arc<LdePrecomputations<Global>>,
    pub setup_trace: Arc<Vec<BF, ConcurrentStaticHostAllocator>>,
    pub setup_trees_and_caps: Arc<OnceLock<SetupTreesAndCaps>>,
}

fn get_setup_trace_from_row_major_trace<const N: usize>(
    trace: &RowMajorTrace<BF, N, Global>,
) -> Arc<Vec<BF, ConcurrentStaticHostAllocator>> {
    let trace_total_size = trace.as_slice().len();
    let trace_total_size_bytes = trace_total_size * size_of::<BF>();
    let trace_len = trace.len();
    assert!(trace_len.is_power_of_two());
    let trace_len_bytes = trace_len * size_of::<BF>();
    let log_trace_len_bytes = trace_len_bytes.trailing_zeros();
    let allocation =
        HostAllocation::alloc(trace_total_size_bytes, CudaHostAllocFlags::DEFAULT).unwrap();
    let allocator = ConcurrentStaticHostAllocator::new([allocation], log_trace_len_bytes);
    let mut setup_evaluations = Vec::with_capacity_in(trace.as_slice().len(), allocator);
    unsafe { setup_evaluations.set_len(trace.as_slice().len()) };
    transpose::transpose(
        trace.as_slice(),
        &mut setup_evaluations,
        trace.padded_width,
        trace_len,
    );
    setup_evaluations.truncate(trace_len * trace.width());
    Arc::new(setup_evaluations)
}

pub fn get_main_circuit_precomputations(
    circuit_type: MainCircuitType,
    bytecode: &[u32],
    worker: &Worker,
) -> CircuitPrecomputations {
    let (compiled_circuit, table_driver) = match circuit_type {
        MainCircuitType::FinalReducedRiscVMachine => {
            let csrs = IWithoutByteAccessIsaConfig::ALLOWED_DELEGATION_CSRS;
            (
                final_reduced_risc_v_machine::get_machine(bytecode, csrs),
                final_reduced_risc_v_machine::get_table_driver(bytecode, csrs),
            )
        }
        MainCircuitType::MachineWithoutSignedMulDiv => {
            let csrs = IMWithoutSignedMulDivIsaConfig::ALLOWED_DELEGATION_CSRS;
            (
                machine_without_signed_mul_div::get_machine(bytecode, csrs),
                machine_without_signed_mul_div::get_table_driver(bytecode, csrs),
            )
        }
        MainCircuitType::ReducedRiscVLog23Machine => {
            let csrs = IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS;
            (
                reduced_risc_v_log_23_machine::get_machine(bytecode, csrs),
                reduced_risc_v_log_23_machine::get_table_driver(bytecode, csrs),
            )
        }
        MainCircuitType::ReducedRiscVMachine => {
            let csrs = IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS;
            (
                reduced_risc_v_machine::get_machine(bytecode, csrs),
                reduced_risc_v_machine::get_table_driver(bytecode, csrs),
            )
        }
        MainCircuitType::RiscVCycles => {
            let csrs = IMStandardIsaConfig::ALLOWED_DELEGATION_CSRS;
            (
                risc_v_cycles::get_machine(bytecode, csrs),
                risc_v_cycles::get_table_driver(bytecode, csrs),
            )
        }
    };
    let domain_size = circuit_type.get_domain_size();
    let lde_precomputations = LdePrecomputations::new(
        domain_size,
        circuit_type.get_lde_factor(),
        circuit_type.get_lde_source_cosets(),
        &worker,
    );
    let setup = SetupPrecomputations::<
        DEFAULT_TRACE_PADDING_MULTIPLE,
        Global,
        DefaultTreeConstructor,
    >::get_main_domain_trace(
        &table_driver,
        domain_size,
        &compiled_circuit.setup_layout,
        &worker,
    );
    CircuitPrecomputations {
        compiled_circuit: Arc::new(compiled_circuit),
        lde_precomputations: Arc::new(lde_precomputations),
        setup_trace: get_setup_trace_from_row_major_trace(&setup),
        setup_trees_and_caps: Arc::new(OnceLock::new()),
    }
}

pub fn get_delegation_circuit_precomputations(
    circuit_type: DelegationCircuitType,
    worker: &Worker,
) -> CircuitPrecomputations {
    let (compiled_circuit, table_driver) = match circuit_type {
        DelegationCircuitType::BigIntWithControl => (
            bigint_with_control::get_delegation_circuit().compiled_circuit,
            bigint_with_control::get_table_driver(),
        ),
        DelegationCircuitType::Blake2WithCompression => (
            blake2_with_compression::get_delegation_circuit().compiled_circuit,
            blake2_with_compression::get_table_driver(),
        ),
    };
    let domain_size = circuit_type.get_domain_size();
    let lde_precomputations = LdePrecomputations::new(
        domain_size,
        circuit_type.get_lde_factor(),
        circuit_type.get_lde_source_cosets(),
        &worker,
    );
    let setup = SetupPrecomputations::<
        DEFAULT_TRACE_PADDING_MULTIPLE,
        Global,
        DefaultTreeConstructor,
    >::get_main_domain_trace(
        &table_driver,
        domain_size,
        &compiled_circuit.setup_layout,
        &worker,
    );
    CircuitPrecomputations {
        compiled_circuit: Arc::new(compiled_circuit),
        lde_precomputations: Arc::new(lde_precomputations),
        setup_trace: get_setup_trace_from_row_major_trace(&setup),
        setup_trees_and_caps: Arc::new(OnceLock::new()),
    }
}
