use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::circuit_type::UnrolledCircuitType::InitsAndTeardowns;
use crate::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use crate::prover::setup::SetupTreesAndCaps;
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use cs::machine::ops::unrolled::materialize_flattened_decoder_table;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use fft::LdePrecomputations;
use field::Mersenne31Field;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::prover_stages::SetupPrecomputations;
use prover::trace_holder::RowMajorTrace;
use prover::{common_constants, DEFAULT_TRACE_PADDING_MULTIPLE};
use setups::{
    add_sub_lui_auipc_mop, bigint_with_control, blake2_with_compression, inits_and_teardowns,
    jump_branch_slt, keccak_special5, load_store_subword_only, load_store_word_only, mul_div,
    mul_div_unsigned, shift_binary_csr, unified_reduced_machine,
};
use std::alloc::Global;
use std::collections::BTreeMap;
use std::iter::once;
use std::sync::{Arc, OnceLock};
use worker::Worker;

type BF = Mersenne31Field;

#[derive(Clone)]
pub struct CircuitPrecomputations {
    pub compiled_circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub lde_precomputations: Arc<LdePrecomputations<Global>>,
    pub setup_trace: Arc<Vec<BF, ConcurrentStaticHostAllocator>>,
    pub setup_trees_and_caps: Arc<OnceLock<SetupTreesAndCaps>>,
    pub decoder_data: Option<Arc<Vec<ExecutorFamilyDecoderData, ConcurrentStaticHostAllocator>>>,
}

impl CircuitPrecomputations {
    pub fn new(
        circuit_type: CircuitType,
        binary_image: &[u32],
        bytecode: &[u32],
        worker: &Worker,
    ) -> Self {
        let (compiled_circuit, table_driver) = match circuit_type {
            CircuitType::Delegation(circuit_type) => match circuit_type {
                DelegationCircuitType::BigIntWithControl => {
                    let circuit = bigint_with_control::get_delegation_circuit();
                    (circuit.compiled_circuit, circuit.table_driver)
                }
                DelegationCircuitType::Blake2WithCompression => {
                    let circuit = blake2_with_compression::get_delegation_circuit();
                    (circuit.compiled_circuit, circuit.table_driver)
                }
                DelegationCircuitType::KeccakSpecial5 => {
                    let circuit = keccak_special5::get_delegation_circuit();
                    (circuit.compiled_circuit, circuit.table_driver)
                }
            },
            CircuitType::Unrolled(circuit_type) => match circuit_type {
                InitsAndTeardowns => (
                    inits_and_teardowns::get_circuit(binary_image),
                    inits_and_teardowns::get_table_driver(binary_image),
                ),
                UnrolledCircuitType::Memory(circuit_type) => match circuit_type {
                    UnrolledMemoryCircuitType::LoadStoreSubwordOnly => (
                        load_store_subword_only::get_circuit(binary_image),
                        load_store_subword_only::get_table_driver(binary_image),
                    ),
                    UnrolledMemoryCircuitType::LoadStoreWordOnly => (
                        load_store_word_only::get_circuit(binary_image),
                        load_store_word_only::get_table_driver(binary_image),
                    ),
                },
                UnrolledCircuitType::NonMemory(circuit_type) => match circuit_type {
                    UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop => (
                        add_sub_lui_auipc_mop::get_circuit(binary_image),
                        add_sub_lui_auipc_mop::get_table_driver(binary_image),
                    ),
                    UnrolledNonMemoryCircuitType::JumpBranchSlt => (
                        jump_branch_slt::get_circuit(binary_image),
                        jump_branch_slt::get_table_driver(binary_image),
                    ),
                    UnrolledNonMemoryCircuitType::MulDiv => (
                        mul_div::get_circuit(binary_image),
                        mul_div::get_table_driver(binary_image),
                    ),
                    UnrolledNonMemoryCircuitType::MulDivUnsigned => (
                        mul_div_unsigned::get_circuit(binary_image),
                        mul_div_unsigned::get_table_driver(binary_image),
                    ),
                    UnrolledNonMemoryCircuitType::ShiftBinaryCsr => (
                        shift_binary_csr::get_circuit(binary_image),
                        shift_binary_csr::get_table_driver(binary_image),
                    ),
                },
                UnrolledCircuitType::Unified => (
                    unified_reduced_machine::get_circuit(binary_image),
                    unified_reduced_machine::get_table_driver(binary_image),
                ),
            },
        };
        let decoder_table = match circuit_type {
            CircuitType::Delegation(_) => None,
            CircuitType::Unrolled(circuit_type) => match circuit_type {
                InitsAndTeardowns => None,
                UnrolledCircuitType::Memory(circuit_type) => {
                    let decoder_table = match circuit_type {
                        UnrolledMemoryCircuitType::LoadStoreSubwordOnly => {
                            load_store_subword_only::get_decoder_table::<Global>(bytecode)
                        }
                        UnrolledMemoryCircuitType::LoadStoreWordOnly => {
                            load_store_word_only::get_decoder_table::<Global>(bytecode)
                        }
                    };
                    Some(decoder_table)
                }
                UnrolledCircuitType::NonMemory(circuit_type) => {
                    let decoder_table = match circuit_type {
                        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop => {
                            add_sub_lui_auipc_mop::get_decoder_table::<Global>(bytecode)
                        }
                        UnrolledNonMemoryCircuitType::JumpBranchSlt => {
                            jump_branch_slt::get_decoder_table::<Global>(bytecode)
                        }
                        UnrolledNonMemoryCircuitType::MulDiv => {
                            mul_div::get_decoder_table::<Global>(bytecode)
                        }
                        UnrolledNonMemoryCircuitType::MulDivUnsigned => {
                            mul_div_unsigned::get_decoder_table::<Global>(bytecode)
                        }
                        UnrolledNonMemoryCircuitType::ShiftBinaryCsr => {
                            shift_binary_csr::get_decoder_table::<Global>(bytecode)
                        }
                    };
                    Some(decoder_table)
                }
                UnrolledCircuitType::Unified => Some(unified_reduced_machine::get_decoder_table::<
                    Global,
                >(bytecode)),
            },
        };
        let (decoder_table, decoder_data) = if let Some((entries, data)) = decoder_table {
            let table = materialize_flattened_decoder_table(&entries);
            let data = {
                let len = data.len();
                const LOG_CHUNK_SIZE: u32 = 22; // 2^22 = 4 MB
                let size_in_bytes = len * size_of::<ExecutorFamilyDecoderData>();
                let length = size_in_bytes.next_multiple_of(1 << LOG_CHUNK_SIZE);
                let allocation =
                    HostAllocation::alloc(length, CudaHostAllocFlags::DEFAULT).unwrap();
                let allocator = ConcurrentStaticHostAllocator::new([allocation], LOG_CHUNK_SIZE);
                let mut h_data = Vec::with_capacity_in(len, allocator);
                h_data.extend(data.into_iter().map(ExecutorFamilyDecoderData::from));
                Some(Arc::new(h_data))
            };
            (table, data)
        } else {
            (vec![], None)
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
            &decoder_table,
            domain_size,
            &compiled_circuit.setup_layout,
            &worker,
        );
        Self {
            compiled_circuit: Arc::new(compiled_circuit),
            lde_precomputations: Arc::new(lde_precomputations),
            setup_trace: get_setup_trace_from_row_major_trace(&setup),
            setup_trees_and_caps: Arc::new(OnceLock::new()),
            decoder_data,
        }
    }
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

pub fn get_common_precomputations(
    worker: &Worker,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    let dummy_binary_image: Vec<u32> = vec![0; common_constants::ROM_WORD_SIZE];
    DelegationCircuitType::get_all_delegation_types()
        .into_iter()
        .copied()
        .map(|ct| CircuitType::Delegation(ct))
        .chain(once(CircuitType::Unrolled(InitsAndTeardowns)))
        .map(|ct| {
            (
                ct,
                CircuitPrecomputations::new(ct, &dummy_binary_image, &[], worker),
            )
        })
        .collect()
}
