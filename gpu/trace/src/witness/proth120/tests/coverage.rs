use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;

pub(super) const SYNTHETIC_RAM_VALUE: u32 = 0x12345678;
pub(super) const SYNTHETIC_TIMESTAMP: u64 = (1 << 19) + 4;
pub(super) const SYNTHETIC_ADDMOD_X: u32 = u32::MAX;
pub(super) const SYNTHETIC_ADDMOD_Y: u32 = u32::MAX;
pub(super) const SYNTHETIC_DELEGATION_FAMILY: u32 = 1 << 7;

/// Compute selector coverage from the same live CPU witness used for GPU parity.
pub(super) fn validate_live(
    circuit: &GKRCircuitArtifact<Proth120>,
    memory: &[Vec<Proth120>],
    witness: &[Vec<Proth120>],
) {
    let execute = circuit
        .memory_layout
        .machine_state
        .as_ref()
        .unwrap()
        .execute;
    let active_rows = memory[execute]
        .iter()
        .filter(|&&value| value != Proth120::new(0))
        .count();
    for address in &circuit
        .memory_layout
        .decoder_input
        .as_ref()
        .unwrap()
        .circuit_family_mask_bits
    {
        let column = match *address {
            GKRAddress::BaseLayerMemory(column) => &memory[column],
            GKRAddress::BaseLayerWitness(column) => &witness[column],
            _ => panic!("selector is not a base-layer column"),
        };
        assert_eq!(column.len(), circuit.trace_len);
        assert!(
            column
                .iter()
                .filter(|&&value| value != Proth120::new(0))
                .count()
                <= active_rows,
            "selector active outside executed rows: {address:?}"
        );
    }
}

pub(super) fn synthetic_rows() -> (
    Vec<riscv_transpiler::witness::UnifiedOpcodeTracingDataWithTimestamp>,
    Vec<Option<cs::gkr_circuits::decoder_trait::ExecutorFamilyDecoderData>>,
    execution_prover_model::trace::InitsAndTeardownsTraceHost<
        execution_prover_model::allocator::CpuTraceAllocator,
    >,
) {
    use common_constants::TimestampData;
    use cs::gkr_circuits::decoder_trait::ExecutorFamilyDecoderData;
    use execution_prover_model::allocator::CpuTraceAllocator;
    use execution_prover_model::trace::{
        ChunkedTraceHolder, InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2,
    };
    use riscv_transpiler::witness::{
        NonMemoryOpcodeTracingData, NonMemoryOpcodeTracingDataWithTimestamp,
        UnifiedOpcodeTracingDataWithTimestamp,
    };
    use std::sync::Arc;
    fn chunk<T: Copy>(values: &[T]) -> ChunkedTraceHolder<T, CpuTraceAllocator> {
        let mut data = Vec::with_capacity_in(
            values.len(),
            CpuTraceAllocator::new(std::mem::size_of_val(values)),
        );
        data.extend_from_slice(values);
        ChunkedTraceHolder {
            chunks: vec![Arc::new(data)],
        }
    }
    let rows = vec![
        UnifiedOpcodeTracingDataWithTimestamp::NonMem(NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: 0,
                new_pc: 4,
                rs1_value: SYNTHETIC_ADDMOD_X,
                rs2_value: SYNTHETIC_ADDMOD_Y,
                rd_value: 536870906,
                ..Default::default()
            },
            cycle_timestamp: TimestampData::from_scalar(4),
            ..Default::default()
        }),
        UnifiedOpcodeTracingDataWithTimestamp::NonMem(NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: 4,
                new_pc: 8,
                ..Default::default()
            },
            cycle_timestamp: TimestampData::from_scalar(8),
            ..Default::default()
        }),
    ];
    let decoder = vec![
        Some(ExecutorFamilyDecoderData {
            rs1_index: 1,
            rs2_index: 2,
            rd_index: 3,
            opcode_family_bits: 1 << 3,
            funct3: Some(0),
            ..Default::default()
        }),
        Some(ExecutorFamilyDecoderData {
            rs1_index: 1,
            opcode_family_bits: SYNTHETIC_DELEGATION_FAMILY,
            funct3: Some(0),
            ..Default::default()
        }),
    ];
    let page_rows = 1 << PAGE_SIZE_LOG2;
    let inits = InitsAndTeardownsTraceHost {
        page_indices: chunk(&[0]),
        values_packed: chunk(&vec![SYNTHETIC_RAM_VALUE; page_rows]),
        timestamps_packed: chunk(&vec![SYNTHETIC_TIMESTAMP; page_rows]),
        top_bits: vec![0, 1],
    };
    (rows, decoder, inits)
}

pub(super) fn standalone_columns(
    circuit: &GKRCircuitArtifact<Proth120>,
) -> (Vec<usize>, Vec<usize>) {
    use std::collections::BTreeSet;
    let decoder = circuit
        .memory_layout
        .decoder_input
        .as_ref()
        .expect("Proth120 standalone decoder");
    let mut fixed = BTreeSet::new();
    for address in [decoder.rs2_index, decoder.rd_index]
        .into_iter()
        .chain(decoder.circuit_family_mask_bits.iter().copied())
        .chain(
            circuit
                .aux_layout_data
                .shuffle_ram_timestamp_comparison_aux_vars
                .iter()
                .flatten()
                .map(|set| set.intermediate_borrow),
        )
    {
        if let GKRAddress::BaseLayerWitness(column) = address {
            fixed.insert(column);
        }
    }
    if !decoder.decoder_witness_is_in_memory {
        fixed.extend(decoder.imm);
        fixed.extend(decoder.funct3);
    }
    let source = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120/generated/witness_generation_fn.cuh"));
    let mut generated = BTreeSet::new();
    for line in source.lines().filter(|line| {
        line.starts_with("SET_WITNESS_PLACE(") || line.starts_with("SET_WITNESS_PLACE_OR_ZERO(")
    }) {
        let column = line
            .split_once('(')
            .unwrap()
            .1
            .split_once(',')
            .unwrap()
            .0
            .parse::<usize>()
            .expect("Proth120 standalone SSA target");
        assert!(
            column
                < circuit
                    .witness_layout
                    .multiplicities_columns_for_range_check_16
                    .start,
            "Proth120 standalone SSA multiplicity target"
        );
        generated.insert(column);
    }
    assert!(!generated.is_empty(), "Proth120 standalone SSA targets");
    assert!(
        fixed.is_disjoint(&generated),
        "Proth120 standalone fixed inputs are not SSA targets"
    );
    (fixed.into_iter().collect(), generated.into_iter().collect())
}
