use crate::cs::cs::cs_reference::BasicAssembly;
use crate::unrolled::{MemoryCircuitOracle, NonMemoryCircuitOracle};
use ::field::*;
use cs::cs::circuit::Circuit;
use cs::cs::oracle::ExecutorFamilyDecoderData;
use cs::definitions::TimestampData;
use cs::machine::ops::unrolled::decoder::process_binary_into_separate_tables_ext;
use riscv_transpiler::machine_mode_only_unrolled::*;
use std::alloc::Global;

pub struct NonMemTestCase {
    pub label: &'static str,
    pub rs1: u32,
    pub rs2: u32,
    pub rd: u32,
}

/// Extract the final register state from the circuit's shuffle RAM queries.
///
/// Iterates over all shuffle RAM queries and collects the write value for each
/// register access.  For read-only accesses the write value equals the read
/// value, so the last write to each register index wins — which is the final
/// value the circuit committed to.
pub fn extract_circuit_registers(cs: &BasicAssembly<Mersenne31Field>) -> [u32; 32] {
    let mut registers = [0u32; 32];
    for query in &cs.shuffle_ram_queries {
        if let Some(id) = query.query_type.get_register_id(cs) {
            registers[id as usize] = query.get_write_value(cs);
        }
    }
    registers
}

/// Run a single opcode through the circuit, check constraint satisfaction,
/// and return the circuit's final register state.
pub fn run_non_mem_circuit_test(
    decoder_data: &[ExecutorFamilyDecoderData],
    table_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    circuit_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    case: &NonMemTestCase,
) -> [u32; 32] {
    let trace_data = make_trace_data(case);

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
        default_pc_value_in_padding: 4,
    };

    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );

    table_fn(&mut cs);
    circuit_fn(&mut cs);

    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );

    extract_circuit_registers(&cs)
}

pub fn make_trace_data_with_pc(
    case: &NonMemTestCase,
    initial_pc: u32,
    new_pc: u32,
) -> Vec<NonMemoryOpcodeTracingDataWithTimestamp> {
    vec![NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc,
            rs1_value: case.rs1,
            rs2_value: case.rs2,
            rd_old_value: 0,
            rd_value: case.rd,
            new_pc,
            delegation_type: 0,
        },
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_read_timestamp: TimestampData::from_scalar(0),
        rd_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }]
}

fn make_trace_data(case: &NonMemTestCase) -> Vec<NonMemoryOpcodeTracingDataWithTimestamp> {
    vec![NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: case.rs1,
            rs2_value: case.rs2,
            rd_old_value: 0,
            rd_value: case.rd,
            new_pc: 4,
            delegation_type: 0,
        },
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_read_timestamp: TimestampData::from_scalar(0),
        rd_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }]
}

/// Prepare decoder data for a single instruction encoding within a given family.
pub fn prepare_decoder_data(
    encoding: u32,
    decoder: Box<dyn cs::machine::ops::unrolled::decoder::OpcodeFamilyDecoder>,
    family_idx: u8,
    supported_csrs: &[u16],
) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data_at_pc(encoding, 0, decoder, family_idx, supported_csrs)
}

/// Prepare decoder data with the encoding placed at the slot corresponding to
/// `initial_pc` (PC must be word-aligned). The bytecode buffer is sized so
/// that the oracle's `decoder_table[pc / 4]` lookup hits the encoding for the
/// requested PC; all other slots decode as no-op padding.
pub fn prepare_decoder_data_at_pc(
    encoding: u32,
    initial_pc: u32,
    decoder: Box<dyn cs::machine::ops::unrolled::decoder::OpcodeFamilyDecoder>,
    family_idx: u8,
    supported_csrs: &[u16],
) -> Vec<ExecutorFamilyDecoderData> {
    assert!(initial_pc % 4 == 0, "initial_pc must be word-aligned");
    let pc_word_idx = (initial_pc as usize) / 4;
    let bytecode_size = std::cmp::max((pc_word_idx + 1).next_power_of_two(), 1 << 10);
    let mut bytecode = vec![0u32; pc_word_idx + 1];
    bytecode[pc_word_idx] = encoding;
    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[decoder],
        bytecode_size,
        supported_csrs,
    );
    let (_, decoder_data) = t.remove(&family_idx).expect("decoder data");
    decoder_data
}

/// Variant for circuits where padding rows need pc=0 (e.g. jump/branch/SLT).
pub fn run_non_mem_circuit_test_with_pc_padding(
    decoder_data: &[ExecutorFamilyDecoderData],
    table_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    circuit_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    case: &NonMemTestCase,
    default_pc_value_in_padding: u32,
) -> [u32; 32] {
    let trace_data = make_trace_data(case);

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
        default_pc_value_in_padding,
    };

    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );

    table_fn(&mut cs);
    circuit_fn(&mut cs);

    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );

    extract_circuit_registers(&cs)
}

/// Test case for memory (load/store) circuits.
pub struct MemTestCase {
    pub label: &'static str,
    pub data: MemoryOpcodeTracingDataWithTimestamp,
}

#[cfg(test)]
mod add_sub;
#[cfg(test)]
mod compliance_vectors;
#[cfg(test)]
mod decoder_negative;
#[cfg(test)]
mod encoding;
#[cfg(test)]
mod jump_branch;
#[cfg(test)]
mod load_store;
#[cfg(test)]
mod load_store_subword;
#[cfg(test)]
mod mul_div;
#[cfg(test)]
mod shift_binop;
