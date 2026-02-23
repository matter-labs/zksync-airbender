use super::option::u8::Option;
use crate::prover::context::DeviceAllocation;
use crate::witness::trace::ChunkedTraceHolder;
use crate::witness::BF;
use cs::definitions::split_timestamp;
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::utils::split_u32_into_pair_u16;
use fft::GoodAllocator;
use prover::definitions::{AuxArgumentsBoundaryValues, LazyInitAndTeardown};
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};

#[repr(C)]
#[derive(Copy, Clone, Default, Debug)]
pub struct ExecutorFamilyDecoderData {
    pub imm: u32,
    pub rs1_index: u8,
    pub rs2_index: u8,
    pub rd_index: u8,
    pub rd_is_zero: bool,
    pub funct3: u8,
    pub funct7: Option<u8>,
    pub opcode_family_bits: u32,
}

impl From<cs::cs::oracle::ExecutorFamilyDecoderData> for ExecutorFamilyDecoderData {
    fn from(value: cs::cs::oracle::ExecutorFamilyDecoderData) -> Self {
        Self {
            imm: value.imm,
            rs1_index: value.rs1_index,
            rs2_index: value.rs2_index,
            rd_index: value.rd_index,
            rd_is_zero: value.rd_is_zero,
            funct3: value.funct3,
            funct7: value.funct7.into(),
            opcode_family_bits: value.opcode_family_bits,
        }
    }
}

pub struct UnrolledMemoryTraceDevice {
    pub tracing_data: DeviceAllocation<MemoryOpcodeTracingDataWithTimestamp>,
}

#[repr(C)]
pub(crate) struct UnrolledMemoryTraceRaw {
    pub cycles_count: u32,
    pub tracing_data: *const MemoryOpcodeTracingDataWithTimestamp,
}

impl From<&UnrolledMemoryTraceDevice> for UnrolledMemoryTraceRaw {
    fn from(value: &UnrolledMemoryTraceDevice) -> Self {
        Self {
            cycles_count: value.tracing_data.len() as u32,
            tracing_data: value.tracing_data.as_ptr(),
        }
    }
}

pub(crate) type UnrolledMemoryTraceHost<A> =
    ChunkedTraceHolder<MemoryOpcodeTracingDataWithTimestamp, A>;

#[repr(C)]
pub(crate) struct UnrolledMemoryOracle {
    pub trace: UnrolledMemoryTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
}

pub struct UnrolledNonMemoryTraceDevice {
    pub tracing_data: DeviceAllocation<NonMemoryOpcodeTracingDataWithTimestamp>,
}

#[repr(C)]
pub(crate) struct UnrolledNonMemoryTraceRaw {
    pub cycles_count: u32,
    pub tracing_data: *const NonMemoryOpcodeTracingDataWithTimestamp,
}

impl From<&UnrolledNonMemoryTraceDevice> for UnrolledNonMemoryTraceRaw {
    fn from(value: &UnrolledNonMemoryTraceDevice) -> Self {
        Self {
            cycles_count: value.tracing_data.len() as u32,
            tracing_data: value.tracing_data.as_ptr(),
        }
    }
}

pub(crate) type UnrolledNonMemoryTraceHost<A> =
    ChunkedTraceHolder<NonMemoryOpcodeTracingDataWithTimestamp, A>;

#[repr(C)]
pub(crate) struct UnrolledNonMemoryOracle {
    pub trace: UnrolledNonMemoryTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
    pub default_pc_value_in_padding: u32,
}

pub struct UnrolledUnifiedTraceDevice {
    pub tracing_data: DeviceAllocation<UnifiedOpcodeTracingDataWithTimestamp>,
}

#[repr(C)]
pub(crate) struct UnrolledUnifiedTraceRaw {
    pub cycles_count: u32,
    pub tracing_data: *const UnifiedOpcodeTracingDataWithTimestamp,
}

impl From<&UnrolledUnifiedTraceDevice> for UnrolledUnifiedTraceRaw {
    fn from(value: &UnrolledUnifiedTraceDevice) -> Self {
        Self {
            cycles_count: value.tracing_data.len() as u32,
            tracing_data: value.tracing_data.as_ptr(),
        }
    }
}

pub(crate) type UnrolledUnifiedTraceHost<A> =
    ChunkedTraceHolder<UnifiedOpcodeTracingDataWithTimestamp, A>;

#[repr(C)]
pub(crate) struct UnrolledUnifiedOracle {
    pub trace: UnrolledUnifiedTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
}

pub struct ShuffleRamInitsAndTeardownsDevice {
    pub inits_and_teardowns: DeviceAllocation<LazyInitAndTeardown>,
}

#[repr(C)]
#[derive(Default)]
pub(crate) struct ShuffleRamInitsAndTeardownsRaw {
    pub count: u32,
    pub inits_and_teardowns: *const LazyInitAndTeardown,
}

impl From<&ShuffleRamInitsAndTeardownsDevice> for ShuffleRamInitsAndTeardownsRaw {
    fn from(value: &ShuffleRamInitsAndTeardownsDevice) -> Self {
        Self {
            count: value.inits_and_teardowns.len() as u32,
            inits_and_teardowns: value.inits_and_teardowns.as_ptr(),
        }
    }
}

pub(crate) type ShuffleRamInitsAndTeardownsHost<A> = ChunkedTraceHolder<LazyInitAndTeardown, A>;

pub(crate) fn get_aux_arguments_boundary_values(
    compiled_circuit: &CompiledCircuitArtifact<BF>,
    inits_and_teardowns: &ShuffleRamInitsAndTeardownsHost<impl GoodAllocator>,
) -> Vec<AuxArgumentsBoundaryValues> {
    let layouts = &compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns;
    let layouts_len = layouts.len();
    assert_eq!(
        layouts_len,
        compiled_circuit.lazy_init_address_aux_vars.len()
    );
    let rows_count = compiled_circuit.trace_len - 1;
    let len = inits_and_teardowns.len();
    assert!(len <= rows_count * layouts_len);
    let padding = rows_count * layouts_len - len;
    let get_data = |index: usize| -> LazyInitAndTeardown {
        if index >= padding {
            inits_and_teardowns.get(index - padding)
        } else {
            LazyInitAndTeardown::default()
        }
    };
    let mut values = Vec::with_capacity(layouts_len);
    assert!(
        (rows_count + 1).is_power_of_two(),
        "rows_count must power of two minus one, but got {rows_count}"
    );
    for i in 0..layouts_len {
        // Lazy init data is laid out in contiguous columns of `rows_count` elements.
        let LazyInitAndTeardown {
            address: lazy_init_address_first_row,
            teardown_value: lazy_teardown_value_first_row,
            teardown_timestamp: lazy_teardown_timestamp_first_row,
        } = get_data(rows_count * i);

        let LazyInitAndTeardown {
            address: lazy_init_address_one_before_last_row,
            teardown_value: lazy_teardown_value_one_before_last_row,
            teardown_timestamp: lazy_teardown_timestamp_one_before_last_row,
        } = get_data((rows_count * (i + 1)) - 1);

        let (lazy_init_address_first_row_low, lazy_init_address_first_row_high) =
            split_u32_into_pair_u16(lazy_init_address_first_row);
        let (teardown_value_first_row_low, teardown_value_first_row_high) =
            split_u32_into_pair_u16(lazy_teardown_value_first_row);
        let (teardown_timestamp_first_row_low, teardown_timestamp_first_row_high) =
            split_timestamp(lazy_teardown_timestamp_first_row.as_scalar());

        let (lazy_init_address_one_before_last_row_low, lazy_init_address_one_before_last_row_high) =
            split_u32_into_pair_u16(lazy_init_address_one_before_last_row);
        let (teardown_value_one_before_last_row_low, teardown_value_one_before_last_row_high) =
            split_u32_into_pair_u16(lazy_teardown_value_one_before_last_row);
        let (
            teardown_timestamp_one_before_last_row_low,
            teardown_timestamp_one_before_last_row_high,
        ) = split_timestamp(lazy_teardown_timestamp_one_before_last_row.as_scalar());

        let aux_value = AuxArgumentsBoundaryValues {
            lazy_init_first_row: [
                BF::new(lazy_init_address_first_row_low as u32),
                BF::new(lazy_init_address_first_row_high as u32),
            ],
            teardown_value_first_row: [
                BF::new(teardown_value_first_row_low as u32),
                BF::new(teardown_value_first_row_high as u32),
            ],
            teardown_timestamp_first_row: [
                BF::new(teardown_timestamp_first_row_low),
                BF::new(teardown_timestamp_first_row_high),
            ],
            lazy_init_one_before_last_row: [
                BF::new(lazy_init_address_one_before_last_row_low as u32),
                BF::new(lazy_init_address_one_before_last_row_high as u32),
            ],
            teardown_value_one_before_last_row: [
                BF::new(teardown_value_one_before_last_row_low as u32),
                BF::new(teardown_value_one_before_last_row_high as u32),
            ],
            teardown_timestamp_one_before_last_row: [
                BF::new(teardown_timestamp_one_before_last_row_low),
                BF::new(teardown_timestamp_one_before_last_row_high),
            ],
        };
        values.push(aux_value);
    }

    values
}

#[cfg(test)]
mod tests {
    use super::{get_aux_arguments_boundary_values, ShuffleRamInitsAndTeardownsHost, BF};
    use cs::definitions::TimestampData;
    use field::PrimeField;
    use prover::definitions::LazyInitAndTeardown;
    use std::alloc::Global;
    use std::sync::Arc;

    fn decode_u32_from_u16_limbs(src: [BF; 2]) -> u32 {
        let low = u16::try_from(src[0].as_u64_reduced()).unwrap() as u32;
        let high = u16::try_from(src[1].as_u64_reduced()).unwrap() as u32;

        low + (high << 16)
    }

    fn make_address(set_idx: usize, row_idx: usize) -> u32 {
        0x1000_0000 + ((set_idx as u32) << 16) + (row_idx as u32) * 4
    }

    #[test]
    fn aux_boundary_values_use_full_column_stride_for_first_row_values() {
        const TRACE_LEN_LOG2: usize = (cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS as usize) + 1;
        const NUM_INIT_AND_TEARDOWN_SETS: usize = 2;
        let rows_count = (1usize << TRACE_LEN_LOG2) - 1;

        let compiler = cs::one_row_compiler::OneRowCompiler::<BF>::default();
        let compiled_circuit =
            compiler.compile_init_and_teardown_circuit(NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2);

        let mut chunk = Vec::with_capacity_in(rows_count * NUM_INIT_AND_TEARDOWN_SETS, Global);
        for set_idx in 0..NUM_INIT_AND_TEARDOWN_SETS {
            for row_idx in 0..rows_count {
                chunk.push(LazyInitAndTeardown {
                    address: make_address(set_idx, row_idx),
                    teardown_value: ((set_idx as u32) << 20) | (row_idx as u32),
                    teardown_timestamp: TimestampData::from_scalar(
                        ((set_idx as u64) << 32) | (row_idx as u64),
                    ),
                });
            }
        }

        let inits_and_teardowns = ShuffleRamInitsAndTeardownsHost {
            chunks: vec![Arc::new(chunk)],
        };

        let aux_boundary_values =
            get_aux_arguments_boundary_values(&compiled_circuit, &inits_and_teardowns);
        assert_eq!(aux_boundary_values.len(), NUM_INIT_AND_TEARDOWN_SETS);

        for (set_idx, aux) in aux_boundary_values.iter().enumerate() {
            let expected_first_row_address = make_address(set_idx, 0);
            let expected_last_row_address = make_address(set_idx, rows_count - 1);

            let actual_first_row_address = decode_u32_from_u16_limbs(aux.lazy_init_first_row);
            let actual_last_row_address =
                decode_u32_from_u16_limbs(aux.lazy_init_one_before_last_row);

            assert_eq!(
                actual_first_row_address, expected_first_row_address,
                "first-row address mismatch for init/teardown set {set_idx}"
            );
            assert_eq!(
                actual_last_row_address, expected_last_row_address,
                "one-before-last-row address mismatch for init/teardown set {set_idx}"
            );
        }
    }
}
