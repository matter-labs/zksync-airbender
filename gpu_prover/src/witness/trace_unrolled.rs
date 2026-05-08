use super::option::u8::Option;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::static_host::StaticPinnedBox;
use crate::witness::trace::ChunkedTraceHolder;
use common_constants::TimestampScalar;
use cs::gkr_circuits::ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use std::sync::Arc;

/// Page size for the inits-and-teardowns trace transfer, in `log2(words)`.
///
/// Each touched page ships `1 << PAGE_SIZE_LOG2` `u32` values plus
/// `1 << PAGE_SIZE_LOG2` `u64` timestamps. Producer / kernel both rely on
/// this value as the contract.
pub const PAGE_SIZE_LOG2: u32 = 10;

#[repr(C)]
#[derive(Copy, Clone, Default, Debug)]
pub struct ExecutorFamilyDecoderData {
    pub imm: u32,
    pub rs1_index: u8,
    pub rs2_index: u16,
    pub rd_index: u8,
    pub rd_is_zero: bool,
    pub funct3: u8,
    pub funct7: Option<u8>,
    pub opcode_family_bits: u32,
}

impl From<CSExecutorFamilyDecoderData> for ExecutorFamilyDecoderData {
    fn from(value: CSExecutorFamilyDecoderData) -> Self {
        Self {
            imm: value.imm,
            rs1_index: value.rs1_index,
            rs2_index: value.rs2_index,
            rd_index: value.rd_index,
            rd_is_zero: value.rd_index == 0,
            funct3: value.funct3.unwrap_or_default(),
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

pub struct InitsAndTeardownsTraceDevice {
    pub page_indices: DeviceAllocation<u32>,
    pub values_packed: DeviceAllocation<u32>,
    pub timestamps_packed: DeviceAllocation<TimestampScalar>,
}

#[repr(C)]
pub(crate) struct InitsAndTeardownsTraceRaw {
    pub num_pages: u32,
    pub page_indices: *const u32,
    pub values_packed: *const u32,
    pub timestamps_packed: *const TimestampScalar,
}

impl From<&InitsAndTeardownsTraceDevice> for InitsAndTeardownsTraceRaw {
    fn from(value: &InitsAndTeardownsTraceDevice) -> Self {
        let num_pages = value.page_indices.len();
        debug_assert_eq!(value.values_packed.len(), num_pages << PAGE_SIZE_LOG2);
        debug_assert_eq!(value.timestamps_packed.len(), num_pages << PAGE_SIZE_LOG2);
        Self {
            num_pages: num_pages as u32,
            page_indices: value.page_indices.as_ptr(),
            values_packed: value.values_packed.as_ptr(),
            timestamps_packed: value.timestamps_packed.as_ptr(),
        }
    }
}

pub(crate) struct InitsAndTeardownsTraceHost {
    pub page_indices: Arc<StaticPinnedBox<u32>>,
    pub values_packed: Arc<StaticPinnedBox<u32>>,
    pub timestamps_packed: Arc<StaticPinnedBox<TimestampScalar>>,
}

// pub(crate) fn get_aux_arguments_boundary_values(
//     compiled_circuit: &CompiledCircuitArtifact<BF>,
//     inits_and_teardowns: &ShuffleRamInitsAndTeardownsHost<impl GoodAllocator>,
// ) -> Vec<AuxArgumentsBoundaryValues> {
//     let layouts = &compiled_circuit
//         .memory_layout
//         .shuffle_ram_inits_and_teardowns;
//     let layouts_len = layouts.len();
//     assert_eq!(
//         layouts_len,
//         compiled_circuit.lazy_init_address_aux_vars.len()
//     );
//     let rows_count = compiled_circuit.trace_len - 1;
//     let len = inits_and_teardowns.len();
//     assert!(len <= rows_count * layouts_len);
//     let padding = rows_count * layouts_len - len;
//     let get_data = |index: usize| -> LazyInitAndTeardown {
//         if index >= padding {
//             inits_and_teardowns.get(index - padding)
//         } else {
//             LazyInitAndTeardown::default()
//         }
//     };
//     let mut values = Vec::with_capacity(layouts_len);
//     for i in 0..layouts_len {
//         let LazyInitAndTeardown {
//             address: lazy_init_address_first_row,
//             teardown_value: lazy_teardown_value_first_row,
//             teardown_timestamp: lazy_teardown_timestamp_first_row,
//         } = get_data((rows_count - 1) * i);
//
//         let LazyInitAndTeardown {
//             address: lazy_init_address_one_before_last_row,
//             teardown_value: lazy_teardown_value_one_before_last_row,
//             teardown_timestamp: lazy_teardown_timestamp_one_before_last_row,
//         } = get_data((rows_count * (i + 1)) - 1);
//
//         let (lazy_init_address_first_row_low, lazy_init_address_first_row_high) =
//             split_u32_into_pair_u16(lazy_init_address_first_row);
//         let (teardown_value_first_row_low, teardown_value_first_row_high) =
//             split_u32_into_pair_u16(lazy_teardown_value_first_row);
//         let (teardown_timestamp_first_row_low, teardown_timestamp_first_row_high) =
//             split_timestamp(lazy_teardown_timestamp_first_row.as_scalar());
//
//         let (lazy_init_address_one_before_last_row_low, lazy_init_address_one_before_last_row_high) =
//             split_u32_into_pair_u16(lazy_init_address_one_before_last_row);
//         let (teardown_value_one_before_last_row_low, teardown_value_one_before_last_row_high) =
//             split_u32_into_pair_u16(lazy_teardown_value_one_before_last_row);
//         let (
//             teardown_timestamp_one_before_last_row_low,
//             teardown_timestamp_one_before_last_row_high,
//         ) = split_timestamp(lazy_teardown_timestamp_one_before_last_row.as_scalar());
//
//         let aux_value = AuxArgumentsBoundaryValues {
//             lazy_init_first_row: [
//                 BF::new(lazy_init_address_first_row_low as u32),
//                 BF::new(lazy_init_address_first_row_high as u32),
//             ],
//             teardown_value_first_row: [
//                 BF::new(teardown_value_first_row_low as u32),
//                 BF::new(teardown_value_first_row_high as u32),
//             ],
//             teardown_timestamp_first_row: [
//                 BF::new(teardown_timestamp_first_row_low),
//                 BF::new(teardown_timestamp_first_row_high),
//             ],
//             lazy_init_one_before_last_row: [
//                 BF::new(lazy_init_address_one_before_last_row_low as u32),
//                 BF::new(lazy_init_address_one_before_last_row_high as u32),
//             ],
//             teardown_value_one_before_last_row: [
//                 BF::new(teardown_value_one_before_last_row_low as u32),
//                 BF::new(teardown_value_one_before_last_row_high as u32),
//             ],
//             teardown_timestamp_one_before_last_row: [
//                 BF::new(teardown_timestamp_one_before_last_row_low),
//                 BF::new(teardown_timestamp_one_before_last_row_high),
//             ],
//         };
//         values.push(aux_value);
//     }
//
//     values
// }
