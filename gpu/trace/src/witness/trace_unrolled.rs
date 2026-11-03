use super::option::u8::Option;
use crate::upstream::CSExecutorFamilyDecoderData;
use common_constants::TimestampScalar;
use gpu_core::primitives::context::DeviceAllocation;

use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};

pub use execution_prover_model::trace::{InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2};

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

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
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

#[repr(C)]
pub(crate) struct UnrolledMemoryOracle {
    pub trace: UnrolledMemoryTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
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

#[repr(C)]
pub(crate) struct UnrolledNonMemoryOracle {
    pub trace: UnrolledNonMemoryTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
    pub default_pc_value_in_padding: u32,
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
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

#[repr(C)]
pub(crate) struct UnrolledUnifiedOracle {
    pub trace: UnrolledUnifiedTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
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
