use super::option::u8::Option;
use crate::upstream::CSExecutorFamilyDecoderData;
use common_constants::TimestampScalar;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::replay::register_u32_argument_patch;

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

/// Visible length of the request's trace buffer, which replayed graphs patch
/// into the `cycles_count` of the raw trace argument.
pub(crate) struct TraceCycles(pub u32);

// Every raw trace and oracle argument starts with `cycles_count`.
const _: () = {
    use std::mem::offset_of;
    assert!(offset_of!(UnrolledMemoryTraceRaw, cycles_count) == 0);
    assert!(offset_of!(UnrolledNonMemoryTraceRaw, cycles_count) == 0);
    assert!(offset_of!(UnrolledUnifiedTraceRaw, cycles_count) == 0);
    assert!(offset_of!(UnrolledMemoryOracle, trace) == 0);
    assert!(offset_of!(UnrolledNonMemoryOracle, trace) == 0);
    assert!(offset_of!(UnrolledUnifiedOracle, trace) == 0);
    assert!(
        offset_of!(
            super::trace_delegation::DelegationTraceRaw<u32>,
            cycles_count
        ) == 0
    );
};

/// Lets a replayed graph patch `cycles_count` in argument `arg` of the kernel
/// just launched on `stream`.
pub(crate) fn register_trace_cycles_patch(stream: &CudaStream, arg: usize) -> CudaResult<()> {
    register_u32_argument_patch(stream, arg, |inputs| inputs.get::<TraceCycles>().0)
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
#[derive(Clone, Copy)]
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
