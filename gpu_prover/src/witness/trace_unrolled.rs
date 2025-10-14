use super::option::u8::Option;
use crate::prover::context::DeviceAllocation;
use era_cudart::slice::CudaSlice;
use fft::GoodAllocator;
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use prover::tracers::unrolled::tracer::{MemTracingFamilyChunk, NonMemTracingFamilyChunk};
use std::sync::Arc;

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
    pub opcode_family_bits: u8,
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
    pub cycles_count: usize,
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

#[derive(Clone)]
pub struct UnrolledMemoryTraceHost<A: GoodAllocator> {
    pub cycles_count: usize,
    pub tracing_data: Arc<Vec<MemoryOpcodeTracingDataWithTimestamp, A>>,
}

impl<A: GoodAllocator> From<MemTracingFamilyChunk<A>> for UnrolledMemoryTraceHost<A> {
    fn from(value: MemTracingFamilyChunk<A>) -> Self {
        Self {
            cycles_count: value.num_cycles,
            tracing_data: Arc::new(value.data),
        }
    }
}

#[repr(C)]
pub(crate) struct UnrolledMemoryOracle {
    pub trace: UnrolledMemoryTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
}

pub struct UnrolledNonMemoryTraceDevice {
    pub cycles_count: usize,
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

#[derive(Clone)]
pub struct UnrolledNonMemoryTraceHost<A: GoodAllocator> {
    pub cycles_count: usize,
    pub tracing_data: Arc<Vec<NonMemoryOpcodeTracingDataWithTimestamp, A>>,
}

impl<A: GoodAllocator> From<NonMemTracingFamilyChunk<A>> for UnrolledNonMemoryTraceHost<A> {
    fn from(value: NonMemTracingFamilyChunk<A>) -> Self {
        Self {
            cycles_count: value.num_cycles,
            tracing_data: Arc::new(value.data),
        }
    }
}

#[repr(C)]
pub(crate) struct UnrolledNonMemoryOracle {
    pub trace: UnrolledNonMemoryTraceRaw,
    pub decoder_table: *const ExecutorFamilyDecoderData,
    pub default_pc_value_in_padding: u32,
}
