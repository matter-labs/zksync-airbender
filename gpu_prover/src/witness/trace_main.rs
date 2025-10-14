use crate::prover::context::DeviceAllocation;
use era_cudart::slice::CudaSlice;
use fft::GoodAllocator;
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::main_cycle_optimized::{CycleData, SingleCycleTracingData};
use std::sync::Arc;

pub struct MainTraceDevice {
    pub(crate) cycle_data: DeviceAllocation<SingleCycleTracingData>,
}

#[repr(C)]
pub(crate) struct MainTraceRaw {
    cycle_data: *const SingleCycleTracingData,
}

impl From<&MainTraceDevice> for MainTraceRaw {
    fn from(value: &MainTraceDevice) -> Self {
        Self {
            cycle_data: value.cycle_data.as_ptr(),
        }
    }
}

#[derive(Clone)]
pub struct MainTraceHost<A: GoodAllocator> {
    pub cycles_traced: usize,
    pub cycle_data: Arc<Vec<SingleCycleTracingData, A>>,
    pub num_cycles_chunk_size: usize,
}

impl<M: MachineConfig, A: GoodAllocator> From<CycleData<M, A>> for MainTraceHost<A> {
    fn from(value: CycleData<M, A>) -> Self {
        Self {
            cycles_traced: value.cycles_traced,
            cycle_data: Arc::new(value.per_cycle_data),
            num_cycles_chunk_size: value.num_cycles_chunk_size,
        }
    }
}
