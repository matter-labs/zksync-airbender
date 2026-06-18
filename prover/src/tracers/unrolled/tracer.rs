use crate::fft::GoodAllocator;
use riscv_transpiler::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use std::alloc::Global;

// These chunk containers are the remaining live part of the old tracer module.
// The current transpiler/replayer path still uses them as the canonical schema
// for unrolled witness buffers and setup factories.

#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct NonMemTracingFamilyChunk<A: GoodAllocator = Global> {
    pub num_cycles: usize,
    #[serde(bound(
        deserialize = "Vec<NonMemoryOpcodeTracingDataWithTimestamp, A>: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "Vec<NonMemoryOpcodeTracingDataWithTimestamp, A>: serde::Serialize"
    ))]
    pub data: Vec<NonMemoryOpcodeTracingDataWithTimestamp, A>,
}

impl<A: GoodAllocator> NonMemTracingFamilyChunk<A> {
    pub fn new_for_num_cycles(num_cycles: usize) -> Self {
        let capacity = num_cycles + 1;
        assert!(capacity.is_power_of_two());

        Self {
            num_cycles,
            data: Vec::with_capacity_in(capacity, A::default()),
        }
    }

    pub fn realloc_to_global(&self) -> NonMemTracingFamilyChunk<Global> {
        NonMemTracingFamilyChunk {
            num_cycles: self.num_cycles,
            data: self.data[..].to_vec(),
        }
    }
}

#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct MemTracingFamilyChunk<A: GoodAllocator = Global> {
    pub num_cycles: usize,
    #[serde(bound(
        deserialize = "Vec<MemoryOpcodeTracingDataWithTimestamp, A>: serde::Deserialize<'de>"
    ))]
    #[serde(bound(serialize = "Vec<MemoryOpcodeTracingDataWithTimestamp, A>: serde::Serialize"))]
    pub data: Vec<MemoryOpcodeTracingDataWithTimestamp, A>,
}

impl<A: GoodAllocator> MemTracingFamilyChunk<A> {
    pub fn new_for_num_cycles(num_cycles: usize) -> Self {
        let capacity = num_cycles + 1;
        assert!(capacity.is_power_of_two());

        Self {
            num_cycles,
            data: Vec::with_capacity_in(capacity, A::default()),
        }
    }

    pub fn realloc_to_global(&self) -> MemTracingFamilyChunk<Global> {
        MemTracingFamilyChunk {
            num_cycles: self.num_cycles,
            data: self.data[..].to_vec(),
        }
    }
}
