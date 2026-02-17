use crate::vm::*;
use common_constants::*;
use std::alloc::Allocator;
use std::collections::HashSet;
use std::ptr::NonNull;
use std::{mem::offset_of, ptr::addr_of_mut};

#[cfg(target_pointer_width = "64")]
mod delegations;
#[cfg(target_pointer_width = "64")]
pub mod minimal_tracer;
#[cfg(target_pointer_width = "64")]
pub mod structs;

#[cfg(target_pointer_width = "64")]
pub use self::delegations::*;
#[cfg(target_pointer_width = "64")]
pub use self::structs::*;

#[cfg(all(target_arch = "x86_64", feature = "jit"))]
mod impls;

#[cfg(all(target_arch = "x86_64", feature = "jit"))]
pub use self::impls::*;

#[cfg(all(target_arch = "x86_64", feature = "jit", test))]
mod tests;

const MAX_RAM_SIZE: usize = 1 << 30; // 1 Gb, as we want to avoid having separate pointers to RAM (that we want to have continuous to perform very simple read/writes), and timestamp bookkeping space

pub const RAM_SIZE: usize = 1 << 30;
const NUM_RAM_WORDS: usize = RAM_SIZE / core::mem::size_of::<u32>();

// We will measure trace chunk in a number of memory accesses and not in a almost fixed number of cycles that did pass between them.
// At most we extend a chunk by the number of accesses in delegation
pub const TRACE_CHUNK_LEN: usize = 1 << 20;
pub const MAX_TRACE_CHUNK_LEN: usize = const {
    let mut max = core::cmp::max(24 + 16, 31 * 2);
    max = core::cmp::max(max, 8 + 8 + 1);

    TRACE_CHUNK_LEN + max
};

pub const MAX_NUM_COUNTERS: usize = 16;

#[repr(u8)]
pub enum CounterType {
    AddSubLui = 0,
    BranchSlt,
    ShiftBinaryCsr,
    MulDiv,
    MemWord,
    MemSubword,
    BlakeDelegation,
    BigintDelegation,
    KeccakDelegation,
    FormalEnd, // must always be the last
}

const _: () = const {
    assert!(CounterType::FormalEnd as u8 as usize <= MAX_NUM_COUNTERS);
};

#[repr(C, align(16))]
#[derive(Debug, Clone, Copy)]
pub struct MachineState {
    pub registers: [u32; 32], // aligned at 16, so we can write XMMs directly into the stack
    pub register_timestamps: [TimestampScalar; 32],
    pub counters: [u64; MAX_NUM_COUNTERS],
    pub pc: u32,
    pub timestamp: TimestampScalar,
    pub(crate) context_ptr: *mut (),
}

impl MachineState {
    const SIZE: usize = core::mem::size_of::<Self>();
    const _T: () = const {
        assert!(Self::SIZE % core::mem::size_of::<u64>() == 0);
        assert!(Self::SIZE % 16 == 0); // so our stack is aligned if we just grow it by this structure size
    };

    const SIZE_IN_QWORDS: usize = Self::SIZE / core::mem::size_of::<u64>();
    const REGISTER_TIMESTAMPS_OFFSET: usize = offset_of!(Self, register_timestamps);
    const COUNTERS_OFFSET: usize = offset_of!(Self, counters);
    const PC_OFFSET: usize = offset_of!(Self, pc);
    const TIMESTAMP_OFFSET: usize = offset_of!(Self, timestamp);
    const CONTEXT_PTR_OFFSET: usize = offset_of!(Self, context_ptr);

    pub fn initial() -> Self {
        Self {
            registers: [0; 32],
            register_timestamps: [0; 32],
            counters: [0; MAX_NUM_COUNTERS],
            pc: 0,
            timestamp: INITIAL_TIMESTAMP,
            context_ptr: core::ptr::dangling_mut(),
        }
    }

    pub fn as_replayer_state(&self) -> State<DelegationsAndFamiliesCounters> {
        State {
            registers: std::array::from_fn(|i| Register {
                timestamp: self.register_timestamps[i],
                value: self.registers[i],
            }),
            timestamp: self.timestamp,
            pc: self.pc,
            counters: DelegationsAndFamiliesCounters {
                add_sub_family: self.counters[CounterType::AddSubLui as u8 as usize] as usize,
                slt_branch_family: self.counters[CounterType::BranchSlt as u8 as usize] as usize,
                binary_shift_csr_family: self.counters[CounterType::ShiftBinaryCsr as u8 as usize]
                    as usize,
                mul_div_family: self.counters[CounterType::MulDiv as u8 as usize] as usize,

                word_size_mem_family: self.counters[CounterType::MemWord as u8 as usize] as usize,
                subword_size_mem_family: self.counters[CounterType::MemSubword as u8 as usize]
                    as usize,

                blake_calls: self.counters[CounterType::BlakeDelegation as u8 as usize] as usize,
                bigint_calls: self.counters[CounterType::BigintDelegation as u8 as usize] as usize,
                keccak_calls: self.counters[CounterType::KeccakDelegation as u8 as usize] as usize,
            },
        }
    }
}

#[repr(C, align(8))]
#[derive(Debug)]
pub struct TraceChunk {
    pub values: [u32; MAX_TRACE_CHUNK_LEN],
    pub timestamps: [TimestampScalar; MAX_TRACE_CHUNK_LEN],
    pub len: u64,
}

pub trait ContextImpl {
    fn read_nondeterminism(&mut self) -> u32;

    fn write_nondeterminism(&mut self, value: u32, memory: &[u32; RAM_SIZE]);

    fn receive_trace(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) -> NonNull<TraceChunk>;

    fn receive_final_trace_piece(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    );

    fn take_final_state(&mut self) -> Option<MachineState>;
    fn final_state_ref(&'_ self) -> Option<&'_ MachineState>;
}
