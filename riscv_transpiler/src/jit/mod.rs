use crate::vm::*;
use common_constants::*;
use std::alloc::Allocator;
use std::collections::HashSet;
use std::mem::offset_of;
use std::ptr::NonNull;

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

pub const RAM_SIZE: usize = 1 << 30;
const NUM_RAM_WORDS: usize = RAM_SIZE / core::mem::size_of::<u32>();

// Keep the RAM backing store type named so rustdoc does not have to normalize the
// large inline `[u32; RAM_SIZE]` array at every public trait boundary.
pub type RamImage = [u32; RAM_SIZE];

// We will measure trace chunk in a number of memory accesses and not in a almost fixed number of cycles that did pass between them.
// At most we extend a chunk by the number of accesses in delegation
pub const TRACE_CHUNK_LEN: usize = 1 << 20;
pub const MAX_TRACE_CHUNK_LEN: usize = const {
    let mut max = core::cmp::max(24 + 16, 31 * 2); // blake round function or keccak
    max = core::cmp::max(max, 8 + 8 + 1); // bigint
    max = core::cmp::max(max, 16 + 16); // blake g function

    TRACE_CHUNK_LEN + max
};

pub const MAX_NUM_COUNTERS: usize = 16;

// Circuit-family counters. These are kept live in vector registers (xmm8..=xmm12)
// during JITted execution and spilled to / reloaded from this array with aligned
// 128-bit moves (movdqa). The explicit `align(16)` guarantees this array's address
// is 16-byte aligned regardless of surrounding `MachineState` layout changes, which
// is required for the aligned vector spill to be correct (an unaligned movdqa #GPs).
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineCounters {
    pub values: [u64; MAX_NUM_COUNTERS],
}

impl MachineCounters {
    pub const fn new() -> Self {
        Self {
            values: [0; MAX_NUM_COUNTERS],
        }
    }
}

impl Default for MachineCounters {
    fn default() -> Self {
        Self::new()
    }
}

// Index by counter slot (e.g. `state.counters[CounterType::MemWord as usize]`).
impl core::ops::Index<usize> for MachineCounters {
    type Output = u64;
    #[inline(always)]
    fn index(&self, idx: usize) -> &u64 {
        &self.values[idx]
    }
}

impl core::ops::IndexMut<usize> for MachineCounters {
    #[inline(always)]
    fn index_mut(&mut self, idx: usize) -> &mut u64 {
        &mut self.values[idx]
    }
}

const _: () = const {
    assert!(MAX_NUM_COUNTERS >= CounterType::FormalEnd as u8 as usize);
    ()
};

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
    BlakeGFunctionDelegation,
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
    pub counters: MachineCounters,
    pub pc: u32,
    pub timestamp: TimestampScalar,
    pub(crate) context_ptr: *mut (),
    // Spill slot used to preserve the cached flattened non-determinism responses
    // pointer (held in an XMM lane during execution) across `save_machine_state!`
    // / `after_call!`, which would otherwise clobber that lane.
    pub(crate) non_determinism_responses_ptr: u64,
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
    const NON_DETERMINISM_RESPONSES_PTR_OFFSET: usize =
        offset_of!(Self, non_determinism_responses_ptr);

    pub fn initial() -> Self {
        Self {
            registers: [0; 32],
            register_timestamps: [0; 32],
            counters: MachineCounters::new(),
            pc: 0,
            timestamp: INITIAL_TIMESTAMP,
            context_ptr: core::ptr::dangling_mut(),
            non_determinism_responses_ptr: 0,
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
                binary_shift_family: self.counters[CounterType::ShiftBinaryCsr as u8 as usize]
                    as usize,
                mul_div_family: self.counters[CounterType::MulDiv as u8 as usize] as usize,

                word_size_mem_family: self.counters[CounterType::MemWord as u8 as usize] as usize,
                subword_size_mem_family: self.counters[CounterType::MemSubword as u8 as usize]
                    as usize,

                blake_calls: self.counters[CounterType::BlakeDelegation as u8 as usize] as usize,
                bigint_calls: self.counters[CounterType::BigintDelegation as u8 as usize] as usize,
                keccak_calls: self.counters[CounterType::KeccakDelegation as u8 as usize] as usize,
                blake_g_function_calls: self.counters
                    [CounterType::BlakeGFunctionDelegation as u8 as usize]
                    as usize,
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
    const PROVIDES_FLATTENED_NON_DETERMINISM: bool = false;

    fn nondeterminism_as_raw_ptr(&self) -> Option<*const u32> {
        None
    }

    fn read_nondeterminism(&mut self) -> u32;

    fn write_nondeterminism(&mut self, value: u32, memory: &RamImage);

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
