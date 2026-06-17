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

// === RISC-V register placement ===========================================
//
// x0 is hardwired to zero and is NEVER materialized in a vector lane (loads of
// x0 emit `xor`, stores to x0 are dropped). The 7 hottest registers (by dynamic
// access frequency on the reference block) live in host x86 GPRs; see
// `rv_to_gpr` in `impls.rs`. The remaining 24 registers are packed *densely*
// into 6 vector registers (xmm0..=xmm5), 4 per register, and spilled to /
// reloaded from the `xmm_register_spill` field with 6 aligned 128-bit moves.
//
// Dropping x0 from the vector file is what lets the 24 remaining registers fit
// in 6 vector registers instead of 7, saving one 128-bit store/load in
// `save_machine_state!` / `update_machine_state_post_call!`.

// Number of RISC-V registers that live in host x86 GPRs (x0 + 24 vector-resident
// registers make up the other 25).
pub const NUM_RV_REGISTERS_IN_GPRS: usize = 7;
// Number of RISC-V registers kept in vector lanes (32 - 1 (x0) - 7 (host GPRs)).
pub const NUM_XMM_RESIDENT_REGISTERS: usize = 24;
// Number of vector registers used to hold those 24 (4 lanes each).
pub const NUM_RV_REGISTER_XMMS: u8 = (NUM_XMM_RESIDENT_REGISTERS as u8) / 4;
// Sentinel meaning "this RISC-V register is not in a vector lane" (i.e. it is x0
// or one of the host-GPR-mapped registers).
pub const RV_XMM_SLOT_NONE: u8 = 0xFF;

// Dense spill slot index (0..24) -> RISC-V register number. The 24 vector-resident
// registers, in ascending register order; slot `s` lives in xmm`(s/4)` lane `s%4`.
pub const XMM_SLOT_TO_RV: [u8; NUM_XMM_RESIDENT_REGISTERS] = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, // xmm0 (slots 0..4) + xmm1 (slots 4..8) + xmm2 lane 0
    15, 17, 18, 19, // xmm2 lanes 1..4 + xmm3 lane 0..
    20, 21, 22, 23, // xmm3 lanes 1..4
    24, 25, 26, 27, // xmm4
    29, 30, 31, // xmm5 lanes 1..4 (slot 21..24)
];

// RISC-V register number -> dense spill slot, or `RV_XMM_SLOT_NONE` for x0 and the
// host-GPR-mapped registers. Inverse of `XMM_SLOT_TO_RV`.
pub const RV_REG_TO_XMM_SLOT: [u8; 32] = {
    let mut table = [RV_XMM_SLOT_NONE; 32];
    let mut slot = 0u8;
    while (slot as usize) < NUM_XMM_RESIDENT_REGISTERS {
        table[XMM_SLOT_TO_RV[slot as usize] as usize] = slot;
        slot += 1;
    }
    table
};

const _: () = {
    // XMM_SLOT_TO_RV must list exactly 24 distinct registers, none of them x0.
    assert!(XMM_SLOT_TO_RV.len() == NUM_XMM_RESIDENT_REGISTERS);
    // Exactly 8 registers (x0 + 7 host GPRs) must be absent from the vector file.
    let mut none_count = 0usize;
    let mut x = 0usize;
    while x < 32 {
        if RV_REG_TO_XMM_SLOT[x] == RV_XMM_SLOT_NONE {
            none_count += 1;
        }
        x += 1;
    }
    assert!(none_count == 32 - NUM_XMM_RESIDENT_REGISTERS);
    // x0 is never in a vector lane.
    assert!(RV_REG_TO_XMM_SLOT[0] == RV_XMM_SLOT_NONE);
};

// Non-vector registers (x0 + the 7 host-GPR-mapped registers) are stored
// compactly in the `gpr_registers` array rather than at their RV index. Slot 0
// is x0 (always zero); it also pads the array to 8 u32s (32 bytes) so the
// following 128-bit `xmm_register_spill` region stays 16-byte aligned.
pub const NUM_GPR_SLOT_REGISTERS: usize = NUM_RV_REGISTERS_IN_GPRS + 1;

// Compact GPR slot index -> RISC-V register number. Slot 0 is x0; slots 1.. are
// the host-GPR-mapped registers. The JIT save/restore (`save_machine_state!` /
// `update_machine_state_post_call!`) writes/reads each host GPR at the matching
// slot offset, so this order must match those macros.
pub const GPR_SLOT_TO_RV: [u8; NUM_GPR_SLOT_REGISTERS] = [
    0,  // slot 0: x0 (zero / padding)
    10, // slot 1: a0 -> r10
    11, // slot 2: a1 -> r11
    12, // slot 3: a2 -> r12
    13, // slot 4: a3 -> r13
    14, // slot 5: a4 -> r14
    16, // slot 6: a6 -> r15
    28, // slot 7: t3 -> rbx
];

// RISC-V register number -> compact GPR slot, or `RV_XMM_SLOT_NONE` for the
// vector-resident registers. Inverse of `GPR_SLOT_TO_RV`.
pub const RV_REG_TO_GPR_SLOT: [u8; 32] = {
    let mut table = [RV_XMM_SLOT_NONE; 32];
    let mut slot = 0u8;
    while (slot as usize) < NUM_GPR_SLOT_REGISTERS {
        table[GPR_SLOT_TO_RV[slot as usize] as usize] = slot;
        slot += 1;
    }
    table
};

const _: () = {
    // Every register lives in exactly one place: a vector lane XOR a GPR slot.
    let mut x = 0usize;
    while x < 32 {
        let in_xmm = RV_REG_TO_XMM_SLOT[x] != RV_XMM_SLOT_NONE;
        let in_gpr = RV_REG_TO_GPR_SLOT[x] != RV_XMM_SLOT_NONE;
        assert!(in_xmm != in_gpr);
        x += 1;
    }
    // x0 occupies GPR slot 0.
    assert!(RV_REG_TO_GPR_SLOT[0] == 0);
};

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
    // Compact storage for the non-vector registers (x0 + the host-GPR-mapped
    // registers), indexed by compact GPR slot (`RV_REG_TO_GPR_SLOT`), NOT by RV
    // index. Slot 0 is x0 (always 0). Private: use `get_register`/
    // `get_register_mut`/`materialized_registers`, which route every register to
    // its correct backing store. Placed first (offset 0, 32 bytes) so the
    // following spill region is 16-byte aligned.
    gpr_registers: [u32; NUM_GPR_SLOT_REGISTERS],
    // Dense spill of the 24 vector-resident registers, in `XMM_SLOT_TO_RV`
    // order. 16-byte aligned, so the 6 128-bit spill/reload moves are aligned.
    // Private for the same reason as `gpr_registers`.
    xmm_register_spill: [u32; NUM_XMM_RESIDENT_REGISTERS],
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
    const GPR_REGISTERS_OFFSET: usize = offset_of!(Self, gpr_registers);
    const XMM_SPILL_OFFSET: usize = offset_of!(Self, xmm_register_spill);
    const REGISTER_TIMESTAMPS_OFFSET: usize = offset_of!(Self, register_timestamps);
    const COUNTERS_OFFSET: usize = offset_of!(Self, counters);
    const PC_OFFSET: usize = offset_of!(Self, pc);
    const TIMESTAMP_OFFSET: usize = offset_of!(Self, timestamp);
    const CONTEXT_PTR_OFFSET: usize = offset_of!(Self, context_ptr);
    const NON_DETERMINISM_RESPONSES_PTR_OFFSET: usize =
        offset_of!(Self, non_determinism_responses_ptr);

    pub fn initial() -> Self {
        Self {
            gpr_registers: [0; NUM_GPR_SLOT_REGISTERS],
            xmm_register_spill: [0; NUM_XMM_RESIDENT_REGISTERS],
            register_timestamps: [0; 32],
            counters: MachineCounters::new(),
            pc: 0,
            timestamp: INITIAL_TIMESTAMP,
            context_ptr: core::ptr::dangling_mut(),
            non_determinism_responses_ptr: 0,
        }
    }

    /// Value of RISC-V register `index`, transparently reading from the dense
    /// vector spill for vector-resident registers and from the compact
    /// `gpr_registers` store for x0 and the host-GPR-mapped registers.
    #[inline]
    pub fn get_register(&self, index: usize) -> u32 {
        let xmm_slot = RV_REG_TO_XMM_SLOT[index];
        if xmm_slot == RV_XMM_SLOT_NONE {
            self.gpr_registers[RV_REG_TO_GPR_SLOT[index] as usize]
        } else {
            self.xmm_register_spill[xmm_slot as usize]
        }
    }

    /// Mutable reference to the storage backing RISC-V register `index` — its
    /// dense vector spill slot, or its compact `gpr_registers` slot for x0 and
    /// the host-GPR-mapped registers. Use this instead of touching the (private)
    /// backing arrays so writes land where the JIT actually reads them.
    #[inline]
    pub fn get_register_mut(&mut self, index: usize) -> &mut u32 {
        let xmm_slot = RV_REG_TO_XMM_SLOT[index];
        if xmm_slot == RV_XMM_SLOT_NONE {
            &mut self.gpr_registers[RV_REG_TO_GPR_SLOT[index] as usize]
        } else {
            &mut self.xmm_register_spill[xmm_slot as usize]
        }
    }

    /// Full RV-ordered register file (x0..x31), materializing vector-resident
    /// registers from the dense spill.
    #[inline]
    pub fn materialized_registers(&self) -> [u32; 32] {
        std::array::from_fn(|i| self.get_register(i))
    }

    pub fn as_replayer_state(&self) -> State<DelegationsAndFamiliesCounters> {
        State {
            registers: std::array::from_fn(|i| Register {
                timestamp: self.register_timestamps[i],
                value: self.get_register(i),
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
