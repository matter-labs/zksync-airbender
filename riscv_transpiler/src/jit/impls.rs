use std::ptr::NonNull;

use super::*;

use dynasmrt::{dynasm, x64, DynasmApi, DynasmLabelApi};

use crate::ir::simple_instruction_set::{Instruction, InstructionName};

pub type ReceiveTraceFn =
    extern "sysv64" fn(*mut (), &mut TraceChunk, &MachineState) -> *mut TraceChunk;
pub type ReceiveFinalStateFn = extern "sysv64" fn(*mut (), &mut TraceChunk, &MachineState);

pub struct JittedCode<I: ContextImpl> {
    code: dynasmrt::ExecutableBuffer,
    start: dynasmrt::AssemblyOffset,
    _marker: core::marker::PhantomData<I>,
}

unsafe impl<I: ContextImpl> Send for JittedCode<I> {}

unsafe impl<I: ContextImpl> Sync for JittedCode<I> {}

// Register use and mapping

// - The 7 hottest RV registers live in host x86 GPRs (see `rv_to_gpr`):
//     a0..a4 (x10..x14) -> r10..r14, a6 (x16) -> r15, t3 (x28) -> rbx
// - RDI holds a pointer to backing array for snapshot itself, with elements being Register struct (TODO: decide if we want aligned or not timestamps. Most likely yes)
// - RSI will contain a pointer to the special structure that begins with backing array for memory, followed by backing array for word timestamps
// - r8 holds a timestamp (0 mod 4 in the cycle)
// - r9 holds a number of elements in the snapshot

// For registers with no dedicated x86 register,
// register writes go via rax and reads via rdx
// rcx also doesn't contain a register because it must be used for bitshifts

// x0 is hardwired zero and is never materialized in a vector lane. The remaining
// 24 registers are packed densely (see `RV_REG_TO_XMM_SLOT`) into 128-bit vector
// registers xmm0..=xmm5, loaded using PEXTRD and stored using PINSRD, and spilled
// to / reloaded from the dense `xmm_register_spill` region with 6 128-bit moves.

// On the stack we will have a structure that will allows us to pass in a single pointer all the global machine state.

// We need to maintain extra information, that are counters of circuit families and delegations - those are also saved in 128-bit vector registers.
// We need at most 6 circuit families and 3 delegation types, and we assume u32 counters at most in realistic scenarios. So we reserve xmm8 and xmm9

// Timestamps of registers will be held on the stack, as well as a pointer to the non-determinism servant. We will later on restructure
// RAM and non-determinism traits to use separate "memory peek" trait, that only allows to view values, but not affect them or timestamps

// NOTE: stack on x86 must be 16-byte aligned, so we should carefully adjust stack when we push/pop

// In general, callee-saved as rbx, r12-r15 and rbp. RSP is also callee saved, but it's special-case.

// The prologue saves all callee-saved registers
// This allows us to use all but rsp. RBP is saved/restored as a callee-saved
// register but is NOT used as a frame pointer, so it is free as scratch inside.
// Using rsp would cause signal handlers to write to some random location
// instead of the stack.
macro_rules! prologue {
    ($ops:ident) => {
        dynasm!($ops
            // stack is 8 mod 16 here
            ; push rbp // saved (callee-saved); we do NOT use it as a frame pointer

            ; push rbx
            ; push r12
            ; push r13
            ; push r14
            ; push r15

            // align stack
            ; sub rsp, 8
        )
    };
}

macro_rules! epilogue {
    ($ops:ident) => {
        dynasm!($ops
            ; add rsp, 8

            ; pop r15
            ; pop r14
            ; pop r13
            ; pop r12
            ; pop rbx
            ; pop rbp // restore caller's RBP (no frame pointer; RSP balanced manually)

            ; ret
        )
    };
}

// Spill / reload the vectorized circuit-family counters (xmm8..=xmm12) to the
// MachineState `counters` array (16-byte aligned, so movdqa is valid). Used ONLY at
// snapshot boundaries (trace flush / final), where the snapshotter reads the counters.
// Delegation and non-determinism external calls deliberately do NOT spill counters:
// they never read or modify them (verified: the delegation implementations only touch
// the trace and registers), so the values just need to survive the call in xmm8..=xmm12.
// MachineState pointer must be in RDX.
macro_rules! spill_counters {
    ($ops:ident) => {
        dynasm!($ops
            ; movdqa [rdx + (MachineState::COUNTERS_OFFSET as i32) + 0], xmm8
            ; movdqa [rdx + (MachineState::COUNTERS_OFFSET as i32) + 16], xmm9
            ; movdqa [rdx + (MachineState::COUNTERS_OFFSET as i32) + 32], xmm10
            ; movdqa [rdx + (MachineState::COUNTERS_OFFSET as i32) + 48], xmm11
            ; movdqa [rdx + (MachineState::COUNTERS_OFFSET as i32) + 64], xmm12
        )
    };
}

macro_rules! reload_counters {
    ($ops:ident) => {
        dynasm!($ops
            ; movdqa xmm8, [rdx + (MachineState::COUNTERS_OFFSET as i32) + 0]
            ; movdqa xmm9, [rdx + (MachineState::COUNTERS_OFFSET as i32) + 16]
            ; movdqa xmm10, [rdx + (MachineState::COUNTERS_OFFSET as i32) + 32]
            ; movdqa xmm11, [rdx + (MachineState::COUNTERS_OFFSET as i32) + 48]
            ; movdqa xmm12, [rdx + (MachineState::COUNTERS_OFFSET as i32) + 64]
        )
    };
}

macro_rules! receive_trace {
    ($ops:ident, $recv:expr) => {
        dynasm!($ops
            // handler for full trace chunk. RDX is expected to have a pointer to the MachineState
            ; ->trace_buffer_full:
            // we only call this function after executing the opcode in full,
            // so we do not care about rax (for stores), rdx (for loads) or rcx (scratch)
            ;; before_call!($ops)
            ;; spill_counters!($ops) // make the live counters visible to the snapshotter
            // ; push rax
            // ; push rcx
            ; push rdx
            ; mov rax, QWORD ($recv as *const ()).addr() as usize as isize as i64
            ; mov rsi, rdi // second argument is our trace chunk
            ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)] // first argument is pointer to the context
            // third argument is machine state
            ; call rax
            ; pop rdx
            ;; after_call!($ops) // actual structure is 8 bytes above RSP
            ;; reload_counters!($ops) // the snapshotter call clobbered caller-saved xmm8..=xmm12
            // and in RAX we expect the return value, that is a NEW pointer to the scratch space if needed
            ; mov rdi, rax
            ; mov r9, [rdi + (TraceChunk::LEN_OFFSET as i32)] // update the counter from what our handler said
            ; ret
        )
    };
}

macro_rules! quit {
    ($ops:ident, $recv:expr) => {
        dynasm!($ops
            // handler for final trace chunk. In r9 we have a counter of snapshotted data in the last chunk
            ; ->quit:
            ; ->quit_impl:
            // we only call this function after executing the opcode in full,
            // so we do not care about rax (for stores), rdx (for loads) or rcx (scratch)
            // ; int 3
            ; mov rdx, rsp // put MachineState into RDX
            ; mov [rdi + (TraceChunk::LEN_OFFSET as i32)], r9 // write length
            ;; before_call!($ops)
            ;; spill_counters!($ops) // make the live counters visible in the final state
            ; push rdx
            ; mov rax, QWORD ($recv as *const ()).addr() as usize as isize as i64
            ; mov rsi, rdi // second argument is our trace chunk
            ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)] // first argument is pointer to the context
            // third is our machine state - already in RDX - no need to load it
            ; sub rsp, 8
            ; call rax
            ; add rsp, 8
            ; pop rdx
            ;; after_call!($ops)
            // ; int 3
            // we return nothing, but should cleanup the stack

            // forget MachineState
            ; add rsp, (MachineState::SIZE as i32)
            // do normal epilogue, and we return nothing
            ;; epilogue!($ops)
        )
    };
}

// This macro saves registers RSI/RDI, and indirectly saves rbx/r8-r15 into machine state.
// MachineState pointer must be in RDX
macro_rules! before_call {
    ($ops:ident) => {
        dynasm!($ops
            ; push rsi
            ; push rdi

            ;; save_machine_state!($ops)
        )
    }
}

// This macro saves registers into MachineState structure in RDX
macro_rules! save_machine_state {
    ($ops:ident) => {
        // Spill the vector-resident registers and the value-mapped host GPRs into the
        // MachineState (pointer in RDX). The exact set differs by register-allocation
        // experiment (see the `xmm_ts` feature), so it lives in cfg'd helpers.
        save_value_xmms(&mut $ops);
        save_value_gprs(&mut $ops);
        dynasm!($ops
            // put current timestamp (without assumptions about mod 4)
            ; mov [rdx + (MachineState::TIMESTAMP_OFFSET as i32)], r8
        );
        // Spill the value-mapped registers' timestamps (live in GPRs or XMM lanes
        // depending on the experiment) into register_timestamps[], so snapshots and
        // external callees see them.
        spill_register_timestamps(&mut $ops);
        dynasm!($ops
            // NOTE: the circuit-family counters (xmm8..=xmm12) are NOT spilled here.
            // External callees reached through before_call! (delegations, non-determinism)
            // do not read or modify counters, and do not clobber xmm8..=xmm12, so the live
            // values survive the call. Counters are spilled only at snapshot boundaries
            // (see `spill_counters!` in `receive_trace!`/`quit!`).
            // NOTE: the flattened non-determinism responses pointer lives directly in the
            // `MachineState` field, which is plain memory and is therefore preserved across
            // the call without any explicit save/restore here.
        )
    }
}

// This macro restores RBX/r8, r10-r15 from MachineState. MachineState is expected to be in RDX. R9 is ignored
macro_rules! after_call {
    ($ops:ident) => {
        dynasm!($ops
            ;; update_machine_state_post_call!($ops)

            ; pop rdi
            ; pop rsi
        )
    }
}

// Restored registers from MachineState pointer in RDX
macro_rules! update_machine_state_post_call {
    ($ops:ident) => {
        dynasm!($ops
            // load updated timestamp (also without assumptions)
            ; mov r8, [rdx + (MachineState::TIMESTAMP_OFFSET as i32)]
        );
        // Restore the value-mapped host GPRs and vector-resident registers (the set
        // differs by experiment; see the `xmm_ts` feature).
        restore_value_gprs(&mut $ops);
        restore_value_xmms(&mut $ops);
        // Reload the value-mapped registers' timestamps (an external callee, e.g. a
        // delegation, may have modified ts[10..12]).
        reload_register_timestamps(&mut $ops);
        dynasm!($ops
            // NOTE: circuit-family counters (xmm8..=xmm12) are not reloaded here; they are
            // not spilled by the matching save_machine_state! and survive the call.
            // NOTE: the flattened non-determinism responses pointer is kept in its own
            // `MachineState` field (plain memory), so there is nothing to restore here.
        )
    }
}

const SCRATCH_REGISTER: u8 = x64::Rq::RCX as u8;

// RISC-V registers whose VALUE lives in a host x86 GPR: a0..a4, a6, t3, a5 (8 registers).
// Keep this set in sync with `RV_REG_TO_XMM_SLOT` (asserted below).
fn rv_to_gpr(x: u32) -> Option<u8> {
    use x64::Rq::*;
    assert!(x < 32);

    Some(
        (match x {
            10 => R10, // a0
            11 => R11, // a1
            12 => R12, // a2
            13 => R13, // a3
            14 => R14, // a4
            15 => RBP, // a5
            16 => R15, // a6
            28 => RBX, // t3
            _ => return None,
        }) as u8,
    )
}

// The host-GPR set must be exactly the registers that `RV_REG_TO_XMM_SLOT`
// marks as not-in-a-vector-lane (besides x0).
const _: () = {
    let mut x = 1u8;
    while x < 32 {
        let in_gpr = matches!(x, 10 | 11 | 12 | 13 | 14 | 15 | 16 | 28);
        let in_xmm = RV_REG_TO_XMM_SLOT[x as usize] != RV_XMM_SLOT_NONE;
        assert!(in_gpr ^ in_xmm); // exactly one of the two for every x in 1..32
        x += 1;
    }
};

fn destination_gpr(x: u32) -> u8 {
    rv_to_gpr(x).unwrap_or(x64::Rq::RAX as u8)
}

// ===========================================================================
// Register-timestamp storage for the value-mapped host GPRs (see `rv_to_gpr`).
//
// Default (packed): `write_reg_timestamp` is a no-op; instead the cycle's base timestamp is
// written once per instruction into the (32x33x33) `packed_timestamps` array
// (`packed_ts_store`), and register timestamps are reconstructed offline
// (`MachineState::reconstruct_register_timestamps`). With the `xmm_ts` feature the 8 mapped
// registers' timestamps are kept live in XMM lanes (`pinsrq`) instead, spilled/reloaded at
// snapshots and external calls. Both expose the same entry points used by the cfg-agnostic
// emitters: `write_reg_timestamp`, `flush_reg_timestamp`, `spill_register_timestamps`,
// `reload_register_timestamps`.
// ===========================================================================

// ---- default (packed): per-register timestamp writes are eliminated entirely ----
#[cfg(not(feature = "xmm_ts"))]
pub(crate) fn write_reg_timestamp(_ops: &mut x64::Assembler, _r: u32) {}

/// packed_ts draft: emit the single per-cycle timestamp store. The slot index
/// `33*33*rs1 + 33*rs2 + rd` is a compile-time constant (rs1/rs2/rd are decoded), so this
/// is one `mov [rsp + const], r8` with no runtime index math. rs2 is forced to 32 for
/// loads and rd to 32 for stores, per the experiment's addressing.
#[cfg(not(feature = "xmm_ts"))]
pub(crate) fn packed_ts_store(
    ops: &mut x64::Assembler,
    name: InstructionName,
    rs1: u32,
    rs2: u32,
    rd: u32,
) {
    let off = packed_ts_off(name, rs1, rs2, rd);
    dynasm!(ops ; mov [rsp + off], r8);
}

/// Byte offset (from RSP, which points at MachineState during JITted execution) of the
/// `packed_timestamps` slot written by `packed_ts_store` for instruction `(name, rs1, rs2,
/// rd)`. Factored out so the fused word-mem-run emitter can write the per-element slot
/// directly with an arbitrary timestamp value (not just live `r8`).
#[cfg(not(feature = "xmm_ts"))]
pub(crate) fn packed_ts_off(name: InstructionName, rs1: u32, rs2: u32, rd: u32) -> i32 {
    use InstructionName as Op;
    let p_rs2 = if matches!(name, Op::Lb | Op::Lbu | Op::Lh | Op::Lhu | Op::Lw) {
        32 // load: rs2 axis is the memory access, not a register
    } else {
        rs2 as usize
    };
    // The rd axis must name the register the eager model touches at sub-slot +2:
    //   * stores: memory (sentinel 32);
    //   * branches: the decoded `rd` is the funct3 selector, not a register — the eager
    //     model touches x0 at +2, so use 0;
    //   * ND-write: rd==0 and the eager model writes x0 at +2 (`pre_bump(1,0)`), so keep
    //     the natural rd=0 (the rs2 axis also names x0 at +1, dominated by +2);
    //   * JALR with rd==0: eager touches x0 only at +1 (via the rs2 axis), NOT at +2, so
    //     steer the rd axis to the sentinel 32 to avoid a spurious x0@+2.
    let p_rd = if matches!(name, Op::Sb | Op::Sh | Op::Sw) {
        32
    } else if matches!(name, Op::Branch) {
        0
    } else if rd == 0 && matches!(name, Op::Jalr) {
        32
    } else {
        rd as usize
    };
    let idx = 33 * 33 * (rs1 as usize) + 33 * p_rs2 + p_rd;
    debug_assert!(idx < PACKED_TS_LEN);
    MachineState::PACKED_TS_OFFSET as i32 + (idx as i32) * 8
}

// packed: register timestamps live only in the packed array (reconstructed offline);
// nothing to spill/reload at call boundaries.
#[cfg(not(feature = "xmm_ts"))]
fn spill_register_timestamps(_ops: &mut x64::Assembler) {}

#[cfg(not(feature = "xmm_ts"))]
fn reload_register_timestamps(_ops: &mut x64::Assembler) {}

// ---- xmm_ts: timestamps of the 8 mapped regs live in XMM lanes ----
// xmm6/7/13/14 hold 2 u64 each (x10/11->xmm6, x12/13->xmm7, x14/15->xmm13, x16/28->xmm14).
// A touch is `pinsrq xmm, r8, lane` (off the store port p4, onto the shuffle/FP side).
// A/B against memory storage via RISCV_TS_IN_XMM=0.
#[cfg(feature = "xmm_ts")]
const REG_TS_XMM: [(u32, u8, u8); 8] = [
    (10, 6, 0),
    (11, 6, 1),
    (12, 7, 0),
    (13, 7, 1),
    (14, 13, 0),
    (15, 13, 1),
    (16, 14, 0),
    (28, 14, 1),
];

#[cfg(feature = "xmm_ts")]
pub(crate) fn ts_in_xmm_enabled() -> bool {
    use std::sync::OnceLock;
    static E: OnceLock<bool> = OnceLock::new();
    *E.get_or_init(|| std::env::var_os("RISCV_TS_IN_XMM").map_or(true, |v| v != "0"))
}

#[cfg(feature = "xmm_ts")]
pub(crate) fn reg_ts_xmm(r: u32) -> Option<(u8, u8)> {
    if !ts_in_xmm_enabled() {
        return None;
    }
    let mut i = 0;
    while i < REG_TS_XMM.len() {
        if REG_TS_XMM[i].0 == r {
            return Some((REG_TS_XMM[i].1, REG_TS_XMM[i].2));
        }
        i += 1;
    }
    None
}

#[cfg(feature = "xmm_ts")]
pub(crate) fn write_reg_timestamp(ops: &mut x64::Assembler, r: u32) {
    if let Some((xmm, lane)) = reg_ts_xmm(r) {
        dynasm!(ops ; pinsrq Rx(xmm), r8, lane as i8);
    } else {
        let rts = MachineState::REGISTER_TIMESTAMPS_OFFSET as i32;
        dynasm!(ops ; mov [rsp + 8 * (r as i32) + rts], r8);
    }
}

#[cfg(feature = "xmm_ts")]
fn spill_register_timestamps(ops: &mut x64::Assembler) {
    if !ts_in_xmm_enabled() {
        return;
    }
    let rts = MachineState::REGISTER_TIMESTAMPS_OFFSET as i32;
    dynasm!(ops
        ; movdqu [rdx + rts + 8 * 10], xmm6  // ts[10], ts[11]
        ; movdqu [rdx + rts + 8 * 12], xmm7  // ts[12], ts[13]
        ; movdqu [rdx + rts + 8 * 14], xmm13 // ts[14], ts[15]
        ; pextrq [rdx + rts + 8 * 16], xmm14, 0 // ts[16]
        ; pextrq [rdx + rts + 8 * 28], xmm14, 1 // ts[28]
    );
}

#[cfg(feature = "xmm_ts")]
fn reload_register_timestamps(ops: &mut x64::Assembler) {
    if !ts_in_xmm_enabled() {
        return;
    }
    let rts = MachineState::REGISTER_TIMESTAMPS_OFFSET as i32;
    dynasm!(ops
        ; movdqu xmm6, [rdx + rts + 8 * 10]
        ; movdqu xmm7, [rdx + rts + 8 * 12]
        ; movdqu xmm13, [rdx + rts + 8 * 14]
        ; pinsrq xmm14, [rdx + rts + 8 * 16], 0
        ; pinsrq xmm14, [rdx + rts + 8 * 28], 1
    );
}

/// Deferred (lazy-flush) form of `write_reg_timestamp`: store register `r`'s timestamp,
/// which is `r8 + k` (the region base plus the deferred sub-slot offset `k`). Routes to
/// the off-memory location (GPR or XMM lane) when `r` is mapped, else to memory. Uses RAX
/// as scratch when `k != 0` — the caller (flush) must ensure RAX is dead.
// packed: the lazy path is not used in packed builds; provide a no-op so it compiles.
#[cfg(not(feature = "xmm_ts"))]
pub(crate) fn flush_reg_timestamp(_ops: &mut x64::Assembler, _r: u32, _k: i32) {}

#[cfg(feature = "xmm_ts")]
pub(crate) fn flush_reg_timestamp(ops: &mut x64::Assembler, r: u32, k: i32) {
    let rts = MachineState::REGISTER_TIMESTAMPS_OFFSET as i32;
    if let Some((xmm, lane)) = reg_ts_xmm(r) {
        if k == 0 {
            dynasm!(ops ; pinsrq Rx(xmm), r8, lane as i8);
        } else {
            dynasm!(ops ; lea rax, [r8 + k] ; pinsrq Rx(xmm), rax, lane as i8);
        }
    } else if k == 0 {
        dynasm!(ops ; mov [rsp + 8 * (r as i32) + rts], r8);
    } else {
        dynasm!(ops ; lea rax, [r8 + k] ; mov [rsp + 8 * (r as i32) + rts], rax);
    }
}

// ---- value save/restore for the mapped host GPRs and the vector-resident registers ----
// (8 value GPRs + 6 vector-register movdqu. The MachineState pointer is in RDX.)
fn save_value_xmms(ops: &mut x64::Assembler) {
    let off = MachineState::XMM_SPILL_OFFSET as i32;
    dynasm!(ops
        ; movdqu [rdx + off + 0], xmm0
        ; movdqu [rdx + off + 16], xmm1
        ; movdqu [rdx + off + 32], xmm2
        ; movdqu [rdx + off + 48], xmm3
        ; movdqu [rdx + off + 64], xmm4
        ; movdqu [rdx + off + 80], xmm5
    );
}
fn restore_value_xmms(ops: &mut x64::Assembler) {
    let off = MachineState::XMM_SPILL_OFFSET as i32;
    dynasm!(ops
        ; movdqu xmm0, [rdx + off + 0]
        ; movdqu xmm1, [rdx + off + 16]
        ; movdqu xmm2, [rdx + off + 32]
        ; movdqu xmm3, [rdx + off + 48]
        ; movdqu xmm4, [rdx + off + 64]
        ; movdqu xmm5, [rdx + off + 80]
    );
}
fn save_value_gprs(ops: &mut x64::Assembler) {
    let off = MachineState::GPR_REGISTERS_OFFSET as i32;
    dynasm!(ops
        ; mov [rdx + off + (1 * 4)], r10d // a0, slot 1
        ; mov [rdx + off + (2 * 4)], r11d // a1, slot 2
        ; mov [rdx + off + (3 * 4)], r12d // a2, slot 3
        ; mov [rdx + off + (4 * 4)], r13d // a3, slot 4
        ; mov [rdx + off + (5 * 4)], r14d // a4, slot 5
        ; mov [rdx + off + (6 * 4)], r15d // a6, slot 6
        ; mov [rdx + off + (7 * 4)], ebx  // t3, slot 7
        ; mov [rdx + off + (8 * 4)], ebp  // a5, slot 8
    );
}
fn restore_value_gprs(ops: &mut x64::Assembler) {
    let off = MachineState::GPR_REGISTERS_OFFSET as i32;
    dynasm!(ops
        ; mov r10d, [rdx + off + (1 * 4)]
        ; mov r11d, [rdx + off + (2 * 4)]
        ; mov r12d, [rdx + off + (3 * 4)]
        ; mov r13d, [rdx + off + (4 * 4)]
        ; mov r14d, [rdx + off + (5 * 4)]
        ; mov r15d, [rdx + off + (6 * 4)]
        ; mov ebx,  [rdx + off + (7 * 4)]
        ; mov ebp,  [rdx + off + (8 * 4)]
    );
}

const RV_REGISTERS_NUM_XMMS: u8 = NUM_RV_REGISTER_XMMS;

// Maps a vector-resident RISC-V register to its (xmm index, lane) via the dense
// `RV_REG_TO_XMM_SLOT` packing. x0 and host-GPR-mapped registers must never be
// passed here (callers special-case x0 and check `rv_to_gpr` first).
fn rv_reg_to_xmm_reg(x: u8) -> (u8, u8) {
    assert!(x != 0);
    assert!(x < 32);
    let slot = RV_REG_TO_XMM_SLOT[x as usize];
    assert!(slot != RV_XMM_SLOT_NONE);
    let xmm_register = slot / 4;
    let imm = slot % 4;
    assert!(xmm_register < RV_REGISTERS_NUM_XMMS);

    (xmm_register, imm)
}

// const MACHINE_STATE_XMM_REG_IDX: u8 = RV_REGISTERS_NUM_XMMS;
// const MACHINE_STATE_XMM_REG_IMM: u8 = 0;

// fn cache_machine_ctx_ptr(ops: &mut x64::Assembler) {
//     dynasm!(ops
//         ; push rdx
//         ; mov [rsp + (MachineState::CONTEXT_PTR_OFFSET as i32)], rdx
//         ; pinsrq Rx(MACHINE_STATE_XMM_REG_IDX), rdx, MACHINE_STATE_XMM_REG_IMM as i8
//         ; pop rdx
//     );
// }

// macro_rules! load_cached_machine_ctx_ptr {
//     ($ops:ident, $d:expr) => {
//         dynasm!($ops
//             ; pextrq $d, Rx(MACHINE_STATE_XMM_REG_IDX), MACHINE_STATE_XMM_REG_IMM as i8
//         );
//     };
// }

// NOTE: the flattened non-determinism responses pointer (cursor into the flat array of
// responses) is kept in the dedicated `MachineState::non_determinism_responses_ptr` field
// rather than in an XMM lane. That field is plain memory, so it survives external calls
// (delegations, trace flushes) without any save/restore, and the hot read path simply
// reloads / bumps / stores it (see the flattened `ZicsrNonDeterminismRead` branch).

fn store_result(ops: &mut x64::Assembler, x: u32) {
    assert!(x != 0);
    assert!(x < 32);

    if rv_to_gpr(x).is_none() {
        let x = x as u8;
        let (xmm_register, imm) = rv_reg_to_xmm_reg(x);
        dynasm!(ops
            ; pinsrd Rx(xmm_register), eax, imm as i8
        )
    }
}

/// Returns the general purpose register that now holds the value of the
/// RISC-V register `x`.
/// Do not use in quick succession; the first value will get overwritten.
fn load(ops: &mut x64::Assembler, x: u32) -> u8 {
    rv_to_gpr(x).unwrap_or_else(|| {
        if x == 0 {
            dynasm!(ops
                ; xor edx, edx
            );
        } else {
            let x = x as u8;
            let (xmm_register, imm) = rv_reg_to_xmm_reg(x);
            dynasm!(ops
                ; pextrd edx, Rx(xmm_register), imm as i8
            );
        }

        x64::Rq::RDX as u8
    })
}

/// Loads the RISC-V register `x` into the specified register.
fn load_into(ops: &mut x64::Assembler, x: u32, destination: u8) {
    if let Some(gpr) = rv_to_gpr(x) {
        if destination != gpr {
            dynasm!(ops
                ; mov Rd(destination), Rd(gpr)
            );
        }
    } else {
        if x == 0 {
            dynasm!(ops
                ; xor Rd(destination), Rd(destination)
            );
        } else {
            let x = x as u8;
            let (xmm_register, imm) = rv_reg_to_xmm_reg(x);
            dynasm!(ops
                ; pextrd Rd(destination), Rx(xmm_register), imm as i8
            );
        }
    }
}

fn load_abelian(ops: &mut x64::Assembler, x: u32, y: u32, destination: u8) -> u8 {
    let a = rv_to_gpr(x);
    let b = rv_to_gpr(y);
    if a == Some(destination) {
        assert!(destination != x64::Rq::RAX as u8);
        load(ops, y)
    } else if b == Some(destination) {
        assert!(destination != x64::Rq::RAX as u8);
        load(ops, x)
    } else {
        // just overwrite the destination
        load_into(ops, x, destination);
        load(ops, y)
    }
}

fn load_abelian_into(ops: &mut x64::Assembler, x: u32, y: u32, destination: u8, temporary: u8) {
    // destination is either RV to GPR mapped register, or RAX
    let a = rv_to_gpr(x);
    let b = rv_to_gpr(y);
    if a == Some(destination) {
        // x is already in GPR
        assert!(destination != x64::Rq::RAX as u8);
        load_into(ops, y, temporary);
    } else if b == Some(destination) {
        // y is already in GPR
        assert!(destination != x64::Rq::RAX as u8);
        load_into(ops, x, temporary);
    } else {
        // just overwrite the destination
        load_into(ops, x, destination);
        load_into(ops, y, temporary);
    }
}

macro_rules! print_registers {
    ($ops:ident, $pc:expr, $instr:expr) => {
        dynasm!($ops
            ; sub rsp, 32 * 4
            ; mov DWORD [rsp], 0
        );
        for i in 1..32 {
            let reg = load(&mut $ops, i);
            dynasm!($ops
                ; mov [rsp + 4 * i as i32], Rd(reg)
            );
        }

        dynasm!($ops
            ; mov rcx, rsp

            ; push rdi
            ; push rsi
            ; push r8
            ; push r9

            ; mov rax, QWORD print_registers as *const ()
            ; mov rdi, rcx
            ; mov rsi, r8
            ; mov edx, $pc as i32
            ; mov ecx, $instr as i32
            ; call rax

            ; pop r9
            ; pop r8
            ; pop rsi
            ; pop rdi
        );

        for i in 1..32 {
            let out = destination_gpr(i);
            dynasm!($ops
                ; mov Rd(out), [rsp + 4 * i as i32]
            );
            store_result(&mut $ops, i);
        }
        dynasm!($ops
            ; add rsp, 32 * 4
        );
    };
}

macro_rules! increment_trace {
    ($ops:ident, $pc:expr) => {
        dynasm!($ops
            ; inc r9
            ;; check_to_save_trace!($ops, $pc)
        );
    };
}

macro_rules! check_to_save_trace {
    ($ops:ident, $pc:expr) => {
        dynasm!($ops
            ; cmp r9, TRACE_CHUNK_LEN as i32
            ; jl >skip
            ; mov [rdi + (TraceChunk::LEN_OFFSET as i32)], r9 // save length
            ;; machine_state_store_pc!($ops, rsp, $pc)
            ; mov rdx, rsp // machine state
            ; call ->trace_buffer_full
            ; skip:
        );
    };
}

// Circuit-family counters are kept in vector registers xmm8..=xmm12 (two u64 lanes
// each, covering counters[0..10]) instead of in memory, so an increment is a `paddq`
// on the vector-ALU ports (p0/1/5) rather than a read-modify-write store on the single
// store port (p4) — the measured bottleneck. They are spilled to / reloaded from the
// MachineState `counters` array in `save_machine_state!`/`after_call!`, so snapshots and
// the final state still observe the correct cumulative values. (Legacy-SSE `paddq` keeps
// us off the AVX/SSE transition penalty, matching the existing pextrd/pinsrd/movdqu code.)
fn record_circuit_type(ops: &mut x64::Assembler, circuit_type: CounterType, by: u16) {
    assert!(by > 0);
    let x = circuit_type as u8;
    let grp = 8 + x / 2; // xmm8..=xmm12
    let lane = x % 2; // qword lane within the register

    if by == 1 {
        if lane == 0 {
            dynasm!(ops ; paddq Rx(grp), [->cve_one_q0]);
        } else {
            dynasm!(ops ; paddq Rx(grp), [->cve_one_q1]);
        }
    } else {
        // Rare (delegations): build `by` at the right qword lane in a scratch xmm.
        dynasm!(ops
            ; mov eax, by as i32
            ; movd Rx(15), eax
        );
        if lane == 1 {
            dynasm!(ops ; pslldq Rx(15), 8);
        }
        dynasm!(ops ; paddq Rx(grp), Rx(15));
    }
}

// NOTE on `packed_ts`: `write_reg_timestamp` is a no-op (register timestamps come from the
// packed array) and the per-sub-slot r8 advances below are gated off. The running timestamp
// is instead advanced once per cycle in the eager loop: a single `add r8, TIMESTAMP_STEP`
// for every opcode except loads/stores, which first bump r8 to their memory sub-slot
// (base+1 for a load read, base+2 for a store) to stamp the memory cell, then complete to
// base+4. Delegations keep their explicit base+3 handler contract in their own arm. Only
// the cycle's 0-mod-4 base is written into the packed array (once, at the loop top).
macro_rules! pre_bump_timestamp_and_touch {
    ($ops:ident, $d:expr, $r:expr) => {
        #[cfg(feature = "xmm_ts")]
        dynasm!($ops ; add r8, $d);
        write_reg_timestamp(&mut $ops, $r as u32);
    };
}

macro_rules! touch_register_and_increment_timestamp {
    ($ops:ident, $r:expr) => {
        write_reg_timestamp(&mut $ops, $r as u32);
        #[cfg(feature = "xmm_ts")]
        dynasm!($ops ; inc r8);
    };
}

macro_rules! touch_register_and_bump_timestamp {
    ($ops:ident, $r:expr, $d:expr) => {
        write_reg_timestamp(&mut $ops, $r as u32);
        #[cfg(feature = "xmm_ts")]
        dynasm!($ops ; add r8, $d);
    };
}

macro_rules! bump_timestamp {
    ($ops:ident, $d:expr) => {
        #[cfg(feature = "xmm_ts")]
        dynasm!($ops
            ; add r8, $d
        );
    };
}

macro_rules! emit_misaligned_runtime_error {
    ($ops:ident) => {
        dynasm!($ops
            ; jmp ->exit_on_misaligned
        )
    };
}

macro_rules! emit_runtime_error {
    ($ops:ident) => {
        dynasm!($ops
            ; jmp ->exit_with_error
        )
    };
}

macro_rules! emit_execution_panic {
    ($ops:ident, $pc:expr) => {
        dynasm!($ops
            ; mov r9, $pc as i32
            ; jmp ->exit_with_execution_panic
        )
    };
}

// Assumes machine state at register
macro_rules! machine_state_store_pc {
    ($ops:ident, $reg:ident, $pc:expr) => {
        dynasm!($ops
            ; mov DWORD [$reg + (MachineState::PC_OFFSET as i32)], ($pc as i32)
        )
    };
}

macro_rules! emit_early_exit {
    ($ops:ident, $pc:expr, $bound:expr) => {
        dynasm!($ops
            ; cmp r8, 4
            ; jl -> exit_with_error

            ; xor rax, rax
            ; mov eax, (($bound >> 32) as u32) as i32
            ; shl rax, 32
            ; add eax, ($bound as u32) as i32
            ; cmp r8, rax

            ; jl >skip
            ;; machine_state_store_pc!($ops, rsp, $pc)
            ; jmp ->quit_impl
            ; skip:
        )
    };
}

// === Fused word load/store runs (feature `mem_merge`, packed-timestamp path only) ========
//
// A run of `g` consecutive RISC-V word accesses (all Lw or all Sw) that share the base
// register `rs1` and ascend by an immediate stride of exactly +4 touch `g` *contiguous*
// memory words. Their four per-access store streams are therefore contiguous and can be
// written with wide vector moves (`movdqu`/`movq`) instead of `g` scalar stores each:
//   * memory value      (loads: the read; stores: the new value)  -> 4*g contiguous RAM bytes
//   * memory timestamp  (the cycle value written into the cell)    -> 8*g contiguous RAM bytes
//   * trace value       (loads: read value; stores: OLD value)     -> 4*g contiguous chunk bytes
//   * trace timestamp   (the OLD memory timestamp)                 -> 8*g contiguous chunk bytes
// The base address is computed once. The per-element packed-timestamp slot store and the
// register-file update stay scalar (distinct stack slots / scattered destination registers).
//
// Bit-exactness vs the scalar path: cycle j (j in 0..g) has base T0+4*j (T0 = `r8` at entry);
// a load stamps its memory word at T0+4*j+1, a store at T0+4*j+2; the packed slot for element
// j records T0+4*j; the trace records the value/timestamp present *before* the access. The
// caller advances r9 by g and performs ONE trace-chunk-full check for the whole run.
//
// BLINDLY ASSUMES no control-flow target lands strictly inside the run (the caller binds the
// inner instruction labels to the run head defensively, so a stray jump cannot crash the JIT).
//
// `window` (max group size, one of 2/4/8) comes from RISCV_MERGE_WINDOW (default 8).
#[cfg(all(feature = "mem_merge", not(feature = "xmm_ts")))]
pub(crate) fn merge_window() -> usize {
    use std::sync::OnceLock;
    static W: OnceLock<usize> = OnceLock::new();
    *W.get_or_init(|| {
        let w = std::env::var("RISCV_MERGE_WINDOW")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(8);
        match w {
            2 | 4 | 8 => w,
            _ => 8,
        }
    })
}

/// Largest fusable group size (a power of two in {1,2,4,8}, capped by `window`) of the run of
/// consecutive same-opcode, same-base word accesses with immediate stride exactly +4 starting
/// at `i`. Returns 1 when nothing fuses.
#[cfg(all(feature = "mem_merge", not(feature = "xmm_ts")))]
fn merged_word_run_g(
    program: &[Instruction],
    is_static_target: &[bool],
    i: usize,
    window: usize,
) -> usize {
    use InstructionName as Op;
    let a = &program[i];
    if window < 2 || !matches!(a.name, Op::Lw | Op::Sw) {
        return 1;
    }
    let op = a.name;
    let base = a.rs1;
    let is_load = matches!(op, Op::Lw);
    let mut run = 1usize;
    while run < window && i + run < program.len() {
        let prev = &program[i + run - 1];
        let nxt = &program[i + run];
        // A load that overwrites the base register changes the address seen by every later
        // access; the address is precomputed once, so such a load must end the run.
        if is_load && prev.rd == base {
            break;
        }
        // A static (JAL/Branch) target could land here; the inner instructions are not
        // independently addressable, so the run cannot fold across it.
        if is_static_target[i + run] {
            break;
        }
        if nxt.name != op || nxt.rs1 != base {
            break;
        }
        if (nxt.imm as i32).wrapping_sub(prev.imm as i32) != 4 {
            break;
        }
        run += 1;
    }
    let mut g = 1usize;
    while g * 2 <= run && g * 2 <= window {
        g *= 2;
    }
    g
}

/// Emit a fused run of `g` (a power of two in {2,4,8}) consecutive word loads or stores. Does
/// NOT touch r9; the caller advances r9 by g and does the chunk-full check. Advances r8 by 4*g.
#[cfg(all(feature = "mem_merge", not(feature = "xmm_ts")))]
fn emit_merged_word_run(
    ops: &mut x64::Assembler,
    program: &[Instruction],
    start: usize,
    g: usize,
) {
    use InstructionName as Op;
    let first = &program[start];
    let is_load = matches!(first.name, Op::Lw);
    let rs1 = first.rs1 as u32;
    let imm0 = first.imm as i32;
    let tso = MemoryHolder::TIMESTAMPS_OFFSET as i32;
    let trtso = TraceChunk::TIMESTAMPS_OFFSET as i32;

    // Vector scratch (all free in the packed, non-xmm_ts mode): xmm6/7/13/14.
    let xv = 6u8; // values
    let xt = 7u8; // old-timestamps copy
    let xb = 13u8; // broadcast of T0 (=r8) into both qwords
    let xc = 14u8; // computed new memory timestamps

    // Base byte address of word 0 into RCX (32-bit, wraps like RISC-V). Computed once.
    let base = load(ops, rs1);
    dynasm!(ops ; lea Rd(SCRATCH_REGISTER), [Rd(base) + imm0]);

    // (1) Copy the words currently in RAM into the trace value column. For loads this is the
    //     read value; for stores it is the OLD value (the write happens in step 3, after).
    let vbytes = 4 * g as i32;
    let mut off = 0i32;
    while off < vbytes {
        if vbytes - off >= 16 {
            dynasm!(ops
                ; movdqu Rx(xv), [rsi + Rq(SCRATCH_REGISTER) + off]
                ; movdqu [rdi + r9 * 4 + off], Rx(xv)
            );
            off += 16;
        } else {
            dynasm!(ops
                ; movq Rx(xv), [rsi + Rq(SCRATCH_REGISTER) + off]
                ; movq [rdi + r9 * 4 + off], Rx(xv)
            );
            off += 8;
        }
    }

    // (2) Copy the OLD memory timestamps into the trace timestamp column (8*g bytes, always a
    //     multiple of 16 since g is a power of two >= 2).
    let tbytes = 8 * g as i32;
    let mut off = 0i32;
    while off < tbytes {
        dynasm!(ops
            ; movdqu Rx(xt), [rsi + 2 * Rq(SCRATCH_REGISTER) + (tso + off)]
            ; movdqu [rdi + r9 * 8 + (trtso + off)], Rx(xt)
        );
        off += 16;
    }

    // (3) Stores only: gather the new values (from the rs2 registers) and write them back to
    //     RAM (wide). Must come AFTER step (1) read the old values.
    if !is_load {
        let mut off = 0i32;
        let mut j = 0usize;
        while j < g {
            let chunk = core::cmp::min(4, g - j);
            for k in 0..chunk {
                let rs2 = program[start + j + k].rs2 as u32;
                load_into(ops, rs2, x64::Rq::RAX as u8);
                dynasm!(ops ; pinsrd Rx(xv), eax, k as i8);
            }
            if chunk == 4 {
                dynasm!(ops ; movdqu [rsi + Rq(SCRATCH_REGISTER) + off], Rx(xv));
                off += 16;
            } else {
                // chunk == 2 (only when g == 2)
                dynasm!(ops ; movq [rsi + Rq(SCRATCH_REGISTER) + off], Rx(xv));
                off += 8;
            }
            j += chunk;
        }
    }

    // (4) Write the new memory timestamps: word w gets T0 + 4*w + delta (delta = 1 for loads,
    //     2 for stores). Build [T0+.., T0+..] two qwords at a time from a precomputed offset
    //     table plus a broadcast of T0. Must come AFTER step (2) read the old timestamps.
    dynasm!(ops
        ; movq Rx(xb), r8
        ; punpcklqdq Rx(xb), Rx(xb)
    );
    if is_load {
        dynasm!(ops ; lea rax, [->ts_word_off_load]);
    } else {
        dynasm!(ops ; lea rax, [->ts_word_off_store]);
    }
    let mut w = 0usize;
    let mut toff = 0i32;
    while w < g {
        dynasm!(ops
            ; movdqu Rx(xc), [rax + (8 * w) as i32]
            ; paddq Rx(xc), Rx(xb)
            ; movdqu [rsi + 2 * Rq(SCRATCH_REGISTER) + (tso + toff)], Rx(xc)
        );
        w += 2;
        toff += 16;
    }

    // (5) Loads only: distribute the read values to their destination registers (scalar reload
    //     from RAM; the value column may span more than one xmm for g==8).
    if is_load {
        for j in 0..g {
            let rd = program[start + j].rd as u32;
            let out = destination_gpr(rd);
            dynasm!(ops ; mov Rd(out), [rsi + Rq(SCRATCH_REGISTER) + (4 * j as i32)]);
            store_result(ops, rd);
        }
    }

    // (6) Per-element packed-timestamp slot store (distinct slots -> stays scalar). Element j
    //     records T0 + 4*j; r8 still holds T0 here.
    for j in 0..g {
        let instr = &program[start + j];
        let off = packed_ts_off(instr.name, instr.rs1 as u32, instr.rs2 as u32, instr.rd as u32);
        if j == 0 {
            dynasm!(ops ; mov [rsp + off], r8);
        } else {
            dynasm!(ops
                ; lea rax, [r8 + (4 * j as i32)]
                ; mov [rsp + off], rax
            );
        }
    }

    // (7) Counters and the running timestamp. MemWord += g (identical to g separate +1s).
    record_circuit_type(ops, CounterType::MemWord, g as u16);
    dynasm!(ops ; add r8, (4 * g) as i32);
}

impl<I: ContextImpl> JittedCode<I> {
    pub fn preprocess_bytecode(program: &[Instruction], cycles_bound: Option<u32>) -> Self {
        let mut ops = x64::Assembler::new().unwrap();
        let start = ops.offset();

        // view_rv32_assembly(&program[..100], 0);

        dynasm!(ops
            ; ->start:
            ;; prologue!(ops)
            ; vzeroall
            // OPTION 1: r10..r13 hold values (a0..a3, init 0); r14/r15/rbx/rbp hold the
            // timestamps of those 4 (init 0 = untouched). All start zeroed.
            ; xor rbx, rbx
            ; xor rbp, rbp
            ; xor r10, r10
            ; xor r11, r11
            ; xor r12, r12
            ; xor r13, r13
            ; xor r14, r14
            ; xor r15, r15

            // set initial timestamp and snapshot counter
            ; mov r8, INITIAL_TIMESTAMP as i32
            ; xor r9, r9
        );

        // allocate stack space for Machine state
        dynasm!(ops
            ; sub rsp, (MachineState::SIZE as i32)
        );
        for i in 0..MachineState::ZERO_INIT_QWORDS {
            dynasm!(ops
                ; mov QWORD [rsp + 8 * i as i32], 0
            );
        }
        // packed_ts: zero the large packed-timestamps tail with a small runtime loop
        // (unrolling ~35k stores would bloat the JIT). Uses rax (pointer) and rcx (count),
        // both free here. Untouched slots must read 0 for the offline reconstruction.
        #[cfg(not(feature = "xmm_ts"))]
        dynasm!(ops
            ; lea rax, [rsp + (MachineState::PACKED_TS_OFFSET as i32)]
            ; mov ecx, PACKED_TS_LEN as i32
            ; packed_ts_zero:
            ; mov QWORD [rax], 0
            ; add rax, 8
            ; dec ecx
            ; jnz <packed_ts_zero
        );

        // we expect trace chunk in RDI, and memory in RSI, and context pointer in RDX,
        // so we need to copy context pointer into our structure
        dynasm!(ops
            ; mov [rsp + (MachineState::CONTEXT_PTR_OFFSET as i32)], rdx
        );
        // // NOTE: potential path for next performance optimization
        // // we will also cache it into XMM for performance
        // cache_machine_ctx_ptr(&mut ops);

        // in case of context that provides flattened responses - we will cache it too
        if I::PROVIDES_FLATTENED_NON_DETERMINISM {
            // stack is all set, so we can call external context and read the value into register.
            // pointer to the context is in RDX already (also stashed at CONTEXT_PTR_OFFSET).
            // We use the usual call wrappers to preserve our live registers across the call,
            // then read the raw responses pointer returned in RAX.
            dynasm!(ops
                ; mov rdx, rsp
                ;; before_call!(ops)
                ; push rdx
                ; push r9
                ; mov rax, QWORD (Context::<I>::nondeterminism_as_raw_ptr as *const ()).addr() as usize as isize as i64
                ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)] // first argument is pointer to the context
                ; call rax
                ; pop r9
                ; pop rdx
                ;; after_call!(ops)
                // RAX now holds the raw non-determinism responses pointer. Store it into the
                // dedicated MachineState field (RDX still points at MachineState), which is the
                // single source of truth used by the flattened ZicsrNonDeterminismRead path.
                ; mov [rdx + (MachineState::NON_DETERMINISM_RESPONSES_PTR_OFFSET as i32)], rax
            );
        }

        // Static jump targets for JAL and branch instructions - we may NOT use some of them, but it is ok
        let instruction_labels = (0..program.len())
            .map(|_| ops.new_dynamic_label())
            .collect::<Vec<_>>();

        // Jump target array for Jalr - we will create them upfront, but track which are meaningful
        // Records the position of each RISC-V instruction relative to the start
        let mut jump_offsets = vec![0; program.len()];
        let mut initialized_jump_offsets = HashSet::new();

        // Static (JAL / Branch) control-flow targets. A fused word-mem run must not extend
        // across one (a transfer could land strictly inside the run, whose inner instructions
        // are not independently addressable). JALR targets are dynamic and are *blindly assumed*
        // never to land inside a run (return sites always follow a transfer, so they are run
        // heads). Index 0 is the entry point.
        #[cfg(all(feature = "mem_merge", not(feature = "xmm_ts")))]
        let is_static_target: Vec<bool> = {
            use InstructionName as Op;
            let mut t = vec![false; program.len()];
            t[0] = true;
            for (i, instr) in program.iter().enumerate() {
                if matches!(instr.name, Op::Jal | Op::Branch) {
                    let target = (i as i64) * 4 + (instr.imm as i32) as i64;
                    if target >= 0 && target % 4 == 0 {
                        let ti = (target / 4) as usize;
                        if ti < t.len() {
                            t[ti] = true;
                        }
                    }
                }
            }
            t
        };
        // We don't enforce a single "final PC" sentinel; each exit path stores its own PC.

        // println!("Will preprocess {} opcodes", program.len());

        if let Some(cycles_bound) = cycles_bound {
            let ts_bound = (cycles_bound as u64) * TIMESTAMP_STEP + INITIAL_TIMESTAMP;
            println!("Timestamp limit is 0x{:x}", ts_bound);
        }

        let mut i = 0;
        while i < program.len() {
            // NOTE: the input is already decoded into the intermediate `Instruction`
            // representation (see `crate::ir::simple_instruction_set::preprocess_bytecode`),
            // so here we only dispatch on the instruction name and emit machine code.
            let instr = program[i];
            let pc = i as u32 * 4;

            dynasm!(ops
                ; => instruction_labels[i]
            );
            jump_offsets[i] = ops.offset().0;
            initialized_jump_offsets.insert(i);

            if let Some(cycles_bound) = cycles_bound {
                let ts_bound = (cycles_bound as u64) * TIMESTAMP_STEP + INITIAL_TIMESTAMP;
                // Early exit uses RAX, but we are before any instruction, so we are ok
                emit_early_exit!(ops, pc, ts_bound);
            }

            // print_registers!(ops, pc, instr);

            // Fuse a run of consecutive same-base word loads/stores (immediate stride +4) into
            // wide vector memory/trace stores (feature `mem_merge`, packed path). The emitter
            // does all packed/timestamp/trace/counter bookkeeping for the whole run, so it
            // bypasses the per-instruction prologue and dispatch below.
            #[cfg(all(feature = "mem_merge", not(feature = "xmm_ts")))]
            {
                if matches!(instr.name, InstructionName::Lw | InstructionName::Sw) {
                    let g = merged_word_run_g(program, &is_static_target, i, merge_window());
                    if g >= 2 {
                        // Defensively bind the inner instruction labels / jump offsets to the
                        // run head (the no-inner-target assumption means they're never used; this
                        // only prevents an unresolved-label panic if it were ever violated).
                        for k in 1..g {
                            dynasm!(ops ; => instruction_labels[i + k]);
                            jump_offsets[i + k] = ops.offset().0;
                            initialized_jump_offsets.insert(i + k);
                        }
                        emit_merged_word_run(&mut ops, program, i, g);
                        dynasm!(ops ; add r9, g as i32);
                        let pc_for_trace = pc + 4 * g as u32;
                        check_to_save_trace!(ops, pc_for_trace);
                        i += g;
                        continue;
                    }
                }
            }

            use InstructionName as Op;

            // Decoded operands. For pure instructions `imm` is already sign-extended
            // (or holds the shift amount / U-type immediate, depending on the opcode),
            // and for branches `rd` carries the funct3 selector.
            let rd = instr.rd as u32;
            let rs1 = instr.rs1 as u32;
            let rs2 = instr.rs2 as u32;
            let imm = instr.imm as i32;

            // packed_ts: write the cycle's initial (0 mod 4) base timestamp once into the
            // slot for this instruction's (rs1, rs2, rd) triple, then advance r8 a single
            // time (the touch/bump macros are no-ops here). Loads/stores only advance to
            // their memory sub-slot now (so the in-arm memory-cell stamp is base+1 / base+2)
            // and complete to base+4 after stamping (see the issue_snapshot blocks);
            // delegations advance to base+3 in their own arm.
            #[cfg(not(feature = "xmm_ts"))]
            {
                packed_ts_store(&mut ops, instr.name, rs1, rs2, rd);
                let pre_bump: i32 = match instr.name {
                    Op::Lb | Op::Lbu | Op::Lh | Op::Lhu | Op::Lw => 1,
                    Op::Sb | Op::Sh | Op::Sw => 2,
                    Op::ZicsrDelegation => 0,
                    _ => TIMESTAMP_STEP as i32,
                };
                if pre_bump != 0 {
                    dynasm!(ops ; add r8, pre_bump);
                }
            }

            // Pure instructions that are fully modeled by the unsigned RV32 JIT and
            // simply compute a value into `rd`. They can never have `rd == x0` here
            // because the decoder rewrites such cases into `Nop`. Signed-M instructions
            // such as `mulh`/`div` are intentionally excluded and fall through to the
            // runtime panic below.
            if matches!(
                instr.name,
                Op::Add
                    | Op::Sub
                    | Op::Slt
                    | Op::Sltu
                    | Op::And
                    | Op::Or
                    | Op::Xor
                    | Op::Sll
                    | Op::Srl
                    | Op::Sra
                    | Op::Auipc
                    | Op::Lb
                    | Op::Lbu
                    | Op::Lh
                    | Op::Lhu
                    | Op::Lw
                    | Op::Mul
                    | Op::Mulhu
                    | Op::Divu
                    | Op::Remu
            ) {
                let out = destination_gpr(rd);
                let mut issue_snapshot = false;

                match instr.name {
                    // Add models ADD / ADDI / LUI. ADDI and LUI have rs2 == x0 and use
                    // the immediate; register ADD has imm == 0 and uses rs2.
                    Op::Add => {
                        if rs2 == 0 {
                            let source = load(&mut ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; lea Rd(out), [Rd(source) + imm]
                            );
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops
                                ; add Rd(out), Rd(other)
                            );
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        }
                    }
                    Op::Sub => {
                        touch_register_and_increment_timestamp!(ops, rs1);
                        touch_register_and_increment_timestamp!(ops, rs2);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        load_into(&mut ops, rs1, out);
                        dynasm!(ops
                            ; sub Rd(out), Rd(SCRATCH_REGISTER)
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }
                    // Slt models SLT / SLTI
                    Op::Slt => {
                        if rs2 == 0 {
                            let source = load(&mut ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; cmp Rd(source), imm
                                ; setl Rb(out)
                                ; movzx Rd(out), Rb(out)
                            );
                            record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            load_into(&mut ops, rs2, SCRATCH_REGISTER);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops
                                ; cmp Rd(out), Rd(SCRATCH_REGISTER)
                                ; setl Rb(out)
                                ; movzx Rd(out), Rb(out)
                            );
                            record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                        }
                    }
                    // Sltu models SLTU / SLTIU
                    Op::Sltu => {
                        if rs2 == 0 {
                            let source = load(&mut ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; cmp Rd(source), imm
                                ; setb Rb(out)
                                ; movzx Rd(out), Rb(out)
                            );
                            record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            load_into(&mut ops, rs2, SCRATCH_REGISTER);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops
                                ; cmp Rd(out), Rd(SCRATCH_REGISTER)
                                ; setb Rb(out)
                                ; movzx Rd(out), Rb(out)
                            );
                            record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                        }
                    }
                    // And models AND / ANDI
                    Op::And => {
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; and Rd(out), imm
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops
                                ; and Rd(out), Rd(other)
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        }
                    }
                    // Or models OR / ORI
                    Op::Or => {
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; or Rd(out), imm
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops
                                ; or Rd(out), Rd(other)
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        }
                    }
                    // Xor models XOR / XORI
                    Op::Xor => {
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; xor Rd(out), imm
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops
                                ; xor Rd(out), Rd(other)
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        }
                    }
                    // Sll models SLL / SLLI (immediate form has rs2 == x0 and the shift
                    // amount in imm)
                    Op::Sll => {
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; shl Rd(out), imm as i8
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            load_into(&mut ops, rs2, x64::Rq::RCX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops
                                ; and rcx, 0x1f
                                ; shl Rd(out), cl
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        }
                    }
                    // Srl models SRL / SRLI
                    Op::Srl => {
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; shr Rd(out), imm as i8
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            load_into(&mut ops, rs2, x64::Rq::RCX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops
                                ; and rcx, 0x1f
                                ; shr Rd(out), cl
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        }
                    }
                    // Sra models SRA / SRAI
                    Op::Sra => {
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, 0);
                            dynasm!(ops
                                ; sar Rd(out), imm as i8
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        } else {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            load_into(&mut ops, rs2, x64::Rq::RCX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops
                                ; and rcx, 0x1f
                                ; sar Rd(out), cl
                            );
                            record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                        }
                    }
                    Op::Auipc => {
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        bump_timestamp!(ops, 1);
                        // NOTE: result is wrapping
                        dynasm!(ops
                            ; mov Rd(out), (pc.wrapping_add(instr.imm)) as i32
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }

                    // for subword loads we need an extra register to store word index. We have RDX "empty"
                    // after loading the address. And we need one more register to store timestamp - for that we will push RBP

                    // Loads
                    Op::Lb => {
                        let address = load(&mut ops, rs1);
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, rs1);
                        dynasm!(ops
                            ; movsx Rd(out), BYTE [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, sign-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write old word value into trace
                            ; mov Rq(SCRATCH_REGISTER), [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // read old timestamp (reuse scratch; frees RBP)
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], Rq(SCRATCH_REGISTER) // write old timestamp into trace
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Op::Lbu => {
                        let address = load(&mut ops, rs1);
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, rs1);
                        dynasm!(ops
                            ; movzx Rd(out), BYTE [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, zero-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write old word value into trace
                            ; mov Rq(SCRATCH_REGISTER), [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // read old timestamp (reuse scratch; frees RBP)
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], Rq(SCRATCH_REGISTER) // write old timestamp into trace
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Op::Lh => {
                        // TODO: exception on misalignment
                        let address = load(&mut ops, rs1);
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, rs1);
                        dynasm!(ops
                            ; movsx Rd(out), WORD [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, sign-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write old word value into trace
                            ; mov Rq(SCRATCH_REGISTER), [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // read old timestamp (reuse scratch; frees RBP)
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], Rq(SCRATCH_REGISTER) // write old timestamp into trace
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Op::Lhu => {
                        // TODO: exception on misalignment
                        let address = load(&mut ops, rs1);
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, rs1);
                        dynasm!(ops
                            ; movzx Rd(out), WORD [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, zero-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write old word value into trace
                            ; mov Rq(SCRATCH_REGISTER), [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // read old timestamp (reuse scratch; frees RBP)
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], Rq(SCRATCH_REGISTER) // write old timestamp into trace
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Op::Lw => {
                        // NOTE: here address is exactly counting in 4 bytes, so we do not need extra word counter and
                        // use RDX for bookkeeping
                        // TODO: exception on misalignment
                        let address = load(&mut ops, rs1);
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                        );
                        touch_register_and_increment_timestamp!(ops, rs1);
                        dynasm!(ops
                            ; mov Rd(out), DWORD [rsi + Rq(SCRATCH_REGISTER)] // load old value into destination
                            ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)] // reuse RDX for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(out) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write old value into trace
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemWord, 1);
                        issue_snapshot = true;
                    }

                    // Multiplication
                    Op::Mul => {
                        touch_register_and_increment_timestamp!(ops, rs1);
                        touch_register_and_increment_timestamp!(ops, rs2);
                        let other = load_abelian(&mut ops, rs1, rs2, out);
                        dynasm!(ops
                            ; imul Rd(out), Rd(other)
                        );
                        record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    Op::Mulhu => {
                        touch_register_and_increment_timestamp!(ops, rs1);
                        touch_register_and_increment_timestamp!(ops, rs2);
                        load_into(&mut ops, rs1, x64::Rq::RAX as u8);
                        let other = load(&mut ops, rs2);
                        dynasm!(ops
                            ; mul Rd(other)
                        );
                        if out != x64::Rq::RDX as u8 {
                            dynasm!(ops
                                ; mov Rd(out), edx
                            );
                        }
                        record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    Op::Divu => {
                        // TODO: handle exception cases
                        touch_register_and_increment_timestamp!(ops, rs1);
                        touch_register_and_increment_timestamp!(ops, rs2);
                        load_into(&mut ops, rs1, x64::Rq::RAX as u8);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        dynasm!(ops
                            ; xor rdx, rdx
                            ; div Rd(SCRATCH_REGISTER)
                        );
                        // quotient is in RAX
                        if out != x64::Rq::RAX as u8 {
                            dynasm!(ops
                                ; mov Rd(out), eax
                            );
                        }
                        record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    Op::Remu => {
                        // TODO: handle exception cases
                        touch_register_and_increment_timestamp!(ops, rs1);
                        touch_register_and_increment_timestamp!(ops, rs2);
                        load_into(&mut ops, rs1, x64::Rq::RAX as u8);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        dynasm!(ops
                            ; xor rdx, rdx
                            ; div Rd(SCRATCH_REGISTER)
                        );
                        // remainder is in RDX
                        if out != x64::Rq::RDX as u8 {
                            dynasm!(ops
                                ; mov Rd(out), edx
                            );
                        }
                        record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    _ => unreachable!(),
                }

                touch_register_and_bump_timestamp!(ops, rd, 2);
                store_result(&mut ops, rd);

                // NOTE: ONLY issue snapshotting after store!
                if issue_snapshot {
                    // packed_ts: in this block issue_snapshot <=> a load; r8 is at its
                    // memory sub-slot (base+1) after stamping — complete to base+4 (0 mod 4)
                    // before the snapshot/trace save so the saved timestamp matches.
                    #[cfg(not(feature = "xmm_ts"))]
                    dynasm!(ops ; add r8, 3);
                    let pc_for_trace = pc + 4;
                    increment_trace!(ops, pc_for_trace);
                }

                i += 1;
                continue;
            }

            let mut issue_snapshot = false;

            match instr.name {
                // Nop is the decoded form of any pure instruction that targets x0
                // (e.g. the canonical `addi x0, x0, 0`). It only touches x0.
                Op::Nop => {
                    touch_register_and_increment_timestamp!(ops, 0);
                    touch_register_and_increment_timestamp!(ops, 0);
                    touch_register_and_bump_timestamp!(ops, 0, 2);
                    record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    i += 1;
                }

                // MOP (Zimop) instructions. Only addmod / submod / mulmod are JIT-ed.
                Op::ZimopAdd | Op::ZimopSub | Op::ZimopMul => {
                    let out = destination_gpr(rd); // either register or EAX
                    assert!(rd != 0);
                    assert!(rs1 != 0);
                    // NOTE: we consider inputs as non-reduced and need to output fully reduced. We are mod p = 2^31 - 1,
                    // so handy relations are 2^31 == 1 and 2^32 == 2.
                    match instr.name {
                        Op::ZimopAdd => {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);

                            // here we will want to special-case a variant when we have rs2 == 0 as it's heavily used in the verifier
                            if rs2 == 0 {
                                // Our purpose is to fully reduce. Max input value is 2^32 - 1, that is 2*p + 1, so we need to subtract at most 2 moduluses.
                                // Ideally we should reduce data dependencies, but it's not like we can do much
                                load_into(&mut ops, rs1, out);
                                dynasm!(ops
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; mov edx, Rd(out)
                                    // try to reduce by 1p
                                    ; sub edx, 0x7fff_ffffu32 as i32
                                    ; cmovnc Rd(out), edx
                                    // and by 2p
                                    ; sub Rd(SCRATCH_REGISTER), (0x7fff_ffffu32 * 2) as i32
                                    ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                                );
                                record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                            } else {
                                // we will reduce inputs to be in range of 31 bit to avoid data dependencies

                                // Either rs1 or rs2 would be overwritten over out, or rs1 will go into EAX, and rs2 go into EDX
                                load_abelian_into(&mut ops, rs1, rs2, out, x64::Rq::RDX as u8);
                                dynasm!(ops
                                    // reduce first
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add Rd(out), Rd(SCRATCH_REGISTER)
                                    // reduce second
                                    ; mov Rd(SCRATCH_REGISTER), edx
                                    ; and edx, 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add edx, Rd(SCRATCH_REGISTER)
                                    // now add and almost reduce
                                    ; add Rd(out), edx
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add Rd(out), Rd(SCRATCH_REGISTER)
                                    // and reduce completely
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; sub Rd(SCRATCH_REGISTER), 0x7fff_ffffu32 as i32
                                    ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                                );
                                record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                            }
                        }
                        Op::ZimopSub => {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            assert!(rs1 != 0);
                            assert!(rs2 != 0);

                            // same logic as with addition
                            load_into(&mut ops, rs2, x64::Rq::RDX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops
                                // reduce first
                                ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                ; and Rd(out), 0x7fff_ffffu32 as i32
                                ; shr Rd(SCRATCH_REGISTER), 31i8
                                ; add Rd(out), Rd(SCRATCH_REGISTER)
                                // reduce second
                                ; mov Rd(SCRATCH_REGISTER), edx
                                ; and edx, 0x7fff_ffffu32 as i32
                                ; shr Rd(SCRATCH_REGISTER), 31i8
                                ; add edx, Rd(SCRATCH_REGISTER)
                                // now add and almost reduce
                                ; sub Rd(out), edx
                                ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                ; and Rd(out), 0x7fff_ffffu32 as i32
                                ; shr Rd(SCRATCH_REGISTER), 31i8
                                ; sub Rd(out), Rd(SCRATCH_REGISTER)
                                // and reduce completely
                                ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                ; sub Rd(SCRATCH_REGISTER), 0x7fff_ffffu32 as i32
                                ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                            );
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        }
                        Op::ZimopMul => {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);

                            assert!(rs1 != 0);
                            assert!(rs2 != 0);

                            // same logic as with addition
                            load_abelian_into(&mut ops, rs1, rs2, out, x64::Rq::RDX as u8);
                            dynasm!(ops
                                // reduce first
                                ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                ; and Rd(out), 0x7fff_ffffu32 as i32
                                ; shr Rd(SCRATCH_REGISTER), 31i8
                                ; add Rd(out), Rd(SCRATCH_REGISTER)
                                // reduce second
                                ; mov Rd(SCRATCH_REGISTER), edx
                                ; and edx, 0x7fff_ffffu32 as i32
                                ; shr Rd(SCRATCH_REGISTER), 31i8
                                ; add edx, Rd(SCRATCH_REGISTER)
                                // reinterpret as u64 and mul low
                                ; imul Rq(out), rdx
                                ; mov rdx, Rq(out)
                                ; shr rdx, 31i8
                                ; and Rd(out), 0x7fff_ffffu32 as i32
                                // now continue as in addition
                                ; add Rd(out), edx
                                ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                ; and Rd(out), 0x7fff_ffffu32 as i32
                                ; shr Rd(SCRATCH_REGISTER), 31i8
                                ; add Rd(out), Rd(SCRATCH_REGISTER)
                                // and reduce completely
                                ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                ; sub Rd(SCRATCH_REGISTER), 0x7fff_ffffu32 as i32
                                ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                            );
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        }
                        _ => unreachable!(),
                    }

                    touch_register_and_bump_timestamp!(ops, rd, 2);
                    store_result(&mut ops, rd);

                    i += 1;
                }

                // Control transfer instructions
                Op::Jal => {
                    let out = destination_gpr(rd);
                    // No reads (so read x0 twice)
                    if rd != 0 {
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        dynasm!(ops
                            ; mov Rd(out), (pc + 4) as i32
                        );
                        store_result(&mut ops, rd);
                        pre_bump_timestamp_and_touch!(ops, 1, rd);
                    } else {
                        pre_bump_timestamp_and_touch!(ops, 2, 0);
                    }

                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::BranchSlt, 1);

                    // NOTE: we finished with all register touches as it'll jump out of our normal control flow

                    let offset = imm;
                    let jump_target = pc as i32 + offset;
                    if offset == 0 {
                        // An infinite loop is used to signal end of execution.
                        // Store the actual PC we're exiting from so multiple exit points are allowed.
                        dynasm!(ops
                            ;; machine_state_store_pc!(ops, rsp, pc)
                            ; jmp ->quit_impl
                        );
                    } else if jump_target % 4 != 0 {
                        panic!("Unaligned jump destination");
                        // emit_runtime_error!(ops)
                    } else {
                        if let Some(&label) = instruction_labels.get((jump_target / 4) as usize) {
                            dynasm!(ops
                                ; jmp => label
                            );
                        } else {
                            panic!("Unknown jump destination");
                            // emit_runtime_error!(ops)
                        }
                    }
                    i += 1;
                }
                Op::Jalr => {
                    let out = destination_gpr(rd);
                    let offset = imm;
                    touch_register_and_increment_timestamp!(ops, rs1);
                    load_into(&mut ops, rs1, SCRATCH_REGISTER);
                    dynasm!(ops
                        ; add Rd(SCRATCH_REGISTER), offset
                        // Must be aligned to an instruction but no need to test the least significant bit,
                        // as it is set to zero according to the specification
                        ; test Rd(SCRATCH_REGISTER), 2
                        ; jnz >misaligned
                        ; shr Rd(SCRATCH_REGISTER), 2
                        ; lea rdx, [->jump_offsets]
                        ; mov rax, [rdx + Rq(SCRATCH_REGISTER) * 8]
                        ; lea rdx, [->start]
                        ; add rdx, rax
                    );

                    // Return address may not be written into register before jump target is computed,
                    // otherwise it could affect the jump target.
                    if rd != 0 {
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; mov Rd(out), (pc + 4) as i32
                        );
                        touch_register_and_bump_timestamp!(ops, rd, 2);
                        store_result(&mut ops, rd);
                    } else {
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        bump_timestamp!(ops, 2);
                    }
                    record_circuit_type(&mut ops, CounterType::BranchSlt, 1);

                    dynasm!(ops
                        ; jmp rdx
                        ; misaligned:
                        ; mov esi, Rd(SCRATCH_REGISTER)
                        ;; emit_misaligned_runtime_error!(ops)
                        // ;; emit_runtime_error!(ops)
                    );
                    i += 1;
                }
                // Branches carry their funct3 selector in `rd`.
                Op::Branch => {
                    let jump_target = pc as i32 + imm;
                    if jump_target % 4 != 0 {
                        panic!("Unaligned jump destination");
                        // emit_runtime_error!(ops);
                    } else {
                        let a = load(&mut ops, rs1);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);

                        touch_register_and_increment_timestamp!(ops, rs1);
                        touch_register_and_increment_timestamp!(ops, rs2);

                        touch_register_and_bump_timestamp!(ops, 0, 2);
                        record_circuit_type(&mut ops, CounterType::BranchSlt, 1);

                        if let Some(&label) = instruction_labels.get((jump_target / 4) as usize) {
                            dynasm!(ops
                                ; cmp Rd(a), Rd(SCRATCH_REGISTER)
                            );
                            match rd {
                                0 => {
                                    dynasm!(ops
                                        ; je =>label
                                    );
                                }
                                1 => {
                                    dynasm!(ops
                                        ; jne =>label
                                    );
                                }
                                4 => {
                                    dynasm!(ops
                                        ; jl =>label
                                    );
                                }
                                5 => {
                                    dynasm!(ops
                                        ; jge =>label
                                    );
                                }
                                6 => {
                                    dynasm!(ops
                                        ; jb =>label
                                    );
                                }
                                7 => {
                                    dynasm!(ops
                                        ; jae =>label
                                    );
                                }
                                _ => {
                                    panic!("Unknown BRANCH funct3 {}", rd);
                                }
                            }
                        } else {
                            panic!("Unknown jump destination");
                            // emit_runtime_error!(ops)
                        }
                        i += 1;
                    }
                }

                // NOTE: we will need one extra register for bookkeeping, so we will use RBP

                // Stores
                Op::Sb => {
                    let address = load(&mut ops, rs1);
                    dynasm!(ops
                        ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                        ; mov rax, Rq(SCRATCH_REGISTER) // put word(!) index in to RAX
                        ; shr rax, 2
                    );
                    touch_register_and_increment_timestamp!(ops, rs1);
                    touch_register_and_increment_timestamp!(ops, rs2);
                    // Read + trace the old word value BEFORE loading the new value, so we
                    // never need 4 scratch registers at once (and avoid RBP). RDX is free
                    // here (value not loaded yet).
                    dynasm!(ops
                        ; mov edx, DWORD [rsi + 4 * rax] // load old word(!) value
                        ; mov [rdi + r9 * 4], edx // write old value into trace
                    );
                    let value = load(&mut ops, rs2);
                    dynasm!(ops
                        ; mov BYTE [rsi + Rq(SCRATCH_REGISTER)], Rb(value) // store new value (frees its register)
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // read timestamp (RDX free; frees RBP)
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8 // update timestamp
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                    );
                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                    issue_snapshot = true;
                    i += 1;
                }
                Op::Sh => {
                    // TODO: exception on misalignment
                    let address = load(&mut ops, rs1);
                    dynasm!(ops
                        ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                        ; mov rax, Rq(SCRATCH_REGISTER) // put word(!) index in to RAX
                        ; shr rax, 2
                    );
                    touch_register_and_increment_timestamp!(ops, rs1);
                    touch_register_and_increment_timestamp!(ops, rs2);
                    // Read + trace the old word value BEFORE loading the new value (see Sb).
                    dynasm!(ops
                        ; mov edx, DWORD [rsi + 4 * rax] // load old word(!) value
                        ; mov [rdi + r9 * 4], edx // write old value into trace
                    );
                    let value = load(&mut ops, rs2);
                    dynasm!(ops
                        ; mov WORD [rsi + Rq(SCRATCH_REGISTER)], Rw(value) // store new value (frees its register)
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // read timestamp (RDX free; frees RBP)
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8 // update timestamp
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                    );
                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                    issue_snapshot = true;
                    i += 1;
                }
                Op::Sw => {
                    // TODO: exception on misalignment
                    let address = load(&mut ops, rs1);
                    dynasm!(ops
                        ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                    );
                    let value = load(&mut ops, rs2);
                    // RDX may hold `value`; RAX and RBP are free here (RBP is no longer a
                    // frame pointer, so it can be clobbered), so use them as scratch for the
                    // old value / old timestamp instead of pushing/popping RDX.
                    touch_register_and_increment_timestamp!(ops, rs1);
                    touch_register_and_increment_timestamp!(ops, rs2);
                    dynasm!(ops
                        // this sequence of operations is: read old value and timestamp, save it, write new value and timestamp
                        ; mov eax, DWORD [rsi + Rq(SCRATCH_REGISTER)] // load old value into RAX
                        ; mov DWORD [rsi + Rq(SCRATCH_REGISTER)], Rd(value) // store new value (frees its register)
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)] // read timestamp (RDX free now; frees RBP)
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)], r8 // update timestamp
                        ; mov [rdi + r9 * 4], eax // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                    );
                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::MemWord, 1);
                    issue_snapshot = true;
                    i += 1;
                }

                // CSRRW reading the non-determinism CSR into rd
                Op::ZicsrNonDeterminismRead => {
                    assert!(rs1 == 0);
                    assert!(rd != 0);

                    if I::PROVIDES_FLATTENED_NON_DETERMINISM {
                        // Flattened responses live as a flat array in memory; the cursor into
                        // that array is kept in the dedicated MachineState field (RSP points at
                        // MachineState here). Reload the cursor, read the next response into the
                        // destination, then bump the cursor by one u32 and store it back.
                        let out = destination_gpr(rd);
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        dynasm!(ops
                            ; mov rcx, [rsp + (MachineState::NON_DETERMINISM_RESPONSES_PTR_OFFSET as i32)]
                            ; mov Rd(out), [rcx]
                            ; add rcx, 4 // size_of::<u32>()
                            ; mov [rsp + (MachineState::NON_DETERMINISM_RESPONSES_PTR_OFFSET as i32)], rcx
                        );
                        store_result(&mut ops, rd);
                        pre_bump_timestamp_and_touch!(ops, 1, rd);
                        bump_timestamp!(ops, 2);
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        issue_snapshot = true;
                        i += 1;
                    } else {
                        // default implementation when we save machine state and call external function
                        let out = destination_gpr(rd);
                        // We want to read non-determinism value into RD
                        // as usual, we will stash our machine state into stack, and call external implementation
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        dynasm!(ops
                            ; mov rdx, rsp
                            ;; before_call!(ops)
                            ; push rdx
                            ; push r9
                            ; mov rax, QWORD (Context::<I>::read_nondeterminism as *const ()).addr() as usize as isize as i64
                            ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)]
                            ; call rax
                            ; pop r9
                            ; pop rdx
                            ;; after_call!(ops)
                            ; mov Rd(out), eax
                            ; mov [rdi + r9 * 4], eax // use common trace for non-determinism reads
                            ; mov QWORD [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], 0 // use 0 for timestamp
                        );
                        store_result(&mut ops, rd);
                        pre_bump_timestamp_and_touch!(ops, 1, rd);
                        bump_timestamp!(ops, 2);
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        issue_snapshot = true;
                        i += 1;
                    }
                }
                // CSRRW writing rs1 into the non-determinism CSR
                Op::ZicsrNonDeterminismWrite => {
                    assert!(rs1 != 0);
                    assert!(rd == 0);

                    if I::PROVIDES_FLATTENED_NON_DETERMINISM {
                        // effectively NOP, just touch registers
                        touch_register_and_increment_timestamp!(ops, rs1);
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        bump_timestamp!(ops, 2);
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        i += 1;
                    } else {
                        load_into(&mut ops, rs1, SCRATCH_REGISTER);
                        touch_register_and_increment_timestamp!(ops, rs1);
                        dynasm!(ops
                            ; mov rdx, rsp
                            ;; before_call!(ops)
                            ; push rdx
                            ; push r9
                            ; mov rax, QWORD (Context::<I>::write_nondeterminism as *const ()).addr() as usize as isize as i64
                            ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)]
                            ; mov rdx, rsi
                            ; mov esi, Rd(SCRATCH_REGISTER)
                            ; call rax
                            ; pop r9
                            ; pop rdx
                            ;; after_call!(ops)
                        );
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        bump_timestamp!(ops, 2);
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        i += 1;
                    }
                }
                // Delegation CSRs. The delegation type is encoded in `imm` and equals
                // the corresponding CSR register number. Consecutive identical
                // delegation instructions belong to a single delegated call.
                Op::ZicsrDelegation => {
                    let mut cycles_taken = 0;
                    // NOTE: all the increment below happen before moving RSP
                    let function: *const () = match instr.imm {
                        BLAKE2S_DELEGATION_CSR_REGISTER => {
                            // we should expect 7 or 10 calls
                            let mut num_calls = 0;
                            for j in 1..=10 {
                                if program[i + j] == program[i] {
                                    continue;
                                } else {
                                    num_calls = j;
                                    break;
                                }
                            }
                            assert!(num_calls == 7 || num_calls == 10);
                            i += num_calls;
                            cycles_taken = num_calls;
                            record_circuit_type(
                                &mut ops,
                                CounterType::BlakeDelegation,
                                num_calls as u16,
                            );
                            process_csr::<BLAKE2S_DELEGATION_CSR_REGISTER> as *const ()
                        }
                        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
                            record_circuit_type(&mut ops, CounterType::BigintDelegation, 1);
                            i += 1;
                            cycles_taken = 1;
                            process_csr::<BIGINT_OPS_WITH_CONTROL_CSR_REGISTER> as *const ()
                        }
                        KECCAK_SPECIAL5_CSR_REGISTER => {
                            // we expect exactly 649 calls for single keccak_f1600
                            let mut num_calls = 0;
                            for j in 1..=NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 {
                                if program[i + j] == program[i] {
                                    continue;
                                } else {
                                    num_calls = j;
                                    break;
                                }
                            }
                            assert_eq!(num_calls, NUM_DELEGATION_CALLS_FOR_KECCAK_F1600);
                            i += num_calls;
                            cycles_taken = num_calls;
                            record_circuit_type(
                                &mut ops,
                                CounterType::KeccakDelegation,
                                num_calls as u16,
                            );
                            process_csr::<KECCAK_SPECIAL5_CSR_REGISTER> as *const ()
                        }
                        other_csrs @ _ => {
                            panic!("Unknown CSR {}", other_csrs);
                        }
                    };
                    assert!(i <= program.len());

                    // NOTE: always record cycles taken before potentially sending trace
                    // outside below
                    assert!(cycles_taken <= u16::MAX as usize);
                    record_circuit_type(&mut ops, CounterType::AddSubLui, cycles_taken as u16);

                    // Those are markers in nature
                    assert_eq!(rs1, 0);
                    assert_eq!(rd, 0);
                    pre_bump_timestamp_and_touch!(ops, 2, 0); // touch x0 at 0/1/2 formally
                    bump_timestamp!(ops, 1); // 3 mod 4
                                             // packed_ts: the macros above are no-ops; advance r8 to base+3 so the
                                             // delegation handler sees its expected (3 mod 4) timestamp.
                    #[cfg(not(feature = "xmm_ts"))]
                    dynasm!(ops ; add r8, 3);

                    let pc_for_trace = pc + ((4 * cycles_taken) as u32);

                    dynasm!(ops
                        ; mov rdx, rsp
                        ;; before_call!(ops) // will save rsi and rdi
                        ; push rdx
                        // NOTE: we should write r9 into structure, so snapshotter is consistent as a structure
                        ; mov [rdi + (TraceChunk::LEN_OFFSET as i32)], r9
                        ; sub rsp, 8
                        ; mov rax, QWORD (function as *const ()).addr() as usize as isize as i64
                        // we already have trace chunk in RDI, memory in RSI, and MachineState in RDX
                        ; call rax
                        ; add rsp, 8
                        ; pop rdx
                        ;; after_call!(ops) // restore rsi and rdi
                        // read snapshot length back into register
                        ; mov r9, [rdi + (TraceChunk::LEN_OFFSET as i32)]
                        // and check if we should save
                        ;; check_to_save_trace!(ops, pc_for_trace)
                    );

                    // delegation implementations are themselves responsible to call trace finalizers
                    bump_timestamp!(ops, 1); // 0 mod 4
                                             // packed_ts: macro above is a no-op; the handler advanced
                                             // MachineState.timestamp and after_call reloaded r8, so step once more
                                             // to reach the next cycle's base (0 mod 4).
                    #[cfg(not(feature = "xmm_ts"))]
                    dynasm!(ops ; add r8, 1);

                    // NOTE: no other snapshot check is required - we do the check above
                }
                _ => {
                    // We only JIT the opcode subset mirrored by the unsigned RV32
                    // transpiler VM and proving circuits. Everything else (illegal
                    // opcodes, signed-M instructions, unsupported MOP variants, the
                    // marker CSR, etc.) still gets compiled so dead code does not block
                    // proving setup, but any reachable unsupported opcode aborts at
                    // runtime.
                    emit_execution_panic!(ops, pc);
                    i += 1;
                    continue;
                }
            }

            // NOTE: again, all snapshotting should only happen after stores (mainly due to CSSRW for non-determinism)
            if issue_snapshot {
                // packed_ts: stores are at their memory sub-slot (base+2) after stamping —
                // complete to base+4 before the save. ND read/write already pre-bumped the
                // full step, so only stores need this.
                #[cfg(not(feature = "xmm_ts"))]
                if matches!(instr.name, Op::Sb | Op::Sh | Op::Sw) {
                    dynasm!(ops ; add r8, 2);
                }
                let pc_for_trace = pc + 4;
                increment_trace!(ops, pc_for_trace);
            }
        }
        assert_eq!(i, program.len());

        // if we even come here without exit condition - it's an error
        emit_runtime_error!(ops);

        dynasm!(ops
            // in r9 we expect PC
            ; ->exit_with_execution_panic:
            // update state
            ; mov rdx, rsp
            ; mov [rdx + (MachineState::PC_OFFSET as i32)], r9d
            ;; save_machine_state!(ops)
            ; mov rax, QWORD (print_runtime_panic as *const ()).addr() as usize as isize as i64
            ; mov rdi, r8
            ; mov rsi, rdx
            ; call rax
        );

        dynasm!(ops
            ; ->exit_on_misaligned:
            ; mov rax, QWORD (print_misaligned as *const ()).addr() as usize as isize as i64
            ; mov rdi, r8
            ; call rax
        );

        let exit_with_error_offset = ops.offset().0;
        dynasm!(ops
            ; ->exit_with_error:
            ; mov rax, QWORD (print_complaint as *const ()).addr() as usize as isize as i64
            ; mov rdi, r8
            ; call rax
        );

        // map jump offsets that were no initialized to point into error
        for (i, offset) in jump_offsets.iter_mut().enumerate() {
            if initialized_jump_offsets.contains(&i) == false {
                assert_eq!(*offset, 0);
                *offset = exit_with_error_offset;
            }
        }

        // record all jump offsets
        dynasm!(ops
            ; ->jump_offsets:
            ; .bytes jump_offsets.into_iter().flat_map(|x| x.to_le_bytes())
        );

        // 16-byte-aligned one-hot constants for the vectorized counter increments
        // (`paddq xmm, [->cve_one_qN]`). q0 increments the low qword lane, q1 the high.
        dynasm!(ops
            ; .align 16
            ; ->cve_one_q0:
            ; .bytes 1u64.to_le_bytes()
            ; .bytes 0u64.to_le_bytes()
            ; ->cve_one_q1:
            ; .bytes 0u64.to_le_bytes()
            ; .bytes 1u64.to_le_bytes()
        );

        // Per-word memory-timestamp sub-slot offsets for the fused word-mem-run emitter
        // (`emit_merged_word_run`): word w of a run gets memory timestamp T0 + (4*w + delta),
        // delta = 1 for loads, 2 for stores. These hold the (4*w + delta) addends as u64 so a
        // 128-bit load of two adjacent entries plus a broadcast `paddq` of T0 builds two
        // consecutive new timestamps. Sized for the largest window (8 words).
        #[cfg(all(feature = "mem_merge", not(feature = "xmm_ts")))]
        dynasm!(ops
            ; .align 16
            ; ->ts_word_off_load:
            ; .bytes 1u64.to_le_bytes()
            ; .bytes 5u64.to_le_bytes()
            ; .bytes 9u64.to_le_bytes()
            ; .bytes 13u64.to_le_bytes()
            ; .bytes 17u64.to_le_bytes()
            ; .bytes 21u64.to_le_bytes()
            ; .bytes 25u64.to_le_bytes()
            ; .bytes 29u64.to_le_bytes()
            ; ->ts_word_off_store:
            ; .bytes 2u64.to_le_bytes()
            ; .bytes 6u64.to_le_bytes()
            ; .bytes 10u64.to_le_bytes()
            ; .bytes 14u64.to_le_bytes()
            ; .bytes 18u64.to_le_bytes()
            ; .bytes 22u64.to_le_bytes()
            ; .bytes 26u64.to_le_bytes()
            ; .bytes 30u64.to_le_bytes()
        );

        let receive_trace_fn = Context::<I>::receive_trace;
        receive_trace!(ops, receive_trace_fn);

        let quit_trace_fn = Context::<I>::receive_final_trace_piece;
        quit!(ops, quit_trace_fn);

        let code = ops.finalize().unwrap();

        // let assembly = unsafe {
        //     core::slice::from_raw_parts(code.ptr(start), code.len())
        // };
        // view_assembly(&assembly[..100], start.0);

        Self {
            code,
            start,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn run(
        &self,
        context: &mut Context<I>,
        memory: &mut MemoryHolder,
        initial_trace_chunk: NonNull<TraceChunk>,
        initial_memory: &[u32],
    ) {
        assert!(initial_memory.len() <= common_constants::rom::ROM_WORD_SIZE);
        assert!(context.final_state_ref().is_none());

        memory.memory[..initial_memory.len()].copy_from_slice(initial_memory);

        let run_program: extern "sysv64" fn(
            NonNull<TraceChunk>,
            &mut MemoryHolder,
            &mut Context<I>,
        ) = unsafe { std::mem::transmute(self.code.ptr(self.start)) };

        let before = std::time::Instant::now();
        run_program(initial_trace_chunk, memory, context);
        let elapsed = before.elapsed();

        if let Some(final_state) = context.final_state_ref() {
            let final_timestamp = final_state.timestamp;
            assert_eq!(final_timestamp % TIMESTAMP_STEP, 0);
            let num_instructions = (final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
            println!(
                "Frequency is {} MHz over {} instructions ({} ns run time)",
                (num_instructions as f64) * 1000f64 / (elapsed.as_nanos() as f64),
                num_instructions,
                elapsed.as_nanos()
            );
        }
    }

    pub fn run_over_prepared_memory(
        &self,
        context: &mut Context<I>,
        memory: &mut MemoryHolder,
        initial_trace_chunk: NonNull<TraceChunk>,
    ) {
        let run_program: extern "sysv64" fn(
            NonNull<TraceChunk>,
            &mut MemoryHolder,
            &mut Context<I>,
        ) = unsafe { std::mem::transmute(self.code.ptr(self.start)) };

        run_program(initial_trace_chunk, memory, context);
    }
}

impl<'a> JittedCode<FlattenedContextImpl<'a>> {
    pub fn run_with_flattened_context(
        program: &[u32],
        non_determinism_responses: &'a [u32],
        initial_memory: &[u32],
        cycles_bound: Option<u32>,
    ) -> (MachineState, Box<MemoryHolder>) {
        let mut context = Context::<FlattenedContextImpl<'_>> {
            implementation: FlattenedContextImpl::new(non_determinism_responses),
        };

        let mut memory: Box<MemoryHolder> = unsafe {
            // let mut memory: Box<MemoryHolder> = Box::new_uninit().assume_init();
            let memory: Box<MemoryHolder> = Box::new_zeroed().assume_init();

            memory
        };

        // println!(
        //     "Memory chunk address = 0x{:x}",
        //     (&*memory as *const MemoryHolder).addr()
        // );

        let mut trace: Box<TraceChunk> = unsafe {
            // let trace = Box::new_uninit().assume_init();
            let trace: Box<TraceChunk> = Box::new_zeroed().assume_init();

            trace
        };

        // println!(
        //     "Initial trace chunk address = 0x{:x}",
        //     (&*trace as *const TraceChunk).addr()
        // );

        let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<
            crate::ir::FullUnsignedMachineDecoderConfig,
            false,
        >(program);
        let runner = Self::preprocess_bytecode(&instructions, cycles_bound);

        // Profiling baseline: when RISCV_PROFILE_SKIP_RUN is set we do all of the
        // setup (decode + JIT compile + the large allocations) but skip execution,
        // so subtracting this run's CPU counters from a full run isolates the cost
        // of `run_program` itself. Production paths never set this variable.
        if std::env::var_os("RISCV_PROFILE_SKIP_RUN").is_some() {
            std::hint::black_box(&runner);
            std::hint::black_box(memory.as_mut());
            std::hint::black_box(trace.as_mut());
            return (MachineState::initial(), memory);
        }

        runner.run(
            &mut context,
            memory.as_mut(),
            unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) },
            initial_memory,
        );

        let final_state = context
            .implementation
            .take_final_state()
            .expect("must finish execution");

        (final_state, memory)
    }
}

impl<N: NonDeterminismCSRSource> JittedCode<DefaultContextImpl<'_, N>> {
    pub fn run_alternative_simulator(
        program: &[u32],
        non_determinism_source: &mut N,
        initial_memory: &[u32],
        cycles_bound: Option<u32>,
    ) -> (MachineState, Box<MemoryHolder>) {
        let mut context = Context::<DefaultContextImpl<'_, N>> {
            implementation: DefaultContextImpl {
                non_determinism_source,
                trace_len: 0,
                final_state: None,
            },
        };

        let mut memory: Box<MemoryHolder> = unsafe {
            // let mut memory: Box<MemoryHolder> = Box::new_uninit().assume_init();
            let mut memory: Box<MemoryHolder> = Box::new_zeroed().assume_init();

            memory
        };

        // println!(
        //     "Memory chunk address = 0x{:x}",
        //     (&*memory as *const MemoryHolder).addr()
        // );

        let mut trace: Box<TraceChunk> = unsafe {
            // let trace = Box::new_uninit().assume_init();
            let trace: Box<TraceChunk> = Box::new_zeroed().assume_init();

            trace
        };

        // println!(
        //     "Initial trace chunk address = 0x{:x}",
        //     (&*trace as *const TraceChunk).addr()
        // );

        let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<
            crate::ir::FullUnsignedMachineDecoderConfig,
            false,
        >(program);
        let runner = Self::preprocess_bytecode(&instructions, cycles_bound);

        runner.run(
            &mut context,
            memory.as_mut(),
            unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) },
            initial_memory,
        );

        let final_state = context
            .implementation
            .take_final_state()
            .expect("must finish execution");

        (final_state, memory)
    }

    pub fn run_alternative_simulator_with_last_snapshot(
        program: &[u32],
        non_determinism_source: &mut N,
        initial_memory: &[u32],
        cycles_bound: Option<u32>,
    ) -> (MachineState, Box<MemoryHolder>, Box<TraceChunk>) {
        let mut context = Context::<DefaultContextImpl<'_, N>> {
            implementation: DefaultContextImpl::new(non_determinism_source),
        };

        let mut memory: Box<MemoryHolder> = unsafe {
            // let mut memory: Box<MemoryHolder> = Box::new_uninit().assume_init();
            let mut memory: Box<MemoryHolder> = Box::new_zeroed().assume_init();

            memory
        };

        // println!(
        //     "Memory chunk address = 0x{:x}",
        //     (&*memory as *const MemoryHolder).addr()
        // );

        let mut trace: Box<TraceChunk> = unsafe {
            // let trace = Box::new_uninit().assume_init();
            let trace: Box<TraceChunk> = Box::new_zeroed().assume_init();

            trace
        };

        // println!(
        //     "Initial trace chunk address = 0x{:x}",
        //     (&*trace as *const TraceChunk).addr()
        // );

        let context_ref_mut = &mut context;

        let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<
            crate::ir::FullUnsignedMachineDecoderConfig,
            false,
        >(program);
        let runner = Self::preprocess_bytecode(&instructions, cycles_bound);

        runner.run(
            &mut context,
            memory.as_mut(),
            unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) },
            initial_memory,
        );

        let final_state = context
            .implementation
            .take_final_state()
            .expect("must finish execution");

        (final_state, memory, trace)
    }
}

extern "sysv64" fn process_csr<const CSR_NUMBER: u32>(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    debug_assert!(
        (machine_state as *const MachineState).is_aligned_to(core::mem::align_of::<MachineState>())
    );
    debug_assert!(
        (trace_piece as *const TraceChunk).is_aligned_to(core::mem::align_of::<TraceChunk>())
    );
    debug_assert!(
        (memory_holder as *const MemoryHolder).is_aligned_to(core::mem::align_of::<MemoryHolder>())
    );
    if CSR_NUMBER == KECCAK_SPECIAL5_CSR_REGISTER {
        keccak_unrolled_implementation(trace_piece, memory_holder, machine_state)
    } else if CSR_NUMBER == BIGINT_OPS_WITH_CONTROL_CSR_REGISTER {
        bigint_implementation(trace_piece, memory_holder, machine_state)
    } else if CSR_NUMBER == BLAKE2S_DELEGATION_CSR_REGISTER {
        blake_implementation(trace_piece, memory_holder, machine_state)
    } else {
        panic!("Unknown CSR number {}", CSR_NUMBER);
    }
}

#[repr(C)]
pub struct Context<I: ContextImpl> {
    pub implementation: I,
}

impl<I: ContextImpl> Context<I> {
    extern "sysv64" fn nondeterminism_as_raw_ptr(&self) -> *const u32 {
        if let Some(ptr) = self.implementation.nondeterminism_as_raw_ptr() {
            ptr
        } else {
            core::ptr::null()
        }
    }

    extern "sysv64" fn read_nondeterminism(&mut self) -> u32 {
        self.implementation.read_nondeterminism()
    }

    extern "sysv64" fn write_nondeterminism(&mut self, value: u32, memory: &RamImage) {
        self.implementation.write_nondeterminism(value, memory)
    }

    extern "sysv64" fn receive_trace(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) -> NonNull<TraceChunk> {
        self.implementation
            .receive_trace(trace_piece, machine_state)
    }

    extern "sysv64" fn receive_final_trace_piece(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) {
        self.implementation
            .receive_final_trace_piece(trace_piece, machine_state);
    }

    pub fn take_final_state(&mut self) -> Option<MachineState> {
        self.implementation.take_final_state()
    }

    pub fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        self.implementation.final_state_ref()
    }
}

extern "sysv64" fn print_registers(
    registers: &[u32; 32],
    timestamp: u64,
    pc: u32,
    instruction: u32,
) {
    let cycle = (timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    // println!(
    //     "Cycle {}: PC = 0x{:08x}, instruction 0x{:08x}",
    //     cycle
    //     pc,
    //     instruction
    // );
    println!(
        "{registers:?} at cycle {} and PC = 0x{:08x}, instruction 0x{:08x}",
        cycle, pc, instruction
    );
    view_rv32_assembly(&[instruction], 0);
}

extern "sysv64" fn print_runtime_panic(timestamp: u64, machine_state: &MachineState) {
    panic!(
        "Runtime explicitly panicked at cycle {} with machine state {:?}",
        (timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP,
        machine_state
    );
}

extern "sysv64" fn print_misaligned(timestamp: u64, dst_pc: u64) {
    panic!(
        "Runtime error at cycle {}: trying to jump to misaligned PC = 0x{:08x}",
        (timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP,
        dst_pc
    );
}

extern "sysv64" fn print_complaint(timestamp: u64) {
    panic!(
        "Runtime error at cycle {}!",
        (timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
    )
}

fn sign_extend<const SOURCE_BITS: u8>(x: u32) -> i32 {
    let shift = 32 - SOURCE_BITS;
    i32::from_ne_bytes((x << shift).to_ne_bytes()) >> shift
}

fn view_assembly(assembly: &[u8], start: usize) {
    /// Print register names
    fn reg_names(cs: &Capstone, regs: &[RegId]) -> String {
        let names: Vec<String> = regs.iter().map(|&x| cs.reg_name(x).unwrap()).collect();
        names.join(", ")
    }

    /// Print instruction group names
    fn group_names(cs: &Capstone, regs: &[InsnGroupId]) -> String {
        let names: Vec<String> = regs.iter().map(|&x| cs.group_name(x).unwrap()).collect();
        names.join(", ")
    }

    use capstone::arch::*;
    use capstone::*;

    let cs = Capstone::new()
        .x86()
        .mode(arch::x86::ArchMode::Mode64)
        .syntax(arch::x86::ArchSyntax::Att)
        .detail(true)
        .build()
        .expect("Failed to create Capstone object");

    let insns = cs
        .disasm_all(assembly, start as u64)
        .expect("Failed to disassemble");
    println!("Found {} instructions", insns.len());
    for i in insns.as_ref() {
        println!();
        println!("{}", i);

        let detail: InsnDetail = cs.insn_detail(&i).expect("Failed to get insn detail");
        let arch_detail: ArchDetail = detail.arch_detail();
        let ops = arch_detail.operands();

        let output: &[(&str, String)] = &[
            ("insn id:", format!("{:?}", i.id().0)),
            ("bytes:", format!("{:?}", i.bytes())),
            ("read regs:", reg_names(&cs, detail.regs_read())),
            ("write regs:", reg_names(&cs, detail.regs_write())),
            ("insn groups:", group_names(&cs, detail.groups())),
        ];

        for &(ref name, ref message) in output.iter() {
            println!("{:4}{:12} {}", "", name, message);
        }

        println!("{:4}operands: {}", "", ops.len());
        for op in ops {
            println!("{:8}{:?}", "", op);
        }
    }
}

// Lazy (batched) timestamp path. Declared here, AFTER every `macro_rules!` above,
// so the child module inherits those macros by textual scope and reaches the
// private helper fns/consts of this module via `super`.
#[path = "impls_lazy_ts.rs"]
mod impls_lazy_ts;

fn view_rv32_assembly(assembly: &[u32], start: usize) {
    let assembly =
        unsafe { core::slice::from_raw_parts(assembly.as_ptr().cast(), assembly.len() * 4) };
    /// Print register names
    fn reg_names(cs: &Capstone, regs: &[RegId]) -> String {
        let names: Vec<String> = regs.iter().map(|&x| cs.reg_name(x).unwrap()).collect();
        names.join(", ")
    }

    /// Print instruction group names
    fn group_names(cs: &Capstone, regs: &[InsnGroupId]) -> String {
        let names: Vec<String> = regs.iter().map(|&x| cs.group_name(x).unwrap()).collect();
        names.join(", ")
    }

    use capstone::arch::*;
    use capstone::*;

    let cs = Capstone::new()
        .riscv()
        .mode(arch::riscv::ArchMode::RiscV32)
        .detail(true)
        .build()
        .expect("Failed to create Capstone object");

    let insns = cs
        .disasm_all(assembly, start as u64)
        .expect("Failed to disassemble");
    println!("Found {} instructions", insns.len());
    for i in insns.as_ref() {
        println!();
        println!("{}", i);

        let detail: InsnDetail = cs.insn_detail(&i).expect("Failed to get insn detail");
        let arch_detail: ArchDetail = detail.arch_detail();
        let ops = arch_detail.operands();

        let output: &[(&str, String)] = &[
            ("insn id:", format!("{:?}", i.id().0)),
            ("bytes:", format!("{:?}", i.bytes())),
            ("read regs:", reg_names(&cs, detail.regs_read())),
            ("write regs:", reg_names(&cs, detail.regs_write())),
            ("insn groups:", group_names(&cs, detail.groups())),
        ];

        for &(ref name, ref message) in output.iter() {
            println!("{:4}{:12} {}", "", name, message);
        }

        println!("{:4}operands: {}", "", ops.len());
        for op in ops {
            println!("{:8}{:?}", "", op);
        }
    }
}
