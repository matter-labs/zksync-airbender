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
        dynasm!($ops
            // offset is an offset of our MachineState from RSP

            // Spill the 24 vector-resident registers (densely packed in xmm0..=xmm5)
            // into the dense spill region. x0 is not in the vector file, so the
            // 24 registers fit in 6 stores rather than the previous 7.
            ; movdqu [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 0], xmm0
            ; movdqu [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 16], xmm1
            ; movdqu [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 32], xmm2
            ; movdqu [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 48], xmm3
            ; movdqu [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 64], xmm4
            ; movdqu [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 80], xmm5

            // Save RV registers mapped into x86 GPRs to their compact GPR slots
            // (see GPR_SLOT_TO_RV). Slot 0 is x0, which stays 0 from
            // initialization and is never written here.
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (1 * 4)], r10d // a0, slot 1
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (2 * 4)], r11d // a1, slot 2
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (3 * 4)], r12d // a2, slot 3
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (4 * 4)], r13d // a3, slot 4
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (5 * 4)], r14d // a4, slot 5
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (6 * 4)], r15d // a6, slot 6
            ; mov [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (7 * 4)], ebx  // t3, slot 7

            // put current timestamp (without assumptions about mod 4)
            ; mov [rdx + (MachineState::TIMESTAMP_OFFSET as i32)], r8
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

            // Restore RV registers mapped into x86 GPRs from their compact GPR slots.
            ; mov r10d, [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (1 * 4)]  // a0, slot 1
            ; mov r11d, [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (2 * 4)]  // a1, slot 2
            ; mov r12d, [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (3 * 4)]  // a2, slot 3
            ; mov r13d, [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (4 * 4)]  // a3, slot 4
            ; mov r14d, [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (5 * 4)]  // a4, slot 5
            ; mov r15d, [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (6 * 4)]  // a6, slot 6
            ; mov ebx,  [rdx + (MachineState::GPR_REGISTERS_OFFSET as i32) + (7 * 4)]  // t3, slot 7

            // Reload the 24 vector-resident registers from the dense spill region.
            ; movdqu xmm0, [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 0]
            ; movdqu xmm1, [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 16]
            ; movdqu xmm2, [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 32]
            ; movdqu xmm3, [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 48]
            ; movdqu xmm4, [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 64]
            ; movdqu xmm5, [rdx + (MachineState::XMM_SPILL_OFFSET as i32) + 80]
            // NOTE: circuit-family counters (xmm8..=xmm12) are not reloaded here; they are
            // not spilled by the matching save_machine_state! and survive the call.
            // NOTE: the flattened non-determinism responses pointer is kept in its own
            // `MachineState` field (plain memory), so there is nothing to restore here.
        )
    }
}

const SCRATCH_REGISTER: u8 = x64::Rq::RCX as u8;

// The 7 hottest RISC-V registers (by dynamic access frequency on the reference
// block) are mapped to host x86 GPRs. x10..x14 keep their natural r10..r14
// homes; a6 (x16) and t3 (x28) take r15/rbx, displacing the colder s1 (x9) and
// a5 (x15) which now live in vector lanes. Keep this set in sync with
// `RV_REG_TO_XMM_SLOT` (asserted below).
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
        let in_gpr = matches!(x, 10 | 11 | 12 | 13 | 14 | 16 | 28);
        let in_xmm = RV_REG_TO_XMM_SLOT[x as usize] != RV_XMM_SLOT_NONE;
        assert!(in_gpr ^ in_xmm); // exactly one of the two for every x in 1..32
        x += 1;
    }
};

fn destination_gpr(x: u32) -> u8 {
    rv_to_gpr(x).unwrap_or(x64::Rq::RAX as u8)
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

macro_rules! pre_bump_timestamp_and_touch {
    ($ops:ident, $d:expr, $r:expr) => {
        dynasm!($ops
            ; add r8, $d
            ; mov [rsp + 8*($r as i32) + (MachineState::REGISTER_TIMESTAMPS_OFFSET as i32)], r8
        );
    };
}

macro_rules! touch_register_and_increment_timestamp {
    ($ops:ident, $r:expr) => {
        dynasm!($ops
            ; mov [rsp + 8*($r as i32) + (MachineState::REGISTER_TIMESTAMPS_OFFSET as i32)], r8
            ; inc r8
        );
    };
}

macro_rules! touch_register_and_bump_timestamp {
    ($ops:ident, $r:expr, $d:expr) => {
        dynasm!($ops
            ; mov [rsp + 8*($r as i32) + (MachineState::REGISTER_TIMESTAMPS_OFFSET as i32)], r8
            ; add r8, $d
        );
    };
}

macro_rules! bump_timestamp {
    ($ops:ident, $d:expr) => {
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

impl<I: ContextImpl> JittedCode<I> {
    pub fn preprocess_bytecode(program: &[Instruction], cycles_bound: Option<u32>) -> Self {
        let mut ops = x64::Assembler::new().unwrap();
        let start = ops.offset();

        // view_rv32_assembly(&program[..100], 0);

        dynasm!(ops
            ; ->start:
            ;; prologue!(ops)
            ; vzeroall
            ; xor rbx, rbx
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
        for i in 0..MachineState::SIZE_IN_QWORDS {
            dynasm!(ops
                ; mov QWORD [rsp + 8 * i as i32], 0
            );
        }

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

            use InstructionName as Op;

            // Decoded operands. For pure instructions `imm` is already sign-extended
            // (or holds the shift amount / U-type immediate, depending on the opcode),
            // and for branches `rd` carries the funct3 selector.
            let rd = instr.rd as u32;
            let rs1 = instr.rs1 as u32;
            let rs2 = instr.rs2 as u32;
            let imm = instr.imm as i32;

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
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
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
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
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
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
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
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
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
                    let value = load(&mut ops, rs2);
                    // RDX is potentially taken by value, so can not use it
                    touch_register_and_increment_timestamp!(ops, rs1);
                    touch_register_and_increment_timestamp!(ops, rs2);
                    dynasm!(ops
                        // this sequence of operations is: read old value and timestamp, save it, write new value and timestamp
                        ; mov ebp, DWORD [rsi + 4 * rax] // load old word(!) value into RAX
                        ; mov BYTE [rsi + Rq(SCRATCH_REGISTER)], Rb(value) // store new value - just enough bytes
                        ; push rdx
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // read timestamp
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8 // update timestamp
                        ; mov [rdi + r9 * 4], ebp // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                        ; pop rdx
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
                    let value = load(&mut ops, rs2);
                    // RDX is potentially taken by value, so can not use it
                    touch_register_and_increment_timestamp!(ops, rs1);
                    touch_register_and_increment_timestamp!(ops, rs2);
                    dynasm!(ops
                        // this sequence of operations is: read old value and timestamp, save it, write new value and timestamp
                        ; mov ebp, DWORD [rsi + 4 * rax] // load old word(!) value into RAX
                        ; mov WORD [rsi + Rq(SCRATCH_REGISTER)], Rw(value) // store new value - just enough bytes
                        ; push rdx
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // read timestamp
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8 // update timestamp
                        ; mov [rdi + r9 * 4], ebp // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                        ; pop rdx
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
                        ; mov DWORD [rsi + Rq(SCRATCH_REGISTER)], Rd(value) // store new value
                        ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)] // read timestamp
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)], r8 // update timestamp
                        ; mov [rdi + r9 * 4], eax // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write timestamp value into trace
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
