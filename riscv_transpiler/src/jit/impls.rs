use std::ptr::NonNull;

use super::*;

use dynasmrt::{dynasm, x64, DynasmApi, DynasmLabelApi};
use riscv_decode::Instruction;

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

// - x10-x15 (RV) are stored in r10-r15 (X86)
// - RDI holds a pointer to backing array for snapshot itself, with elements being Register struct (TODO: decide if we want aligned or not timestamps. Most likely yes)
// - RSI will contain a pointer to the special structure that begins with backing array for memory, followed by backing array for word timestamps
// - r8 holds a timestamp (0 mod 4 in the cycle)
// - r9 holds a number of elements in the snapshot

// For registers with no dedicated x86 register,
// register writes go via rax and reads via rdx
// rcx also doesn't contain a register because it must be used for bitshifts
//
// x10 - x15 are assiged to r10 - r15
// rbx is for x9

// Registers that are placed not in the GPR are instead placed into 128-bit vector registers, and loaded using PEXTRD and stored using PINSRD.
// In total we still use upper bound of 8 vector registers xmm0-xmm7.

// On the stack we will have a structure that will allows us to pass in a single pointer all the global machine state.

// We need to maintain extra information, that are counters of circuit families and delegations - those are also saved in 128-bit vector registers.
// We need at most 6 circuit families and 3 delegation types, and we assume u32 counters at most in realistic scenarios. So we reserve xmm8 and xmm9

// Timestamps of registers will be held on the stack, as well as a pointer to the non-determinism servant. We will later on restructure
// RAM and non-determinism traits to use separate "memory peek" trait, that only allows to view values, but not affect them or timestamps

// NOTE: stack on x86 must be 16-byte aligned, so we should carefully adjust stack when we push/pop

// In general, callee-saved as rbx, r12-r15 and rbp. RSP is also callee saved, but it's special-case.

// The prologue saves all callee-saved registers
// This allows us to use all but rbp and rsp
// Using rbp would mess with debuggers
// Using rsp would cause signal handlers to write to some random location
// instead of the stack.
macro_rules! prologue {
    ($ops:ident) => {
        dynasm!($ops
            // stack is 8 mod 16 here
            ; push rbp
            ; mov rbp, rsp

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
            ; leave // movs RBP into RSP, and pops RBP

            ; ret
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
            // ; push rax
            // ; push rcx
            ; push rdx
            ; mov rax, QWORD $recv as _
            ; mov rsi, rdi // second argument is our trace chunk
            ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)] // first argument is pointer to the context
            // third argument is machine state
            ; call rax
            ; pop rdx
            ;; after_call!($ops) // actual structure is 8 bytes above RSP
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
            ; push rdx
            ; mov rax, QWORD $recv as _
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

            // First write all registers that are mapped into XMMs
            ; movdqu [rdx + 0], xmm0
            ; movdqu [rdx + 16], xmm1
            ; movdqu [rdx + 32], xmm2 // x8 fits here
            // ; movdqu [rdx + 48], xmm3
            ; movdqu [rdx + 64], xmm4
            ; movdqu [rdx + 80], xmm5
            ; movdqu [rdx + 96], xmm6
            ; movdqu [rdx + 112], xmm7

            // Save RV registers that are mapped into X86 GPRs (x9-x15)
            ; mov [rdx + (9 * 4 as i32)], ebx // x9 -> RBX
            ; mov [rdx + (10 * 4 as i32)], r10d // x10 -> R10
            ; mov [rdx + (11 * 4 as i32)], r11d // x11 -> R11
            ; mov [rdx + (12 * 4 as i32)], r12d // x12 -> R12
            ; mov [rdx + (13 * 4 as i32)], r13d // x13 -> R13
            ; mov [rdx + (14 * 4 as i32)], r14d // x14 -> R14
            ; mov [rdx + (15 * 4 as i32)], r15d // x15 -> R15

            // put current timestamp (without asumptions about mod 4)
            ; mov [rdx + (MachineState::TIMESTAMP_OFFSET as i32)], r8
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

            // Restore RV registers that are mapped into X86 GPRs (x9-x15)
            ; mov ebx, [rdx + (9 * 4 as i32)]  // x9 -> RBX
            ; mov r10d, [rdx + (10 * 4 as i32)]  // x10 -> R10
            ; mov r11d, [rdx + (11 * 4 as i32)]  // x11 -> R11
            ; mov r12d, [rdx + (12 * 4 as i32)]  // x12 -> R12
            ; mov r13d, [rdx + (13 * 4 as i32)]  // x13 -> R13
            ; mov r14d, [rdx + (14 * 4 as i32)]  // x14 -> R14
            ; mov r15d, [rdx + (15 * 4 as i32)]  // x15 -> R15

            ; movdqu xmm0, [rdx + 0]
            ; movdqu xmm1, [rdx + 16]
            ; movdqu xmm2, [rdx + 32]
            // ; movdqu xmm3, [rdx + 48]
            ; movdqu xmm4, [rdx + 64]
            ; movdqu xmm5, [rdx + 80]
            ; movdqu xmm6, [rdx + 96]
            ; movdqu xmm7, [rdx + 112]
        )
    }
}

const SCRATCH_REGISTER: u8 = x64::Rq::RCX as u8;

fn rv_to_gpr(x: u32) -> Option<u8> {
    use x64::Rq::*;
    assert!(x < 32);

    Some(
        (match x {
            9 => RBX,
            10 => R10,
            11 => R11,
            12 => R12,
            13 => R13,
            14 => R14,
            15 => R15,
            _ => return None,
        }) as u8,
    )
}

fn destination_gpr(x: u32) -> u8 {
    rv_to_gpr(x).unwrap_or(x64::Rq::RAX as u8)
}

const RV_REGISTERS_NUM_XMMS: u8 = 8;

fn rv_reg_to_xmm_reg(x: u8) -> (u8, u8) {
    assert!(x != 0);
    assert!(x < 32);
    let imm = x & 0b11;
    let xmm_register = x >> 2;
    assert!(xmm_register < RV_REGISTERS_NUM_XMMS);

    (xmm_register, imm)
}

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

            ; mov rax, QWORD print_registers as _
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
            ; cmp r9, TRACE_CHUNK_LEN as _
            ; jl >skip
            ; mov [rdi + (TraceChunk::LEN_OFFSET as i32)], r9 // save length
            ;; machine_state_store_pc!($ops, rsp, $pc)
            ; mov rdx, rsp // machine state
            ; call ->trace_buffer_full
            ; skip:
        );
    };
}

fn record_circuit_type(ops: &mut x64::Assembler, circuit_type: CounterType, by: u16) {
    assert!(by > 0);
    let x = circuit_type as u8;

    if by == 1 {
        dynasm!(ops
            ; inc QWORD [rsp + 8 * (x as i32) + (MachineState::COUNTERS_OFFSET as i32)]
        );
    } else {
        dynasm!(ops
            ; add QWORD [rsp + 8 * (x as i32) + (MachineState::COUNTERS_OFFSET as i32)], by as i32
        );
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
    pub fn preprocess_bytecode(program: &[u32], cycles_bound: Option<u32>) -> Self {
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
            ; mov r8, INITIAL_TIMESTAMP as _
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
            let raw_instruction = program[i];
            let pc = i as u32 * 4;

            dynasm!(ops
                ; => instruction_labels[i]
            );
            jump_offsets[i] = ops.offset().0;
            initialized_jump_offsets.insert(i);

            // NOTE: MOP instructions are not supported here, so we will have to handle them beforehand

            if let Some(cycles_bound) = cycles_bound {
                let ts_bound = (cycles_bound as u64) * TIMESTAMP_STEP + INITIAL_TIMESTAMP;
                // Early exit uses RAX, but we are before any instruction, so we are ok
                emit_early_exit!(ops, pc, ts_bound);
            }

            // print_registers!(ops, pc, raw_instruction);

            {
                use crate::ir::instructions::*;
                use crate::ir::*;

                const MOP_FUNCT7_TEST: u8 = 0b1000001u8;
                const ZIMOP_FUNCT3: u8 = 0b100;

                let rd = get_rd_bits(raw_instruction);
                let formal_rs1 = get_formal_rs1_bits(raw_instruction);
                let formal_rs2 = get_formal_rs2_bits(raw_instruction);
                let op = get_opcode_bits(raw_instruction);
                let funct3 = funct3_bits(raw_instruction);
                let funct7 = funct7_bits(raw_instruction);
                if op == OPCODE_SYSTEM {
                    if funct3 == ZIMOP_FUNCT3 {
                        if funct7 & MOP_FUNCT7_TEST == MOP_FUNCT7_TEST {
                            let mop_number = ((funct7 & 0b110) >> 1) | ((funct7 & 0b100000) >> 5);
                            assert!(rd != 0);
                            assert!(formal_rs1 != 0);
                            let out = destination_gpr(rd as u32); // either register or EAX
                                                                  // NOTE: we consider inputs as non-reduced and need to output fully reduced. We are mod p = 2^31 - 1,
                                                                  // so handy relations are 2^31 == 1 and 2^32 == 2.

                            match mop_number {
                                0 => {
                                    touch_register_and_increment_timestamp!(ops, formal_rs1);
                                    touch_register_and_increment_timestamp!(ops, formal_rs2);

                                    // here we will want to special-case a variant when we have rs2 == 0 as it's heavily used in the verifier
                                    if formal_rs2 == 0 {
                                        // Our purpose is to fully reduce. Max input value is 2^32 - 1, that is 2*p + 1, so we need to subtract at most 2 moduluses.
                                        // Ideally we should reduce data dependencies, but it's not like we can do much
                                        load_into(&mut ops, formal_rs1 as u32, out);
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
                                        load_abelian_into(
                                            &mut ops,
                                            formal_rs1 as u32,
                                            formal_rs2 as u32,
                                            out,
                                            x64::Rq::RDX as u8,
                                        );
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
                                1 => {
                                    touch_register_and_increment_timestamp!(ops, formal_rs1);
                                    touch_register_and_increment_timestamp!(ops, formal_rs2);
                                    assert!(formal_rs1 != 0);
                                    assert!(formal_rs2 != 0);

                                    // same logic as with addition
                                    load_into(&mut ops, formal_rs2 as u32, x64::Rq::RDX as u8);
                                    load_into(&mut ops, formal_rs1 as u32, out);
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
                                2 => {
                                    touch_register_and_increment_timestamp!(ops, formal_rs1);
                                    touch_register_and_increment_timestamp!(ops, formal_rs2);

                                    assert!(formal_rs1 != 0);
                                    assert!(formal_rs2 != 0);

                                    // if pc == 0x0015db60 {
                                    //     dynasm!(ops
                                    //         ; int 3
                                    //     );
                                    // }

                                    // same logic as with addition
                                    load_abelian_into(
                                        &mut ops,
                                        formal_rs1 as u32,
                                        formal_rs2 as u32,
                                        out,
                                        x64::Rq::RDX as u8,
                                    );
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
                                _ => {
                                    panic!("Unknown MOP number {}", mop_number);
                                }
                            }

                            touch_register_and_bump_timestamp!(ops, rd, 2);
                            store_result(&mut ops, rd as u32);

                            i += 1;
                            continue;
                        }
                    }
                }
            }

            let Ok(instruction) = riscv_decode::decode(raw_instruction) else {
                panic!(
                    "Unknown instruction 0x{:08x} at PC = 0x{:08x}",
                    raw_instruction, pc
                );
                emit_runtime_error!(ops);
                continue;
            };

            // Pure instructions
            if matches!(
                instruction,
                Instruction::Addi(_)
                    | Instruction::Andi(_)
                    | Instruction::Ori(_)
                    | Instruction::Xori(_)
                    | Instruction::Slti(_)
                    | Instruction::Sltiu(_)
                    | Instruction::Slli(_)
                    | Instruction::Srli(_)
                    | Instruction::Srai(_)
                    | Instruction::Lui(_)
                    | Instruction::Auipc(_)
                    | Instruction::Add(_)
                    | Instruction::Sub(_)
                    | Instruction::Slt(_)
                    | Instruction::Sltu(_)
                    | Instruction::And(_)
                    | Instruction::Or(_)
                    | Instruction::Xor(_)
                    | Instruction::Sll(_)
                    | Instruction::Srl(_)
                    | Instruction::Sra(_)
                    | Instruction::Lb(_)
                    | Instruction::Lbu(_)
                    | Instruction::Lh(_)
                    | Instruction::Lhu(_)
                    | Instruction::Lw(_)
                    | Instruction::Mul(_)
                    | Instruction::Mulh(_)
                    | Instruction::Mulhu(_)
                    | Instruction::Mulhsu(_)
                    | Instruction::Div(_)
                    | Instruction::Divu(_)
                    | Instruction::Rem(_)
                    | Instruction::Remu(_)
            ) {
                let rd = (raw_instruction >> 7) & 0x1F;
                let out = destination_gpr(rd);
                // Instructions that just compute a result are NOPs if they write to x0, and formally touch x0 twice on read
                if rd == 0 {
                    println!(
                        "Skipping instuction {:?} (0x{:08x}) at PC = 0x{:08x}",
                        instruction, raw_instruction, pc
                    );
                    pre_bump_timestamp_and_touch!(ops, 2, 0);
                    bump_timestamp!(ops, 2);
                    continue;
                }

                let mut issue_snapshot = false;

                match instruction {
                    // Arithmetic
                    Instruction::Addi(parts) => {
                        let source = load(&mut ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; lea Rd(out), [Rd(source) + sign_extend::<12>(parts.imm())]
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }
                    Instruction::Andi(parts) => {
                        load_into(&mut ops, parts.rs1(), out);
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; and Rd(out), sign_extend::<12>(parts.imm())
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Ori(parts) => {
                        load_into(&mut ops, parts.rs1(), out);
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; or Rd(out), sign_extend::<12>(parts.imm())
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Xori(parts) => {
                        load_into(&mut ops, parts.rs1(), out);
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; xor Rd(out), sign_extend::<12>(parts.imm())
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Slti(parts) => {
                        let source = load(&mut ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; cmp Rd(source), sign_extend::<12>(parts.imm())
                            ; setl Rb(out)
                            ; movzx Rd(out), Rb(out)
                        );
                        record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                    }
                    Instruction::Sltiu(parts) => {
                        let source = load(&mut ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; cmp Rd(source), sign_extend::<12>(parts.imm())
                            ; setb Rb(out)
                            ; movzx Rd(out), Rb(out)
                        );
                        record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                    }
                    Instruction::Slli(parts) => {
                        load_into(&mut ops, parts.rs1(), out);
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; shl Rd(out), parts.shamt() as i8
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Srli(parts) => {
                        load_into(&mut ops, parts.rs1(), out);
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; shr Rd(out), parts.shamt() as i8
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Srai(parts) => {
                        load_into(&mut ops, parts.rs1(), out);
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, 0);
                        dynasm!(ops
                            ; sar Rd(out), parts.shamt() as i8
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Lui(parts) => {
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        bump_timestamp!(ops, 1);
                        dynasm!(ops
                            ; mov Rd(out), parts.imm() as i32
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }
                    Instruction::Auipc(parts) => {
                        pre_bump_timestamp_and_touch!(ops, 1, 0);
                        bump_timestamp!(ops, 1);
                        // NOTE: result is wrapping
                        dynasm!(ops
                            ; mov Rd(out), (pc.wrapping_add(parts.imm())) as i32
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }
                    Instruction::Add(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        let other = load_abelian(&mut ops, parts.rs1(), parts.rs2(), out);
                        dynasm!(ops
                            ; add Rd(out), Rd(other)
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }
                    Instruction::Sub(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);
                        load_into(&mut ops, parts.rs1(), out);
                        dynasm!(ops
                            ; sub Rd(out), Rd(SCRATCH_REGISTER)
                        );
                        record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                    }
                    Instruction::Slt(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);
                        load_into(&mut ops, parts.rs1(), out);
                        dynasm!(ops
                            ; cmp Rd(out), Rd(SCRATCH_REGISTER)
                            ; setl Rb(out)
                            ; movzx Rd(out), Rb(out)
                        );
                        record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                    }
                    Instruction::Sltu(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);
                        load_into(&mut ops, parts.rs1(), out);
                        dynasm!(ops
                            ; cmp Rd(out), Rd(SCRATCH_REGISTER)
                            ; setb Rb(out)
                            ; movzx Rd(out), Rb(out)
                        );
                        record_circuit_type(&mut ops, CounterType::BranchSlt, 1);
                    }
                    Instruction::And(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        let other = load_abelian(&mut ops, parts.rs1(), parts.rs2(), out);
                        dynasm!(ops
                            ; and Rd(out), Rd(other)
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Or(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        let other = load_abelian(&mut ops, parts.rs1(), parts.rs2(), out);
                        dynasm!(ops
                            ; or Rd(out), Rd(other)
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Xor(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        let other = load_abelian(&mut ops, parts.rs1(), parts.rs2(), out);
                        dynasm!(ops
                            ; xor Rd(out), Rd(other)
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Sll(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs2(), x64::Rq::RCX as u8);
                        load_into(&mut ops, parts.rs1(), out);
                        dynasm!(ops
                            ; and rcx, 0x1f
                            ; shl Rd(out), cl
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Srl(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs2(), x64::Rq::RCX as u8);
                        load_into(&mut ops, parts.rs1(), out);
                        dynasm!(ops
                            ; and rcx, 0x1f
                            ; shr Rd(out), cl
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }
                    Instruction::Sra(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs2(), x64::Rq::RCX as u8);
                        load_into(&mut ops, parts.rs1(), out);
                        dynasm!(ops
                            ; and rcx, 0x1f
                            ; sar Rd(out), cl
                        );
                        record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                    }

                    // for subword loads we need an extra register to store word index. We have RDX "empty"
                    // after loading the address. And we need one more register to store timestamp - for that we will push RBP

                    // Loads
                    Instruction::Lb(parts) => {
                        let address = load(&mut ops, parts.rs1());
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                            // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                            // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        dynasm!(ops
                            ; movsx Rd(out), BYTE [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, sign-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; push rbp
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
                            ; pop rbp
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Instruction::Lbu(parts) => {
                        let address = load(&mut ops, parts.rs1());
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                            // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                            // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        dynasm!(ops
                            ; movzx Rd(out), BYTE [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, zero-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; push rbp
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
                            ; pop rbp
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Instruction::Lh(parts) => {
                        // TODO: exception on misalignment
                        let address = load(&mut ops, parts.rs1());
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                            // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                            // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        dynasm!(ops
                            ; movsx Rd(out), WORD [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, sign-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; push rbp
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
                            ; pop rbp
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Instruction::Lhu(parts) => {
                        // TODO: exception on misalignment
                        let address = load(&mut ops, parts.rs1());
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                            // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                            // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                            ; mov rdx, Rq(SCRATCH_REGISTER) // put word(!) index in to RDX
                            ; shr rdx, 2
                        );
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        dynasm!(ops
                            ; movzx Rd(out), WORD [rsi + Rq(SCRATCH_REGISTER)] // load value into destination, zero-extend
                            ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx] // load old word(!) value into scratch
                            ; push rbp
                            ; mov rbp, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // for read timestamp
                            ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8 // update timestamp
                            ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // write value into trace
                            ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rbp // write old value into trace
                            ; pop rbp
                        );
                        bump_timestamp!(ops, 1);
                        record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        issue_snapshot = true;
                    }
                    Instruction::Lw(parts) => {
                        // NOTE: here address is exactly couting in 4 bytes, so we do not need extra word counter and
                        // use RDX for bookkeeping
                        // TODO: exception on misalignment
                        let address = load(&mut ops, parts.rs1());
                        dynasm!(ops
                            ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                            // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                            // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                        );
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
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
                    Instruction::Mul(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        let other = load_abelian(&mut ops, parts.rs1(), parts.rs2(), out);
                        dynasm!(ops
                            ; imul Rd(out), Rd(other)
                        );
                        record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    Instruction::Mulh(parts) => {
                        emit_runtime_error!(ops);
                        // unimplemented!("unsupported by default");
                        // touch_register_and_increment_timestamp!(ops, parts.rs1());
                        // touch_register_and_increment_timestamp!(ops, parts.rs2());
                        // load_into(&mut ops, parts.rs1(), x64::Rq::RAX as u8);
                        // let other = load(&mut ops, parts.rs2());
                        // dynasm!(ops
                        //     ; imul Rd(other)
                        // );
                        // if out != x64::Rq::RDX as u8 {
                        //     dynasm!(ops
                        //         ; mov Rd(out), edx
                        //     );
                        // }
                        // record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    Instruction::Mulhu(parts) => {
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs1(), x64::Rq::RAX as u8);
                        let other = load(&mut ops, parts.rs2());
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
                    Instruction::Mulhsu(parts) => {
                        unimplemented!("unsupported by default");
                        // touch_register_and_increment_timestamp!(ops, parts.rs1());
                        // touch_register_and_increment_timestamp!(ops, parts.rs2());
                        // load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);
                        // load_into(&mut ops, parts.rs1(), out);
                        // dynasm!(ops
                        //     ; movsx Rq(out), Rd(out)
                        //     ; imul Rq(out), Rq(SCRATCH_REGISTER)
                        //     ; shr Rq(out), 32
                        // );
                        // record_circuit_type(&mut ops, CounterType::MulDiv, 1);
                    }
                    Instruction::Div(parts) => {
                        unimplemented!("unsupported by default");
                    }
                    Instruction::Divu(parts) => {
                        // TODO: handle exception cases
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs1(), x64::Rq::RAX as u8);
                        load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);
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
                    Instruction::Rem(parts) => {
                        unimplemented!("unsupported by default");
                    }
                    Instruction::Remu(parts) => {
                        // TODO: handle exception cases
                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());
                        load_into(&mut ops, parts.rs1(), x64::Rq::RAX as u8);
                        load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);
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
                    a @ _ => {
                        panic!("Opcode {:?} is not supported", a);
                    }
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

            match instruction {
                // Control transfer instructions
                Instruction::Jal(parts) => {
                    let rd = (raw_instruction >> 7) & 0x1F;
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

                    let offset = sign_extend::<21>(parts.imm());
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
                Instruction::Jalr(parts) => {
                    let rd = (raw_instruction >> 7) & 0x1F;
                    let out = destination_gpr(rd);
                    let offset = sign_extend::<12>(parts.imm());
                    touch_register_and_increment_timestamp!(ops, parts.rs1());
                    load_into(&mut ops, parts.rs1(), SCRATCH_REGISTER);
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
                Instruction::Beq(parts)
                | Instruction::Bne(parts)
                | Instruction::Blt(parts)
                | Instruction::Bltu(parts)
                | Instruction::Bge(parts)
                | Instruction::Bgeu(parts) => {
                    let jump_target = pc as i32 + sign_extend::<13>(parts.imm());
                    if jump_target % 4 != 0 {
                        panic!("Unaligned jump destination");
                        // emit_runtime_error!(ops);
                    } else {
                        let a = load(&mut ops, parts.rs1());
                        load_into(&mut ops, parts.rs2(), SCRATCH_REGISTER);

                        touch_register_and_increment_timestamp!(ops, parts.rs1());
                        touch_register_and_increment_timestamp!(ops, parts.rs2());

                        touch_register_and_bump_timestamp!(ops, 0, 2);
                        record_circuit_type(&mut ops, CounterType::BranchSlt, 1);

                        if let Some(&label) = instruction_labels.get((jump_target / 4) as usize) {
                            dynasm!(ops
                                ; cmp Rd(a), Rd(SCRATCH_REGISTER)
                            );
                            match instruction {
                                Instruction::Beq(_) => {
                                    dynasm!(ops
                                        ; je =>label
                                    );
                                }
                                Instruction::Bne(_) => {
                                    dynasm!(ops
                                        ; jne =>label
                                    );
                                }
                                Instruction::Blt(_) => {
                                    dynasm!(ops
                                        ; jl =>label
                                    );
                                }
                                Instruction::Bltu(_) => {
                                    dynasm!(ops
                                        ; jb =>label
                                    );
                                }
                                Instruction::Bge(_) => {
                                    dynasm!(ops
                                        ; jge =>label
                                    );
                                }
                                Instruction::Bgeu(_) => {
                                    dynasm!(ops
                                        ; jae =>label
                                    );
                                }
                                _ => unreachable!(),
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
                Instruction::Sb(parts) => {
                    let address = load(&mut ops, parts.rs1());
                    dynasm!(ops
                        ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                        // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                        // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                        ; mov rax, Rq(SCRATCH_REGISTER) // put word(!) index in to RAX
                        ; shr rax, 2
                    );
                    let value = load(&mut ops, parts.rs2());
                    // RDX is potentially taken by value, so can not use it
                    touch_register_and_increment_timestamp!(ops, parts.rs1());
                    touch_register_and_increment_timestamp!(ops, parts.rs2());
                    dynasm!(ops
                        // this sequence of operations is: read old value and timestamp, save it, write new value and timestamp
                        ; push rbp
                        ; mov ebp, DWORD [rsi + 4 * rax] // load old word(!) value into RAX
                        ; mov BYTE [rsi + Rq(SCRATCH_REGISTER)], Rb(value) // store new value - just enough bytes
                        ; push rdx
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // read timestamp
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8 // update timestamp
                        ; mov [rdi + r9 * 4], ebp // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                        ; pop rdx
                        ; pop rbp
                    );
                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                    issue_snapshot = true;
                    i += 1;
                }
                Instruction::Sh(parts) => {
                    // TODO: exception on misalignment
                    let address = load(&mut ops, parts.rs1());
                    dynasm!(ops
                        ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                        // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                        // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                        ; mov rax, Rq(SCRATCH_REGISTER) // put word(!) index in to RAX
                        ; shr rax, 2
                    );
                    let value = load(&mut ops, parts.rs2());
                    // RDX is potentially taken by value, so can not use it
                    touch_register_and_increment_timestamp!(ops, parts.rs1());
                    touch_register_and_increment_timestamp!(ops, parts.rs2());
                    dynasm!(ops
                        // this sequence of operations is: read old value and timestamp, save it, write new value and timestamp
                        ; push rbp
                        ; mov ebp, DWORD [rsi + 4 * rax] // load old word(!) value into RAX
                        ; mov WORD [rsi + Rq(SCRATCH_REGISTER)], Rw(value) // store new value - just enough bytes
                        ; push rdx
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // read timestamp
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8 // update timestamp
                        ; mov [rdi + r9 * 4], ebp // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                        ; pop rdx
                        ; pop rbp
                    );
                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                    issue_snapshot = true;
                    i += 1;
                }
                Instruction::Sw(parts) => {
                    // TODO: exception on misalignment
                    let address = load(&mut ops, parts.rs1());
                    dynasm!(ops
                        ; lea Rd(SCRATCH_REGISTER), [Rd(address) + sign_extend::<12>(parts.imm())]
                        // ; movsx Rq(SCRATCH_REGISTER), Rd(address)
                        // ; add Rq(SCRATCH_REGISTER), sign_extend::<12>(parts.imm()) // compute address, as we will need it a lot
                    );
                    let value = load(&mut ops, parts.rs2());
                    // RDX is potentially taken by value, so can not use it. But RAX is available
                    touch_register_and_increment_timestamp!(ops, parts.rs1());
                    touch_register_and_increment_timestamp!(ops, parts.rs2());
                    dynasm!(ops
                        // this sequence of operations is: read old value and timestamp, save it, write new value and timestamp
                        ; mov eax, DWORD [rsi + Rq(SCRATCH_REGISTER)] // load old value into RAX
                        ; mov DWORD [rsi + Rq(SCRATCH_REGISTER)], Rd(value) // store new value
                        ; push rdx
                        ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)] // read timestamp
                        ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)], r8 // update timestamp
                        ; mov [rdi + r9 * 4], eax // write old value into trace
                        ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx // write timestamp value into trace
                        ; pop rdx
                    );
                    bump_timestamp!(ops, 2);
                    record_circuit_type(&mut ops, CounterType::MemWord, 1);
                    issue_snapshot = true;
                    i += 1;
                }
                Instruction::Csrrw(parts) => {
                    assert!(parts.rs1() == 0 || parts.rd() == 0);
                    match parts.csr() {
                        NON_DETERMINISM_CSR => {
                            if parts.rd() != 0 {
                                let rd = (raw_instruction >> 7) & 0x1F;
                                let out = destination_gpr(rd);
                                // We want to read non-determinism value into RD
                                assert!(parts.rs1() == 0);
                                // as usual, we will stash our machine state into stack, and call external implementation
                                pre_bump_timestamp_and_touch!(ops, 1, 0);
                                dynasm!(ops
                                    ; mov rdx, rsp
                                    ;; before_call!(ops)
                                    ; push rdx
                                    ; push r9
                                    ; mov rax, QWORD Context::<I>::read_nondeterminism as _
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
                                record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                                issue_snapshot = true;
                            } else if parts.rs1() != 0 {
                                let rd = (raw_instruction >> 7) & 0x1F;
                                assert_eq!(rd, 0);

                                // // in practice we do NOT care, so just touch enough times
                                // {
                                //     touch_register_and_increment_timestamp!(ops, parts.rs1());
                                //     pre_bump_timestamp_and_touch!(ops, 1, 0);
                                //     bump_timestamp!(ops, 2);
                                //     record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                                // }

                                load_into(&mut ops, parts.rs1(), SCRATCH_REGISTER);
                                touch_register_and_increment_timestamp!(ops, parts.rs1());
                                dynasm!(ops
                                    ; mov rdx, rsp
                                    ;; before_call!(ops)
                                    ; push rdx
                                    ; push r9
                                    ; mov rax, QWORD Context::<I>::write_nondeterminism as _
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
                                record_circuit_type(&mut ops, CounterType::ShiftBinaryCsr, 1);
                            } else {
                                panic!(
                                    "CSRRW with non-determinism CSR and invalid rs1/rd combination"
                                );
                            }
                            i += 1;
                        }
                        csr => {
                            let mut cycles_taken = 0;
                            // NOTE: all the increment below happen before moving RSP
                            let function: *const () = match csr {
                                BLAKE2S_DELEGATION_CSR_REGISTER => {
                                    // we should expect 7 or 10 calls
                                    let mut num_calls = 0;
                                    for j in 1..=10 {
                                        if program[i + j] == raw_instruction {
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
                                    process_csr::<BLAKE2S_DELEGATION_CSR_REGISTER> as _
                                }
                                BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
                                    record_circuit_type(&mut ops, CounterType::BigintDelegation, 1);
                                    i += 1;
                                    cycles_taken = 1;
                                    process_csr::<BIGINT_OPS_WITH_CONTROL_CSR_REGISTER> as _
                                }
                                KECCAK_SPECIAL5_CSR_REGISTER => {
                                    // we expect exactly 649 calls for single keccak_f1600
                                    let mut num_calls = 0;
                                    for j in 1..=NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 {
                                        if program[i + j] == raw_instruction {
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
                                    process_csr::<KECCAK_SPECIAL5_CSR_REGISTER> as _
                                }
                                3072 => {
                                    assert_eq!(raw_instruction, 0xc0001073);
                                    // csrrw x0, cycle, x0 is a canonical panic
                                    emit_execution_panic!(ops, pc);
                                    i += 1;
                                    continue;
                                }
                                other_csrs @ _ => {
                                    panic!("Unknown CSR {}", other_csrs);
                                }
                            };
                            assert!(i <= program.len());

                            // NOTE: always record cycles taken before potentially sending trace
                            // outside below
                            assert!(cycles_taken <= u16::MAX as usize);
                            record_circuit_type(
                                &mut ops,
                                CounterType::ShiftBinaryCsr,
                                cycles_taken as u16,
                            );

                            // Those are markers in nature
                            assert_eq!(parts.rs1(), 0);
                            assert_eq!(parts.rd(), 0);
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
                                ; mov rax, QWORD function as _
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
                    }
                }
                opcode @ _ => {
                    panic!("Unknown opcode {:?}", opcode);
                    // emit_runtime_error!(ops);
                    // i += 1;
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
            ; mov rax, QWORD print_runtime_panic as _
            ; mov rdi, r8
            ; mov rsi, rdx
            ; call rax
        );

        dynasm!(ops
            ; ->exit_on_misaligned:
            ; mov rax, QWORD print_misaligned as _
            ; mov rdi, r8
            ; call rax
        );

        let exit_with_error_offset = ops.offset().0;
        dynasm!(ops
            ; ->exit_with_error:
            ; mov rax, QWORD print_complaint as _
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
                "Frequency is {} MHz over {} instructions (0x{:x} ns run time)",
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

        let context_ref_mut = &mut context;

        let runner = Self::preprocess_bytecode(program, cycles_bound);

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

        let runner = Self::preprocess_bytecode(program, cycles_bound);

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
    extern "sysv64" fn read_nondeterminism(&mut self) -> u32 {
        self.implementation.read_nondeterminism()
    }

    extern "sysv64" fn write_nondeterminism(&mut self, value: u32, memory: &[u32; RAM_SIZE]) {
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
    if cycle < 836694 {
        return;
    }
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
    if let Ok(opcode) = riscv_decode::decode(instruction) {
        println!("Will execute {:?}", opcode);
    } else {
        println!("Will execute some custom opcode");
    }
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
