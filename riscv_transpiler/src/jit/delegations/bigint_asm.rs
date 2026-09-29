//! The bigint delegation as a routine in the JIT's own code, in place of a call into
//! `bigint_implementation`.
//!
//! A bigint delegation is one cycle that stands for a 256-bit operation and 17 trace elements,
//! and delegation-heavy programs run tens of millions of them. Called as a Rust function, each
//! one pays for a spill and a reload of the whole machine state around the call, for an
//! element-by-element trace append, and for a generic big integer routine. The routine below
//! works on the machine state where the JIT keeps it:
//!
//! - it is entered with `call ->bigint_delegation` and uses the JIT's own register assignment:
//!   `r10d`/`r11d`/`r12d` are `a0`/`a1`/`a2` (the pointer to `a`, the pointer to `b`, the control
//!   mask), `rsi` the memory holder, `rdi` the trace chunk, `r8` the timestamp (already the
//!   cycle's base + 3, the write timestamp), `r9` the trace length;
//! - it clobbers only the JIT's scratch registers (`rax`, `rcx`, `rdx`, `xmm6`, `xmm7`,
//!   `xmm13..=xmm15`); the multiplications borrow four more general purpose registers with
//!   `push`/`pop`. Nothing is spilled or reloaded;
//! - the operation is selected by a jump through a table of the control bits;
//! - additions and subtractions are `adc`/`sbb` chains on the operands in memory, the
//!   multiplications a `mulx`/`adcx`/`adox` schoolbook product (BMI2 and ADX).
//!
//! The effects are those of `bigint_implementation`, which stays the reference (and the
//! fallback for processors without BMI2/ADX, or on request with the environment variable
//! `RISCV_JIT_BIGINT_HANDLER=rust`): the words of `b`, then of `a`, go to the trace with their
//! previous timestamps, the timestamps of those words and of `a0`/`a1`/`a2` become the write
//! timestamp, `a` receives the result, `a2` and the 17-th trace element the overflow flag.

use super::*;
use dynasmrt::{dynasm, x64, DynasmApi, DynasmLabelApi};

/// Whether the JIT emits the routine instead of calls into `bigint_implementation`: it does by
/// default, on every processor with BMI2 and ADX
pub(crate) fn bigint_asm_enabled() -> bool {
    let requested = match std::env::var("RISCV_JIT_BIGINT_HANDLER") {
        Ok(value) if value == "rust" => false,
        Ok(value) if value == "asm" => true,
        Ok(value) => panic!("RISCV_JIT_BIGINT_HANDLER must be 'asm' or 'rust' (got {value:?})"),
        Err(_) => true,
    };
    requested
        && std::arch::is_x86_feature_detected!("bmi2")
        && std::arch::is_x86_feature_detected!("adx")
}

/// The end of the routine for operands or a control mask that `bigint_implementation` rejects
/// with an assertion
extern "sysv64" fn bigint_delegation_bad_input(a_ptr: u64, b_ptr: u64, control_mask: u64) {
    panic!(
        "bigint delegation with invalid inputs: a at 0x{a_ptr:08x}, b at 0x{b_ptr:08x} (both must be \
         32-byte aligned, distinct, above ROM and inside RAM), control mask 0b{control_mask:b} \
         (one operation bit, optionally the carry bit)"
    );
}

const A0: i32 = 0;
const WORD_BYTES: i32 = 32;
const TRACE_ELEMENTS: i32 = 17;

/// `rax = ` the address of the timestamps of the memory words at the guest address in `pointer`
/// (`r10` or `r11`)
fn emit_timestamps_address(ops: &mut x64::Assembler, ram_config: JitRunnerRam, pointer: u8) {
    let offset = ram_config.timestamps_offset();
    if offset > (1 << 30) {
        dynasm!(ops
            ; .arch x64
            ; lea rax, [rsi + 2 * Rq(pointer)]
            ; add rax, [->timestamps_offset_constant_label]
        );
    } else {
        dynasm!(ops
            ; .arch x64
            ; lea rax, [rsi + 2 * Rq(pointer) + (offset as i32)]
        );
    }
}

/// The 8 words of the operand at the guest address in `pointer` go to the trace at element
/// `position` with their timestamps, which become the write timestamp (in both lanes of
/// `xmm15`)
fn emit_operand_bookkeeping(
    ops: &mut x64::Assembler,
    ram_config: JitRunnerRam,
    pointer: u8,
    position: i32,
) {
    let timestamps = TraceChunk::TIMESTAMPS_OFFSET as i32 + 8 * position;
    dynasm!(ops
        ; .arch x64
        ; movdqu xmm6, [rsi + Rq(pointer)]
        ; movdqu xmm7, [rsi + Rq(pointer) + 16]
        ; movdqu [rdi + r9 * 4 + (4 * position)], xmm6
        ; movdqu [rdi + r9 * 4 + (4 * position + 16)], xmm7
    );
    emit_timestamps_address(ops, ram_config, pointer);
    dynasm!(ops
        ; .arch x64
        ; movdqu xmm6, [rax]
        ; movdqu xmm7, [rax + 16]
        ; movdqu xmm13, [rax + 32]
        ; movdqu xmm14, [rax + 48]
        ; movdqu [rdi + r9 * 8 + timestamps], xmm6
        ; movdqu [rdi + r9 * 8 + (timestamps + 16)], xmm7
        ; movdqu [rdi + r9 * 8 + (timestamps + 32)], xmm13
        ; movdqu [rdi + r9 * 8 + (timestamps + 48)], xmm14
        ; movdqu [rax], xmm15
        ; movdqu [rax + 16], xmm15
        ; movdqu [rax + 32], xmm15
        ; movdqu [rax + 48], xmm15
    );
}

/// `a = a op b op carry` limb by limb, for `op` one of `adc`/`sbb` (`reversed`: `a = b - a -
/// borrow`), then `a2 = ` the carry or borrow out
fn emit_carry_chain(ops: &mut x64::Assembler, subtract: bool, reversed: bool) {
    // the carry flag is the carry bit of the mask; `mov` leaves the flags alone
    dynasm!(ops ; .arch x64 ; bt r12d, CARRY_BIT_IDX as i8);
    for limb in 0..4 {
        let at = 8 * limb;
        match (subtract, reversed) {
            (false, _) => dynasm!(ops
                ; .arch x64
                ; mov rax, [rsi + r10 + at]
                ; adc rax, [rsi + r11 + at]
                ; mov [rsi + r10 + at], rax
            ),
            (true, false) => dynasm!(ops
                ; .arch x64
                ; mov rax, [rsi + r10 + at]
                ; sbb rax, [rsi + r11 + at]
                ; mov [rsi + r10 + at], rax
            ),
            (true, true) => dynasm!(ops
                ; .arch x64
                ; mov rax, [rsi + r11 + at]
                ; sbb rax, [rsi + r10 + at]
                ; mov [rsi + r10 + at], rax
            ),
        }
    }
    dynasm!(ops
        ; .arch x64
        ; setc r12b
        ; movzx r12d, r12b
        ; jmp ->bigint_done
    );
}

/// The 512-bit product `a * b` by rows of `mulx` with the two carry chains of `adcx`/`adox`,
/// then either half of it into `a`: the low half with the "high half is not zero" flag in
/// `a2`, or the high half with a zero flag
fn emit_product(ops: &mut x64::Assembler, low_half: bool) {
    use x64::Rq::*;
    // the five limbs in flight, rotating by one per row; two more registers for a partial
    // product. `r12` (the mask) is free by now, the others are restored at the end
    let mut window = [RAX as u8, RCX as u8, RBX as u8, RBP as u8, R13 as u8];
    let (low, high) = (R14 as u8, R12 as u8);
    dynasm!(ops
        ; .arch x64
        ; push rbx
        ; push rbp
        ; push r13
        ; push r14
    );
    if low_half {
        // the low limbs wait here until the last row has read `a`
        dynasm!(ops ; .arch x64 ; sub rsp, WORD_BYTES);
    }

    // the first row has one carry chain
    dynasm!(ops
        ; .arch x64
        ; mov rdx, [rsi + r11]
        ; mulx Rq(window[1]), Rq(window[0]), [rsi + r10]
        ; mulx Rq(window[2]), Rq(low), [rsi + r10 + 8]
        ; add Rq(window[1]), Rq(low)
        ; mulx Rq(window[3]), Rq(low), [rsi + r10 + 16]
        ; adc Rq(window[2]), Rq(low)
        ; mulx Rq(window[4]), Rq(low), [rsi + r10 + 24]
        ; adc Rq(window[3]), Rq(low)
        ; adc Rq(window[4]), 0
    );
    for row in 1..4 {
        // window[0] is a limb of the result; its register becomes the new top limb
        if low_half {
            dynasm!(ops ; .arch x64 ; mov [rsp + 8 * (row - 1)], Rq(window[0]));
        }
        window.rotate_left(1);
        let top = window[4];
        dynasm!(ops
            ; .arch x64
            ; mov rdx, [rsi + r11 + 8 * row]
            // the top limb starts at zero, and both carry flags are cleared
            ; xor Rd(top), Rd(top)
            ; mulx Rq(high), Rq(low), [rsi + r10]
            ; adcx Rq(window[0]), Rq(low)
            ; adox Rq(window[1]), Rq(high)
            ; mulx Rq(high), Rq(low), [rsi + r10 + 8]
            ; adcx Rq(window[1]), Rq(low)
            ; adox Rq(window[2]), Rq(high)
            ; mulx Rq(high), Rq(low), [rsi + r10 + 16]
            ; adcx Rq(window[2]), Rq(low)
            ; adox Rq(window[3]), Rq(high)
            ; mulx Rq(high), Rq(low), [rsi + r10 + 24]
            ; adcx Rq(window[3]), Rq(low)
            // the top limb is below 2^64 - 1 after this, so the two additions into it do not
            // carry out
            ; adox Rq(top), Rq(high)
            ; mov Rd(low), 0
            ; adcx Rq(top), Rq(low)
        );
    }
    // window[0] is the limb 3 of the product, window[1..5] its high half
    if low_half {
        dynasm!(ops
            ; .arch x64
            ; mov [rsi + r10 + 24], Rq(window[0])
            ; mov Rq(low), [rsp]
            ; mov Rq(high), [rsp + 8]
            ; mov [rsi + r10], Rq(low)
            ; mov [rsi + r10 + 8], Rq(high)
            ; mov Rq(low), [rsp + 16]
            ; mov [rsi + r10 + 16], Rq(low)
            ; or Rq(window[1]), Rq(window[2])
            ; or Rq(window[3]), Rq(window[4])
            ; xor r12d, r12d
            ; or Rq(window[1]), Rq(window[3])
            ; setne r12b
            ; add rsp, WORD_BYTES
        );
    } else {
        dynasm!(ops
            ; .arch x64
            ; mov [rsi + r10], Rq(window[1])
            ; mov [rsi + r10 + 8], Rq(window[2])
            ; mov [rsi + r10 + 16], Rq(window[3])
            ; mov [rsi + r10 + 24], Rq(window[4])
            ; xor r12d, r12d
        );
    }
    dynasm!(ops
        ; .arch x64
        ; pop r14
        ; pop r13
        ; pop rbp
        ; pop rbx
        ; jmp ->bigint_done
    );
}

/// Emits the routine `->bigint_delegation` (see the module documentation) for the memory layout
/// of `ram_config`. With the largest memory it refers to
/// `->timestamps_offset_constant_label`.
pub(crate) fn emit_bigint_delegation_routine(ops: &mut x64::Assembler, ram_config: JitRunnerRam) {
    // the machine state is on the stack, above the return address
    let register_timestamps = (8 + MachineState::REGISTER_TIMESTAMPS_OFFSET) as i32;
    let rom_end = common_constants::rom::ROM_BYTE_SIZE as i32;
    let last_operand = (ram_config.ram_size() - WORD_BYTES as usize) as u32;
    let operation_bits = ((1u32 << BIGINT_NUM_CONTROL_BITS) - 1) & !(1 << CARRY_BIT_IDX);
    let (a, b) = (x64::Rq::R10 as u8, x64::Rq::R11 as u8);

    dynasm!(ops
        ; .arch x64
        ; .align 16
        ; ->bigint_delegation:
        // the operands: 32-byte aligned, above ROM, inside RAM, distinct
        ; mov eax, r10d
        ; or eax, r11d
        ; test eax, WORD_BYTES - 1
        ; jnz ->bigint_bad_input
        ; cmp r10d, rom_end
        ; jb ->bigint_bad_input
        ; cmp r11d, rom_end
        ; jb ->bigint_bad_input
        ; cmp r10d, last_operand as i32
        ; ja ->bigint_bad_input
        ; cmp r11d, last_operand as i32
        ; ja ->bigint_bad_input
        ; cmp r10d, r11d
        ; je ->bigint_bad_input
        // the control mask: one operation bit, and nothing above the control bits
        ; cmp r12d, 1 << BIGINT_NUM_CONTROL_BITS
        ; jae ->bigint_bad_input
        ; mov edx, r12d
        ; and edx, operation_bits as i32
        ; jz ->bigint_bad_input
        ; lea eax, [rdx - 1]
        ; test eax, edx
        ; jnz ->bigint_bad_input
        // the index of the operation, kept in `rdx` until the dispatch
        ; tzcnt edx, edx

        // the registers of the call are written at the write timestamp
        ; mov [rsp + (register_timestamps + 8 * 10)], r8
        ; mov [rsp + (register_timestamps + 8 * 11)], r8
        ; mov [rsp + (register_timestamps + 8 * 12)], r8
        ; movq xmm15, r8
        ; punpcklqdq xmm15, xmm15
    );
    // `b` is read first, then `a`
    emit_operand_bookkeeping(ops, ram_config, b, A0);
    emit_operand_bookkeeping(ops, ram_config, a, 8);
    dynasm!(ops
        ; .arch x64
        // the last element is the flag, written at the end; it has no timestamp
        ; add r9, TRACE_ELEMENTS
        ; mov QWORD [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32 - 8)], 0
        // dispatch: the table has an 8-byte slot per control bit
        ; lea rax, [->bigint_operations]
        ; lea rax, [rax + rdx * 8]
        ; jmp rax

        ; .align 8
        ; ->bigint_operations:
        ; jmp ->bigint_add
        ; .align 8
        ; jmp ->bigint_sub
        ; .align 8
        ; jmp ->bigint_sub_and_negate
        ; .align 8
        ; jmp ->bigint_mul_low
        ; .align 8
        ; jmp ->bigint_mul_high
        ; .align 8
        ; jmp ->bigint_eq
        ; .align 8
        // the carry bit is not an operation (and is masked out of the index)
        ; jmp ->bigint_bad_input
        ; .align 8
        ; jmp ->bigint_memcopy
        ; .align 8

        ; ->bigint_done:
        ; mov [rdi + r9 * 4 - 4], r12d
        ; ret
    );
    const {
        assert!(ADD_OP_BIT_IDX == 0);
        assert!(SUB_OP_BIT_IDX == 1);
        assert!(SUB_AND_NEGATE_OP_BIT_IDX == 2);
        assert!(MUL_LOW_OP_BIT_IDX == 3);
        assert!(MUL_HIGH_OP_BIT_IDX == 4);
        assert!(EQ_OP_BIT_IDX == 5);
        assert!(CARRY_BIT_IDX == 6);
        assert!(MEMCOPY_BIT_IDX == 7);
        assert!(BIGINT_NUM_CONTROL_BITS == 8);
    }

    dynasm!(ops ; .arch x64 ; ->bigint_add:);
    emit_carry_chain(ops, false, false);
    dynasm!(ops ; .arch x64 ; ->bigint_sub:);
    emit_carry_chain(ops, true, false);
    dynasm!(ops ; .arch x64 ; ->bigint_sub_and_negate:);
    emit_carry_chain(ops, true, true);
    dynasm!(ops ; .arch x64 ; ->bigint_mul_low:);
    emit_product(ops, true);
    dynasm!(ops ; .arch x64 ; ->bigint_mul_high:);
    emit_product(ops, false);

    dynasm!(ops
        ; .arch x64
        // `a` stays, the flag is the equality
        ; ->bigint_eq:
        ; mov rax, [rsi + r10]
        ; mov rcx, [rsi + r10 + 8]
        ; xor rax, [rsi + r11]
        ; xor rcx, [rsi + r11 + 8]
        ; or rax, rcx
        ; mov rcx, [rsi + r10 + 16]
        ; mov rdx, [rsi + r10 + 24]
        ; xor rcx, [rsi + r11 + 16]
        ; xor rdx, [rsi + r11 + 24]
        ; or rcx, rdx
        ; xor r12d, r12d
        ; or rax, rcx
        ; sete r12b
        ; jmp ->bigint_done

        // `a = b + carry`, the flag is the carry out
        ; ->bigint_memcopy:
        ; bt r12d, CARRY_BIT_IDX as i8
        ; mov rax, [rsi + r11]
        ; adc rax, 0
        ; mov [rsi + r10], rax
        ; mov rax, [rsi + r11 + 8]
        ; adc rax, 0
        ; mov [rsi + r10 + 8], rax
        ; mov rax, [rsi + r11 + 16]
        ; adc rax, 0
        ; mov [rsi + r10 + 16], rax
        ; mov rax, [rsi + r11 + 24]
        ; adc rax, 0
        ; mov [rsi + r10 + 24], rax
        ; setc r12b
        ; movzx r12d, r12b
        ; jmp ->bigint_done

        // does not return: the stack is only aligned for the call
        ; ->bigint_bad_input:
        ; mov edi, r10d
        ; mov esi, r11d
        ; mov edx, r12d
        ; and rsp, -16
        ; mov rax, QWORD (bigint_delegation_bad_input as *const ()).addr() as usize as isize as i64
        ; call rax
        ; ud2
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::offset_of;
    use ruint::aliases::U256;

    const GPR_CANARIES: usize = 5;
    // xmm0..=xmm5 hold registers, xmm8..=xmm12 counters
    const XMM_CANARIES: [u8; 11] = [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12];

    /// The registers the routine is entered with, and what it leaves in them
    #[repr(C)]
    #[derive(Default)]
    struct Call {
        trace: u64,
        memory: u64,
        timestamp: u64,
        len: u64,
        a: u64,
        b: u64,
        mask: u64,
        gprs_in: [u64; GPR_CANARIES],
        xmms_in: [[u64; 2]; XMM_CANARIES.len()],
        // a2, the trace length, the timestamp, a0, a1, the trace and the memory pointers
        out: [u64; 7],
        gprs_out: [u64; GPR_CANARIES],
        xmms_out: [[u64; 2]; XMM_CANARIES.len()],
        register_timestamps: [u64; 3],
    }

    /// A function that enters the routine with the registers of a `Call`: the JIT's state
    /// registers hold the call's inputs and canaries, the stack a machine state's worth of room
    fn harness(ram_config: JitRunnerRam) -> (dynasmrt::ExecutableBuffer, dynasmrt::AssemblyOffset) {
        use x64::Rq::*;
        let mut ops = x64::Assembler::new().unwrap();
        let start = ops.offset();
        let timestamps = MachineState::REGISTER_TIMESTAMPS_OFFSET as i32;
        let frame = (MachineState::REGISTER_TIMESTAMPS_OFFSET + 8 * 32).next_multiple_of(16) as i32;
        let canaries = [RBX, RBP, R13, R14, R15];
        dynasm!(ops
            ; .arch x64
            ; push rbp
            ; push rbx
            ; push r12
            ; push r13
            ; push r14
            ; push r15
            ; push rdi
            ; sub rsp, frame
            ; mov rax, rdi
            ; mov QWORD [rsp + (timestamps + 8 * 10)], 0
            ; mov QWORD [rsp + (timestamps + 8 * 11)], 0
            ; mov QWORD [rsp + (timestamps + 8 * 12)], 0
        );
        for (i, register) in canaries.into_iter().enumerate() {
            let at = (offset_of!(Call, gprs_in) + 8 * i) as i32;
            dynasm!(ops ; .arch x64 ; mov Rq(register as u8), [rax + at]);
        }
        for (i, register) in XMM_CANARIES.into_iter().enumerate() {
            let at = (offset_of!(Call, xmms_in) + 16 * i) as i32;
            dynasm!(ops ; .arch x64 ; movdqu Rx(register), [rax + at]);
        }
        dynasm!(ops
            ; .arch x64
            ; mov rdi, [rax + offset_of!(Call, trace) as i32]
            ; mov rsi, [rax + offset_of!(Call, memory) as i32]
            ; mov r8, [rax + offset_of!(Call, timestamp) as i32]
            ; mov r9, [rax + offset_of!(Call, len) as i32]
            ; mov r10, [rax + offset_of!(Call, a) as i32]
            ; mov r11, [rax + offset_of!(Call, b) as i32]
            ; mov r12, [rax + offset_of!(Call, mask) as i32]
            ; call ->bigint_delegation
            ; mov rax, [rsp + frame]
        );
        for (i, register) in [R12, R9, R8, R10, R11, RDI, RSI].into_iter().enumerate() {
            let at = (offset_of!(Call, out) + 8 * i) as i32;
            dynasm!(ops ; .arch x64 ; mov [rax + at], Rq(register as u8));
        }
        for (i, register) in canaries.into_iter().enumerate() {
            let at = (offset_of!(Call, gprs_out) + 8 * i) as i32;
            dynasm!(ops ; .arch x64 ; mov [rax + at], Rq(register as u8));
        }
        for (i, register) in XMM_CANARIES.into_iter().enumerate() {
            let at = (offset_of!(Call, xmms_out) + 16 * i) as i32;
            dynasm!(ops ; .arch x64 ; movdqu [rax + at], Rx(register));
        }
        for i in 0..3 {
            let at = (offset_of!(Call, register_timestamps) + 8 * i) as i32;
            dynasm!(ops
                ; .arch x64
                ; mov rcx, [rsp + (timestamps + 8 * (10 + i as i32))]
                ; mov [rax + at], rcx
            );
        }
        dynasm!(ops
            ; .arch x64
            ; add rsp, frame
            ; pop rax
            ; pop r15
            ; pop r14
            ; pop r13
            ; pop r12
            ; pop rbx
            ; pop rbp
            ; ret
        );
        emit_bigint_delegation_routine(&mut ops, ram_config);
        (ops.finalize().unwrap(), start)
    }

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        /// A limb that is often all zeroes, all ones, or near them
        fn limb(&mut self) -> u64 {
            match self.next() % 8 {
                0 => 0,
                1 => u64::MAX,
                2 => 1,
                3 => u64::MAX - 1,
                4 => 1 << 63,
                _ => self.next(),
            }
        }

        fn operand(&mut self) -> [u64; 4] {
            core::array::from_fn(|_| self.limb())
        }
    }

    /// What one delegation changes: `a`, the timestamps of both operands, the trace elements
    /// and its length, `a2` and the timestamps of the registers of the call
    #[derive(Debug, PartialEq)]
    struct Effects {
        a: [u64; 4],
        a_timestamps: [TimestampScalar; 8],
        b_timestamps: [TimestampScalar; 8],
        trace_values: [u32; 17],
        trace_timestamps: [TimestampScalar; 17],
        len: u64,
        a2: u32,
        register_timestamps: [TimestampScalar; 3],
    }

    unsafe fn words(memory: &mut MemoryHolder, pointer: u32) -> *mut [u64; 4] {
        let (values, _) = memory.memory_and_timestamps_mut();
        values.as_mut_ptr().add(pointer as usize / 4).cast()
    }

    unsafe fn timestamps(memory: &mut MemoryHolder, pointer: u32) -> *mut [TimestampScalar; 8] {
        let (_, timestamps) = memory.memory_and_timestamps_mut();
        timestamps.as_mut_ptr().add(pointer as usize / 4).cast()
    }

    unsafe fn effects(
        memory: &mut MemoryHolder,
        trace: &TraceChunk,
        (a, b): (u32, u32),
        len: u64,
        a2: u32,
        register_timestamps: [TimestampScalar; 3],
    ) -> Effects {
        Effects {
            a: *words(memory, a),
            a_timestamps: *timestamps(memory, a),
            b_timestamps: *timestamps(memory, b),
            trace_values: core::array::from_fn(|i| trace.values[len as usize + i]),
            trace_timestamps: core::array::from_fn(|i| trace.timestamps[len as usize + i]),
            len: trace.len,
            a2,
            register_timestamps,
        }
    }

    /// The routine is what the JIT uses unless the Rust handler is asked for
    #[test]
    fn routine_is_the_default() {
        if std::env::var_os("RISCV_JIT_BIGINT_HANDLER").is_some() {
            eprintln!("RISCV_JIT_BIGINT_HANDLER is set, the default is not in effect");
            return;
        }
        assert_eq!(
            bigint_asm_enabled(),
            std::arch::is_x86_feature_detected!("bmi2")
                && std::arch::is_x86_feature_detected!("adx")
        );
    }

    /// The routine against `bigint_implementation` on the same inputs: every operation with and
    /// without the carry bit, operands with limbs at the edges, at operand addresses up to the
    /// last one of the memory and trace lengths up to the last one before a flush. The
    /// registers that hold the rest of the machine state must come back untouched.
    #[test]
    fn routine_matches_the_rust_handler() {
        if !(std::arch::is_x86_feature_detected!("bmi2")
            && std::arch::is_x86_feature_detected!("adx"))
        {
            eprintln!("no BMI2/ADX on this processor, the routine is not used");
            return;
        }
        let ram_config = JitRunnerRam::Tiny;
        let (code, start) = harness(ram_config);
        let enter: extern "sysv64" fn(*mut Call) = unsafe { core::mem::transmute(code.ptr(start)) };

        let mut memory = MemoryHolder::allocate_zeroed(ram_config, std::alloc::Global);
        let mut trace: Box<TraceChunk> = unsafe { Box::new_zeroed().assume_init() };
        let mut state = Box::new(MachineState::initial());
        state.ram_config = ram_config;
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);

        let first = common_constants::rom::ROM_BYTE_SIZE as u32;
        let last = (ram_config.ram_size() - 32) as u32;
        let operations = [
            ADD_OP_BIT_IDX,
            SUB_OP_BIT_IDX,
            SUB_AND_NEGATE_OP_BIT_IDX,
            MUL_LOW_OP_BIT_IDX,
            MUL_HIGH_OP_BIT_IDX,
            EQ_OP_BIT_IDX,
            MEMCOPY_BIT_IDX,
        ];
        let mut checked = 0usize;
        for round in 0..20_000usize {
            let operation = operations[round % operations.len()];
            let carry = (round / operations.len()) % 2 == 1;
            let mask = (1u32 << operation) | ((carry as u32) << CARRY_BIT_IDX);
            let a = match round % 5 {
                0 => first,
                1 => last,
                _ => first + 32 * (rng.next() % ((last - first) as u64 / 32)) as u32,
            };
            let b = match round % 3 {
                0 if a != last => a + 32,
                1 if a != first => a - 32,
                _ => {
                    let b = first + 32 * (rng.next() % ((last - first) as u64 / 32)) as u32;
                    if b == a {
                        if a == last {
                            a - 32
                        } else {
                            a + 32
                        }
                    } else {
                        b
                    }
                }
            };
            let len = match round % 4 {
                0 => 0,
                1 => TRACE_CHUNK_LEN as u64 - 1,
                _ => rng.next() % TRACE_CHUNK_LEN as u64,
            };
            let timestamp = INITIAL_TIMESTAMP + TIMESTAMP_STEP * (rng.next() % (1 << 40)) + 3;
            let a_value = rng.operand();
            let b_value = match round % 6 {
                0 => a_value,
                _ => rng.operand(),
            };
            let old_a_timestamps: [TimestampScalar; 8] = core::array::from_fn(|_| rng.next() >> 20);
            let old_b_timestamps: [TimestampScalar; 8] = core::array::from_fn(|_| rng.next() >> 20);

            let mut outcomes = [None, None];
            for (outcome, reference) in outcomes.iter_mut().zip([false, true]) {
                unsafe {
                    *words(&mut memory, a) = a_value;
                    *words(&mut memory, b) = b_value;
                    *timestamps(&mut memory, a) = old_a_timestamps;
                    *timestamps(&mut memory, b) = old_b_timestamps;
                    for i in 0..17 {
                        trace.values[len as usize + i] = 0xdead_beef;
                        trace.timestamps[len as usize + i] = 0xdead_beef;
                    }
                    trace.len = len;
                }
                let (a2, register_timestamps) = if reference {
                    *state.get_register_mut(10) = a;
                    *state.get_register_mut(11) = b;
                    *state.get_register_mut(12) = mask;
                    state.timestamp = timestamp;
                    state.register_timestamps = [0; 32];
                    bigint_implementation(&mut trace, &mut memory, &mut state);
                    (
                        state.get_register(12),
                        core::array::from_fn(|i| state.register_timestamps[10 + i]),
                    )
                } else {
                    let mut call = Call {
                        trace: (&mut *trace as *mut TraceChunk).addr() as u64,
                        memory: memory.as_mut_ptr().as_ptr().addr() as u64,
                        timestamp,
                        len,
                        a: a as u64,
                        b: b as u64,
                        mask: mask as u64,
                        gprs_in: core::array::from_fn(|_| rng.next()),
                        xmms_in: core::array::from_fn(|_| [rng.next(), rng.next()]),
                        ..Default::default()
                    };
                    enter(&mut call);
                    assert_eq!(
                        call.gprs_out, call.gprs_in,
                        "a register of the state changed"
                    );
                    assert_eq!(
                        call.xmms_out, call.xmms_in,
                        "a vector register of the state changed"
                    );
                    assert_eq!(
                        call.out[2..],
                        [timestamp, a as u64, b as u64, call.trace, call.memory],
                        "the timestamp, a0, a1 or a base pointer changed"
                    );
                    // the routine keeps the length in the register only
                    trace.len = call.out[1];
                    assert_eq!(call.out[0] >> 32, 0);
                    (call.out[0] as u32, call.register_timestamps)
                };
                *outcome = Some(unsafe {
                    effects(&mut memory, &trace, (a, b), len, a2, register_timestamps)
                });
                assert_eq!(unsafe { *words(&mut memory, b) }, b_value, "b changed");
            }
            let [routine, reference] = outcomes;
            assert_eq!(
                routine,
                reference,
                "mask 0b{mask:b}, a = {:?} at 0x{a:x}, b = {:?} at 0x{b:x}, trace length {len}",
                U256::from_limbs(a_value),
                U256::from_limbs(b_value),
            );
            checked += 1;
        }
        assert_eq!(checked, 20_000);
    }
}
