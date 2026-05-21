#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]
#![no_builtins]

use riscv_common::{csr_read_word, zksync_os_finish_success};

extern "C" {
    static mut _sheap: usize;
    static mut _eheap: usize;
    static mut _sstack: usize;
    static mut _estack: usize;
}

core::arch::global_asm!(include_str!("../../scripts/asm/asm_reduced.S"));

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    unsafe { core::hint::unreachable_unchecked() }
}

#[inline(never)]
fn step(seed: u32, idx: u32) -> u32 {
    // Family 3: XOR + variable shift left + bitwise OR/AND.
    let mixed = seed ^ 0xA5A5_5A5Au32;
    let shifted = mixed << (idx & 7);
    let masked = shifted & 0x00FF_FF00u32;
    masked | (idx ^ 0x5Au32)
}

unsafe fn workload() -> ! {
    // Read two non-deterministic inputs to prevent constant folding.
    // `n` is now the unbounded RISC-V cycle target (~50 cycles/iter, so
    // n = 20_000 ≈ 1M cycles). The 16-element stack array is reused via
    // modulo indexing so n can be arbitrary.
    let n = csr_read_word();
    let seed = csr_read_word();

    // Stack-allocated array touched via volatile to force LW / SW.
    let mut arr: [u32; 16] = [0; 16];
    let arr_ptr: *mut u32 = arr.as_mut_ptr();

    let mut sum: u32 = 0;
    let mut slt_acc: u32 = 0;
    let mut sltu_acc: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        // Index modulo 16 — keeps the stack array bounded while letting
        // `i` grow unbounded for cycle padding.
        let idx16 = (i & 0xFu32) as usize;

        // Family 3 (step) + Family 4 (volatile write to stack RAM).
        let v = step(seed, i);
        core::ptr::write_volatile(arr_ptr.add(idx16), v);

        // Family 4 (volatile read).
        let r = core::ptr::read_volatile(arr_ptr.add(idx16));

        // Family 2 SLT — signed less-than as a value (forces RISC-V SLT, not branch).
        let lt_signed = ((r as i32) < (seed as i32)) as u32;
        slt_acc = slt_acc.wrapping_add(lt_signed);
        // Family 2 SLTU — unsigned less-than as a value (forces SLTU).
        let lt_unsigned = (r < seed) as u32;
        sltu_acc = sltu_acc.wrapping_add(lt_unsigned);
        // Family 2 SLTI — signed less-than against a small immediate.
        let lt_imm = ((r as i32) < 5) as u32;
        slt_acc = slt_acc.wrapping_add(lt_imm);

        // Family 2 branches — both signed and unsigned conditional flow.
        if r < 100u32 {
            sum = sum.wrapping_add(r);
        } else {
            sum = sum.wrapping_sub(r);
        }
        // Family 3: arithmetic shift right + XOR.
        let signed = (r as i32) >> (i & 7);
        sum = sum ^ (signed as u32);

        i = i.wrapping_add(1);
    }

    #[cfg(any(feature = "blake2_with_compression", feature = "blake2_g_function"))]
    let blake_out = {
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();
        hasher.input_buffer.fill(0);
        hasher.input_buffer[0] = seed;
        hasher.run_round_function::<false>(1, true);
        hasher.read_state_for_output_ref()[0]
    };
    #[cfg(not(any(feature = "blake2_with_compression", feature = "blake2_g_function")))]
    let blake_out: u32 = 0;

    zksync_os_finish_success(&[sum, slt_acc, sltu_acc, n, seed, blake_out, 0, 0]);
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
