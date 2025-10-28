
#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

// use primitive_types::U256;
// This example shows how to use the big int library to perform arithmetic operations on large numbers.

use riscv_common::{csr_read_word, zksync_os_finish_success};

extern "C" {
    // Boundaries of the heap
    static mut _sheap: usize;
    static mut _eheap: usize;

    // Boundaries of the stack
    static mut _sstack: usize;
    static mut _estack: usize;

    // Boundaries of the data region - to init .data section. Yet unused
    static mut _sdata: usize;
    static mut _edata: usize;
    static mut _sidata: usize;
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

    // xtvec::write(_machine_start_trap as *const () as usize, xTrapMode::Direct);
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

/// Exception (trap) handler in rust.
/// Called from the asm/asm.S
#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

#[inline(always)]
fn csr_trigger_delegation(
    input_a: *mut u32,
    input_b: *const u32,
    round_mask: &mut u32,
) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7ca, x0",
            in("x10") input_a.addr(),
            in("x11") input_b.addr(),
            inlateout("x12") *round_mask,
            options(nostack, preserves_flags)
        )
    }
}

#[repr(C)]
#[repr(align(32))]
pub struct U256(pub [u32; 8]);


const MODULUS: u32 = 1_000_000_000;


unsafe fn workload() -> ! {
    let mut a = U256([1, 2, 3, 4, 0, 0, 0, 0]);
    let b = U256([6, 1, 0, 0, 126, 0, 0, 0]);
    let mut round_mask = 1;
    csr_trigger_delegation( a.0.as_mut_ptr(), b.0.as_ptr(), &mut round_mask );


    zksync_os_finish_success(&[a.0[0], a.0[1], a.0[2], a.0[3], a.0[4], a.0[5], a.0[6], a.0[7]]);
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
