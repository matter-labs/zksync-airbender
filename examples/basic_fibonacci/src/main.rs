#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]
#![no_builtins]

use riscv_common::zksync_os_finish_success;

extern "C" {
    // Boundaries of the heap
    static mut _sheap: usize;
    static mut _eheap: usize;

    // Boundaries of the stack
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

/// Exception (trap) handler in rust.
/// Called from the asm/asm.S
#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

unsafe fn workload() -> ! {
    let mut a = 1;
    let mut b = 1;
    for _i in 0..10 {
        let c = a + b;
        a = b;
        b = c;
    }
    zksync_os_finish_success(&[b, 0, 0, 0, 0, 0, 0, 0]);
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
