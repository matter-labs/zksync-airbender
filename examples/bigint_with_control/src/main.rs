#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

use common_constants::bigint_with_control::{bigint_csr_trigger_delegation, ADD_OP_BIT_IDX};
use riscv_common::zksync_os_finish_success;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[repr(C, align(32))]
struct AlignedU256 {
    words: [u32; 8],
}

unsafe fn workload() -> ! {
    // The bigint delegation ABI reads a mutable 256-bit operand from x10 and an
    // immutable one from x11. Both pointers must live in RAM and be 32-byte aligned.
    let mut accumulator = AlignedU256 {
        words: [u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0],
    };
    let addend = AlignedU256 {
        words: [1, 0, 0, 0, 0, 0, 0, 0],
    };

    // This addition overflows the low 64-bit limb and produces:
    // [0, 0, 1, 0, 0, 0, 0, 0].
    let carry = unsafe {
        bigint_csr_trigger_delegation(
            accumulator.words.as_mut_ptr(),
            addend.words.as_ptr(),
            1 << ADD_OP_BIT_IDX,
        )
    };

    zksync_os_finish_success(&[
        accumulator.words[0],
        accumulator.words[1],
        accumulator.words[2],
        carry,
        0,
        0,
        0,
        0,
    ]);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
