#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

mod test_suite;

use riscv_common::zksync_os_finish_success;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

unsafe fn workload() -> ! {
    test_suite::run_edge_case_tests();
    zksync_os_finish_success(&[0, 0, 0, 0, 0, 0, 0, 0]);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
