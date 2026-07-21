#![no_std]
#![no_main]
#![no_builtins]

use riscv_common::zksync_os_finish_success;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
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
