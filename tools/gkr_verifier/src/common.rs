use non_determinism_source::CSRBasedSource;
use riscv_common::zksync_os_finish_success;
use verifier_common::errors::PanicErrorCreator;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

unsafe fn workload() -> ! {
    // PanicErrorCreator returns Infallible, so Result<(), Infallible> is always Ok
    let Ok(()) = generated_gkr::verify::<CSRBasedSource, PanicErrorCreator>();
    zksync_os_finish_success(&[1, 0, 0, 0, 0, 0, 0, 0]);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
