use non_determinism_source::CSRBasedSource;
use riscv_common::zksync_os_finish_success_extended;
use verifier_common::errors::PanicErrorCreator;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

unsafe fn workload() -> ! {
    let Ok(regs) = full_statement_verifier::unrolled_proof_statement::verify_unrolled_base_layer::<
        CSRBasedSource,
        PanicErrorCreator,
        true,
    >(&mut CSRBasedSource);
    zksync_os_finish_success_extended(&regs);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
