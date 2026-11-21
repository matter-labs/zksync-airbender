use non_determinism_source::CSRBasedSource;
#[cfg(not(feature = "zk_masking_exit"))]
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
    let external_challenges = ::verifier_common::read_external_challenges::<_, _, CSRBasedSource>(&mut CSRBasedSource);
    let Ok(..) = generated_gkr::verify::<CSRBasedSource, PanicErrorCreator>(&external_challenges, &mut CSRBasedSource);
    #[cfg(not(feature = "zk_masking_exit"))]
    zksync_os_finish_success(&[1, 0, 0, 0, 0, 0, 0, 0]);
    // a per-circuit verifier has no recursion counters: fixed values that the host test checks
    #[cfg(feature = "zk_masking_exit")]
    riscv_common::finish_execution_recursion_extended(
        &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        &[0x11, 0x22, 0x33],
    );
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
