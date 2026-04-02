use non_determinism_source::CSRBasedSource;
use riscv_common::zksync_os_finish_success;
use verifier_common::gkr::GKRVerificationError;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

unsafe fn workload() -> ! {
    match generated_gkr::verify::<CSRBasedSource>() {
        Ok(()) => {
            zksync_os_finish_success(&[1, 0, 0, 0, 0, 0, 0, 0]);
        }
        Err(e) => match e {
            generated_gkr::VerificationError::Gkr(gkr_err) => match gkr_err {
                GKRVerificationError::SumcheckRoundFailed { layer, round } => {
                    zksync_os_finish_success(&[
                        0xDEAD, 1, layer as u32, round as u32, 0, 0, 0, 0,
                    ]);
                }
                GKRVerificationError::FinalStepCheckFailed { layer } => {
                    zksync_os_finish_success(&[0xDEAD, 2, layer as u32, 0, 0, 0, 0, 0]);
                }
                GKRVerificationError::CacheRelationFailed { layer } => {
                    zksync_os_finish_success(&[0xDEAD, 4, layer as u32, 0, 0, 0, 0, 0]);
                }
            },
            generated_gkr::VerificationError::Whir(_) => {
                zksync_os_finish_success(&[0xDEAD, 3, 0, 0, 0, 0, 0, 0]);
            }
        },
    }
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
