#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

use non_determinism_source::CSRBasedSource;
use riscv_common::zksync_os_finish_success;
use verifier_common::gkr::GKRVerificationError;

#[cfg(feature = "add_sub_lui_auipc_mop")]
#[path = "../../../verifier/src/generated/add_sub_lui_auipc_mop/mod.rs"]
mod generated_gkr;

#[cfg(feature = "jump_branch_slt")]
#[path = "../../../verifier/src/generated/jump_branch_slt/mod.rs"]
mod generated_gkr;

#[cfg(feature = "shift_binop")]
#[path = "../../../verifier/src/generated/shift_binop/mod.rs"]
mod generated_gkr;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

unsafe fn workload() -> ! {
    match generated_gkr::verify_all::<CSRBasedSource>() {
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
