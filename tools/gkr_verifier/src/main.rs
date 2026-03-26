#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

use non_determinism_source::CSRBasedSource;
use riscv_common::zksync_os_finish_success;
use verifier_common::gkr::GKRVerificationError;

#[cfg(feature = "add_sub")]
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
    let gkr_result = generated_gkr::verify_gkr_sumcheck::<CSRBasedSource>();

    match gkr_result {
        Ok(gkr_output) => {
            let mut seed = gkr_output.whir_transcript_seed;
            let whir_result =
                generated_gkr::whir::verify_initial_whir_round::<CSRBasedSource>(
                    &mut seed,
                    gkr_output.whir_batching_challenge,
                    &gkr_output.setup_cap,
                    &gkr_output.memory_cap,
                    &gkr_output.witness_cap,
                );
            match whir_result {
                Ok((mut claim, mut cap)) => {
                    let mut round_idx = 1;
                    while round_idx <= generated_gkr::whir::NUM_INTERNAL_ROUNDS {
                        match generated_gkr::whir::verify_internal_whir_round::<CSRBasedSource>(
                            &mut seed, claim, &cap, round_idx,
                        ) {
                            Ok((new_claim, new_cap)) => {
                                claim = new_claim;
                                cap = new_cap;
                            }
                            Err(_) => {
                                zksync_os_finish_success(&[
                                    0xDEAD,
                                    4,
                                    round_idx as u32,
                                    0,
                                    0,
                                    0,
                                    0,
                                    0,
                                ]);
                            }
                        }
                        round_idx += 1;
                    }
                    match generated_gkr::whir::verify_final_whir_round::<CSRBasedSource>(
                        &mut seed, claim, &cap,
                    ) {
                        Ok(_final_claim) => {
                            zksync_os_finish_success(&[1, 0, 0, 0, 0, 0, 0, 0]);
                        }
                        Err(_) => {
                            zksync_os_finish_success(&[0xDEAD, 5, 0, 0, 0, 0, 0, 0]);
                        }
                    }
                }
                Err(_) => {
                    zksync_os_finish_success(&[0xDEAD, 3, 0, 0, 0, 0, 0, 0]);
                }
            }
        }
        Err(GKRVerificationError::SumcheckRoundFailed { layer, round }) => {
            zksync_os_finish_success(&[0xDEAD, 1, layer as u32, round as u32, 0, 0, 0, 0]);
        }
        Err(GKRVerificationError::FinalStepCheckFailed { layer }) => {
            zksync_os_finish_success(&[0xDEAD, 2, layer as u32, 0, 0, 0, 0, 0]);
        }
    }
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
