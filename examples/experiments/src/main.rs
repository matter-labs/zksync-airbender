#![no_std]
#![no_main]

use riscv_common::{zksync_os_finish_success};

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[inline(never)]
fn main() -> ! {
    use blake2s_u32::*;
    let mut state = Blake2sState::new();
    unsafe {
        state.run_round_function::<true>(0, true);
    }

    zksync_os_finish_success(state.read_state_for_output_ref())
}
