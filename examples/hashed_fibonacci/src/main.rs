#![no_std]
#![no_main]

use riscv_common::{csr_read_word, zksync_os_finish_success};

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

const MODULUS: u32 = 1_000_000_000;

unsafe fn workload() -> ! {
    // Read the n number from the input.
    let n = csr_read_word();
    let h = csr_read_word();
    let mut a = 1;
    let mut b = 1;
    // The actual fibonacci computation - so that we have different values to hash later.
    for _i in 0..n {
        let c = (a + b) % MODULUS;
        a = b;
        b = c;
    }

    let mut hashed_b = b;

    let mut hasher = blake2s_u32::DelegatedBlake2sState::new();

    for _i in 0..h {
        let last_round = _i == h - 1;
        hasher.input_buffer.fill(0);
        hasher.input_buffer[0] = hashed_b;

        hasher.run_round_function::<false>(1, last_round);

        hashed_b = hasher.read_state_for_output_ref()[0];
    }

    // If you want to verify the blake correctness, you have to remember about little endianness here.
    // Here's how to do it:
    // let's say that the value is 1597 (15th fibonacci number).
    // 1597 in hex is 0x63d. But in little endinaness for u32 is 3d060000
    // You can paste this value on https://emn178.github.io/online-tools/blake2s/
    // Make sure to select input encoding as hex.
    // You'll end up with a hash: 5ec9af85a33128ba97a843b6ce4de37c6f9fc09b3ff7c82a6ce2a7b528870711
    // Now first 4 bytes there are 5ec9af85 - which translates to 0x85afc95e into 2242890078
    // and this is the value that you should get in dst[0].

    // And now, we can put the part of the blake (just first element) into response.
    zksync_os_finish_success(&[b, n, hashed_b, 0, 0, 0, 0, 0]);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
