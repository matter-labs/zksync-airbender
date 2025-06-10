#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

use riscv_common::{csr_read_word, zksync_os_finish_success};

extern "C" {
    // Boundaries of the heap
    static mut _sheap: usize;
    static mut _eheap: usize;

    // Boundaries of the stack
    static mut _sstack: usize;
    static mut _estack: usize;

    // Boundaries of the data region - to init .data section. Yet unused
    static mut _sdata: usize;
    static mut _edata: usize;
    static mut _sidata: usize;
}

core::arch::global_asm!(include_str!("../../scripts/asm/asm_reduced.S"));

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }

    // xtvec::write(_machine_start_trap as *const () as usize, xTrapMode::Direct);
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

/// Exception (trap) handler in rust.
/// Called from the asm/asm.S
#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

#[inline(always)]
fn csr_trigger_delegation(
    states_ptr: *mut u32,
    input_ptr: *const u32,
    round_mask: u32,
    control_mask: u32,
) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7c7, x0",
            in("x10") states_ptr.addr(),
            in("x11") input_ptr.addr(),
            in("x12") round_mask,
            in("x13") control_mask,
            options(nostack, preserves_flags)
        )
    }
}

const MODULUS: u32 = 1_000_000_000;

// We have to be sure that the memory that we pass to the delegation is properly aligned.
#[repr(align(65536))]
struct Aligner;

pub const CONFIGURED_IV: [u32; 8] = [
    0x6A09E667 ^ 0x01010000 ^ 32,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
];

// Blake magic.
pub const EXTENDED_IV: [u32; 16] = [
    0x6A09E667 ^ 0x01010000 ^ 32,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
];

#[repr(C)]
struct BlakeState {
    pub _aligner: Aligner,
    pub state: [u32; 8],
    pub ext_state: [u32; 16],
    pub input_buffer: [u32; 16],
    pub round_bitmask: u32,
    pub t: u32, // we limit ourselves to <4Gb inputs
}

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

    for _i in 0..h {
        let mut state = BlakeState {
            _aligner: Aligner,
            // The order here is extremely important - as it has to match
            // the expected 'ABI' of the delegation circuit.
            // When we later call the csr_trigger_delegation, it will look at all the fields
            // below.
            state: CONFIGURED_IV,
            ext_state: EXTENDED_IV,
            input_buffer: [0u32; 16],
            round_bitmask: 0,
            t: 0,
        };

        // let's hash the n-th fibonacci number.
        // The size will be u32 - so 4 bytes.
        state.t = 4u32;

        // our data - no alignment requirements
        let mut input_buffer = [0u32; 16];
        input_buffer[0] = hashed_b;

        const NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER: u32 = 0b000;
        const NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER: u32 = 0b001;

        // This is some Blake initialization magic.
        state.ext_state[12] = state.t ^ EXTENDED_IV[12];
        state.ext_state[14] = 0xffffffff ^ EXTENDED_IV[14];

        // Now we have to call the 'precompile' - blake requires us to actually call it 10 times.
        let mut round_bitmask = 1;
        for _round_idx in 0..9 {
            // We are passing the pointer to the state, but the code inside is actually reading
            // other fields from the BlakeState too (including input_buffer and round bitmask).
            // That's why we're in the 'unsafe' block.
            csr_trigger_delegation(
                ((&mut state) as *mut BlakeState).cast::<u32>(),
                input_buffer.as_ptr(),
                round_bitmask,
                NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER,
            );
            // Every time, we're pushing the bitmask, that is used internally to figure out which round it is.
            round_bitmask <<= 1;
        }
        // final one with final xor
        csr_trigger_delegation(
            ((&mut state) as *mut BlakeState).cast::<u32>(),
            input_buffer.as_ptr(),
            round_bitmask,
            NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER,
        );

        hashed_b = state.state[0];
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
    unsafe { workload() }
}
