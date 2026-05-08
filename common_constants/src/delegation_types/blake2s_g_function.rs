pub const BLAKE2S_G_FUNCTION_NUM_CONTROL_BITS: usize = 1;
pub const BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION: usize = 8; // round function uses 8 mixing functions internally
pub const BLAKE2S_G_FUNCTION_COUNTER_BOUND: usize =
    super::BLAKE2S_MAX_ROUNDS * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
pub const BLAKE2S_G_FUNCTION_COUNTER_BITS: usize = BLAKE2S_G_FUNCTION_COUNTER_BOUND
    .next_power_of_two()
    .trailing_zeros() as usize;
pub const BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS: usize =
    BLAKE2S_G_FUNCTION_NUM_CONTROL_BITS + BLAKE2S_G_FUNCTION_COUNTER_BITS;
pub const BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 8;

// #[cfg(target_arch = "riscv32")]
// #[inline(always)]
// pub unsafe fn blake2s_g_function_csr_trigger_delegation(
//     states_ptr: *mut u32,
//     input_ptr: *const u32,
//     mut control_mask: u32,
// ) -> u32 {
//     unsafe {
//         core::arch::asm!(
//             "csrrw x0, 0x7C8, x0",
//             in("x10") states_ptr.addr(),
//             in("x11") input_ptr.addr(),
//             inlateout("x12") control_mask,
//             options(nostack, preserves_flags)
//         );
//     }
//     control_mask
// }

// ABI: feed extended state (aligned by 64) via x10, and input (aligned by 64) via x11. Use x12 for control

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn blake_g_function_csr_trigger_delegation_reduced_rounds(
    extended_state_ptr: *mut u32,
    input_ptr: *const u32,
) {
    unsafe {
        core::arch::asm!(
            "addi x12, x0, {imm}",
            // can not use seq macro here easily, will hand-copy by 8
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            in("x10") extended_state_ptr.addr(),
            in("x11") input_ptr.addr(),
            out("x12") _,
            imm = const BLAKE2S_G_FUNCTION_REDUCED_ROUNDS_INITIAL_CONTROL_REGISTER,
            options(nostack, preserves_flags)
        );
    }
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn blake_g_function_csr_trigger_delegation_full_rounds(
    extended_state_ptr: *mut u32,
    input_ptr: *const u32,
) {
    unsafe {
        core::arch::asm!(
            "addi x12, x0, {imm}",
            // can not use seq macro here easily, will hand-copy by 8
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",
            "csrrw x0, 0x7C8, x0",

            in("x10") extended_state_ptr.addr(),
            in("x11") input_ptr.addr(),
            out("x12") _,
            imm = const BLAKE2S_G_FUNCTION_FULL_ROUNDS_INITIAL_CONTROL_REGISTER,
            options(nostack, preserves_flags)
        );
    }
}

pub const NUM_BLAKE2S_G_FUNCTION_REGISTER_ACCESSES: usize = 3;
pub const NUM_BLAKE2S_G_FUNCTION_VARIABLE_OFFSETS: usize = 6;

pub const BLAKE2S_G_FUNCTION_X10_NUM_WRITES: usize = 4;
pub const BLAKE2S_G_FUNCTION_X11_NUM_READS: usize = 2;

pub const BLAKE2S_G_FUNCTION_FULL_ROUNDS_INITIAL_CONTROL_REGISTER: u32 = 0;
pub const BLAKE2S_G_FUNCTION_REDUCED_ROUNDS_INITIAL_CONTROL_REGISTER: u32 =
    1 << BLAKE2S_G_FUNCTION_COUNTER_BITS;

pub const BLAKE2S_G_FUNCTION_TOTAL_RAM_ACCESSES: usize =
    BLAKE2S_G_FUNCTION_X10_NUM_WRITES + BLAKE2S_G_FUNCTION_X11_NUM_READS;
pub const BLAKE2S_G_FUNCTION_BASE_ABI_REGISTER: u32 = 10;
