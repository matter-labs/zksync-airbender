pub const BLAKE2S_MAX_ROUNDS: usize = 10;
pub const BLAKE2S_NUM_CONTROL_BITS: usize = 3;

pub const BLAKE2S_DELEGATION_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 7;
// pub const BLAKE2S_DELEGATION_CSR_INVOCATION_STR: &str =
//     const_format::concatcp!("csrrw x0, ", BLAKE2S_DELEGATION_CSR_REGISTER, ", x0");

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn blake2s_csr_trigger_delegation(
    states_ptr: *mut u32,
    input_ptr: *const u32,
    round_mask: u32,
    control_mask: u32,
) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7C7, x0",
            in("x10") states_ptr.addr(),
            in("x11") input_ptr.addr(),
            in("x12") round_mask,
            in("x13") control_mask,
            options(nostack, preserves_flags)
        )
    }
}

pub const BLAKE2S_NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER: u32 = 0b000;
pub const BLAKE2S_NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER: u32 = 0b001;
pub const BLAKE2S_COMPRESSION_MODE_FIRST_ROUNDS_BASE_CONTROL_REGISTER: u32 = 0b100;
pub const BLAKE2S_COMPRESSION_MODE_LAST_ROUND_EXTRA_BITS: u32 = 0b001;
pub const BLAKE2S_COMPRESSION_MODE_IS_RIGHT_EXTRA_BITS: u32 = 0b010;

pub const BLAKE2S_X10_NUM_WRITES: usize = 8 + 16;
pub const BLAKE2S_X11_NUM_READS: usize = 16;

pub const BLAKE2S_TOTAL_RAM_ACCESSES: usize = BLAKE2S_X10_NUM_WRITES + BLAKE2S_X11_NUM_READS;
pub const BLAKE2S_BASE_ABI_REGISTER: u32 = 10;
