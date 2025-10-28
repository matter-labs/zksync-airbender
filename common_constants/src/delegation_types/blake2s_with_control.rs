pub const BLAKE2S_MAX_ROUNDS: usize = 10;
pub const BLAKE2S_NUM_CONTROL_BITS: usize = 3;
pub const BLAKE2S_NUM_CONTROL_REGISTER_BITS: usize = BLAKE2S_MAX_ROUNDS + BLAKE2S_NUM_CONTROL_BITS;

pub const BLAKE2S_DELEGATION_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 7;
// pub const BLAKE2S_DELEGATION_CSR_INVOCATION_STR: &str =
//     const_format::concatcp!("csrrw x0, ", BLAKE2S_DELEGATION_CSR_REGISTER, ", x0");

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn blake2s_csr_trigger_delegation(
    states_ptr: *mut u32,
    input_ptr: *const u32,
    mut control_mask: u32,
) -> u32 {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7C7, x0",
            in("x10") states_ptr.addr(),
            in("x11") input_ptr.addr(),
            inout("x12") control_mask,
            options(nostack, preserves_flags)
        );
    }
    control_mask
}

pub const NUM_BLAKE2S_REGISTER_ACCESSES: usize = 3;
pub const NUM_BLAKE2S_VARIABLE_OFFSETS: usize = 0;

pub const BLAKE2S_NORMAL_MODE_FULL_ROUNDS_INITIAL_CONTROL_REGISTER: u32 = (0b1000 | 0b000) << 16;
pub const BLAKE2S_NORMAL_MODE_REDUCED_ROUNDS_INITIAL_CONTROL_REGISTER: u32 = (0b1000 | 0b001) << 16;
pub const BLAKE2S_COMPRESSION_MODE_IS_RIGHT_EXTRA_BITS: u32 = 0b010 << 16;
pub const BLAKE2S_COMPRESSION_MODE_EXTRA_BITS: u32 = 0b100 << 16;

pub const BLAKE2S_X10_NUM_WRITES: usize = 8 + 16;
pub const BLAKE2S_X11_NUM_READS: usize = 16;

pub const BLAKE2S_TOTAL_RAM_ACCESSES: usize = BLAKE2S_X10_NUM_WRITES + BLAKE2S_X11_NUM_READS;
pub const BLAKE2S_BASE_ABI_REGISTER: u32 = 10;
