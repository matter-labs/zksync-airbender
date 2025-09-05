pub const KECCAK5_NUM_ROUNDS: usize = 5;
pub const PRECOMPILE_MODE_NUM_CONTROL_BITS: usize = 5;
pub const ITERATION_NUM_CONTROL_BITS: usize = 5;

pub const KECCAK5_TOTAL_NUM_CONTROL_BITS: usize =
    KECCAK5_NUM_ROUNDS + PRECOMPILE_MODE_NUM_CONTROL_BITS + ITERATION_NUM_CONTROL_BITS;

pub const NUM_X10_INDIRECT_U64_WORDS: usize = 6;
pub const KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS: usize = 6;

pub const KECCAK_SPECIAL5_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 11;
// pub const KECCAK_SPECIAL5_CSR_INVOCATION_STR: &str =
//     const_format::concatcp!("csrrw x0, ", KECCAK_SPECIAL5_CSR_REGISTER, ", x0");

pub const CONTROL_INIT: u32 = 0b00000_00001_00001 << 4; // LUI skips only 12 bits not 16
pub const ROUND_CONSTANT_FINAL: u64 = 0x8000000080008008;

#[cfg(target_arch = "riscv32")]
#[macro_export]
macro_rules! keccak_special5_load_initial_control {
    () => {
        core::arch::asm!(
            "lui x10, {imm}",
            imm = const CONTROL_INIT,
            out("x10") _,
            options(nostack, preserves_flags)
        )
    };
}

#[cfg(target_arch = "riscv32")]
#[macro_export]
macro_rules! keccak_special5_invoke {
    ($state: expr) => {
        core::arch::asm!(
            "csrrw x0, 0x7CB, x0",
            in("x11") $state,
            out("x10") _,
            options(nostack, preserves_flags)
        )
    };
}

pub const KECCAK_SPECIAL5_X11_NUM_WRITES: usize = NUM_X10_INDIRECT_U64_WORDS * 2; // 6 u64 r/w
pub const KECCAK_SPECIAL5_TOTAL_RAM_ACCESSES: usize = KECCAK_SPECIAL5_X11_NUM_WRITES;
pub const KECCAK_SPECIAL5_BASE_ABI_REGISTER: u32 = 10;

pub const KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS: usize = 30;
