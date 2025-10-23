pub const PRECOMPILE_MODE_BITS: usize = 3;
pub const ITERATION_BITS: usize = 3;
pub const ROUND_BITS: usize = 5;

pub const KECCAK5_TOTAL_NUM_CONTROL_BITS: usize =
    PRECOMPILE_MODE_BITS + ITERATION_BITS + ROUND_BITS;

pub const NUM_X10_INDIRECT_U64_WORDS: usize = 6;
pub const KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS: usize = NUM_X10_INDIRECT_U64_WORDS;

pub const KECCAK_SPECIAL5_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 11;
// pub const KECCAK_SPECIAL5_CSR_INVOCATION_STR: &str =
//     const_format::concatcp!("csrrw x0, ", KECCAK_SPECIAL5_CSR_REGISTER, ", x0");

// no more need for LUI once we're modifying control in-circuit
#[cfg(target_arch = "riscv32")]
#[macro_export]
macro_rules! keccak_special5_load_initial_control {
    () => {
        core::arch::asm!(
            "add x10, x0, x0",
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

pub const KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS: usize = 31;
