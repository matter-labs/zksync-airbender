pub const BIGINT_NUM_CONTROL_BITS: usize = 8;

pub const ADD_OP_BIT_IDX: usize = 0;
pub const SUB_OP_BIT_IDX: usize = 1;
pub const SUB_AND_NEGATE_OP_BIT_IDX: usize = 2;
pub const MUL_LOW_OP_BIT_IDX: usize = 3;
pub const MUL_HIGH_OP_BIT_IDX: usize = 4;
pub const EQ_OP_BIT_IDX: usize = 5;
pub const CARRY_BIT_IDX: usize = 6;
pub const MEMCOPY_BIT_IDX: usize = 7;

pub const BIGINT_OPS_WITH_CONTROL_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 10;
// pub const BIGINT_OPS_CSR_INVOCATION_STR: &str =
//     const_format::concatcp!("csrrw x0, ", BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, ", x0");

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn bigint_csr_trigger_delegation(
    mut_ptr: *mut u32,
    immut_ptr: *const u32,
    mask: u32,
) -> u32 {
    let mut mask = mask;
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7CA, x0",
            in("x10") mut_ptr,
            in("x11") immut_ptr,
            inlateout("x12") mask,
            options(nostack, preserves_flags)
        );
    }

    mask
}

pub const BIGINT_TOTAL_RAM_ACCESSES: usize = 8 * 2;
pub const BIGINT_BASE_ABI_REGISTER: u32 = 10;
