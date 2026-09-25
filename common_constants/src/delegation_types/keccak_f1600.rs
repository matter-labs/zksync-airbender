// Keccak-f1600 on keccak_special5's state layout: per round 5 column parity, 5 theta/rho and 5 chi
// calls, then one column parity call for the delayed final iota.

pub const KECCAK_THETA_RHO_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 12;
pub const KECCAK_COLUMN_PARITY_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 13;
pub const KECCAK_CHI5_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 14;

pub const KECCAK_COLUMN_PARITY_PRECOMPILE: u32 = 0;
pub const KECCAK_THETA_RHO_PRECOMPILE: u32 = 3;
pub const KECCAK_CHI5_PRECOMPILE: u32 = 5;

pub const NUM_KECCAK_F1600_CALLS_PER_ROUND: usize = 15;
pub const NUM_KECCAK_F1600_CALLS: usize = 24 * NUM_KECCAK_F1600_CALLS_PER_ROUND + 1;
pub const NUM_KECCAK_F1600_COLUMN_PARITY_CALLS: usize = 24 * 5 + 1;
pub const NUM_KECCAK_F1600_THETA_RHO_CALLS: usize = 24 * 5;
pub const NUM_KECCAK_F1600_CHI5_CALLS: usize = 24 * 5;

pub const KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS: usize = 7;
pub const KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS: usize = 6;
pub const KECCAK_CHI5_NUM_VARIABLE_OFFSETS: usize = 5;

// CSR of call `i` of one permutation
pub const fn keccak_f1600_call_csr(i: usize) -> u32 {
    if i == NUM_KECCAK_F1600_CALLS - 1 {
        return KECCAK_COLUMN_PARITY_CSR_REGISTER;
    }
    match (i % NUM_KECCAK_F1600_CALLS_PER_ROUND) / 5 {
        0 => KECCAK_COLUMN_PARITY_CSR_REGISTER,
        1 => KECCAK_THETA_RHO_CSR_REGISTER,
        _ => KECCAK_CHI5_CSR_REGISTER,
    }
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub(super) fn keccak_f1600(state: &mut super::keccak_special5::KeccakF1600State) {
    let state_ptr = state.0.as_mut_ptr();

    unsafe {
        // one asm block keeps LLVM from scheduling anything into the run, which the transpiler
        // recognizes by its first CSR and the call count
        seq_macro::seq!(_ in 0..24 {
            core::arch::asm!(
                "add x10, x0, x0",
                #(
                    "csrrw x0, {column_parity_csr}, x0",
                    "csrrw x0, {column_parity_csr}, x0",
                    "csrrw x0, {column_parity_csr}, x0",
                    "csrrw x0, {column_parity_csr}, x0",
                    "csrrw x0, {column_parity_csr}, x0",
                    "csrrw x0, {theta_rho_csr}, x0",
                    "csrrw x0, {theta_rho_csr}, x0",
                    "csrrw x0, {theta_rho_csr}, x0",
                    "csrrw x0, {theta_rho_csr}, x0",
                    "csrrw x0, {theta_rho_csr}, x0",
                    "csrrw x0, {chi5_csr}, x0",
                    "csrrw x0, {chi5_csr}, x0",
                    "csrrw x0, {chi5_csr}, x0",
                    "csrrw x0, {chi5_csr}, x0",
                    "csrrw x0, {chi5_csr}, x0",
                )*
                "csrrw x0, {column_parity_csr}, x0",
                chi5_csr = const KECCAK_CHI5_CSR_REGISTER,
                column_parity_csr = const KECCAK_COLUMN_PARITY_CSR_REGISTER,
                theta_rho_csr = const KECCAK_THETA_RHO_CSR_REGISTER,
                in("x11") state_ptr.addr(),
                out("x10") _,
                options(nostack, preserves_flags)
            );
        });
    }
}

// every lane access is read-write: read-only lanes are written back unchanged
pub const KECCAK_F1600_BASE_ABI_REGISTER: u32 = 10;
pub const NUM_KECCAK_F1600_REGISTER_ACCESSES: usize = 2;
pub const NUM_KECCAK_F1600_INDIRECT_READS: usize = 0;
pub const KECCAK_COLUMN_PARITY_X11_NUM_WRITES: usize =
    2 * KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS;
pub const KECCAK_THETA_RHO_X11_NUM_WRITES: usize = 2 * KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS;
pub const KECCAK_CHI5_X11_NUM_WRITES: usize = 2 * KECCAK_CHI5_NUM_VARIABLE_OFFSETS;
