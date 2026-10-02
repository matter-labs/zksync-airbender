// Keccak-f1600 on keccak_special5's state layout: per round 5 column parity, 5 theta/rho and 5 chi
// calls, then one column parity call for the delayed final iota.

pub const KECCAK_THETA_RHO_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 12;
pub const KECCAK_COLUMN_PARITY_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 13;
pub const KECCAK_CHI5_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 14;

pub const KECCAK_COLUMN_PARITY_PRECOMPILE: u32 = 0;
pub const KECCAK_THETA_RHO_PRECOMPILE: u32 = 3;
pub const KECCAK_CHI5_PRECOMPILE: u32 = 5;

pub const KECCAK_F1600_NUM_ROUNDS: usize = 24;
pub const NUM_KECCAK_F1600_CALLS_PER_ROUND: usize = 15;
pub const NUM_KECCAK_F1600_CALLS: usize =
    KECCAK_F1600_NUM_ROUNDS * NUM_KECCAK_F1600_CALLS_PER_ROUND + 1;
pub const NUM_KECCAK_F1600_COLUMN_PARITY_CALLS: usize = KECCAK_F1600_NUM_ROUNDS * 5 + 1;
pub const NUM_KECCAK_F1600_THETA_RHO_CALLS: usize = KECCAK_F1600_NUM_ROUNDS * 5;
pub const NUM_KECCAK_F1600_CHI5_CALLS: usize = KECCAK_F1600_NUM_ROUNDS * 5;

// callers size trace ranges that the tracer writes unchecked, so a partial permutation is rejected
// rather than rounded down
pub const fn keccak_f1600_permutations(calls: usize) -> usize {
    assert!(
        calls % NUM_KECCAK_F1600_CALLS == 0,
        "Keccak-f1600 calls must end on a full permutation"
    );
    calls / NUM_KECCAK_F1600_CALLS
}

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

// row r (pi_r in the circuit comments): the slot holding each lane at the start of round r; the
// round permutation updates this map instead of moving lanes
pub const KECCAK_F1600_PERMUTATIONS: [[usize; 25]; 25] = {
    const FLAT: [usize; 625] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
        0, 9, 13, 17, 21, 18, 22, 1, 5, 14, 6, 10, 19, 23, 2, 24, 3, 7, 11, 15, 12, 16, 20, 4, 8,
        0, 22, 19, 11, 8, 17, 14, 6, 3, 20, 9, 1, 23, 15, 12, 21, 18, 10, 7, 4, 13, 5, 2, 24, 16,
        0, 14, 23, 7, 16, 11, 20, 9, 18, 2, 22, 6, 15, 4, 13, 8, 17, 1, 10, 24, 19, 3, 12, 21, 5,
        0, 20, 15, 10, 5, 7, 2, 22, 17, 12, 14, 9, 4, 24, 19, 16, 11, 6, 1, 21, 23, 18, 13, 8, 3,
        0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18,
        0, 12, 24, 6, 18, 1, 13, 20, 7, 19, 2, 14, 21, 8, 15, 3, 10, 22, 9, 16, 4, 11, 23, 5, 17,
        0, 13, 21, 9, 17, 6, 19, 2, 10, 23, 12, 20, 8, 16, 4, 18, 1, 14, 22, 5, 24, 7, 15, 3, 11,
        0, 19, 8, 22, 11, 9, 23, 12, 1, 15, 13, 2, 16, 5, 24, 17, 6, 20, 14, 3, 21, 10, 4, 18, 7,
        0, 23, 16, 14, 7, 22, 15, 13, 6, 4, 19, 12, 5, 3, 21, 11, 9, 2, 20, 18, 8, 1, 24, 17, 10,
        0, 15, 5, 20, 10, 14, 4, 19, 9, 24, 23, 13, 3, 18, 8, 7, 22, 12, 2, 17, 16, 6, 21, 11, 1,
        0, 4, 3, 2, 1, 20, 24, 23, 22, 21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6,
        0, 24, 18, 12, 6, 2, 21, 15, 14, 8, 4, 23, 17, 11, 5, 1, 20, 19, 13, 7, 3, 22, 16, 10, 9,
        0, 21, 17, 13, 9, 12, 8, 4, 20, 16, 24, 15, 11, 7, 3, 6, 2, 23, 19, 10, 18, 14, 5, 1, 22,
        0, 8, 11, 19, 22, 13, 16, 24, 2, 5, 21, 4, 7, 10, 18, 9, 12, 15, 23, 1, 17, 20, 3, 6, 14,
        0, 16, 7, 23, 14, 19, 5, 21, 12, 3, 8, 24, 10, 1, 17, 22, 13, 4, 15, 6, 11, 2, 18, 9, 20,
        0, 5, 10, 15, 20, 23, 3, 8, 13, 18, 16, 21, 1, 6, 11, 14, 19, 24, 4, 9, 7, 12, 17, 22, 2,
        0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12,
        0, 18, 6, 24, 12, 4, 17, 5, 23, 11, 3, 16, 9, 22, 10, 2, 15, 8, 21, 14, 1, 19, 7, 20, 13,
        0, 17, 9, 21, 13, 24, 11, 3, 15, 7, 18, 5, 22, 14, 1, 12, 4, 16, 8, 20, 6, 23, 10, 2, 19,
        0, 11, 22, 8, 19, 21, 7, 18, 4, 10, 17, 3, 14, 20, 6, 13, 24, 5, 16, 2, 9, 15, 1, 12, 23,
        0, 7, 14, 16, 23, 8, 10, 17, 24, 1, 11, 18, 20, 2, 9, 19, 21, 3, 5, 12, 22, 4, 6, 13, 15,
        0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4,
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    ];
    let mut result = [[0usize; 25]; 25];
    let mut i = 0;
    while i < 625 {
        result[i / 25][i % 25] = FLAT[i];
        i += 1;
    }
    result
};

pub const KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED: [u64; 25] = [
    0,
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

pub const KECCAK_F1600_RHO: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

use super::keccak_special5::{
    ITERATION_BITS, KECCAK5_TOTAL_NUM_CONTROL_BITS, KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS,
    PRECOMPILE_MODE_BITS,
};

// control word: precompile | iteration << 3 | round << 6; lookup keys add the execute flag
pub const KECCAK_F1600_CONTROL_EXECUTE_FLAG: u32 = 1 << KECCAK5_TOTAL_NUM_CONTROL_BITS;

#[inline(always)]
pub const fn keccak_f1600_encode_control(precompile: u32, x: usize, round: usize) -> u32 {
    precompile
        | (x as u32) << PRECOMPILE_MODE_BITS
        | (round as u32) << (PRECOMPILE_MODE_BITS + ITERATION_BITS)
}

#[inline(always)]
pub const fn keccak_f1600_decode_control(control: u32) -> (u32, usize, usize) {
    (
        control & ((1 << PRECOMPILE_MODE_BITS) - 1),
        ((control >> PRECOMPILE_MODE_BITS) & ((1 << ITERATION_BITS) - 1)) as usize,
        (control >> (PRECOMPILE_MODE_BITS + ITERATION_BITS)) as usize,
    )
}

pub const KECCAK_F1600_INITIAL_CONTROL_VALUE: u32 =
    keccak_f1600_encode_control(KECCAK_COLUMN_PARITY_PRECOMPILE, 0, 0);
// the run ends after round 24's only call, column parity iteration 0 (the delayed final iota)
pub const KECCAK_F1600_FINAL_CONTROL_VALUE: u32 =
    keccak_f1600_encode_control(KECCAK_COLUMN_PARITY_PRECOMPILE, 1, 24);

pub const fn keccak_f1600_csr_for_precompile(precompile: u32) -> u32 {
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => KECCAK_COLUMN_PARITY_CSR_REGISTER,
        KECCAK_THETA_RHO_PRECOMPILE => KECCAK_THETA_RHO_CSR_REGISTER,
        KECCAK_CHI5_PRECOMPILE => KECCAK_CHI5_CSR_REGISTER,
        _ => panic!("not a Keccak-f1600 precompile"),
    }
}

#[inline(always)]
pub const fn keccak_f1600_num_slots(precompile: u32) -> usize {
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
        KECCAK_THETA_RHO_PRECOMPILE => KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
        KECCAK_CHI5_PRECOMPILE => KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
        _ => panic!("not a Keccak-f1600 precompile"),
    }
}

#[inline(always)]
pub const fn keccak_f1600_bump_control(control: u32) -> u32 {
    let (precompile, x, round) = keccak_f1600_decode_control(control);
    if x < 4 {
        return keccak_f1600_encode_control(precompile, x + 1, round);
    }
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => {
            keccak_f1600_encode_control(KECCAK_THETA_RHO_PRECOMPILE, 0, round)
        }
        KECCAK_THETA_RHO_PRECOMPILE => {
            keccak_f1600_encode_control(KECCAK_CHI5_PRECOMPILE, 0, round)
        }
        KECCAK_CHI5_PRECOMPILE => {
            keccak_f1600_encode_control(KECCAK_COLUMN_PARITY_PRECOMPILE, 0, round + 1)
        }
        _ => panic!("not a Keccak-f1600 precompile"),
    }
}

// slots 0..25 hold the lanes, 25 + x the column parity C[x]; slot 30 is never accessed
pub const KECCAK_F1600_PARITY_SLOT_OFFSET: usize = 25;
pub const KECCAK_F1600_ACCESSED_SLOTS: usize = KECCAK_F1600_PARITY_SLOT_OFFSET + 5;
pub const KECCAK_F1600_UNUSED_SLOT: usize = KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS;

// u64 slots of one call in the circuit's access order: column parity reads the five lanes of
// column x and writes C[x] to slot 25 + x; theta/rho also reads C[x - 1] and C[x + 1]; chi5 takes
// plane x at its slots after the round permutation
#[inline(always)]
pub const fn keccak_f1600_slots(control: u32) -> [usize; 7] {
    let (precompile, x, round) = keccak_f1600_decode_control(control);
    let mut slots = [KECCAK_F1600_UNUSED_SLOT; 7];
    let mut y = 0;
    while y < 5 {
        slots[y] = match precompile {
            KECCAK_COLUMN_PARITY_PRECOMPILE | KECCAK_THETA_RHO_PRECOMPILE => {
                KECCAK_F1600_PERMUTATIONS[round][x + 5 * y]
            }
            KECCAK_CHI5_PRECOMPILE => KECCAK_F1600_PERMUTATIONS[round + 1][5 * x + y],
            _ => panic!("not a Keccak-f1600 precompile"),
        };
        y += 1;
    }
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => slots[5] = KECCAK_F1600_PARITY_SLOT_OFFSET + x,
        KECCAK_THETA_RHO_PRECOMPILE => {
            slots[5] = KECCAK_F1600_PARITY_SLOT_OFFSET + (x + 4) % 5;
            slots[6] = KECCAK_F1600_PARITY_SLOT_OFFSET + (x + 1) % 5;
        }
        _ => {}
    }
    slots
}

// every call of the run touches distinct in-range slots, so its indirect accesses never alias
const _: () = {
    let mut control = KECCAK_F1600_INITIAL_CONTROL_VALUE;
    let mut call = 0;
    while call < NUM_KECCAK_F1600_CALLS {
        let (precompile, _, _) = keccak_f1600_decode_control(control);
        assert!(keccak_f1600_csr_for_precompile(precompile) == keccak_f1600_call_csr(call));
        let slots = keccak_f1600_slots(control);
        let num_slots = keccak_f1600_num_slots(precompile);
        let mut i = 0;
        while i < slots.len() {
            assert!((i < num_slots) == (slots[i] < KECCAK_F1600_ACCESSED_SLOTS));
            let mut j = i + 1;
            while j < num_slots {
                assert!(slots[i] != slots[j]);
                j += 1;
            }
            i += 1;
        }
        control = keccak_f1600_bump_control(control);
        call += 1;
    }
    assert!(control == KECCAK_F1600_FINAL_CONTROL_VALUE);
};

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
