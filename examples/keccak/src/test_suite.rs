//! Sanity tests for the unified Keccak-f1600 delegation API.
//!
//! The local software implementation intentionally mirrors Keccak-f1600 rather
//! than delegating to another crate. This keeps the example self-contained and
//! verifies the RISC-V precompile path directly.

use common_constants::delegation_types::keccak_special5::KeccakF1600State;

const RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

const PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

const RC: [u64; 24] = [
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

const KNOWN_INPUT: [u64; 25] = [
    0xF1258F7940E1DDE7,
    0x84D5CCF933C0478A,
    0xD598261EA65AA9EE,
    0xBD1547306F80494D,
    0x8B284E056253D057,
    0xFF97A42D7F8E6FD4,
    0x90FEE5A0A44647C4,
    0x8C5BDA0CD6192E76,
    0xAD30A6F71B19059C,
    0x30935AB7D08FFC64,
    0xEB5AA93F2317D635,
    0xA9A6E6260D712103,
    0x81A57C16DBCF555F,
    0x43B831CD0347C826,
    0x01F22F1A11A5569F,
    0x05E5635A21D9AE61,
    0x64BEFEF28CC970F2,
    0x613670957BC46611,
    0xB87C5A554FD00ECB,
    0x8C3EE88A1CCF32C8,
    0x940C7922AE3A2614,
    0x1841F924A2C509E4,
    0x16F53526E70465C2,
    0x75F644E97F30A13B,
    0xEAF1FF7B5CECA249,
];

const KNOWN_OUTPUT: [u64; 25] = [
    0x2D5C954DF96ECB3C,
    0x6A332CD07057B56D,
    0x093D8D1270D76B6C,
    0x8A20D9B25569D094,
    0x4F9C4F99E5E7F156,
    0xF957B9A2DA65FB38,
    0x85773DAE1275AF0D,
    0xFAF4F247C3D810F7,
    0x1F1B9EE6F79A8759,
    0xE4FECC0FEE98B425,
    0x68CE61B6B9CE68A1,
    0xDEEA66C4BA8F974F,
    0x33C43D836EAFB1F5,
    0xE00654042719DBD9,
    0x7CF8A9F009831265,
    0xFD5449A6BF174743,
    0x97DDAD33D8994B40,
    0x48EAD5FC5D0BE774,
    0xE3B8C8EE55B7B03C,
    0x91A0226E649E42E9,
    0x900E3129E7BADD7B,
    0x202A9EC5FAA3CCE8,
    0x5B3402464E1C3DB6,
    0x609F4E62A44C1059,
    0x20D06CD26A8FBF5C,
];

pub fn run_keccak_tests() {
    let known_output = run_single_test(KNOWN_INPUT);
    assert_first_25_lanes(&known_output, &KNOWN_OUTPUT);

    run_single_test([0; 25]);
    run_single_test(patterned_state());
}

fn run_single_test(initial_lanes: [u64; 25]) -> KeccakF1600State {
    let mut expected = make_state(initial_lanes);
    keccak_f1600_reference(&mut expected.0);

    let mut delegated = make_state(initial_lanes);
    common_constants::delegation_types::keccak_special5::keccak_f1600(&mut delegated);

    assert_all_lanes(&delegated, &expected);

    delegated
}

fn make_state(initial_lanes: [u64; 25]) -> KeccakF1600State {
    let mut state = KeccakF1600State::zeroed();
    state.0[..25].copy_from_slice(&initial_lanes);

    // The scratch lanes are not Keccak state, but setting non-zero values makes
    // the test check that the delegation overwrites them with its ABI values.
    let mut i = 25;
    while i < 31 {
        state.0[i] = 0xDEAD_BEEF_0000_0000 | i as u64;
        i += 1;
    }

    state
}

fn patterned_state() -> [u64; 25] {
    let mut state = [0u64; 25];
    let mut i = 0;
    while i < 25 {
        state[i] = 0x0102_0304_0506_0708u64
            .wrapping_mul((i as u64) + 1)
            .rotate_left((i * 7) as u32);
        i += 1;
    }

    state
}

fn keccak_f1600_reference(state: &mut [u64; 31]) {
    let mut round = 0;
    while round < 24 {
        keccak_round(state, round);
        round += 1;
    }

    state[25] = state[0] ^ state[5] ^ state[10] ^ state[15] ^ state[20];
}

fn keccak_round(state: &mut [u64; 31], round: usize) {
    let mut column = [0u64; 5];

    let mut x = 0;
    while x < 5 {
        let mut y = 0;
        while y < 5 {
            column[x] ^= state[5 * y + x];
            y += 1;
        }
        x += 1;
    }

    x = 0;
    while x < 5 {
        let t1 = column[(x + 4) % 5];
        let t2 = column[(x + 1) % 5].rotate_left(1);
        let mix = t1 ^ t2;

        // The delegation circuit exposes these final-round intermediate values
        // through scratch lanes, so the reference computes them too.
        if round == 23 {
            if x == 0 {
                state[29] = mix;
            }
            if x == 3 {
                state[27] = mix;
            }
            if x == 4 {
                state[28] = mix;
                state[30] = t2;
            }
        }

        let mut y = 0;
        while y < 5 {
            state[5 * y + x] ^= mix;
            y += 1;
        }
        x += 1;
    }

    let mut last = state[1];
    let mut i = 0;
    while i < 24 {
        let next = state[PI[i]];
        state[PI[i]] = last.rotate_left(RHO[i]);
        last = next;
        i += 1;
    }

    if round == 23 {
        state[26] = state[21];
    }

    let mut y_step = 0;
    while y_step < 5 {
        let y = 5 * y_step;
        x = 0;
        while x < 5 {
            column[x] = state[y + x];
            x += 1;
        }

        x = 0;
        while x < 5 {
            state[y + x] = column[x] ^ (!column[(x + 1) % 5] & column[(x + 2) % 5]);
            x += 1;
        }

        y_step += 1;
    }

    state[0] ^= RC[round];
}

fn assert_first_25_lanes(actual: &KeccakF1600State, expected: &[u64; 25]) {
    let mut i = 0;
    while i < 25 {
        assert_eq!(actual.0[i], expected[i]);
        i += 1;
    }
}

fn assert_all_lanes(actual: &KeccakF1600State, expected: &KeccakF1600State) {
    let mut i = 0;
    while i < 31 {
        assert_eq!(actual.0[i], expected.0[i]);
        i += 1;
    }
}
