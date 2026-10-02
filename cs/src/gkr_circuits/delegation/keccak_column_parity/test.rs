use super::*;
use crate::gkr_circuits::delegation::keccak_theta_rho::test::*;
use std::sync::OnceLock;

fn rows(seed: u64) -> Vec<KeccakRowOracle> {
    schedule_rows(KECCAK_COLUMN_PARITY_PRECOMPILE, seed, |x, round| {
        (0..5)
            .map(|y| pi(round, x + 5 * y))
            .chain([25 + x])
            .collect()
    })
}

fn tables() -> &'static Tables {
    static TABLES: OnceLock<Tables> = OnceLock::new();
    TABLES.get_or_init(|| generated_tables::<TOTAL_TABLE_WIDTH>(all_table_types()))
}

fn satisfied_row(oracle: KeccakRowOracle) -> bool {
    satisfied(
        oracle,
        tables(),
        define_keccak_column_parity_delegation_circuit,
    )
}

fn rejected_row(honest: KeccakRowOracle, tampered: KeccakRowOracle) -> bool {
    rejected(
        honest,
        tampered,
        tables(),
        define_keccak_column_parity_delegation_circuit,
    )
}

// lane 0 xored with `constant`, C consistent with the slots actually read
fn recompute(oracle: &mut KeccakRowOracle, constant: u64) {
    let s = oracle.state_in;
    oracle.state_out = s;
    oracle.state_out[oracle.indices[0]] = s[oracle.indices[0]] ^ constant;
    oracle.state_out[oracle.indices[5]] =
        oracle.state_out[oracle.indices[0]] ^ (1..5).fold(0, |acc, y| acc ^ s[oracle.indices[y]]);
}

#[test]
fn column_parity_rows_are_satisfied() {
    let rows = rows(1);
    assert_eq!(rows.len(), NUM_KECCAK_F1600_COLUMN_PARITY_CALLS);
    for oracle in rows {
        assert!(satisfied_row(oracle), "control {:#x}", oracle.control_in);
    }
    assert!(satisfied_row(KeccakRowOracle::padding(
        KECCAK_COLUMN_PARITY_CSR_REGISTER
    )));
}

#[test]
fn column_parity_rejections() {
    let rows = rows(2);
    // every written u16 limb of the parity, the first lane and two of the unchanged lanes
    for (position, offset) in [(5, 0), (0, 3), (2, 5), (4, 9)] {
        for m in 0..4 {
            let call = (31 * m + 11 * position + offset) % rows.len();
            let bit = 16 * m + (7 * m + call) % 16;
            let mut oracle = rows[call];
            oracle.state_out[oracle.indices[position]] ^= 1 << bit;
            assert!(
                rejected_row(rows[call], oracle),
                "call {call} slot {position} bit {bit}"
            );
        }
    }
    // iota: missing, another round's constant, applied outside iteration 0
    for (call, constant) in [
        (5, 0),
        (5, KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[2]),
        (120, KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[23]),
        (7, KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[1]),
    ] {
        let mut oracle = rows[call];
        recompute(&mut oracle, constant);
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} constant {constant:#x}"
        );
    }
    for (call, position) in [(3, 0), (3, 2), (11, 4), (11, 5)] {
        let mut oracle = rows[call];
        let (_, x, round) = keccak_f1600_decode_control(oracle.control_in);
        oracle.indices[position] = if position < 5 {
            (0..25).find(|slot| !oracle.indices.contains(slot)).unwrap()
        } else {
            25 + (x + 1) % 5
        };
        recompute(
            &mut oracle,
            if x == 0 {
                KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[round]
            } else {
                0
            },
        );
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} position {position}"
        );
    }
    for (call, delta) in [(4, 1u32), (9, 1 << 3), (15, 1 << 6)] {
        let mut oracle = rows[call];
        oracle.control_out += delta;
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} delta {delta}"
        );
    }
    // round 24 exists only in iteration 0, and the control must name column parity
    for (call, control_in) in [
        (
            120,
            keccak_f1600_encode_control(KECCAK_COLUMN_PARITY_PRECOMPILE, 1, 24),
        ),
        (
            0,
            keccak_f1600_encode_control(KECCAK_THETA_RHO_PRECOMPILE, 0, 0),
        ),
    ] {
        let mut oracle = rows[call];
        oracle.control_in = control_in;
        assert!(rejected_row(rows[call], oracle), "control {control_in:#x}");
    }
    let padding = KeccakRowOracle::padding(KECCAK_COLUMN_PARITY_CSR_REGISTER);
    assert!(rejected_row(
        padding,
        KeccakRowOracle::padding_with_key_of(rows[1])
    ));
}
