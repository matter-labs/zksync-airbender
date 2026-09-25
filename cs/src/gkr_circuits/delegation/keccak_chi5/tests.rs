use super::*;
use crate::gkr_circuits::delegation::keccak_theta_rho::test::*;
use common_constants::delegation_types::keccak_f1600::KECCAK_CHI5_PRECOMPILE;
use std::sync::OnceLock;

fn rows(seed: u64) -> Vec<KeccakRowOracle> {
    schedule_rows(
        KECCAK_CHI5_PRECOMPILE,
        seed,
        KECCAK_CHI5_CSR_REGISTER,
        |x, round| (0..5).map(|k| pi(round + 1, 5 * x + k)).collect(),
    )
}

fn tables() -> &'static Tables {
    static TABLES: OnceLock<Tables> = OnceLock::new();
    TABLES.get_or_init(|| {
        full_membership(vec![
            (TableType::KeccakChi5, chi_table()),
            (TableType::KeccakChi5Control, control_table()),
        ])
    })
}

fn satisfied_row(oracle: KeccakRowOracle) -> bool {
    satisfied(oracle, tables(), define_keccak_chi5_delegation_circuit)
}

fn rejected_row(honest: KeccakRowOracle, tampered: KeccakRowOracle) -> bool {
    rejected(
        honest,
        tampered,
        tables(),
        define_keccak_chi5_delegation_circuit,
    )
}

// outputs consistent with the slots actually read
fn recompute(oracle: &mut KeccakRowOracle) {
    let a: [u64; 5] = from_fn(|k| oracle.state_in[oracle.indices[k]]);
    oracle.state_out = oracle.state_in;
    for k in 0..5 {
        oracle.state_out[oracle.indices[k]] = a[k] ^ (!a[(k + 1) % 5] & a[(k + 2) % 5]);
    }
}

#[test]
fn chi5_rows_are_satisfied() {
    let rows = rows(1);
    assert_eq!(rows.len(), 24 * 5);
    for oracle in rows {
        assert!(satisfied_row(oracle), "control {:#x}", oracle.control_in);
    }
    assert!(satisfied_row(KeccakRowOracle::padding(
        KECCAK_CHI5_CSR_REGISTER
    )));
}

#[test]
fn chi5_rejections() {
    let rows = rows(2);
    // every written u16 limb, at a bit that varies with the lane, limb and row
    for y in 0..5 {
        for m in 0..4 {
            let call = (29 * (4 * y + m) + 7) % rows.len();
            let bit = 16 * m + (5 * y + 3 * m + call) % 16;
            let mut oracle = rows[call];
            oracle.state_out[oracle.indices[y]] ^= 1 << bit;
            assert!(
                rejected_row(rows[call], oracle),
                "call {call} lane {y} bit {bit}"
            );
        }
    }
    for (call, delta) in [(2, 1u32 << 6), (4, 1 << 3), (9, 1)] {
        let mut oracle = rows[call];
        oracle.control_out += delta;
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} delta {delta}"
        );
    }
    for (call, position) in [(6, 0), (17, 3), (21, 4)] {
        let mut oracle = rows[call];
        oracle.indices[position] = (0..25).find(|slot| !oracle.indices.contains(slot)).unwrap();
        recompute(&mut oracle);
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} position {position}"
        );
    }
    let mut oracle = rows[3];
    oracle.control_in += 1;
    assert!(rejected_row(rows[3], oracle));
}
