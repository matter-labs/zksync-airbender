//! Phase-1 pre-build gates for ISA-v2 (spec §1a, §8, §9).

use gkr_design_space::import::load_circuit;
use gkr_eval_isa::test_support::{all_fixtures, collect_v2_addresses, column_offset};

/// R3 gate: the largest column offset any source OR destination references must
/// fit the declared 1024-column ISA cap (10-bit `col`). Measured max is 645.
pub const COL_CAP: u32 = 1024;

#[test]
fn r3_col_within_cap() {
    let mut global_max = 0u32;
    for p in all_fixtures() {
        let c = load_circuit(&p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap();
        for (li, layer) in c.circuit.layers.iter().enumerate() {
            for addr in collect_v2_addresses(layer) {
                let col = column_offset(&addr);
                global_max = global_max.max(col);
                assert!(
                    col < COL_CAP,
                    "{name} L{li}: column offset {col} >= cap {COL_CAP} \
                     — R3 option (c) invalid, escalate (source-id table or wider lane)"
                );
            }
        }
    }
    eprintln!("[R3] global max column offset = {global_max} (cap {COL_CAP})");
    assert!(global_max <= 645 + 64, "max column drifted far above the measured 645");
}
