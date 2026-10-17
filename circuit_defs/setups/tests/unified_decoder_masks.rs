#![feature(allocator_api)]

use prover::cs::gkr_circuits::unified_reduced_machine::{
    unified_decoder_mask_violation, UNIFIED_RD_IS_ZERO_BIT,
};
use std::alloc::Global;

fn read_words(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    assert_eq!(bytes.len() % 4, 0, "{path} is not word aligned");
    bytes
        .chunks_exact(4)
        .map(|w| u32::from_le_bytes(w.try_into().unwrap()))
        .collect()
}

/// The unified setups' own decoder-table builder, over every in-repo regular-ROM unified
/// guest, yields only masks that pass the decoder-mask validator (the builder panics on
/// any other), and each guest reaches the Family-2 RD_IS_ZERO classes.
#[test]
fn unified_setup_decoder_tables_pass_the_mask_validator() {
    for stem in [
        "../../examples/multi_family_smoke/app_blake2_g_function",
        "../../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_blake2_with_compression",
        "../../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_special_opcodes_extension",
        "../../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension",
    ] {
        let text = read_words(&format!("{stem}.text"));
        let table = setups::unified_decoder_table::<Global>(&text);
        let mut entries = 0usize;
        let mut rd_is_zero_entries = 0usize;
        for entry in table.iter().flatten() {
            let bits = entry.opcode_family_bits;
            assert_eq!(unified_decoder_mask_violation(bits), None, "{stem}: {bits:#b}");
            entries += 1;
            rd_is_zero_entries += (bits >> UNIFIED_RD_IS_ZERO_BIT & 1) as usize;
        }
        assert!(entries > 0, "{stem}: empty decoder table");
        assert!(rd_is_zero_entries > 0, "{stem}: no RD_IS_ZERO entry");
    }
}
