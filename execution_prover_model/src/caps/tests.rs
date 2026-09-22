use super::*;

#[test]
fn caps_preserve_coset_order() {
    let flat = MerkleTreeCapVarLength {
        cap: (0..16).map(|i| [i; 8]).collect(),
    };
    for lde in [1, 2, 4, 8, 16] {
        let split = split_memory_cap(&flat, lde, 16);
        assert_eq!(join_memory_caps(&split, lde, 16).cap, flat.cap);
    }
    let split = split_memory_cap(&flat, 4, 16);
    for (coset, start) in [0, 8, 4, 12].into_iter().enumerate() {
        assert_eq!(split[coset].cap, flat.cap[start..start + 4]);
    }
}
