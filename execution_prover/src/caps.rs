use crate::upstream::MerkleTreeCapVarLength;

/// Joins natural-order per-coset caps into a bit-reversed tree cap.
pub fn join_per_coset_caps(caps: &[MerkleTreeCapVarLength]) -> MerkleTreeCapVarLength {
    let lde_factor = caps.len();
    assert!(lde_factor.is_power_of_two());
    let per_coset_cap_size = caps[0].cap.len();
    assert!(per_coset_cap_size.is_power_of_two());
    let mut cap = Vec::with_capacity(lde_factor * per_coset_cap_size);
    let log_lde_factor = lde_factor.trailing_zeros();
    for index in 0..lde_factor {
        let coset_index = if log_lde_factor == 0 {
            0
        } else {
            index.reverse_bits() >> (usize::BITS - log_lde_factor)
        };
        let coset = &caps[coset_index];
        assert_eq!(coset.cap.len(), per_coset_cap_size);
        cap.extend_from_slice(&coset.cap);
    }
    MerkleTreeCapVarLength { cap }
}
