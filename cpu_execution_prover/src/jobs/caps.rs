//! Memory caps use bit-reversed tree order and natural per-coset order.

use crate::upstream::MerkleTreeCapVarLength;
pub(super) use prover::merkle_trees::split_memory_cap;

#[inline]
pub(super) fn join_memory_caps(
    caps: &[MerkleTreeCapVarLength],
    lde_factor: usize,
    cap_size: usize,
) -> MerkleTreeCapVarLength {
    assert_eq!(caps.len(), lde_factor);
    let flat = execution_prover::join_per_coset_caps(caps);
    assert_eq!(flat.cap.len(), cap_size);
    flat
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn caps_preserve_coset_order() {
        let flat = MerkleTreeCapVarLength {
            cap: (0..16).map(|i| [i; 8]).collect(),
        };
        for lde in [1, 2, 4, 8, 16] {
            let split = split_memory_cap(&flat, lde, 16);
            assert_eq!(join_memory_caps(&split, lde, 16).cap, flat.cap, "LDE {lde}");
        }
        let split = split_memory_cap(&flat, 4, 16);
        for (coset, start) in [0, 8, 4, 12].into_iter().enumerate() {
            assert_eq!(split[coset].cap, flat.cap[start..start + 4]);
        }
    }
}
