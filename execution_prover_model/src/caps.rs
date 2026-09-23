//! Memory caps use bit-reversed tree order and natural per-coset order.

use crate::upstream::MerkleTreeCapVarLength;

#[inline]
fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

fn segment_size(lde_factor: usize, cap_size: usize) -> usize {
    assert!(lde_factor.is_power_of_two());
    assert!(cap_size.is_power_of_two() && cap_size >= lde_factor);
    cap_size / lde_factor
}

pub fn split_memory_cap(
    flat: &MerkleTreeCapVarLength,
    lde_factor: usize,
    cap_size: usize,
) -> Vec<MerkleTreeCapVarLength> {
    let size = segment_size(lde_factor, cap_size);
    assert_eq!(flat.cap.len(), cap_size);
    (0..lde_factor)
        .map(|coset| {
            let start = bitreverse_index(coset, lde_factor.trailing_zeros()) * size;
            MerkleTreeCapVarLength {
                cap: flat.cap[start..start + size].to_vec(),
            }
        })
        .collect()
}

pub fn join_memory_caps(
    caps: &[MerkleTreeCapVarLength],
    lde_factor: usize,
    cap_size: usize,
) -> MerkleTreeCapVarLength {
    let size = segment_size(lde_factor, cap_size);
    assert_eq!(caps.len(), lde_factor);
    let mut flat = Vec::with_capacity(cap_size);
    for segment in 0..lde_factor {
        let cap = &caps[bitreverse_index(segment, lde_factor.trailing_zeros())].cap;
        assert_eq!(cap.len(), size);
        flat.extend_from_slice(cap);
    }
    MerkleTreeCapVarLength { cap: flat }
}

#[cfg(test)]
mod tests;
