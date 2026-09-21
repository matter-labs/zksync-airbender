//! Merkle memory-cap layout conversion shared by every backend.
//!
//! A committed tree is built over LDE cosets in bit-reversed order, so a flat
//! cap holds canonical segment `p` for natural coset `bitreverse_index(p, k)`
//! with `k = log2(lde_factor)`. The protocol carries one cap per coset in
//! natural order, so split and join are that permutation and its inverse. At
//! the production `DEFAULT_LDE_FACTOR = 2` the reversal is the identity; do
//! not rely on it.
//!
//! Geometry comes from the `ProverConfig` the commitment was produced with, so
//! a mismatch is an internal inconsistency and every check here asserts.

use crate::upstream::MerkleTreeCapVarLength;

/// Reverse the low `num_bits` of `index`.
#[inline]
pub fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

/// Validated `(lde_factor, cap_size)` pair plus the derived segment layout.
///
/// Both values come from the `ProverConfig` the commitment was produced with.
/// Deriving them from a circuit's convenience accessors instead can disagree
/// with what was actually committed, so callers must pass the config's values.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CapGeometry {
    lde_factor: usize,
    log_lde_factor: u32,
    digests_per_coset: usize,
}

impl CapGeometry {
    pub fn new(lde_factor: usize, cap_size: usize) -> Self {
        assert!(
            lde_factor != 0 && lde_factor.is_power_of_two(),
            "LDE factor {lde_factor} is not a power of two"
        );
        assert!(
            cap_size != 0 && cap_size.is_power_of_two(),
            "cap size {cap_size} is not a power of two"
        );
        assert!(
            cap_size >= lde_factor,
            "cap size {cap_size} is below the LDE factor {lde_factor}, so cosets have no whole cap segment"
        );
        let log_lde_factor = lde_factor.trailing_zeros();
        Self {
            lde_factor,
            log_lde_factor,
            digests_per_coset: cap_size >> log_lde_factor,
        }
    }

    /// Digests one coset contributes to the flat cap.
    #[inline]
    pub fn digests_per_coset(&self) -> usize {
        self.digests_per_coset
    }

    /// Natural coset index held by canonical (tree-order) segment `p`.
    #[inline]
    pub fn natural_coset_for_canonical_segment(&self, canonical_segment: usize) -> usize {
        debug_assert!(canonical_segment < self.lde_factor);
        bitreverse_index(canonical_segment, self.log_lde_factor)
    }

    /// Byte-free digest range of canonical segment `p` inside a flat cap.
    #[inline]
    pub fn canonical_segment_range(&self, canonical_segment: usize) -> std::ops::Range<usize> {
        let start = canonical_segment * self.digests_per_coset;
        start..start + self.digests_per_coset
    }
}

/// Canonical flat cap -> per-coset caps in natural coset order.
pub fn split_memory_cap(
    flat: &MerkleTreeCapVarLength,
    lde_factor: usize,
    cap_size: usize,
) -> Vec<MerkleTreeCapVarLength> {
    let geometry = CapGeometry::new(lde_factor, cap_size);
    assert_eq!(
        flat.cap.len(),
        cap_size,
        "flat cap has {} digests, expected {cap_size}",
        flat.cap.len()
    );
    let mut per_coset = vec![MerkleTreeCapVarLength { cap: Vec::new() }; lde_factor];
    for canonical_segment in 0..lde_factor {
        let natural = geometry.natural_coset_for_canonical_segment(canonical_segment);
        per_coset[natural].cap =
            flat.cap[geometry.canonical_segment_range(canonical_segment)].to_vec();
    }
    per_coset
}

/// Per-coset caps in natural coset order -> canonical flat cap.
pub fn join_memory_caps(
    caps: &[MerkleTreeCapVarLength],
    lde_factor: usize,
    cap_size: usize,
) -> MerkleTreeCapVarLength {
    let geometry = CapGeometry::new(lde_factor, cap_size);
    assert_eq!(
        caps.len(),
        lde_factor,
        "got {} per-coset caps, expected {lde_factor}",
        caps.len()
    );
    for (index, cap) in caps.iter().enumerate() {
        assert_eq!(
            cap.cap.len(),
            geometry.digests_per_coset(),
            "per-coset cap {index} has {} digests, expected {}",
            cap.cap.len(),
            geometry.digests_per_coset()
        );
    }
    let mut flat = Vec::with_capacity(cap_size);
    for canonical_segment in 0..lde_factor {
        let natural = geometry.natural_coset_for_canonical_segment(canonical_segment);
        flat.extend_from_slice(&caps[natural].cap);
    }
    MerkleTreeCapVarLength { cap: flat }
}

#[cfg(test)]
mod tests;
