//! Merkle memory-cap layout conversion shared by every backend.
//!
//! A committed memory tree is built over LDE cosets in **bit-reversed** order
//! (`prover::gkr::prover::stages::commitment_utils::build_tree_over_cosets`
//! passes `bitreverse_cosets = true`), so the flat cap a CPU commitment returns
//! holds its per-coset segments in that canonical tree order. The execution
//! protocol instead carries one `MerkleTreeCapVarLength` per coset in **natural**
//! coset order. These helpers are the only place that permutation is written
//! down; both the CPU commitment adapter and the GPU cap readback/upload use
//! them so the two cannot drift.
//!
//! With `k = log2(lde_factor)`, canonical segment `p` holds natural coset
//! `bitreverse_index(p, k)`. For the production `DEFAULT_LDE_FACTOR = 2` the
//! one-bit reversal is the identity; that coincidence must not be relied on.

use crate::upstream::MerkleTreeCapVarLength;
use std::fmt;

/// Reverse the low `num_bits` of `index`.
#[inline]
pub fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CapGeometryError {
    LdeFactorNotPowerOfTwo {
        lde_factor: usize,
    },
    CapSizeNotPowerOfTwo {
        cap_size: usize,
    },
    CapSizeBelowLdeFactor {
        cap_size: usize,
        lde_factor: usize,
    },
    FlatCapLengthMismatch {
        expected: usize,
        actual: usize,
    },
    SegmentCountMismatch {
        expected: usize,
        actual: usize,
    },
    SegmentLengthMismatch {
        index: usize,
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for CapGeometryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LdeFactorNotPowerOfTwo { lde_factor } => {
                write!(f, "LDE factor {lde_factor} is not a power of two")
            }
            Self::CapSizeNotPowerOfTwo { cap_size } => {
                write!(f, "cap size {cap_size} is not a power of two")
            }
            Self::CapSizeBelowLdeFactor {
                cap_size,
                lde_factor,
            } => write!(
                f,
                "cap size {cap_size} is below the LDE factor {lde_factor}, so cosets have no whole cap segment"
            ),
            Self::FlatCapLengthMismatch { expected, actual } => {
                write!(f, "flat cap has {actual} digests, expected {expected}")
            }
            Self::SegmentCountMismatch { expected, actual } => {
                write!(f, "got {actual} per-coset caps, expected {expected}")
            }
            Self::SegmentLengthMismatch {
                index,
                expected,
                actual,
            } => write!(
                f,
                "per-coset cap {index} has {actual} digests, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for CapGeometryError {}

/// Validated `(lde_factor, cap_size)` pair plus the derived segment layout.
///
/// Both values come from the `ProverConfig` the commitment was produced with.
/// Deriving them from a circuit's convenience accessors instead can disagree
/// with what was actually committed, so callers must pass the config's values.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CapGeometry {
    lde_factor: usize,
    cap_size: usize,
    log_lde_factor: u32,
    digests_per_coset: usize,
}

impl CapGeometry {
    pub fn new(lde_factor: usize, cap_size: usize) -> Result<Self, CapGeometryError> {
        if lde_factor == 0 || !lde_factor.is_power_of_two() {
            return Err(CapGeometryError::LdeFactorNotPowerOfTwo { lde_factor });
        }
        if cap_size == 0 || !cap_size.is_power_of_two() {
            return Err(CapGeometryError::CapSizeNotPowerOfTwo { cap_size });
        }
        if cap_size < lde_factor {
            return Err(CapGeometryError::CapSizeBelowLdeFactor {
                cap_size,
                lde_factor,
            });
        }
        let log_lde_factor = lde_factor.trailing_zeros();
        Ok(Self {
            lde_factor,
            cap_size,
            log_lde_factor,
            digests_per_coset: cap_size >> log_lde_factor,
        })
    }

    #[inline]
    pub fn lde_factor(&self) -> usize {
        self.lde_factor
    }

    #[inline]
    pub fn cap_size(&self) -> usize {
        self.cap_size
    }

    #[inline]
    pub fn log_lde_factor(&self) -> u32 {
        self.log_lde_factor
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
) -> Result<Vec<MerkleTreeCapVarLength>, CapGeometryError> {
    let geometry = CapGeometry::new(lde_factor, cap_size)?;
    if flat.cap.len() != cap_size {
        return Err(CapGeometryError::FlatCapLengthMismatch {
            expected: cap_size,
            actual: flat.cap.len(),
        });
    }
    let mut per_coset = vec![MerkleTreeCapVarLength { cap: Vec::new() }; lde_factor];
    for canonical_segment in 0..lde_factor {
        let natural = geometry.natural_coset_for_canonical_segment(canonical_segment);
        per_coset[natural].cap =
            flat.cap[geometry.canonical_segment_range(canonical_segment)].to_vec();
    }
    Ok(per_coset)
}

/// Per-coset caps in natural coset order -> canonical flat cap.
pub fn join_memory_caps(
    caps: &[MerkleTreeCapVarLength],
    lde_factor: usize,
    cap_size: usize,
) -> Result<MerkleTreeCapVarLength, CapGeometryError> {
    let geometry = CapGeometry::new(lde_factor, cap_size)?;
    if caps.len() != lde_factor {
        return Err(CapGeometryError::SegmentCountMismatch {
            expected: lde_factor,
            actual: caps.len(),
        });
    }
    for (index, cap) in caps.iter().enumerate() {
        if cap.cap.len() != geometry.digests_per_coset() {
            return Err(CapGeometryError::SegmentLengthMismatch {
                index,
                expected: geometry.digests_per_coset(),
                actual: cap.cap.len(),
            });
        }
    }
    let mut flat = Vec::with_capacity(cap_size);
    for canonical_segment in 0..lde_factor {
        let natural = geometry.natural_coset_for_canonical_segment(canonical_segment);
        flat.extend_from_slice(&caps[natural].cap);
    }
    Ok(MerkleTreeCapVarLength { cap: flat })
}

#[cfg(test)]
mod tests;
