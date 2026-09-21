use super::*;

/// Digests are opaque to this module; distinct values are all the tests need.
fn digest(seed: u32) -> [u32; 8] {
    [seed; 8]
}

fn flat(cap_size: usize) -> MerkleTreeCapVarLength {
    MerkleTreeCapVarLength {
        cap: (0..cap_size as u32).map(digest).collect(),
    }
}

#[test]
fn bitreverse_index_handles_zero_width() {
    // LDE factor 1 gives `num_bits == 0`, where `>> (usize::BITS - 0)` is a
    // shift by the full word width: an overflow that panics in debug builds and
    // is a deny-by-default lint for a literal. The zero case is handled
    // explicitly rather than relying on the shift.
    assert_eq!(bitreverse_index(0, 0), 0);
}

#[test]
fn bitreverse_index_matches_known_permutations() {
    assert_eq!(
        (0..2).map(|i| bitreverse_index(i, 1)).collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert_eq!(
        (0..4).map(|i| bitreverse_index(i, 2)).collect::<Vec<_>>(),
        vec![0, 2, 1, 3]
    );
    assert_eq!(
        (0..8).map(|i| bitreverse_index(i, 3)).collect::<Vec<_>>(),
        vec![0, 4, 2, 6, 1, 5, 3, 7]
    );
}

#[test]
fn single_coset_split_is_the_whole_cap() {
    let cap_size = 16;
    let per_coset = split_memory_cap(&flat(cap_size), 1, cap_size).unwrap();

    assert_eq!(per_coset.len(), 1);
    assert_eq!(per_coset[0].cap, flat(cap_size).cap);
    assert_eq!(
        join_memory_caps(&per_coset, 1, cap_size).unwrap().cap,
        flat(cap_size).cap
    );
}

#[test]
fn two_coset_split_is_the_identity_permutation() {
    // Production geometry (`prover::definitions::DEFAULT_LDE_FACTOR == 2`):
    // one-bit reversal is the identity, so segments stay in place. Every other
    // test here exists so that coincidence is never generalised.
    let cap_size = 16;
    let per_coset = split_memory_cap(&flat(cap_size), 2, cap_size).unwrap();

    assert_eq!(per_coset.len(), 2);
    assert_eq!(per_coset[0].cap, (0..8).map(digest).collect::<Vec<_>>());
    assert_eq!(per_coset[1].cap, (8..16).map(digest).collect::<Vec<_>>());
}

#[test]
fn four_coset_split_permutes_distinct_segments() {
    // The case an identity permutation would silently pass: canonical segment
    // `p` holds natural coset `bitreverse_index(p, 2)`, i.e. 0,2,1,3.
    let cap_size = 16;
    let per_coset = split_memory_cap(&flat(cap_size), 4, cap_size).unwrap();

    assert_eq!(per_coset.len(), 4);
    assert_eq!(per_coset[0].cap, (0..4).map(digest).collect::<Vec<_>>());
    assert_eq!(per_coset[2].cap, (4..8).map(digest).collect::<Vec<_>>());
    assert_eq!(per_coset[1].cap, (8..12).map(digest).collect::<Vec<_>>());
    assert_eq!(per_coset[3].cap, (12..16).map(digest).collect::<Vec<_>>());
}

#[test]
fn split_join_round_trips() {
    for lde_factor in [1usize, 2, 4, 8, 16] {
        let cap_size = 16;
        let original = flat(cap_size);
        let per_coset = split_memory_cap(&original, lde_factor, cap_size).unwrap();
        let rejoined = join_memory_caps(&per_coset, lde_factor, cap_size).unwrap();

        assert_eq!(
            rejoined.cap, original.cap,
            "round trip failed at LDE {lde_factor}"
        );
    }
}

#[test]
fn split_agrees_with_the_gpu_readback_permutation() {
    // Independent oracle: the loop `gpu_trace::trace::memory` runs on a device
    // cap readback, written out here rather than reused, so a change to either
    // side has to be made twice to go unnoticed.
    let (lde_factor, cap_size) = (4usize, 16usize);
    let original = flat(cap_size);
    let log_lde = lde_factor.trailing_zeros();
    let digests_per_coset = cap_size / lde_factor;

    let mut expected = vec![MerkleTreeCapVarLength { cap: Vec::new() }; lde_factor];
    for stage1_pos in 0..lde_factor {
        let natural_coset_index = bitreverse_index(stage1_pos, log_lde);
        expected[natural_coset_index].cap = original.cap
            [stage1_pos * digests_per_coset..(stage1_pos + 1) * digests_per_coset]
            .to_vec();
    }

    let actual = split_memory_cap(&original, lde_factor, cap_size).unwrap();

    assert_eq!(actual.len(), expected.len());
    for (a, e) in actual.iter().zip(expected.iter()) {
        assert_eq!(a.cap, e.cap);
    }
}

#[test]
fn rejects_non_power_of_two_lde_factor() {
    assert_eq!(
        split_memory_cap(&flat(16), 3, 16).unwrap_err(),
        CapGeometryError::LdeFactorNotPowerOfTwo { lde_factor: 3 }
    );
    assert_eq!(
        split_memory_cap(&flat(16), 0, 16).unwrap_err(),
        CapGeometryError::LdeFactorNotPowerOfTwo { lde_factor: 0 }
    );
}

#[test]
fn rejects_non_power_of_two_cap_size() {
    assert_eq!(
        split_memory_cap(&flat(12), 2, 12).unwrap_err(),
        CapGeometryError::CapSizeNotPowerOfTwo { cap_size: 12 }
    );
}

#[test]
fn rejects_cap_size_below_lde_factor() {
    assert_eq!(
        split_memory_cap(&flat(2), 4, 2).unwrap_err(),
        CapGeometryError::CapSizeBelowLdeFactor {
            cap_size: 2,
            lde_factor: 4
        }
    );
}

#[test]
fn rejects_flat_cap_of_the_wrong_length() {
    assert_eq!(
        split_memory_cap(&flat(8), 2, 16).unwrap_err(),
        CapGeometryError::FlatCapLengthMismatch {
            expected: 16,
            actual: 8
        }
    );
}

#[test]
fn rejects_wrong_per_coset_count() {
    let per_coset = split_memory_cap(&flat(16), 4, 16).unwrap();

    assert_eq!(
        join_memory_caps(&per_coset[..3], 4, 16).unwrap_err(),
        CapGeometryError::SegmentCountMismatch {
            expected: 4,
            actual: 3
        }
    );
}

#[test]
fn rejects_unequal_or_empty_segments() {
    let mut per_coset = split_memory_cap(&flat(16), 4, 16).unwrap();
    per_coset[2].cap.pop();

    assert_eq!(
        join_memory_caps(&per_coset, 4, 16).unwrap_err(),
        CapGeometryError::SegmentLengthMismatch {
            index: 2,
            expected: 4,
            actual: 3
        }
    );

    per_coset[2].cap.clear();
    assert_eq!(
        join_memory_caps(&per_coset, 4, 16).unwrap_err(),
        CapGeometryError::SegmentLengthMismatch {
            index: 2,
            expected: 4,
            actual: 0
        }
    );
}

#[test]
fn geometry_exposes_the_derived_layout() {
    let geometry = CapGeometry::new(4, 32).unwrap();

    assert_eq!(geometry.lde_factor(), 4);
    assert_eq!(geometry.cap_size(), 32);
    assert_eq!(geometry.log_lde_factor(), 2);
    assert_eq!(geometry.digests_per_coset(), 8);
    assert_eq!(geometry.canonical_segment_range(2), 16..24);
    assert_eq!(geometry.natural_coset_for_canonical_segment(1), 2);
}

/// Flattening a cap for transcript absorption, matching `flatten_merkle_cap` in
/// `trace_and_split`: digests concatenated in cap order, no separators.
fn absorb_flat(cap: &MerkleTreeCapVarLength) -> transcript::Seed {
    let mut words = Vec::new();
    for digest in cap.cap.iter() {
        words.extend_from_slice(digest);
    }
    let mut transcript = transcript::Blake2sBufferingTranscript::<true>::new();
    transcript.absorb(&words);
    transcript.finalize()
}

#[test]
fn joined_cap_absorbs_as_the_canonical_flat_order() {
    // The protocol absorbs one flat cap per circuit instance. A backend that
    // holds per-coset caps has to rebuild exactly the canonical order the
    // committing tree produced, or its Fiat-Shamir seed diverges. Four distinct
    // cosets are the smallest case where the permutation is observable.
    let (lde_factor, cap_size) = (4usize, 16usize);
    let per_coset: Vec<MerkleTreeCapVarLength> = (0..lde_factor)
        .map(|coset| MerkleTreeCapVarLength {
            cap: (0..4).map(|i| digest(100 * coset as u32 + i)).collect(),
        })
        .collect();

    // Independently specified expectation: canonical segment `p` carries
    // natural coset `bitreverse_index(p, 2)`, i.e. cosets 0,2,1,3 in order.
    let mut expected_flat = Vec::new();
    for canonical_segment in 0..lde_factor {
        let natural = bitreverse_index(canonical_segment, 2);
        expected_flat.extend_from_slice(&per_coset[natural].cap);
    }
    let expected = MerkleTreeCapVarLength { cap: expected_flat };

    let joined = join_memory_caps(&per_coset, lde_factor, cap_size).unwrap();

    assert_eq!(joined.cap, expected.cap);
    assert_eq!(absorb_flat(&joined), absorb_flat(&expected));

    // Negative control: concatenating the per-coset caps in natural index order
    // is what a naive adapter would do, and it must NOT produce the same seed.
    // Without this the permutation could be dropped entirely and every
    // positive assertion above would still pass at LDE 2.
    let naive = MerkleTreeCapVarLength {
        cap: per_coset
            .iter()
            .flat_map(|c| c.cap.iter().copied())
            .collect(),
    };

    assert_ne!(naive.cap, joined.cap);
    assert_ne!(absorb_flat(&naive), absorb_flat(&joined));
}

#[test]
fn two_coset_join_absorbs_identically_to_naive_concatenation() {
    // Production geometry: at LDE 2 the permutation IS the identity, so the
    // naive concatenation and the canonical join agree. Pinning this keeps the
    // conversion from silently changing the current production transcript.
    let (lde_factor, cap_size) = (2usize, 16usize);
    let per_coset: Vec<MerkleTreeCapVarLength> = (0..lde_factor)
        .map(|coset| MerkleTreeCapVarLength {
            cap: (0..8).map(|i| digest(100 * coset as u32 + i)).collect(),
        })
        .collect();
    let naive = MerkleTreeCapVarLength {
        cap: per_coset
            .iter()
            .flat_map(|c| c.cap.iter().copied())
            .collect(),
    };

    let joined = join_memory_caps(&per_coset, lde_factor, cap_size).unwrap();

    assert_eq!(joined.cap, naive.cap);
    assert_eq!(absorb_flat(&joined), absorb_flat(&naive));
}
