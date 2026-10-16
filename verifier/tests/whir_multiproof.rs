use prover::merkle_trees::multiproof::{boundary_nodes, MerkleMultiProof};
use verifier_common::blake2s_u32::{Blake2sState, DelegatedBlake2sState};
use verifier_common::gkr::flatten::{append_merkle_multiproof, append_merkle_query_order};
use verifier_common::whir::{
    prepare_merkle_queries, prepare_merkle_queries_from_hint, verify_merkle_multiproof,
    MerkleQueryIndex, MERKLE_HINT_HEIGHT_BITS,
};

type Digest = [u32; 8];
fn tree() -> Vec<Vec<Digest>> {
    let mut layers = vec![(0..8)
        .map(|i| core::array::from_fn(|j| i * 19 + j as u32))
        .collect::<Vec<_>>()];
    while layers.last().unwrap().len() > 1 {
        let next = layers
            .last()
            .unwrap()
            .chunks_exact(2)
            .map(|pair| {
                let mut block = [0; 16];
                block[..8].copy_from_slice(&pair[0]);
                block[8..].copy_from_slice(&pair[1]);
                let mut output = [0; 8];
                Blake2sState::compress_two_to_one::<true>(&block, &mut output);
                output
            })
            .collect();
        layers.push(next);
    }
    layers
}
fn verify(indices: &[usize], leaves: &[Digest], depth: usize, cap: &[u32], words: &[u32]) -> bool {
    let mut order: Vec<_> = indices
        .iter()
        .enumerate()
        .map(|(query, &index)| MerkleQueryIndex { index, query })
        .collect();
    let plan = prepare_merkle_queries::<16>(&mut order);
    let mut leaves = leaves.to_vec();
    let mut nds = words.iter().copied();
    let result = verify_merkle_multiproof::<_, 16>(
        &mut DelegatedBlake2sState::new(),
        &plan,
        &mut leaves,
        depth,
        cap,
        &mut nds,
    );
    if result {
        assert_eq!(nds.len(), 0, "all proof words must be consumed");
    }
    let mut hinted_order: Vec<_> = indices
        .iter()
        .enumerate()
        .map(|(query, &index)| MerkleQueryIndex { index, query })
        .collect();
    let mut hinted_words = Vec::new();
    append_merkle_query_order(indices.iter().copied(), &mut hinted_words);
    hinted_words.extend_from_slice(words);
    let mut hinted_nds = hinted_words.into_iter();
    let hinted_plan =
        prepare_merkle_queries_from_hint::<_, 16>(&mut hinted_order, &mut hinted_nds).unwrap();
    let hinted_result = verify_merkle_multiproof::<_, 16>(
        &mut DelegatedBlake2sState::new(),
        &hinted_plan,
        &leaves,
        depth,
        cap,
        &mut hinted_nds,
    );
    assert_eq!(hinted_result, result, "hinted and sorted queries disagree");
    if result {
        assert_eq!(hinted_nds.len(), 0);
    }
    result
}
#[test]
fn exhaustive_frontiers_match_full_tree_and_legacy_serialization() {
    let tree = tree();
    for depth in 0..=3 {
        let cap: Vec<_> = tree[depth].iter().flatten().copied().collect();
        for mask in 0..256 {
            let mut indices: Vec<_> = (0..8).rev().filter(|i| mask & (1 << i) != 0).collect();
            if let Some(&index) = indices.first() {
                indices.push(index);
            }
            let leaves: Vec<_> = indices.iter().map(|&i| tree[0][i]).collect();
            let siblings: Vec<_> = boundary_nodes(&indices, depth)
                .iter()
                .map(|&(l, i)| tree[l][i])
                .collect();
            let proof = MerkleMultiProof { depth, siblings };
            let mut compact = Vec::new();
            append_merkle_multiproof(
                indices.iter().map(|&i| (i, &[][..])),
                Some(&proof),
                &mut compact,
            );
            let paths: Vec<Vec<_>> = indices
                .iter()
                .map(|&i| (0..depth).map(|l| tree[l][(i >> l) ^ 1]).collect())
                .collect();
            let mut legacy = Vec::new();
            append_merkle_multiproof(
                indices.iter().copied().zip(paths.iter().map(Vec::as_slice)),
                None,
                &mut legacy,
            );
            assert_eq!(compact, legacy);
            assert!(
                verify(&indices, &leaves, depth, &cap, &compact),
                "depth={depth} mask={mask}"
            );
        }
    }
}
#[test]
fn rejects_bad_boundary_leaf_duplicate_cap_and_truncation() {
    let tree = tree();
    let indices = [6, 1, 0, 6];
    let leaves: Vec<_> = indices.iter().map(|&i| tree[0][i]).collect();
    let cap: Vec<_> = tree[2].iter().flatten().copied().collect();
    let words: Vec<_> = boundary_nodes(&indices, 2)
        .iter()
        .flat_map(|&(l, i)| tree[l][i])
        .collect();
    assert!(verify(&indices, &leaves, 2, &cap, &words));
    for i in 0..words.len() {
        let mut bad = words.clone();
        bad[i] ^= 1;
        assert!(!verify(&indices, &leaves, 2, &cap, &bad));
    }
    for i in 0..leaves.len() {
        let mut bad = leaves.clone();
        bad[i][0] ^= 1;
        assert!(!verify(&indices, &bad, 2, &cap, &words));
    }
    let mut bad_cap = cap.clone();
    bad_cap[0] ^= 1;
    assert!(!verify(&indices, &leaves, 2, &bad_cap, &words));
    assert!(!verify(&[8], &[tree[0][0]], 2, &cap, &[]));
    assert!(!verify(&[0], &[tree[0][0]], 0, &[], &[]));
    assert!(std::panic::catch_unwind(|| verify(
        &indices,
        &leaves,
        2,
        &cap,
        &words[..words.len() - 1]
    ))
    .is_err());
}

#[test]
fn authenticates_long_unary_chains_with_high_index_bits() {
    for depth in [1, 8, 16, 31] {
        for index in [0usize, (1usize << depth) - 1, ((1usize << depth) - 1) / 3] {
            let leaf = [17u32; 8];
            let mut digest = leaf;
            let mut words = Vec::new();
            for level in 0..depth {
                let sibling = [101 + level as u32; 8];
                words.extend(sibling);
                let mut block = [0u32; 16];
                let (left, right) = if (index >> level) & 1 == 0 {
                    (digest, sibling)
                } else {
                    (sibling, digest)
                };
                block[..8].copy_from_slice(&left);
                block[8..].copy_from_slice(&right);
                Blake2sState::compress_two_to_one::<true>(&block, &mut digest);
            }
            assert!(verify(&[index], &[leaf], depth, &digest, &words));
        }
    }
}

#[test]
fn rejects_invalid_query_order_hints() {
    let indices = [7, 0, 7, 3];
    let mut valid = Vec::new();
    append_merkle_query_order(indices.into_iter(), &mut valid);
    // Repeated slots, wrong index order, wrong tie order, and out-of-range slots.
    for hint in [
        [1, 3, 0, 0],
        [3, 1, 0, 2],
        [1, 3, 2, 0],
        [1, 3, 0, 4],
        [1, 3, 0, u32::MAX >> MERKLE_HINT_HEIGHT_BITS],
    ] {
        let mut queries = core::array::from_fn::<_, 4, _>(|query| MerkleQueryIndex {
            index: indices[query],
            query,
        });
        // Preserve correct split heights so the duplicate and out-of-range
        // cases reach the deliberately corrupted slot after a valid prefix.
        let words: Vec<_> = hint
            .into_iter()
            .zip(valid.iter())
            .map(|(slot, word)| (slot << MERKLE_HINT_HEIGHT_BITS) | (word & 63))
            .collect();
        assert!(
            prepare_merkle_queries_from_hint::<_, 4>(&mut queries, &mut words.into_iter())
                .is_none()
        );
    }
    let mut queries = core::array::from_fn::<_, 4, _>(|query| MerkleQueryIndex {
        index: indices[query],
        query,
    });
    let mut truncated = Vec::new();
    append_merkle_query_order(indices.into_iter(), &mut truncated);
    truncated.pop();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = prepare_merkle_queries_from_hint::<_, 4>(&mut queries, &mut truncated.into_iter());
    }))
    .is_err());
}

#[test]
fn validates_every_split_height_and_rejects_altered_heights() {
    // Include high bits to catch wire-format and shift-width mistakes.
    for height in 0..usize::BITS {
        let indices = [1usize << height, 0, 1usize << height];
        let mut hint = Vec::new();
        append_merkle_query_order(indices.into_iter(), &mut hint);
        let accepts = |words: &[u32]| {
            let mut queries = core::array::from_fn::<_, 3, _>(|query| MerkleQueryIndex {
                index: indices[query],
                query,
            });
            prepare_merkle_queries_from_hint::<_, 3>(&mut queries, &mut words.iter().copied())
                .is_some()
        };
        assert!(accepts(&hint));
        for position in 0..hint.len() {
            let original = hint[position];
            for wrong_height in 0..64 {
                if wrong_height == original & 63 {
                    continue;
                }
                hint[position] = (original & !63) | wrong_height;
                assert!(!accepts(&hint));
            }
            hint[position] = original;
        }
    }
}
