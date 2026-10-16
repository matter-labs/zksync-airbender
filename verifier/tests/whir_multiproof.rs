use prover::merkle_trees::multiproof::{boundary_nodes, MerkleMultiProof};
use verifier_common::blake2s_u32::{Blake2sState, DelegatedBlake2sState};
use verifier_common::gkr::flatten::append_merkle_multiproof;
use verifier_common::whir::{prepare_merkle_queries, verify_merkle_multiproof, MerkleQueryIndex};

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
