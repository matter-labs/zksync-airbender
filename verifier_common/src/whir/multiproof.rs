//! Pruned Merkle multiproofs for a round's query openings.
//!
//! A round opens `Q` leaves of one tree (three trees sharing the leaf indices
//! in the base round). Independent paths hash `Q * depth` nodes and ship as
//! many siblings; the distinct ancestors of the queried leaves are fewer, and
//! every sibling that is itself an ancestor of another queried leaf need not
//! be shipped at all. This module verifies the openings as ONE multiproof
//! with exactly one compression per distinct ancestor, without ever
//! materializing the union of the paths:
//!
//! * the verifier sorts the drawn queries by tree index itself (a stable
//!   bucket sort, [`sort_queries_by_tree_index`]: cheaper than reading and
//!   validating a prover-supplied permutation, and one fewer prover input);
//! * the verifier walks the queries in that order, each from its leaf hash
//!   (already in the hasher state) upward, keeping the running node hash in
//!   the hasher state as a plain path walk does;
//! * at a node whose right sibling subtree holds a LATER query, the walk
//!   stops: the node hash is pushed on a small stack, and the later query
//!   picks it up as its left sibling when it reaches that level. At a node
//!   whose left sibling subtree holds an EARLIER query, that sibling is the
//!   stack top (the pushes nest: at any moment the un-consumed pushes are the
//!   ancestors-to-be of the current query, deepest on top), so it is popped
//!   straight into the hasher's sibling slot. Every other sibling comes from
//!   the proof, as on a plain path.
//!
//! The stack never holds more than `depth` entries, and the only copies on
//! top of a plain path walk are one 8-word store per push (a pop replaces the
//! 8 non-determinism reads of a shipped sibling). The decisions depend only
//! on the sorted indices, so the prover (`gkr::flatten`) emits exactly the
//! siblings the walk reads, in the order it reads them.
//!
//! A leaf queried twice is hashed twice (both openings carry the leaf data):
//! the first occurrence pushes its leaf hash, the second pops it and requires
//! equality before walking as the single representative.

use crate::lazy_vec::LazyVec;
use blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use core::mem::MaybeUninit;
use non_determinism_source::U32WordNonDeterminismSource;

/// `next_index` of the last query in sorted order: no leaf is to its right.
pub const NO_NEXT_INDEX: usize = usize::MAX;
const NO_LEVEL: usize = usize::MAX;
/// The most buckets [`sort_queries_by_tree_index`] distributes into.
const MAX_SORT_BUCKETS: usize = 1024;

/// The node hashes handed from a query to a later one, with the tree level
/// each was computed at (see the module docs for why this is a stack).
pub struct MerkleMultiproofStack<const MAX_DEPTH: usize> {
    hashes: [MaybeUninit<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>; MAX_DEPTH],
    levels: [usize; MAX_DEPTH],
    len: usize,
    /// The top entry's level ([`NO_LEVEL`] when empty): the walk compares
    /// against it at every level, so it is kept as one plain word.
    top_level: usize,
}

impl<const MAX_DEPTH: usize> MerkleMultiproofStack<MAX_DEPTH> {
    #[allow(clippy::new_without_default)]
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            hashes: [const { MaybeUninit::uninit() }; MAX_DEPTH],
            levels: [0; MAX_DEPTH],
            len: 0,
            top_level: NO_LEVEL,
        }
    }

    #[inline(always)]
    fn top_level(&self) -> usize {
        self.top_level
    }

    #[inline(always)]
    fn refresh_top_level(&mut self) {
        self.top_level = if self.len == 0 {
            NO_LEVEL
        } else {
            unsafe { *self.levels.get_unchecked(self.len - 1) }
        };
    }

    #[inline(always)]
    fn push(&mut self, level: usize, hash: &[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]) {
        debug_assert!(self.len < MAX_DEPTH);
        unsafe {
            self.hashes.get_unchecked_mut(self.len).write(*hash);
            *self.levels.get_unchecked_mut(self.len) = level;
        }
        self.len += 1;
        self.top_level = level;
    }

    #[inline(always)]
    fn pop_into(&mut self, dst: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]) {
        debug_assert!(self.len > 0);
        self.len -= 1;
        unsafe {
            *dst = self.hashes.get_unchecked(self.len).assume_init();
        }
        self.refresh_top_level();
    }

    #[inline(always)]
    fn pop_equals(&mut self, hash: &[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]) -> bool {
        debug_assert!(self.len > 0);
        self.len -= 1;
        self.refresh_top_level();
        unsafe { self.hashes.get_unchecked(self.len).assume_init_ref() == hash }
    }

    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// Sort a round's drawn queries by tree index, stably (equal indices keep
/// their draw order, as the prover's `gkr::flatten` sorts). Fills `perm`
/// with the draw positions in sorted order and `sorted` with the tree
/// indices along it. One counting pass on the index's top bits into
/// `MAX_Q.next_power_of_two()` buckets, then one insertion pass to order
/// within buckets: the indices are uniform over `index_bits` bits, so a
/// bucket holds about one query and the pass moves almost nothing.
#[inline(always)]
pub fn sort_queries_by_tree_index<const MAX_Q: usize>(
    tree_indices: &LazyVec<usize, MAX_Q>,
    index_bits: usize,
    perm: &mut LazyVec<usize, MAX_Q>,
    sorted: &mut LazyVec<usize, MAX_Q>,
) {
    let num_queries = tree_indices.len();
    let num_buckets = MAX_Q.next_power_of_two().min(MAX_SORT_BUCKETS);
    // Opaque to the optimizer: with a constant shift of 16, `index >> shift`
    // is narrowed to a halfword load of the upper half, which the reduced
    // machine has not.
    let shift =
        core::hint::black_box(index_bits.saturating_sub(num_buckets.trailing_zeros() as usize));

    // counts[b + 1] = queries in bucket b, then prefix sums = bucket starts
    let mut counts = [const { MaybeUninit::<u32>::uninit() }; MAX_SORT_BUCKETS + 1];
    let counts = unsafe { counts.get_unchecked_mut(..num_buckets + 1) };
    let mut b = 0;
    while b <= num_buckets {
        unsafe { counts.get_unchecked_mut(b).write(0) };
        b += 1;
    }
    let counts: &mut [u32] =
        unsafe { core::slice::from_raw_parts_mut(counts.as_mut_ptr().cast(), num_buckets + 1) };
    let mut q = 0;
    while q < num_queries {
        let b = *tree_indices.get(q) >> shift;
        unsafe { *counts.get_unchecked_mut(b + 1) += 1 };
        q += 1;
    }
    let mut b = 1;
    while b <= num_buckets {
        unsafe { *counts.get_unchecked_mut(b) += *counts.get_unchecked(b - 1) };
        b += 1;
    }
    unsafe {
        perm.set_len(num_queries);
        sorted.set_len(num_queries);
    }
    let mut q = 0;
    while q < num_queries {
        let index = *tree_indices.get(q);
        let slot = unsafe { counts.get_unchecked_mut(index >> shift) };
        let pos = *slot as usize;
        *slot += 1;
        unsafe {
            perm.set_unchecked(pos, q);
            sorted.set_unchecked(pos, index);
        }
        q += 1;
    }

    // insertion pass: finishes the order inside the buckets, stably
    let perm = perm.as_mut_slice();
    let sorted = sorted.as_mut_slice();
    let mut j = 1;
    while j < num_queries {
        let index = unsafe { *sorted.get_unchecked(j) };
        let mut k = j;
        while k > 0 && unsafe { *sorted.get_unchecked(k - 1) } > index {
            k -= 1;
        }
        if k < j {
            let p = unsafe { *perm.get_unchecked(j) };
            let mut m = j;
            while m > k {
                unsafe {
                    *sorted.get_unchecked_mut(m) = *sorted.get_unchecked(m - 1);
                    *perm.get_unchecked_mut(m) = *perm.get_unchecked(m - 1);
                }
                m -= 1;
            }
            unsafe {
                *sorted.get_unchecked_mut(k) = index;
                *perm.get_unchecked_mut(k) = p;
            }
        }
        j += 1;
    }
}

/// Continue the multiproof walk from the leaf whose hash is in the hasher
/// state: the `j`-th query in sorted order, at tree index `index`, with
/// `prev_index_equal` telling whether the previous sorted query opened the
/// same leaf and `next_index` the following sorted query's tree index
/// ([`NO_NEXT_INDEX`] for the last). Reads the shipped siblings from
/// `nd_source`; `false` on a cap or duplicate-leaf mismatch.
#[inline(always)]
pub fn verify_merkle_multiproof_leaf<I: U32WordNonDeterminismSource, const MAX_DEPTH: usize>(
    hasher: &mut DelegatedBlake2sState,
    stack: &mut MerkleMultiproofStack<MAX_DEPTH>,
    index: usize,
    prev_index_equal: bool,
    next_index: usize,
    depth: usize,
    cap: &[u32],
    nd_source: &mut I,
) -> bool {
    if prev_index_equal {
        // The previous query opened the same leaf and left its hash on top.
        if !stack.pop_equals(hasher.read_state_for_output_ref()) {
            return false;
        }
    }
    if next_index == index {
        stack.push(0, hasher.read_state_for_output_ref());
        return true;
    }

    // Every level touches the stack only through its cached top level, and
    // keeps as little live across the compression as a plain path walk
    // does: the hasher call clobbers the registers, so each extra live word
    // is a spill per level.
    let mut node = index;
    let mut level = 0;
    while level < depth {
        let is_right = node & 1 == 1;
        if is_right {
            if stack.top_level() == level {
                // The left sibling's subtree holds earlier queries: its hash
                // was pushed by the last of them.
                let proof_buf = hasher.get_merkle_path_proof_buffer(true);
                stack.pop_into(proof_buf);
                hasher.compress_node::<true>(true);
                node >>= 1;
                level += 1;
                continue;
            }
        } else if (next_index >> level) == node + 1 {
            // The right sibling's subtree holds later queries: the last of
            // them continues from here with this hash as its left sibling.
            stack.push(level, hasher.read_state_for_output_ref());
            return true;
        }
        {
            let proof_buf = hasher.get_merkle_path_proof_buffer(is_right);
            let mut i = 0;
            while i < BLAKE2S_DIGEST_SIZE_U32_WORDS {
                proof_buf[i] = nd_source.read_word();
                i += 1;
            }
            hasher.compress_node::<true>(is_right);
        }
        node >>= 1;
        level += 1;
    }

    // A zero-column oracle has no Merkle tree — nothing to verify.
    if cap.is_empty() {
        return true;
    }
    let output_hash = hasher.read_state_for_output_ref();
    debug_assert!(cap.len() >= (node + 1) * BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let cap_start = node * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    unsafe {
        *output_hash.get_unchecked(0) == *cap.get_unchecked(cap_start)
            && *output_hash.get_unchecked(1) == *cap.get_unchecked(cap_start + 1)
            && *output_hash.get_unchecked(2) == *cap.get_unchecked(cap_start + 2)
            && *output_hash.get_unchecked(3) == *cap.get_unchecked(cap_start + 3)
            && *output_hash.get_unchecked(4) == *cap.get_unchecked(cap_start + 4)
            && *output_hash.get_unchecked(5) == *cap.get_unchecked(cap_start + 5)
            && *output_hash.get_unchecked(6) == *cap.get_unchecked(cap_start + 6)
            && *output_hash.get_unchecked(7) == *cap.get_unchecked(cap_start + 7)
    }
}

/// The prover side of the walk: which path levels of the `j`-th sorted query
/// ship a sibling, in the order the verifier reads them. `stack_levels`
/// mirrors the verifier's stack (levels only) across the calls for one tree,
/// starting empty. `sorted` holds the tree indices in sorted order.
#[cfg(any(test, feature = "proof_utils"))]
pub fn shipped_sibling_levels(
    sorted: &[usize],
    j: usize,
    depth: usize,
    stack_levels: &mut alloc::vec::Vec<usize>,
) -> alloc::vec::Vec<usize> {
    let index = sorted[j];
    let prev_index_equal = j > 0 && sorted[j - 1] == index;
    let next_index = if j + 1 < sorted.len() {
        sorted[j + 1]
    } else {
        NO_NEXT_INDEX
    };
    let mut levels = alloc::vec::Vec::new();
    if prev_index_equal {
        assert_eq!(stack_levels.pop(), Some(0));
    }
    if next_index == index {
        stack_levels.push(0);
        return levels;
    }
    let mut node = index;
    for level in 0..depth {
        if node & 1 == 1 {
            if stack_levels.last() == Some(&level) {
                stack_levels.pop();
                node >>= 1;
                continue;
            }
        } else if (next_index >> level) == node + 1 {
            stack_levels.push(level);
            return levels;
        }
        levels.push(level);
        node >>= 1;
    }
    levels
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::hash_leaf_data_into_state;
    use blake2s_u32::{AlignedArray64, BLAKE2S_BLOCK_SIZE_U32_WORDS};

    type Digest = [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];

    fn leaf_hash(hasher: &mut DelegatedBlake2sState, leaf: &[u32; 4]) -> Digest {
        let mut buf = AlignedArray64::<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>::from_value(0);
        buf[..4].copy_from_slice(leaf);
        hash_leaf_data_into_state(hasher, &buf, 4);
        *hasher.read_state_for_output_ref()
    }

    fn hash_pair(hasher: &mut DelegatedBlake2sState, left: &Digest, right: &Digest) -> Digest {
        *hasher.get_merkle_path_proof_buffer(true) = *left;
        hasher.reset_with_chaining_value(right);
        hasher.compress_node::<true>(true);
        *hasher.read_state_for_output_ref()
    }

    /// Levels of a tree over `leaves`, level 0 = leaf hashes.
    fn build_tree(hasher: &mut DelegatedBlake2sState, leaves: &[[u32; 4]]) -> Vec<Vec<Digest>> {
        let mut levels = vec![leaves
            .iter()
            .map(|l| leaf_hash(hasher, l))
            .collect::<Vec<_>>()];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let next: Vec<Digest> = prev
                .chunks(2)
                .map(|pair| hash_pair(hasher, &pair[0], &pair[1]))
                .collect();
            levels.push(next);
        }
        levels
    }

    /// Flatten the openings of `queries` (draw order) the way the flattener
    /// does: per sorted query its leaf words and shipped siblings. Returns
    /// the stream and the sorted indices.
    fn flatten(
        tree: &[Vec<Digest>],
        leaves: &[[u32; 4]],
        queries: &[usize],
        depth: usize,
    ) -> (Vec<u32>, Vec<usize>) {
        let mut perm: Vec<usize> = (0..queries.len()).collect();
        perm.sort_by_key(|&p| queries[p]);
        let sorted: Vec<usize> = perm.iter().map(|&p| queries[p]).collect();
        let mut nds: Vec<u32> = Vec::new();
        let mut stack_levels = Vec::new();
        for j in 0..sorted.len() {
            nds.extend_from_slice(&leaves[sorted[j]]);
            for level in shipped_sibling_levels(&sorted, j, depth, &mut stack_levels) {
                let node = sorted[j] >> level;
                nds.extend_from_slice(&tree[level][node ^ 1]);
            }
        }
        assert!(stack_levels.is_empty());
        (nds, sorted)
    }

    fn verify(
        nds: &[u32],
        queries: &[usize],
        leaves_count: usize,
        depth: usize,
        cap: &[u32],
    ) -> bool {
        let index_bits = leaves_count.trailing_zeros() as usize;
        const MAX_Q: usize = 64;
        const MAX_DEPTH: usize = 16;
        let mut it = nds.iter().copied();
        let mut hasher = DelegatedBlake2sState::new();
        let mut tree_indices = LazyVec::<usize, MAX_Q>::new();
        for &q in queries {
            tree_indices.push(q);
        }
        let mut perm = LazyVec::<usize, MAX_Q>::new();
        let mut sorted = LazyVec::<usize, MAX_Q>::new();
        sort_queries_by_tree_index::<MAX_Q>(&tree_indices, index_bits, &mut perm, &mut sorted);
        {
            // stable, and the same order the flattener used
            let mut expect: Vec<usize> = (0..queries.len()).collect();
            expect.sort_by_key(|&p| queries[p]);
            assert_eq!(perm.as_slice(), &expect[..]);
        }
        let mut stack = MerkleMultiproofStack::<MAX_DEPTH>::new();
        for j in 0..queries.len() {
            let index = *sorted.get(j);
            assert!(index < leaves_count);
            let mut leaf = [0u32; 4];
            for w in leaf.iter_mut() {
                *w = it.next().unwrap();
            }
            leaf_hash(&mut hasher, &leaf);
            let prev_equal = j > 0 && *sorted.get(j - 1) == index;
            let next = if j + 1 < queries.len() {
                *sorted.get(j + 1)
            } else {
                NO_NEXT_INDEX
            };
            if !verify_merkle_multiproof_leaf::<_, MAX_DEPTH>(
                &mut hasher,
                &mut stack,
                index,
                prev_equal,
                next,
                depth,
                cap,
                &mut it,
            ) {
                return false;
            }
        }
        assert!(stack.is_empty());
        it.next().is_none()
    }

    fn run_case(tree_log2: usize, cap_log2: usize, queries: &[usize], seed: u32) {
        let num_leaves = 1usize << tree_log2;
        let mut state = seed;
        let leaves: Vec<[u32; 4]> = (0..num_leaves)
            .map(|_| {
                core::array::from_fn(|_| {
                    state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                    state >> 1
                })
            })
            .collect();
        let mut hasher = DelegatedBlake2sState::new();
        let tree = build_tree(&mut hasher, &leaves);
        let depth = tree_log2 - cap_log2;
        let cap: Vec<u32> = tree[depth].iter().flatten().copied().collect();
        let (nds, sorted) = flatten(&tree, &leaves, queries, depth);

        // Fewer shipped siblings than independent paths whenever paths merge.
        let shipped = (nds.len() - queries.len() * 4) / 8;
        let mut distinct = 0;
        for level in 1..=depth {
            let mut nodes: Vec<usize> = sorted.iter().map(|&i| i >> level).collect();
            nodes.dedup();
            distinct += nodes.len();
        }
        let leaves_distinct = {
            let mut s = sorted.clone();
            s.dedup();
            s.len()
        };
        // Every distinct ancestor costs one compression whose sibling input is
        // either shipped or computed; the computed ones are exactly the merges
        // (distinct leaves minus distinct cap nodes).
        assert_eq!(
            shipped,
            distinct - (leaves_distinct - distinct_at_cap(&sorted, depth)),
            "case {tree_log2}/{cap_log2}/{queries:?}"
        );
        assert!(verify(&nds, queries, num_leaves, depth, &cap));

        // Any tampering (a leaf word, a sibling) is rejected.
        for pos in [0, 2, nds.len() - 1] {
            let mut bad = nds.clone();
            bad[pos] ^= 1;
            assert!(
                !verify(&bad, queries, num_leaves, depth, &cap),
                "tamper at {pos}"
            );
        }
        let mut bad_cap = cap.clone();
        bad_cap[(sorted[0] >> depth) * BLAKE2S_DIGEST_SIZE_U32_WORDS] ^= 1;
        assert!(!verify(&nds, queries, num_leaves, depth, &bad_cap), "cap");
    }

    fn distinct_at_cap(sorted: &[usize], depth: usize) -> usize {
        let mut nodes: Vec<usize> = sorted.iter().map(|&i| i >> depth).collect();
        nodes.dedup();
        nodes.len()
    }

    #[test]
    fn multiproof_round_trips_and_rejects_tampering() {
        run_case(3, 0, &[5, 2, 6, 0], 1);
        run_case(
            4,
            1,
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            2,
        );
        run_case(5, 2, &[31, 0, 17, 16, 3, 30], 3);
        run_case(6, 2, &[7, 7, 9, 7, 40, 41, 41, 2, 63], 4);
        run_case(6, 6, &[3, 3, 60, 1], 5);
        run_case(8, 4, &[200, 13, 13, 199, 201, 0, 255, 128, 127, 64, 65], 6);
    }
}
