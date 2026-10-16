//! Deterministic boundary-node multiproofs. Query order is not proof order:
//! leaves remain in transcript order, while authentication follows a depth-first walk.
use super::{Digest, PathQueryable};

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct MerkleMultiProof {
    pub depth: usize,
    pub siblings: Vec<Digest>,
}

/// Missing siblings in depth-first postorder of the queried subtrees.
/// Each boundary node is ordered by the right endpoint of its queried sibling's
/// subtree, then by height. This lets the verifier retain its running digest
/// through unary chains instead of materializing every intermediate frontier.
/// `depth` stops at the committed cap, not necessarily at a single root.
pub fn boundary_nodes(indices: &[usize], depth: usize) -> Vec<(usize, usize)> {
    assert!(depth < usize::BITS as usize);
    let mut frontier = indices.to_vec();
    frontier.sort_unstable();
    frontier.dedup();
    let mut boundary = Vec::new();
    for level in 0..depth {
        let mut read = 0;
        let mut write = 0;
        while read < frontier.len() {
            let index = frontier[read];
            if index & 1 == 0 && frontier.get(read + 1) == Some(&(index + 1)) {
                read += 2;
            } else {
                boundary.push((level, index ^ 1));
                read += 1;
            }
            frontier[write] = index >> 1;
            write += 1;
        }
        frontier.truncate(write);
    }
    boundary.sort_unstable_by_key(|&(level, sibling)| {
        let subtree_end = ((sibling ^ 1) << level) | ((1usize << level) - 1);
        (subtree_end, level)
    });
    boundary
}

pub fn from_tree<T: PathQueryable + ?Sized>(tree: &T, indices: &[usize]) -> MerkleMultiProof {
    let depth = tree.proof_depth();
    // Also validate indices for a cap-only tree (where no sibling is read).
    for &index in indices {
        let _ = tree.get_node(0, index);
    }
    let siblings = boundary_nodes(indices, depth)
        .into_iter()
        .map(|(level, index)| tree.get_node(level, index))
        .collect();
    MerkleMultiProof { depth, siblings }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle_trees::MerkleTreeCapVarLength;
    #[derive(Debug)]
    struct DirectTree;
    impl PathQueryable for DirectTree {
        fn proof_depth(&self) -> usize {
            3
        }
        fn get_node(&self, level: usize, index: usize) -> Digest {
            assert!(index < (16 >> level));
            [((level << 16) | index) as u32; 8]
        }
        fn get_cap(&self) -> MerkleTreeCapVarLength {
            MerkleTreeCapVarLength {
                cap: vec![self.get_node(3, 0), self.get_node(3, 1)],
            }
        }
        fn get_proof(&self, _: usize) -> (Digest, Vec<Digest>) {
            panic!("compact generation must not construct full paths")
        }
    }
    #[test]
    fn direct_boundary_generation_preserves_duplicates_and_cap_geometry() {
        let indices = [9, 1, 0, 9, 7];
        let expected = vec![(1, 1), (0, 6), (1, 2), (0, 8), (1, 5), (2, 3)];
        assert_eq!(boundary_nodes(&indices, 3), expected);
        let proof = DirectTree.get_multiproof(&indices);
        assert_eq!(proof.depth, 3);
        assert_eq!(
            proof.siblings,
            expected
                .into_iter()
                .map(|(l, i)| DirectTree.get_node(l, i))
                .collect::<Vec<_>>()
        );
        assert!(boundary_nodes(&(0..16).collect::<Vec<_>>(), 3).is_empty());
        assert!(boundary_nodes(&[], 3).is_empty());
        assert!(boundary_nodes(&indices, 0).is_empty());
    }
}
