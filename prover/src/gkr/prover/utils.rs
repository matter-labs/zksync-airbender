use crate::merkle_trees::MerkleTreeCapVarLength;

pub fn flatten_merkle_caps_iter_into(
    tree_caps_iter: impl Iterator<Item = MerkleTreeCapVarLength>,
    dst: &mut Vec<u32>,
) {
    for cap in tree_caps_iter {
        cap.add_into_buffer(dst);
    }
}
