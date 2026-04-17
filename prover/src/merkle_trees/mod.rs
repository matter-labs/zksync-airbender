use crate::definitions::{LeafInclusionVerifier, MerkleTreeCap, DIGEST_SIZE_U32_WORDS};

// const USE_REDUCED_BLAKE2_ROUNDS: bool = false;
const USE_REDUCED_BLAKE2_ROUNDS: bool = true;

use fft::GoodAllocator;
use field::Mersenne31Field;
use field::Mersenne31Quartic;
use trace_holder::ColumnMajorTrace;
use trace_holder::RowMajorTrace;
use worker::Worker;

pub mod blake2s_for_everything_tree;
pub mod blake2s_hash_leafs;

// Rustdoc currently struggles to normalize the inline `[u32; DIGEST_SIZE_U32_WORDS]`
// return type of `MerkleTreeConstructor::get_proof` when another crate documents APIs
// that depend on this trait. Giving the digest a stable alias keeps the public API the
// same while avoiding the problematic method-local const normalization path.
pub type MerkleTreeDigest = [u32; DIGEST_SIZE_U32_WORDS];

pub type DefaultTreeConstructor =
    crate::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap<
        std::alloc::Global,
    >;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct MerkleTreeCapVarLength {
    pub cap: Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
}

impl MerkleTreeCapVarLength {
    pub fn into_fixed_holder<const N: usize>(self) -> MerkleTreeCap<N> {
        MerkleTreeCap {
            cap: self.cap.try_into().unwrap(),
        }
    }
}

pub trait MerkleTreeConstructor: Sized + Send + Sync {
    type Verifier: LeafInclusionVerifier;

    fn construct_for_coset<A: GoodAllocator, const N: usize>(
        trace: &RowMajorTrace<Mersenne31Field, N, A>,
        cap_size: usize,
        bitreverse: bool,
        worker: &Worker,
    ) -> Self;

    fn construct_separated_for_coset<A: GoodAllocator, const N: usize>(
        trace: &RowMajorTrace<Mersenne31Field, N, A>,
        separators: &[usize],
        cap_size: usize,
        bitreverse: bool,
        worker: &Worker,
    ) -> Vec<Self>;

    fn construct_for_column_major_coset<A: GoodAllocator>(
        trace: &ColumnMajorTrace<Mersenne31Quartic, A>,
        combine_by: usize,
        cap_size: usize,
        bitreverse: bool,
        worker: &Worker,
    ) -> Self;

    fn get_cap(&self) -> MerkleTreeCapVarLength;

    fn dump_caps(caps: &[Self]) -> Vec<MerkleTreeCapVarLength> {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (MerkleTreeDigest, Vec<MerkleTreeDigest, C>);

    // pub fn verify_proof_over_cap(
    //     _proof: &[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]],
    //     _cap: &[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]],
    //     _leaf_hash: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    //     _idx: usize,
    // ) -> bool {
    //     todo!();

    //     // let mut idx = idx;
    //     // let mut current = leaf_hash;
    //     // for proof_el in proof.iter() {
    //     //     if idx & 1 == 0 {
    //     //         current = H::hash_into_node(&current, proof_el, 0);
    //     //     } else {
    //     //         current = H::hash_into_node(proof_el, &current, 0);
    //     //     }

    //     //     idx >>= 1;
    //     // }

    //     // let cap_el = &cap[idx];
    //     // H::normalize_output(&mut current);

    //     // cap_el == &current
    // }
}
