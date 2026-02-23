use crate::definitions::{LeafInclusionVerifier, MerkleTreeCap, DIGEST_SIZE_U32_WORDS};

// const USE_REDUCED_BLAKE2_ROUNDS: bool = false;
const USE_REDUCED_BLAKE2_ROUNDS: bool = true;

use fft::GoodAllocator;
use field::FieldExtension;
use field::Mersenne31Field;
use field::Mersenne31Quartic;
use field::PrimeField;
// use poseidon2::m31::HASH_SIZE_U32_WORDS;
use trace_holder::ColumnMajorTrace;
use trace_holder::RowMajorTrace;
use worker::Worker;

pub mod blake2s_for_everything_tree;
// pub mod blake2s_for_leafs_poseidon2_for_nodes_tree;
pub mod blake2s_hash_leafs;

pub type DefaultTreeConstructor =
    crate::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap<
        std::alloc::Global,
    >;

// pub type DefaultTreeConstructor =
//     crate::merkle_trees::blake2s_for_leafs_poseidon2_for_nodes_tree::Blake2sU32ForLeafsPoseidon2ForNodesTree<
//         std::alloc::Global,
//     >;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
pub struct MerkleTreeCapVarLength {
    pub cap: Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
}

impl MerkleTreeCapVarLength {
    pub fn into_fixed_holder<const N: usize>(self) -> MerkleTreeCap<N> {
        MerkleTreeCap {
            cap: self.cap.try_into().unwrap(),
        }
    }

    pub fn add_into_buffer(&self, buffer: &mut Vec<u32>) {
        for el in self.cap.iter() {
            buffer.extend_from_slice(el);
        }
    }

    pub fn estimate_size(&self) -> usize {
        self.cap.len() * DIGEST_SIZE_U32_WORDS * core::mem::size_of::<u32>()
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
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    );
}

pub trait ColumnMajorMerkleTreeConstructor<F: PrimeField>:
    Sized + Send + Sync + core::fmt::Debug
{
    type Verifier: LeafInclusionVerifier;

    fn dummy() -> Self;

    // fn construct_for_column_major_coset<E: FieldExtension<F>, A: GoodAllocator>(
    //     trace: &[&[E]],
    //     combine_by: usize,
    //     cap_size: usize,
    //     bitreverse_input: bool,
    //     bitreverse_output: bool,
    //     worker: &Worker,
    // ) -> Self
    // where
    //     [(); E::DEGREE]: Sized;

    fn construct_from_cosets<E: FieldExtension<F>, A: GoodAllocator>(
        trace: &[&[&[E]]], // slice of cosets, each coset - is a slice of column evaluations
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self
    where
        [(); E::DEGREE]: Sized;

    fn get_cap(&self) -> MerkleTreeCapVarLength;

    // fn dump_caps(caps: &[Self]) -> Vec<MerkleTreeCapVarLength> {
    //     let mut result = Vec::with_capacity(caps.len());
    //     for el in caps.iter() {
    //         result.push(el.get_cap());
    //     }

    //     result
    // }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    );
}
