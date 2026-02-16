use crate::definitions::Blake2sForEverythingVerifier;

use super::*;
use blake2s_hash_leafs::{
    blake2s_leaf_hashes_for_column_major_coset, blake2s_leaf_hashes_for_coset,
    blake2s_leaf_hashes_separated_for_coset,
};
use blake2s_u32::*;
use std::alloc::Global;

#[derive(Clone, Debug)]
pub struct Blake2sU32MerkleTreeWithCap<A: GoodAllocator = Global> {
    pub cap_size: usize,
    pub leaf_hashes: Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], A>,
    pub node_hashes_enumerated_from_leafs: Vec<Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], A>>,
}

impl<B: GoodAllocator> MerkleTreeConstructor for Blake2sU32MerkleTreeWithCap<B> {
    type Verifier = Blake2sForEverythingVerifier;

    fn construct_for_coset<A: GoodAllocator, const N: usize>(
        trace: &RowMajorTrace<Mersenne31Field, N, A>,
        cap_size: usize,
        bitreverse: bool,
        worker: &Worker,
    ) -> Self {
        let leaf_hashes = blake2s_leaf_hashes_for_coset(trace, bitreverse, worker);

        Self::continue_from_leaf_hashes(leaf_hashes, cap_size, worker)
    }

    fn construct_separated_for_coset<A: GoodAllocator, const N: usize>(
        trace: &RowMajorTrace<Mersenne31Field, N, A>,
        separators: &[usize],
        cap_size: usize,
        bitreverse: bool,
        worker: &Worker,
    ) -> Vec<Self> {
        let leaf_hashes_set =
            blake2s_leaf_hashes_separated_for_coset(trace, separators, bitreverse, worker);

        leaf_hashes_set
            .into_iter()
            .map(|lh| Self::continue_from_leaf_hashes(lh, cap_size, worker))
            .collect()
    }

    fn construct_for_column_major_coset<A: GoodAllocator>(
        trace: &ColumnMajorTrace<Mersenne31Quartic, A>,
        combine_by: usize,
        cap_size: usize,
        bitreverse: bool,
        worker: &Worker,
    ) -> Self {
        let leaf_hashes =
            blake2s_leaf_hashes_for_column_major_coset(trace, combine_by, bitreverse, worker);

        Self::continue_from_leaf_hashes(leaf_hashes, cap_size, worker)
    }

    fn get_cap(&self) -> MerkleTreeCapVarLength {
        let output = if let Some(cap) = self.node_hashes_enumerated_from_leafs.last() {
            let mut result = Vec::new();
            result.extend_from_slice(cap);

            result
        } else {
            let mut result = Vec::new();
            result.extend_from_slice(&self.leaf_hashes);

            result
        };

        MerkleTreeCapVarLength { cap: output }
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    ) {
        let depth = self.node_hashes_enumerated_from_leafs.len(); // we do not need the element of the cap
        let mut result = Vec::with_capacity_in(depth, C::default());
        let mut idx = idx;
        let this_el_leaf_hash = self.leaf_hashes[idx];
        for i in 0..depth {
            let pair_idx = idx ^ 1;
            let proof_element = if i == 0 {
                self.leaf_hashes[pair_idx]
            } else {
                self.node_hashes_enumerated_from_leafs[i - 1][pair_idx]
            };

            result.push(proof_element);
            idx >>= 1;
        }

        (this_el_leaf_hash, result)
    }

    fn dump_caps(caps: &[Self]) -> Vec<MerkleTreeCapVarLength> {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(<Self as MerkleTreeConstructor>::get_cap(el));
        }

        result
    }
}

impl<A: GoodAllocator> Blake2sU32MerkleTreeWithCap<A> {
    fn continue_from_leaf_hashes(
        leaf_hashes: Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], A>,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        assert!(leaf_hashes.len().is_power_of_two());
        assert!(cap_size.is_power_of_two());
        debug_assert!(leaf_hashes.len() >= cap_size);

        #[cfg(feature = "timing_logs")]
        println!(
            "Continuing Merkle tree construction from {} leaf hashes",
            leaf_hashes.len(),
        );

        let tree_depth = leaf_hashes.len().trailing_zeros();
        let layers_to_skip = cap_size.trailing_zeros();
        let num_layers_to_construct = tree_depth - layers_to_skip;

        if num_layers_to_construct == 0 {
            #[cfg(feature = "timing_logs")]
            println!("Do not need to construct nodes, can use leaf hashes directly to form a cap");

            assert_eq!(cap_size, leaf_hashes.len());
            return Self {
                cap_size,
                leaf_hashes,
                node_hashes_enumerated_from_leafs: Vec::new(),
            };
        }

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();

        assert!(num_layers_to_construct > 0);

        let mut previous = &leaf_hashes[..];
        let mut node_hashes_enumerated_from_leafs =
            Vec::with_capacity(num_layers_to_construct as usize);
        for _ in 0..num_layers_to_construct {
            let next_layer_len = previous.len() / 2;
            debug_assert!(next_layer_len > 0);
            debug_assert!(next_layer_len.is_power_of_two());
            let mut new_layer_node_hashes: Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], A> =
                Vec::with_capacity_in(next_layer_len, A::default());

            unsafe {
                worker.scope(next_layer_len, |scope, geometry| {
                    let mut dst = &mut new_layer_node_hashes.spare_capacity_mut()[..next_layer_len];
                    let mut src = previous;
                    for thread_idx in 0..geometry.len() {
                        let chunk_size = geometry.get_chunk_size(thread_idx);

                        let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                        dst = rest;
                        let (src_chunk, rest) = src.split_at_unchecked(chunk_size * 2);
                        src = rest;

                        Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                            let mut dst_ptr = dst_chunk.as_mut_ptr();
                            // easier to use pointers
                            let mut src_ptr = src_chunk
                                .as_ptr()
                                .cast::<[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS]>();
                            for _i in 0..chunk_size {
                                let read_from = &*src_ptr;
                                let write_into = (&mut *dst_ptr).assume_init_mut();
                                Blake2sState::compress_two_to_one::<USE_REDUCED_BLAKE2_ROUNDS>(
                                    read_from, write_into,
                                );

                                src_ptr = src_ptr.add(1);
                                dst_ptr = dst_ptr.add(1);
                            }
                        });
                    }
                });

                new_layer_node_hashes.set_len(next_layer_len)
            };

            node_hashes_enumerated_from_leafs.push(new_layer_node_hashes);
            previous = node_hashes_enumerated_from_leafs.last().unwrap();
        }

        debug_assert_eq!(previous.len(), cap_size);

        #[cfg(feature = "timing_logs")]
        println!(
            "Nodes construction of size 2^{} taken {:?}",
            leaf_hashes.len().trailing_zeros(),
            now.elapsed()
        );

        Self {
            cap_size,
            leaf_hashes,
            node_hashes_enumerated_from_leafs,
        }
    }
}

impl<F: PrimeField, B: GoodAllocator> ColumnMajorMerkleTreeConstructor<F>
    for Blake2sU32MerkleTreeWithCap<B>
{
    type Verifier = Blake2sForEverythingVerifier;

    fn dummy() -> Self {
        Blake2sU32MerkleTreeWithCap {
            cap_size: 0,
            leaf_hashes: Vec::new_in(B::default()),
            node_hashes_enumerated_from_leafs: vec![],
        }
    }

    fn get_cap(&self) -> MerkleTreeCapVarLength {
        let output = if let Some(cap) = self.node_hashes_enumerated_from_leafs.last() {
            let mut result = Vec::new();
            result.extend_from_slice(cap);

            result
        } else {
            let mut result = Vec::new();
            result.extend_from_slice(&self.leaf_hashes);

            result
        };

        MerkleTreeCapVarLength { cap: output }
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    ) {
        let depth = self.node_hashes_enumerated_from_leafs.len(); // we do not need the element of the cap
        let mut result = Vec::with_capacity_in(depth, C::default());
        let mut idx = idx;
        let this_el_leaf_hash = self.leaf_hashes[idx];
        for i in 0..depth {
            let pair_idx = idx ^ 1;
            let proof_element = if i == 0 {
                self.leaf_hashes[pair_idx]
            } else {
                self.node_hashes_enumerated_from_leafs[i - 1][pair_idx]
            };

            result.push(proof_element);
            idx >>= 1;
        }

        (this_el_leaf_hash, result)
    }

    // fn construct_for_column_major_coset<E: FieldExtension<F>, A: GoodAllocator>(
    //     trace: &[&[E]],
    //     combine_by: usize,
    //     cap_size: usize,
    //     bitreverse_input: bool,
    //     bitreverse_output: bool,
    //     worker: &Worker,
    // ) -> Self
    // where
    //     [(); E::DEGREE]: Sized,
    // {
    //     use crate::merkle_trees::blake2s_hash_leafs::blake2s_leaf_hashes_from_columns;
    //     let leaf_hashes = blake2s_leaf_hashes_from_columns::<F, E, A, _>(
    //         trace,
    //         combine_by,
    //         bitreverse_input,
    //         bitreverse_output,
    //         worker,
    //     );

    //     Self::continue_from_leaf_hashes(leaf_hashes, cap_size, worker)
    // }

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
        [(); E::DEGREE]: Sized,
    {
        use crate::merkle_trees::blake2s_hash_leafs::blake2s_leaf_hashes_from_cosets;
        let leaf_hashes = blake2s_leaf_hashes_from_cosets::<F, E, A, _>(
            trace,
            combine_by,
            bitreverse_evaluations,
            bitreverse_cosets,
            bitreverse_leaf_hashes,
            worker,
        );

        Self::continue_from_leaf_hashes(leaf_hashes, cap_size, worker)
    }
}
