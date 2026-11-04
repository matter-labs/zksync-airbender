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
    ) -> (MerkleTreeDigest, Vec<MerkleTreeDigest, C>) {
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
            result.push(el.get_cap());
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

        let tree_depth = leaf_hashes.len().trailing_zeros();
        let layers_to_skip = cap_size.trailing_zeros();
        let num_layers_to_construct = tree_depth - layers_to_skip;

        if num_layers_to_construct == 0 {
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

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use fft::CACHE_LINE_MULTIPLE;

//     #[test]
//     fn test_constructing_separate_merkle_trees() {
//         const LENGTH: usize = 1 << 22;
//         const WIDTH1: usize = 34;
//         const WIDTH2: usize = 75;
//         const BIG_WIDTH: usize = WIDTH1 + WIDTH2;
//         const CAP_SIZE: usize = 32;

//         let worker = Worker::new();

//         let big_trace = RowMajorTrace::new_zeroed_for_size(LENGTH, BIG_WIDTH, Global::default());
//         let trace1 = RowMajorTrace::new_zeroed_for_size(LENGTH, WIDTH1, Global::default());
//         let trace2 = RowMajorTrace::new_zeroed_for_size(LENGTH, WIDTH2, Global::default());

//         let mut view1 = trace1.row_view(0..LENGTH);
//         let mut view2 = trace2.row_view(0..LENGTH);
//         let mut big_view = big_trace.row_view(0..LENGTH);

//         for _ in 0..LENGTH {
//             let slice = get_random_slice(BIG_WIDTH);

//             view1.current_row().copy_from_slice(&slice[..WIDTH1]);
//             view2.current_row().copy_from_slice(&slice[WIDTH1..]);
//             big_view.current_row().copy_from_slice(&slice);

//             view1.advance_row();
//             view2.advance_row();
//             big_view.advance_row();
//         }

//         let big_res = Blake2sU32MerkleTreeWithCap::construct_separate_for_coset::<
//             CACHE_LINE_MULTIPLE,
//         >(&big_trace, &[WIDTH1, BIG_WIDTH], CAP_SIZE, true, &worker);

//         let res1 = Blake2sU32MerkleTreeWithCap::construct_for_coset::<CACHE_LINE_MULTIPLE>(
//             &trace1, CAP_SIZE, true, &worker,
//         );

//         let res2 = Blake2sU32MerkleTreeWithCap::construct_for_coset::<CACHE_LINE_MULTIPLE>(
//             &trace2, CAP_SIZE, true, &worker,
//         );

//         for _ in 0..9 {
//             let _res2 = Blake2sU32MerkleTreeWithCap::construct_for_coset::<CACHE_LINE_MULTIPLE>(
//                 &trace2, CAP_SIZE, true, &worker,
//             );
//         }

//         assert_eq!(res1.get_cap_ref(), big_res[0].get_cap_ref());
//         assert_eq!(res2.get_cap_ref(), big_res[1].get_cap_ref());
//     }

//     fn get_random_slice(len: usize) -> Vec<Mersenne31Field> {
//         use rand::Rng;
//         let mut rng = rand::thread_rng();

//         (0..len)
//             .map(|_| Mersenne31Field::from_u64(rng.gen_range(0..(1 << 31) - 1)).unwrap())
//             .collect()
//     }
// }
