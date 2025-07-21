use super::context::{HostAllocator, ProverContext};
use super::BF;
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{gather_merkle_paths, gather_rows, Digest};
use crate::device_structures::{DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut};
use crate::prover::callbacks::Callbacks;
use crate::prover::setup::SetupPrecomputations;
use crate::prover::stage_1::StageOneOutput;
use crate::prover::stage_2::StageTwoOutput;
use crate::prover::stage_3::StageThreeOutput;
use crate::prover::stage_4::StageFourOutput;
use crate::prover::stage_5::StageFiveOutput;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use itertools::Itertools;
use prover::definitions::{FoldingDescription, Transcript};
use prover::prover_stages::query_producer::{assemble_query_index, BitSource};
use prover::prover_stages::stage5::Query;
use prover::prover_stages::QuerySet;
use prover::transcript::Seed;
use std::alloc::Allocator;
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex};

struct LeafsAndDigests<A: Allocator> {
    leafs: Vec<BF, A>,
    digests: Vec<Digest, A>,
}

struct LeafsAndDigestsSet<A: Allocator> {
    witness: LeafsAndDigests<A>,
    memory: LeafsAndDigests<A>,
    setup: LeafsAndDigests<A>,
    stage_2: LeafsAndDigests<A>,
    quotient: LeafsAndDigests<A>,
    initial_fri: LeafsAndDigests<A>,
    intermediate_fri: Vec<LeafsAndDigests<A>>,
}

pub(crate) struct QueriesOutput<'a> {
    leafs_and_digest_sets: Vec<LeafsAndDigestsSet<HostAllocator>>,
    query_indexes: Arc<Mutex<Vec<u32>>>,
    log_domain_size: u32,
    folding_sequence: Vec<u32>,
    callbacks: Callbacks<'a>,
}

impl<'a> QueriesOutput<'a> {
    pub fn new(
        seed: Arc<Mutex<Seed>>,
        setup: &SetupPrecomputations,
        stage_1_output: &StageOneOutput,
        stage_2_output: &StageTwoOutput,
        stage_3_output: &StageThreeOutput,
        stage_4_output: &StageFourOutput,
        stage_5_output: &StageFiveOutput,
        log_domain_size: u32,
        log_lde_factor: u32,
        num_queries: usize,
        folding_description: &FoldingDescription,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let tree_index_bits = log_domain_size;
        let tree_index_mask = (1 << tree_index_bits) - 1;
        let coset_index_bits = log_lde_factor;
        let lde_factor = 1 << log_lde_factor;
        let log_tree_cap_size = folding_description.total_caps_size_log2 as u32;
        let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
        let query_index_bits = tree_index_bits + coset_index_bits;
        let num_required_bits = query_index_bits * num_queries as u32;
        let num_required_words = num_required_bits.next_multiple_of(u32::BITS) / u32::BITS;
        let num_required_words_padded =
            (num_required_words as usize + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
        let query_indexes = Vec::with_capacity(num_queries);
        let query_indexes = Arc::new(Mutex::new(query_indexes));
        let mut tree_indexes = Vec::with_capacity_in(num_queries, HostAllocator::default());
        unsafe { tree_indexes.set_len(num_queries) };
        let tree_indexes = Arc::new(Mutex::new(tree_indexes));
        let query_indexes_clone = query_indexes.clone();
        let tree_indexes_clone = tree_indexes.clone();
        let get_query_indexes = move || {
            let mut query_indexes = query_indexes_clone.lock().unwrap();
            let mut tree_indexes = tree_indexes_clone.lock().unwrap();
            let mut source = vec![0u32; num_required_words_padded];
            Transcript::draw_randomness(&mut seed.lock().unwrap(), &mut source);
            let mut bit_source = BitSource::new(source[1..].to_vec());
            for i in 0..num_queries {
                let query_index =
                    assemble_query_index(query_index_bits as usize, &mut bit_source) as u32;
                let tree_index = query_index & tree_index_mask;
                query_indexes.push(query_index);
                tree_indexes[i] = tree_index;
            }
        };
        let mut callbacks = Callbacks::new();
        let stream = context.get_exec_stream();
        callbacks.schedule(get_query_indexes, stream)?;
        let mut leafs_and_digest_sets = Vec::with_capacity(lde_factor);
        for coset_idx in 0..lde_factor {
            let mut h_tree_indexes = Vec::with_capacity_in(num_queries, HostAllocator::default());
            unsafe { h_tree_indexes.set_len(num_queries) };
            let h_tree_indexes = Arc::new(Mutex::new(h_tree_indexes));
            let tree_indexes_clone = tree_indexes.clone();
            let h_tree_indexes_clone = h_tree_indexes.clone();
            let copy_tree_indexes = move || {
                h_tree_indexes_clone
                    .lock()
                    .unwrap()
                    .copy_from_slice(&tree_indexes_clone.lock().unwrap());
            };
            callbacks.schedule(copy_tree_indexes, stream)?;
            let mut d_tree_indexes = context.alloc(num_queries, AllocationPlacement::BestFit)?;
            memory_copy_async(
                d_tree_indexes.deref_mut(),
                h_tree_indexes.lock().unwrap().deref(),
                stream,
            )?;
            let mut log_domain_size = log_domain_size;
            let mut layers_count = log_domain_size - log_coset_tree_cap_size;
            let witness_holder = &stage_1_output.witness_holder;
            let witness = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                witness_holder.get_coset_evaluations(coset_idx),
                &witness_holder.trees[coset_idx],
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            let memory_holder = &stage_1_output.memory_holder;
            let memory = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                memory_holder.get_coset_evaluations(coset_idx),
                &memory_holder.trees[coset_idx],
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            let setup_holder = &setup.trace_holder;
            let setup = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                setup_holder.get_coset_evaluations(coset_idx),
                &setup_holder.trees[coset_idx],
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            let stage_2_holder = &stage_2_output.trace_holder;
            let stage_2 = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                &stage_2_holder.get_coset_evaluations(coset_idx),
                &stage_2_holder.trees[coset_idx],
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            let stage_3_holder = &stage_3_output.trace_holder;
            let quotient = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                &stage_3_holder.get_coset_evaluations(coset_idx),
                &stage_3_holder.trees[coset_idx],
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            let folding_sequence = folding_description.folding_sequence;
            let initial_log_fold = folding_sequence[0] as u32;
            let h_tree_indexes_clone = h_tree_indexes.clone();
            let initial_indexes_fold_fn = move || {
                h_tree_indexes_clone
                    .lock()
                    .unwrap()
                    .iter_mut()
                    .for_each(|x| *x >>= initial_log_fold);
            };
            callbacks.schedule(initial_indexes_fold_fn, stream)?;
            memory_copy_async(
                d_tree_indexes.deref_mut(),
                h_tree_indexes.lock().unwrap().deref(),
                stream,
            )?;
            layers_count -= initial_log_fold;
            let stage_4_holder = &stage_4_output.trace_holder;
            let initial_fri = Self::get_leafs_and_digests(
                &d_tree_indexes,
                false,
                unsafe { stage_4_holder.get_coset_evaluations(coset_idx).transmute() },
                &stage_4_holder.trees[coset_idx],
                log_domain_size + 2,
                initial_log_fold + 2,
                layers_count,
                context,
            )?;
            log_domain_size -= initial_log_fold;
            let mut intermediate_fri = vec![];
            for (i, intermediate_oracle) in stage_5_output.fri_oracles.iter().enumerate() {
                if intermediate_oracle.trees.is_empty() {
                    continue;
                }
                let log_fold = folding_sequence[i + 1] as u32;
                layers_count -= log_fold;
                let h_tree_indexes_clone = h_tree_indexes.clone();
                let indexes_fold_fn = move || {
                    h_tree_indexes_clone
                        .lock()
                        .unwrap()
                        .iter_mut()
                        .for_each(|x| *x >>= log_fold);
                };
                callbacks.schedule(indexes_fold_fn, stream)?;
                memory_copy_async(
                    d_tree_indexes.deref_mut(),
                    h_tree_indexes.lock().unwrap().deref(),
                    stream,
                )?;
                let queries = Self::get_leafs_and_digests(
                    &d_tree_indexes,
                    false,
                    unsafe { intermediate_oracle.ldes[coset_idx].transmute() },
                    &intermediate_oracle.trees[coset_idx],
                    log_domain_size + 2,
                    log_fold + 2,
                    layers_count,
                    context,
                )?;
                log_domain_size -= log_fold;
                intermediate_fri.push(queries);
            }
            let set = LeafsAndDigestsSet {
                witness,
                memory,
                setup,
                stage_2,
                quotient,
                initial_fri,
                intermediate_fri,
            };
            leafs_and_digest_sets.push(set);
        }
        let folding_sequence = folding_description
            .folding_sequence
            .iter()
            .map(|&x| x as u32)
            .collect_vec();
        let result = Self {
            leafs_and_digest_sets,
            query_indexes,
            log_domain_size,
            folding_sequence,
            callbacks,
        };
        Ok(result)
    }

    fn get_leafs_and_digests(
        indexes: &DeviceSlice<u32>,
        bit_reverse_leaf_indexing: bool,
        values: &DeviceSlice<BF>,
        tree: &DeviceSlice<Digest>,
        log_domain_size: u32,
        log_rows_per_index: u32,
        layers_count: u32,
        context: &ProverContext,
    ) -> CudaResult<LeafsAndDigests<HostAllocator>> {
        let queries_count = indexes.len();
        let domain_size = 1 << log_domain_size;
        let values_matrix = DeviceMatrix::new(values, domain_size);
        let columns_count = values_matrix.cols();
        let values_per_column_count = queries_count << log_rows_per_index;
        let leafs_len = values_per_column_count * columns_count;
        let stream = context.get_exec_stream();
        let mut d_leafs = context.alloc(leafs_len, AllocationPlacement::BestFit)?;
        let mut leafs_matrix = DeviceMatrixMut::new(&mut d_leafs, values_per_column_count);
        gather_rows(
            indexes,
            bit_reverse_leaf_indexing,
            log_rows_per_index,
            &values_matrix,
            &mut leafs_matrix,
            stream,
        )?;
        let mut leafs = Vec::with_capacity_in(leafs_len, HostAllocator::default());
        unsafe { leafs.set_len(leafs_len) };
        memory_copy_async(&mut leafs, d_leafs.deref(), stream)?;
        d_leafs.free();
        let digests_len = queries_count * layers_count as usize;
        let mut d_digests = context.alloc(digests_len, AllocationPlacement::BestFit)?;
        gather_merkle_paths(indexes, tree, &mut d_digests, layers_count, stream)?;
        let mut digests = Vec::with_capacity_in(digests_len, HostAllocator::default());
        unsafe { digests.set_len(digests_len) };
        memory_copy_async(&mut digests, d_digests.deref(), stream)?;
        let result = LeafsAndDigests { leafs, digests };
        Ok(result)
    }

    fn produce_queries(
        query_indexes: &[u32],
        tree_indexes: &[u32],
        leafs_and_digests: &LeafsAndDigests<HostAllocator>,
        log_rows_per_index: u32,
    ) -> Vec<Query> {
        let queries_count = query_indexes.len();
        let leafs = &leafs_and_digests.leafs;
        let digests = &leafs_and_digests.digests;
        let values_per_column_count = queries_count << log_rows_per_index;
        assert_eq!(leafs.len() % values_per_column_count, 0);
        let columns_count = leafs.len() / values_per_column_count;
        assert_eq!(digests.len() % queries_count, 0);
        let layers_count = digests.len() / queries_count;
        let produce_query = |(i, &query_index)| {
            let tree_index = tree_indexes[i];
            let mut leaf_content = Vec::with_capacity(columns_count << log_rows_per_index);
            let leaf_offset = i << log_rows_per_index;
            for col in 0..columns_count {
                for row in 0..1 << log_rows_per_index {
                    leaf_content.push(leafs[leaf_offset + values_per_column_count * col + row]);
                }
            }
            let mut merkle_proof = Vec::with_capacity(layers_count);
            for layer in 0..layers_count {
                merkle_proof.push(digests[i + layer * queries_count]);
            }
            Query {
                query_index,
                tree_index,
                leaf_content,
                merkle_proof,
            }
        };
        let mut queries = Vec::with_capacity(queries_count);
        query_indexes
            .iter()
            .enumerate()
            .map(produce_query)
            .for_each(|query| queries.push(query));
        queries
    }

    pub fn produce_query_sets(self) -> Vec<QuerySet> {
        drop(self.callbacks);
        let query_indexes = self.query_indexes.lock().unwrap().clone();
        let tree_index_bits = self.log_domain_size;
        let tree_index_mask = (1 << tree_index_bits) - 1;
        let tree_indexes = query_indexes
            .iter()
            .map(|&x| x & tree_index_mask)
            .collect_vec();
        let mut witness_queries_by_coset = vec![];
        let mut memory_queries_by_coset = vec![];
        let mut setup_queries_by_coset = vec![];
        let mut stage_2_queries_by_coset = vec![];
        let mut quotient_queries_by_coset = vec![];
        let mut initial_fri_queries_by_coset = vec![];
        let mut intermediate_fri_queries_by_coset = vec![];
        for set in self.leafs_and_digest_sets.iter() {
            let mut tree_indexes = tree_indexes.clone();
            let witness = Self::produce_queries(&query_indexes, &tree_indexes, &set.witness, 0);
            witness_queries_by_coset.push(witness);
            let memory = Self::produce_queries(&query_indexes, &tree_indexes, &set.memory, 0);
            memory_queries_by_coset.push(memory);
            let setup = Self::produce_queries(&query_indexes, &tree_indexes, &set.setup, 0);
            setup_queries_by_coset.push(setup);
            let stage_2 = Self::produce_queries(&query_indexes, &tree_indexes, &set.stage_2, 0);
            stage_2_queries_by_coset.push(stage_2);
            let quotient = Self::produce_queries(&query_indexes, &tree_indexes, &set.quotient, 0);
            quotient_queries_by_coset.push(quotient);
            let initial_log_fold = self.folding_sequence[0];
            tree_indexes
                .iter_mut()
                .for_each(|x| *x >>= initial_log_fold);
            let initial_fri = Self::produce_queries(
                &query_indexes,
                &tree_indexes,
                &set.initial_fri,
                initial_log_fold + 2,
            );
            initial_fri_queries_by_coset.push(initial_fri);
            let intermediate_fri = set
                .intermediate_fri
                .iter()
                .zip(self.folding_sequence.iter().skip(1))
                .map(|(leafs_and_digests, &fold)| {
                    tree_indexes.iter_mut().for_each(|x| *x >>= fold);
                    Self::produce_queries(
                        &query_indexes,
                        &tree_indexes,
                        leafs_and_digests,
                        fold + 2,
                    )
                })
                .collect_vec();
            intermediate_fri_queries_by_coset.push(intermediate_fri);
        }
        let result = query_indexes
            .iter()
            .enumerate()
            .map(|(i, &query_index)| {
                let coset_index = query_index as usize >> tree_index_bits;
                let set = QuerySet {
                    witness_query: witness_queries_by_coset[coset_index][i].clone(),
                    memory_query: memory_queries_by_coset[coset_index][i].clone(),
                    setup_query: setup_queries_by_coset[coset_index][i].clone(),
                    stage_2_query: stage_2_queries_by_coset[coset_index][i].clone(),
                    quotient_query: quotient_queries_by_coset[coset_index][i].clone(),
                    initial_fri_query: initial_fri_queries_by_coset[coset_index][i].clone(),
                    intermediate_fri_queries: intermediate_fri_queries_by_coset[coset_index]
                        .iter()
                        .map(|queries| queries[i].clone())
                        .collect_vec(),
                };
                set
            })
            .collect_vec();
        result
    }
}

// fn produce_queries(
//     query_indexes: &[u32],
//     tree_indexes: &[u32],
//     indexes: &DeviceSlice<u32>,
//     bit_reverse_leaf_indexing: bool,
//     values: &DeviceSlice<BF>,
//     tree: &DeviceSlice<Digest>,
//     log_domain_size: u32,
//     log_rows_per_index: u32,
//     layers_count: u32,
//     context: &impl ProverContext,
// ) -> CudaResult<VecDeque<Query>> {
//     let queries_count = query_indexes.len();
//     let domain_size = 1 << log_domain_size;
//     let values_matrix = DeviceMatrix::new(values, domain_size);
//     let columns_count = values_matrix.cols();
//     let values_per_column_count = queries_count << log_rows_per_index;
//     let leafs_len = values_per_column_count * columns_count;
//     let stream = context.get_exec_stream();
//     let mut d_leafs = context.alloc(leafs_len)?;
//     let mut h_leafs = vec![BF::default(); leafs_len];
//     let mut leafs_matrix = DeviceMatrixMut::new(&mut d_leafs, values_per_column_count);
//     gather_rows(
//         indexes,
//         bit_reverse_leaf_indexing,
//         log_rows_per_index,
//         &values_matrix,
//         &mut leafs_matrix,
//         stream,
//     )?;
//     memory_copy_async(&mut h_leafs, d_leafs.deref(), stream)?;
//     let digests_len = queries_count * layers_count as usize;
//     let mut d_digests = context.alloc(digests_len)?;
//     let mut h_digests = vec![Digest::default(); digests_len];
//     gather_merkle_paths(indexes, tree, &mut d_digests, layers_count, stream)?;
//     memory_copy_async(&mut h_digests, d_digests.deref(), stream)?;
//     stream.synchronize()?;
//     let produce_query = |(i, &query_index)| {
//         let tree_index = tree_indexes[i];
//         let mut leaf_content = Vec::with_capacity(columns_count << log_rows_per_index);
//         let leaf_offset = i << log_rows_per_index;
//         for col in 0..columns_count {
//             for row in 0..1 << log_rows_per_index {
//                 leaf_content.push(h_leafs[leaf_offset + values_per_column_count * col + row]);
//             }
//         }
//         let mut merkle_proof = Vec::with_capacity(layers_count as usize);
//         for layer in 0..layers_count {
//             merkle_proof.push(h_digests[i + layer as usize * queries_count]);
//         }
//         Query {
//             query_index,
//             tree_index,
//             leaf_content,
//             merkle_proof,
//         }
//     };
//     let mut queries = VecDeque::with_capacity(queries_count);
//     query_indexes
//         .iter()
//         .enumerate()
//         .map(produce_query)
//         .for_each(|query| queries.push_back(query));
//     Ok(queries)
// }
//
// struct QueriesSet {
//     witness_queries: VecDeque<Query>,
//     memory_queries: VecDeque<Query>,
//     setup_queries: VecDeque<Query>,
//     stage_2_queries: VecDeque<Query>,
//     quotient_queries: VecDeque<Query>,
//     initial_fri_queries: VecDeque<Query>,
//     intermediate_fri_queries: Vec<VecDeque<Query>>,
// }
//
// pub fn get_queries<C: ProverContext>(
//     mut seed: Seed,
//     setup_output: &SetupOutput<C>,
//     stage_1_output: &StageOneOutput<C>,
//     stage_2_output: &StageTwoOutput<C>,
//     stage_3_output: &StageThreeOutput<C>,
//     stage_4_output: &StageFourOutput<C>,
//     stage_5_output: &StageFiveOutput<C>,
//     log_domain_size: u32,
//     log_lde_factor: u32,
//     num_queries: usize,
//     folding_description: &FoldingDescription,
//     context: &C,
// ) -> CudaResult<Vec<QuerySet>> {
//     let tree_index_bits = log_domain_size;
//     let tree_index_mask = (1 << tree_index_bits) - 1;
//     let coset_index_bits = log_lde_factor;
//     let lde_factor = 1 << log_lde_factor;
//     let log_tree_cap_size = folding_description.total_caps_size_log2 as u32;
//     let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
//     let query_index_bits = tree_index_bits + coset_index_bits;
//     let num_required_bits = query_index_bits * num_queries as u32;
//     let num_required_words = num_required_bits.next_multiple_of(u32::BITS) / u32::BITS;
//     let num_required_words_padded =
//         (num_required_words as usize + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
//     let mut source = vec![0u32; num_required_words_padded];
//     Transcript::draw_randomness(&mut seed, &mut source);
//     let mut bit_source = BitSource::new(source[1..].to_vec());
//     let mut query_indexes = Vec::with_capacity(num_queries);
//     let mut query_indexes_by_coset = vec![Vec::default(); lde_factor];
//     let mut tree_indexes_by_coset = vec![Vec::default(); lde_factor];
//     let mut queries_sets_by_coset = vec![];
//     for _ in 0..num_queries {
//         let query_index = assemble_query_index(query_index_bits as usize, &mut bit_source);
//         let tree_index = (query_index & tree_index_mask) as u32;
//         let coset_index = query_index >> tree_index_bits;
//         let query_index = query_index as u32;
//         query_indexes.push(query_index);
//         query_indexes_by_coset[coset_index].push(query_index);
//         tree_indexes_by_coset[coset_index].push(tree_index);
//     }
//     for (coset_idx, (query_indexes, tree_indexes)) in query_indexes_by_coset
//         .iter()
//         .zip(tree_indexes_by_coset.iter())
//         .enumerate()
//     {
//         let len = query_indexes.len();
//         let queries_set = if len == 0 {
//             QueriesSet {
//                 witness_queries: VecDeque::default(),
//                 memory_queries: VecDeque::default(),
//                 setup_queries: VecDeque::default(),
//                 stage_2_queries: VecDeque::default(),
//                 quotient_queries: VecDeque::default(),
//                 initial_fri_queries: VecDeque::default(),
//                 intermediate_fri_queries: vec![],
//             }
//         } else {
//             let mut log_domain_size = log_domain_size;
//             let mut layers_count = log_domain_size - log_coset_tree_cap_size;
//             let mut h_tree_indexes = tree_indexes.clone();
//             let h_bitreversed_tree_indexes = tree_indexes
//                 .iter()
//                 .map(|&x| bitreverse_index(x as usize, log_domain_size) as u32)
//                 .collect_vec();
//             let stream = context.get_exec_stream();
//             let mut d_tree_indexes = context.alloc(len)?;
//             let mut d_bitreversed_tree_indexes = context.alloc(len)?;
//             memory_copy_async(d_tree_indexes.deref_mut(), &h_tree_indexes, stream)?;
//             memory_copy_async(
//                 d_bitreversed_tree_indexes.deref_mut(),
//                 &h_bitreversed_tree_indexes,
//                 stream,
//             )?;
//             let witness_values_count = stage_1_output.witness_columns_count << log_domain_size;
//             let witness_queries = produce_queries(
//                 query_indexes,
//                 &h_tree_indexes,
//                 &d_tree_indexes,
//                 true,
//                 &stage_1_output.ldes[coset_idx][..witness_values_count],
//                 &stage_1_output.witness_trees[coset_idx],
//                 log_domain_size,
//                 0,
//                 layers_count,
//                 context,
//             )?;
//             let memory_values_count = stage_1_output.memory_columns_count << log_domain_size;
//             let memory_queries = produce_queries(
//                 query_indexes,
//                 &h_tree_indexes,
//                 &d_tree_indexes,
//                 true,
//                 &stage_1_output.ldes[coset_idx]
//                     [witness_values_count..witness_values_count + memory_values_count],
//                 &stage_1_output.memory_trees[coset_idx],
//                 log_domain_size,
//                 0,
//                 layers_count,
//                 context,
//             )?;
//             let setup_values_count = setup_output.columns_count << log_domain_size;
//             let setup_queries = produce_queries(
//                 query_indexes,
//                 &h_tree_indexes,
//                 &d_tree_indexes,
//                 true,
//                 &setup_output.ldes[coset_idx][..setup_values_count],
//                 &setup_output.trees[coset_idx],
//                 log_domain_size,
//                 0,
//                 layers_count,
//                 context,
//             )?;
//             let stage_2_queries = produce_queries(
//                 query_indexes,
//                 &h_tree_indexes,
//                 &d_tree_indexes,
//                 true,
//                 &stage_2_output.ldes[coset_idx],
//                 &stage_2_output.trees[coset_idx],
//                 log_domain_size,
//                 0,
//                 layers_count,
//                 context,
//             )?;
//             let quotient_queries = produce_queries(
//                 query_indexes,
//                 &h_tree_indexes,
//                 &d_tree_indexes,
//                 true,
//                 &stage_3_output.ldes[coset_idx],
//                 &stage_3_output.trees[coset_idx],
//                 log_domain_size,
//                 0,
//                 layers_count,
//                 context,
//             )?;
//             let folding_sequence = folding_description.folding_sequence;
//             let initial_log_fold = folding_sequence[0] as u32;
//             h_tree_indexes
//                 .iter_mut()
//                 .for_each(|x| *x >>= initial_log_fold);
//             memory_copy_async(d_tree_indexes.deref_mut(), &h_tree_indexes, stream)?;
//             layers_count -= initial_log_fold;
//             let initial_fri_queries = produce_queries(
//                 query_indexes,
//                 &h_tree_indexes,
//                 &d_tree_indexes,
//                 false,
//                 unsafe { stage_4_output.ldes[coset_idx].transmute() },
//                 &stage_4_output.trees[coset_idx],
//                 log_domain_size + 2,
//                 initial_log_fold + 2,
//                 layers_count,
//                 context,
//             )?;
//             log_domain_size -= initial_log_fold;
//             let mut intermediate_fri_queries = vec![];
//             for (i, intermediate_oracle) in stage_5_output.fri_oracles.iter().enumerate() {
//                 if intermediate_oracle.trees.is_empty() {
//                     continue;
//                 }
//                 let log_fold = folding_sequence[i + 1] as u32;
//                 layers_count -= log_fold;
//                 h_tree_indexes.iter_mut().for_each(|x| *x >>= log_fold);
//                 memory_copy_async(d_tree_indexes.deref_mut(), &h_tree_indexes, stream)?;
//                 let queries = produce_queries(
//                     query_indexes,
//                     &h_tree_indexes,
//                     &d_tree_indexes,
//                     false,
//                     unsafe { intermediate_oracle.ldes[coset_idx].transmute() },
//                     &intermediate_oracle.trees[coset_idx],
//                     log_domain_size + 2,
//                     log_fold + 2,
//                     layers_count,
//                     context,
//                 )?;
//                 log_domain_size -= log_fold;
//                 intermediate_fri_queries.push(queries);
//             }
//             QueriesSet {
//                 witness_queries,
//                 memory_queries,
//                 setup_queries,
//                 stage_2_queries,
//                 quotient_queries,
//                 initial_fri_queries,
//                 intermediate_fri_queries,
//             }
//         };
//         queries_sets_by_coset.push(queries_set);
//     }
//     let mut queries = vec![];
//     for query_index in query_indexes {
//         let query_index = query_index as usize;
//         let coset_index = query_index >> tree_index_bits;
//         let queries_set = &mut queries_sets_by_coset[coset_index];
//         let witness_query = queries_set.witness_queries.pop_front().unwrap();
//         let memory_query = queries_set.memory_queries.pop_front().unwrap();
//         let setup_query = queries_set.setup_queries.pop_front().unwrap();
//         let stage_2_query = queries_set.stage_2_queries.pop_front().unwrap();
//         let quotient_query = queries_set.quotient_queries.pop_front().unwrap();
//         let initial_fri_query = queries_set.initial_fri_queries.pop_front().unwrap();
//         let intermediate_fri_queries = queries_set
//             .intermediate_fri_queries
//             .iter_mut()
//             .map(|x| x.pop_front().unwrap())
//             .collect_vec();
//         let set = QuerySet {
//             witness_query,
//             memory_query,
//             setup_query,
//             stage_2_query,
//             quotient_query,
//             initial_fri_query,
//             intermediate_fri_queries,
//         };
//         queries.push(set);
//     }
//     Ok(queries)
// }
