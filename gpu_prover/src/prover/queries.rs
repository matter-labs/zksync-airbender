use super::callbacks::Callbacks;
use super::context::{HostAllocation, ProverContext, UnsafeAccessor};
use super::setup::SetupPrecomputations;
use super::stage_1::StageOneOutput;
use super::stage_2::StageTwoOutput;
use super::stage_3::StageThreeOutput;
use super::stage_4::StageFourOutput;
use super::stage_5::StageFiveOutput;
use super::BF;
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{gather_merkle_paths, gather_rows, Digest};
use crate::device_structures::{DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut};
use crate::prover::trace_holder::{CosetsHolder, TreesHolder};
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

struct LeafsAndDigests {
    leafs: HostAllocation<[BF]>,
    digests: HostAllocation<[Digest]>,
}

struct LeafsAndDigestsAccessors {
    leafs: UnsafeAccessor<[BF]>,
    digests: UnsafeAccessor<[Digest]>,
}

impl LeafsAndDigests {
    fn get_accessor(&self) -> LeafsAndDigestsAccessors {
        let leafs_accessor = self.leafs.get_accessor();
        let digests_accessor = self.digests.get_accessor();
        LeafsAndDigestsAccessors {
            leafs: leafs_accessor,
            digests: digests_accessor,
        }
    }
}

struct LeafsAndDigestsSet {
    witness: LeafsAndDigests,
    memory: LeafsAndDigests,
    setup: LeafsAndDigests,
    stage_2: LeafsAndDigests,
    quotient: LeafsAndDigests,
    initial_fri: LeafsAndDigests,
    intermediate_fri: Vec<LeafsAndDigests>,
}

struct LeafsAndDigestsSetAccessors {
    witness: LeafsAndDigestsAccessors,
    memory: LeafsAndDigestsAccessors,
    setup: LeafsAndDigestsAccessors,
    stage_2: LeafsAndDigestsAccessors,
    quotient: LeafsAndDigestsAccessors,
    initial_fri: LeafsAndDigestsAccessors,
    intermediate_fri: Vec<LeafsAndDigestsAccessors>,
}

impl LeafsAndDigestsSet {
    fn get_accessor(&self) -> LeafsAndDigestsSetAccessors {
        let witness = self.witness.get_accessor();
        let memory = self.memory.get_accessor();
        let setup = self.setup.get_accessor();
        let stage_2 = self.stage_2.get_accessor();
        let quotient = self.quotient.get_accessor();
        let initial_fri = self.initial_fri.get_accessor();
        let intermediate_fri = self
            .intermediate_fri
            .iter()
            .map(LeafsAndDigests::get_accessor)
            .collect_vec();
        LeafsAndDigestsSetAccessors {
            witness,
            memory,
            setup,
            stage_2,
            quotient,
            initial_fri,
            intermediate_fri,
        }
    }
}

pub(crate) struct QueriesOutput {
    leafs_and_digest_sets: Vec<LeafsAndDigestsSet>,
    query_indexes: HostAllocation<[u32]>,
    log_domain_size: u32,
    folding_sequence: Vec<u32>,
}

pub(crate) struct QueriesOutputAccessors {
    leafs_and_digest_sets: Vec<LeafsAndDigestsSetAccessors>,
    query_indexes: UnsafeAccessor<[u32]>,
    log_domain_size: u32,
    folding_sequence: Vec<u32>,
}

impl QueriesOutput {
    pub fn new(
        mut seed: HostAllocation<Seed>,
        setup: &mut SetupPrecomputations,
        stage_1_output: &mut StageOneOutput,
        stage_2_output: &mut StageTwoOutput,
        stage_3_output: &mut StageThreeOutput,
        stage_4_output: &mut StageFourOutput,
        stage_5_output: &StageFiveOutput,
        log_domain_size: u32,
        log_lde_factor: u32,
        num_queries: usize,
        folding_description: &FoldingDescription,
        callbacks: &mut Callbacks,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let seed_accessor = seed.get_mut_accessor();
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
        let mut query_indexes = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let query_indexes_accessor = query_indexes.get_mut_accessor();
        let mut tree_indexes = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let tree_indexes_accessor = tree_indexes.get_mut_accessor();
        let get_query_indexes = move || unsafe {
            let query_indexes = query_indexes_accessor.get_mut();
            let tree_indexes = tree_indexes_accessor.get_mut();
            let mut source = vec![0u32; num_required_words_padded];
            Transcript::draw_randomness(seed_accessor.get_mut(), &mut source);
            let mut bit_source = BitSource::new(source[1..].to_vec());
            for i in 0..num_queries {
                let query_index =
                    assemble_query_index(query_index_bits as usize, &mut bit_source) as u32;
                let tree_index = query_index & tree_index_mask;
                query_indexes[i] = query_index;
                tree_indexes[i] = tree_index;
            }
        };
        let stream = context.get_exec_stream();
        callbacks.schedule(get_query_indexes, stream)?;
        let mut leafs_and_digest_sets = Vec::with_capacity(lde_factor);
        for coset_idx in 0..lde_factor {
            let mut h_tree_indexes = unsafe { context.alloc_host_uninit_slice(num_queries) };
            let h_tree_indexes_accessor = h_tree_indexes.get_mut_accessor();
            let copy_tree_indexes = move || unsafe {
                h_tree_indexes_accessor
                    .get_mut()
                    .copy_from_slice(tree_indexes_accessor.get());
            };
            callbacks.schedule(copy_tree_indexes, stream)?;
            let mut d_tree_indexes = context.alloc(num_queries, AllocationPlacement::BestFit)?;
            memory_copy_async(
                &mut d_tree_indexes,
                unsafe { h_tree_indexes_accessor.get() },
                stream,
            )?;
            let mut log_domain_size = log_domain_size;
            let mut layers_count = log_domain_size - log_coset_tree_cap_size;
            let (witness_evaluations, witness_tree) = stage_1_output
                .witness_holder
                .get_coset_evaluations_and_tree(coset_idx, context)?;
            let witness = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                witness_evaluations,
                &witness_tree,
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            drop(witness_tree);
            let (memory_evaluations, memory_tree) = stage_1_output
                .memory_holder
                .get_coset_evaluations_and_tree(coset_idx, context)?;
            let memory = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                memory_evaluations,
                &memory_tree,
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            drop(memory_tree);
            let (setup_evaluations, setup_tree) = setup
                .trace_holder
                .get_coset_evaluations_and_tree(coset_idx, context)?;
            let setup = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                setup_evaluations,
                &setup_tree,
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            drop(setup_tree);
            let (stage_2_evaluations, stage_2_tree) = stage_2_output
                .trace_holder
                .get_coset_evaluations_and_tree(coset_idx, context)?;
            let stage_2 = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                stage_2_evaluations,
                &stage_2_tree,
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            drop(stage_2_tree);
            let (stage_3_evaluations, stage_3_tree) = stage_3_output
                .trace_holder
                .get_coset_evaluations_and_tree(coset_idx, context)?;
            let quotient = Self::get_leafs_and_digests(
                &d_tree_indexes,
                true,
                stage_3_evaluations,
                &stage_3_tree,
                log_domain_size,
                0,
                layers_count,
                context,
            )?;
            drop(stage_3_tree);
            let folding_sequence = folding_description.folding_sequence;
            let initial_log_fold = folding_sequence[0] as u32;
            let initial_indexes_fold_fn = move || unsafe {
                h_tree_indexes_accessor
                    .get_mut()
                    .iter_mut()
                    .for_each(|x| *x >>= initial_log_fold);
            };
            callbacks.schedule(initial_indexes_fold_fn, stream)?;
            memory_copy_async(
                &mut d_tree_indexes,
                unsafe { h_tree_indexes_accessor.get() },
                stream,
            )?;
            layers_count -= initial_log_fold;
            let stage_4_evaluations = match &stage_4_output.trace_holder.cosets {
                CosetsHolder::Full { evaluations } => &evaluations[coset_idx],
                CosetsHolder::Single { .. } => unreachable!(),
            };
            let stage_4_tree = match &stage_4_output.trace_holder.trees {
                TreesHolder::Device { trees } => &trees[coset_idx],
                TreesHolder::None => unreachable!(),
            };
            let initial_fri = Self::get_leafs_and_digests(
                &d_tree_indexes,
                false,
                unsafe { stage_4_evaluations.transmute() },
                stage_4_tree,
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
                let indexes_fold_fn = move || unsafe {
                    h_tree_indexes_accessor
                        .get_mut()
                        .iter_mut()
                        .for_each(|x| *x >>= log_fold);
                };
                callbacks.schedule(indexes_fold_fn, stream)?;
                memory_copy_async(
                    &mut d_tree_indexes,
                    unsafe { h_tree_indexes_accessor.get() },
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
    ) -> CudaResult<LeafsAndDigests> {
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
        let mut leafs = unsafe { context.alloc_host_uninit_slice(leafs_len) };
        memory_copy_async(
            unsafe { leafs.get_mut_accessor().get_mut() },
            &d_leafs,
            stream,
        )?;
        d_leafs.free();
        let digests_len = queries_count * layers_count as usize;
        let mut d_digests = context.alloc(digests_len, AllocationPlacement::BestFit)?;
        gather_merkle_paths(indexes, tree, &mut d_digests, layers_count, stream)?;
        let mut digests = unsafe { context.alloc_host_uninit_slice(digests_len) };
        memory_copy_async(
            unsafe { digests.get_mut_accessor().get_mut() },
            &d_digests,
            stream,
        )?;
        let result = LeafsAndDigests { leafs, digests };
        Ok(result)
    }

    pub fn get_accessors(&self) -> QueriesOutputAccessors {
        let leafs_and_digest_sets = self
            .leafs_and_digest_sets
            .iter()
            .map(LeafsAndDigestsSet::get_accessor)
            .collect_vec();
        let query_indexes = self.query_indexes.get_accessor();
        QueriesOutputAccessors {
            leafs_and_digest_sets,
            query_indexes,
            log_domain_size: self.log_domain_size,
            folding_sequence: self.folding_sequence.clone(),
        }
    }
}

impl QueriesOutputAccessors {
    unsafe fn produce_queries(
        query_indexes: &[u32],
        tree_indexes: &[u32],
        leafs_and_digests: &LeafsAndDigestsAccessors,
        log_rows_per_index: u32,
    ) -> Vec<Query> {
        let queries_count = query_indexes.len();
        let leafs = leafs_and_digests.leafs.get();
        let digests = leafs_and_digests.digests.get();
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

    pub unsafe fn produce_query_sets(&self) -> Vec<QuerySet> {
        let query_indexes = self.query_indexes.get();
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
