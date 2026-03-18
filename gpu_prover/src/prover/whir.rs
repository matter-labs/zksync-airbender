use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use field::{Field, FieldExtension};
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::utils::{extension_field_from_base_coeffs, extension_field_into_base_coeffs};

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::ops::complex::{
    bit_reverse_in_place, pack_rows_for_whir_leaves, serialize_whir_e4_columns,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixChunkMut, DeviceMatrixMut};
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::alloc_static_pinned_box_from_slice;
use crate::prover::trace_holder::{TraceHolder, TreesCacheMode};

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GpuWhirExtensionQuery {
    pub(crate) index: usize,
    pub(crate) leaf_values_concatenated: Vec<E4>,
    pub(crate) path: Vec<Digest>,
}

pub(crate) struct GpuWhirExtensionOracle {
    trace_holder: TraceHolder<BF>,
    values_per_leaf: usize,
    lde_factor: usize,
    trace_len_log2: usize,
    packed_leaf_count: usize,
}

pub(crate) struct GpuWhirScheduledExtensionQuery {
    pub(crate) index: usize,
    pub(crate) coset_index: usize,
    // Keeps index-fill and query-index callbacks alive until the stream executes them.
    #[allow(dead_code)]
    callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    leafs: HostAllocation<[BF]>,
    #[allow(dead_code)]
    merkle_paths: HostAllocation<[Digest]>,
    values_per_leaf: usize,
}

impl GpuWhirScheduledExtensionQuery {
    pub(crate) fn leafs_accessor(&self) -> UnsafeAccessor<[BF]> {
        self.leafs.get_accessor()
    }

    pub(crate) fn merkle_paths_accessor(&self) -> UnsafeAccessor<[Digest]> {
        self.merkle_paths.get_accessor()
    }

    pub(crate) fn values_per_leaf(&self) -> usize {
        self.values_per_leaf
    }

    pub(crate) fn decode(&self) -> (Vec<E4>, GpuWhirExtensionQuery) {
        self.decode_with_index(self.index)
    }

    pub(crate) fn decode_with_index(&self, index: usize) -> (Vec<E4>, GpuWhirExtensionQuery) {
        let leaf_values_concatenated = decode_leaf_values(
            unsafe { self.leafs.get_accessor().get() },
            self.values_per_leaf,
        );
        let path = unsafe { self.merkle_paths.get_accessor().get().to_vec() };
        let query = GpuWhirExtensionQuery {
            index,
            leaf_values_concatenated: leaf_values_concatenated.clone(),
            path,
        };

        (leaf_values_concatenated, query)
    }
}

impl GpuWhirExtensionOracle {
    pub(crate) fn from_monomial_coeffs(
        monomial_coeffs: &[E4],
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut monomial_coeffs_device =
            context.alloc(monomial_coeffs.len(), AllocationPlacement::BestFit)?;
        let stream = context.get_exec_stream();
        let host = alloc_static_pinned_box_from_slice(monomial_coeffs)?;
        memory_copy_async(&mut monomial_coeffs_device, &host[..], stream)?;
        Self::from_device_monomial_coeffs(
            &monomial_coeffs_device,
            lde_factor,
            values_per_leaf,
            tree_cap_size,
            context,
        )
    }

    pub(crate) fn from_device_monomial_coeffs(
        monomial_coeffs: &DeviceSlice<E4>,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::from_device_monomial_coeffs_impl(
            monomial_coeffs,
            lde_factor,
            values_per_leaf,
            tree_cap_size,
            context,
            true,
        )
    }

    pub(crate) fn schedule_from_device_monomial_coeffs(
        monomial_coeffs: &DeviceSlice<E4>,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::from_device_monomial_coeffs_impl(
            monomial_coeffs,
            lde_factor,
            values_per_leaf,
            tree_cap_size,
            context,
            false,
        )
    }

    fn from_device_monomial_coeffs_impl(
        monomial_coeffs: &DeviceSlice<E4>,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        context: &ProverContext,
        synchronize_at_end: bool,
    ) -> CudaResult<Self> {
        assert!(!monomial_coeffs.is_empty());
        assert!(monomial_coeffs.len().is_power_of_two());
        assert!(lde_factor.is_power_of_two());
        assert!(values_per_leaf.is_power_of_two());
        assert!(tree_cap_size.is_power_of_two());
        assert!(
            lde_factor > 1,
            "recursive WHIR oracles require LDE factor > 1"
        );

        let trace_len = monomial_coeffs.len();
        let trace_len_log2 = trace_len.trailing_zeros() as usize;
        let log_lde_factor = lde_factor.trailing_zeros() as u32;
        let log_values_per_leaf = values_per_leaf.trailing_zeros() as u32;
        let log_tree_cap_size = tree_cap_size.trailing_zeros();
        assert!(trace_len_log2 >= log_values_per_leaf as usize);
        let packed_leaf_count = trace_len / values_per_leaf;
        let packed_leaf_count_log2 = packed_leaf_count.trailing_zeros();
        let total_leaf_count_log2 = packed_leaf_count_log2 + log_lde_factor;

        let mut serialized_coeffs_device =
            context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
        let stream = context.get_exec_stream();
        serialize_whir_e4_columns(monomial_coeffs, &mut serialized_coeffs_device, stream)?;
        {
            let mut coeffs_matrix = DeviceMatrixMut::new(&mut serialized_coeffs_device, trace_len);
            bit_reverse_in_place(&mut coeffs_matrix, stream)?;
        }

        let mut trace_holder = TraceHolder::new(
            total_leaf_count_log2,
            0,
            0,
            log_tree_cap_size,
            EXT4_DEGREE * values_per_leaf,
            TreesCacheMode::CacheFull,
            context,
        )?;
        let mut natural_coset_values =
            context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;

        for coset_index in 0..lde_factor {
            for base_column in 0..EXT4_DEGREE {
                let column_start = base_column * trace_len;
                let src = &serialized_coeffs_device[column_start..column_start + trace_len];
                let dst = &mut natural_coset_values[column_start..column_start + trace_len];
                crate::ntt::bitreversed_coeffs_to_natural_coset(
                    src,
                    dst,
                    trace_len_log2,
                    log_lde_factor as usize,
                    coset_index,
                    stream,
                )?;
            }
            let natural_matrix = DeviceMatrix::new(&natural_coset_values, trace_len);
            let packed_trace = trace_holder.get_uninit_coset_evaluations_mut(0);
            let stage1_coset_index = bitreverse_index(coset_index, log_lde_factor);
            let mut packed_matrix = DeviceMatrixChunkMut::new(
                packed_trace,
                packed_leaf_count << log_lde_factor,
                stage1_coset_index * packed_leaf_count,
                packed_leaf_count,
            );
            pack_rows_for_whir_leaves(
                &natural_matrix,
                &mut packed_matrix,
                log_values_per_leaf,
                1,
                0,
                stream,
            )?;
        }

        trace_holder.mark_cosets_materialized();
        trace_holder.commit_all(context)?;
        if synchronize_at_end {
            stream.synchronize()?;
        }

        Ok(Self {
            trace_holder,
            values_per_leaf,
            lde_factor,
            trace_len_log2,
            packed_leaf_count,
        })
    }

    pub(crate) fn get_tree_cap(&self) -> MerkleTreeCapVarLength {
        self.trace_holder
            .get_tree_caps()
            .pop()
            .expect("whir oracle must materialize at least one tree cap")
    }

    pub(crate) fn lde_factor(&self) -> usize {
        self.lde_factor
    }

    pub(crate) fn values_per_leaf(&self) -> usize {
        self.values_per_leaf
    }

    pub(crate) fn tree_cap_accessors(&self) -> Vec<UnsafeAccessor<[Digest]>> {
        self.trace_holder.get_tree_caps_accessors()
    }

    pub(crate) fn into_host_tree_caps(self) -> Vec<HostAllocation<[Digest]>> {
        let Self {
            mut trace_holder, ..
        } = self;
        trace_holder.take_tree_caps_host()
    }

    pub(crate) fn query_for_folded_index(
        &mut self,
        index: usize,
        context: &ProverContext,
    ) -> CudaResult<(usize, Vec<E4>, GpuWhirExtensionQuery)> {
        let scheduled = self.schedule_query_for_folded_index(index, context)?;
        context.get_exec_stream().synchronize()?;
        let (leaf_values_concatenated, query) = scheduled.decode();

        Ok((scheduled.coset_index, leaf_values_concatenated, query))
    }

    pub(crate) fn schedule_query_for_folded_index(
        &mut self,
        index: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuWhirScheduledExtensionQuery> {
        assert!(index < (1usize << self.trace_len_log2) * self.lde_factor / self.values_per_leaf);

        let coset_index = index & (self.lde_factor - 1);
        let internal_index = index / self.lde_factor;
        let stage1_coset_index =
            bitreverse_index(coset_index, self.lde_factor.trailing_zeros() as u32);
        let logical_row_index = stage1_coset_index * self.packed_leaf_count + internal_index;

        let mut callbacks = Callbacks::new();
        let mut host_value_index = unsafe { context.alloc_host_uninit_slice(1) };
        let vi_accessor = host_value_index.get_mut_accessor();
        callbacks.schedule(
            move || unsafe { vi_accessor.get_mut()[0] = logical_row_index as u32 },
            context.get_exec_stream(),
        )?;
        let mut device_value_index = context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut device_value_index,
            &host_value_index,
            context.get_exec_stream(),
        )?;
        drop(host_value_index);
        let value_query =
            self.trace_holder
                .get_leafs_and_merkle_paths(0, &device_value_index, context)?;
        let mut host_path_index = unsafe { context.alloc_host_uninit_slice(1) };
        let pi_accessor = host_path_index.get_mut_accessor();
        callbacks.schedule(
            move || unsafe { pi_accessor.get_mut()[0] = index as u32 },
            context.get_exec_stream(),
        )?;
        let mut device_path_index = context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut device_path_index,
            &host_path_index,
            context.get_exec_stream(),
        )?;
        drop(host_path_index);
        let path_query =
            self.trace_holder
                .get_leafs_and_merkle_paths(0, &device_path_index, context)?;
        Ok(GpuWhirScheduledExtensionQuery {
            index,
            coset_index,
            callbacks,
            leafs: value_query.leafs,
            merkle_paths: path_query.merkle_paths,
            values_per_leaf: self.values_per_leaf,
        })
    }

    pub(crate) fn schedule_query_for_folded_index_from_host(
        &mut self,
        query_index: HostAllocation<[u32]>,
        context: &ProverContext,
    ) -> CudaResult<GpuWhirScheduledExtensionQuery> {
        let mut callbacks = Callbacks::new();
        let mut value_index = unsafe { context.alloc_host_uninit_slice(1) };
        let value_index_accessor = value_index.get_mut_accessor();
        let mut path_index = unsafe { context.alloc_host_uninit_slice(1) };
        let path_index_accessor = path_index.get_mut_accessor();
        let query_index_accessor = query_index.get_accessor();
        let lde_factor = self.lde_factor;
        let packed_leaf_count = self.packed_leaf_count;
        callbacks.schedule(
            move || unsafe {
                let index = query_index_accessor.get()[0] as usize;
                let coset_index = index & (lde_factor - 1);
                let internal_index = index / lde_factor;
                let stage1_coset_index =
                    bitreverse_index(coset_index, lde_factor.trailing_zeros() as u32);
                value_index_accessor.get_mut()[0] =
                    (stage1_coset_index * packed_leaf_count + internal_index) as u32;
                path_index_accessor.get_mut()[0] = index as u32;
            },
            context.get_exec_stream(),
        )?;
        let mut device_value_index = context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut device_value_index,
            &value_index,
            context.get_exec_stream(),
        )?;
        drop(value_index);
        let mut device_path_index = context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut device_path_index,
            &path_index,
            context.get_exec_stream(),
        )?;
        drop(path_index);
        drop(query_index);
        let value_query =
            self.trace_holder
                .get_leafs_and_merkle_paths(0, &device_value_index, context)?;
        let path_query =
            self.trace_holder
                .get_leafs_and_merkle_paths(0, &device_path_index, context)?;
        Ok(GpuWhirScheduledExtensionQuery {
            index: 0,
            coset_index: 0,
            callbacks,
            leafs: value_query.leafs,
            merkle_paths: path_query.merkle_paths,
            values_per_leaf: self.values_per_leaf,
        })
    }

    #[cfg(test)]
    fn copy_coset_values(&self, coset_index: usize, context: &ProverContext) -> Vec<E4> {
        let total_leaf_count = self.packed_leaf_count * self.lde_factor;
        let full_trace = self.trace_holder.get_coset_evaluations(0);
        let mut host = vec![BF::ZERO; full_trace.len()];
        memory_copy_async(&mut host, full_trace, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let stage1_coset_index =
            bitreverse_index(coset_index, self.lde_factor.trailing_zeros() as u32);
        let row_offset = stage1_coset_index * self.packed_leaf_count;
        let mut packed_coset =
            vec![BF::ZERO; self.packed_leaf_count * self.values_per_leaf * EXT4_DEGREE];
        for column in 0..(self.values_per_leaf * EXT4_DEGREE) {
            let src_column = &host[column * total_leaf_count..(column + 1) * total_leaf_count];
            let dst_column = &mut packed_coset
                [column * self.packed_leaf_count..(column + 1) * self.packed_leaf_count];
            dst_column
                .copy_from_slice(&src_column[row_offset..row_offset + self.packed_leaf_count]);
        }
        decode_packed_coset_values(&packed_coset, self.packed_leaf_count, self.values_per_leaf)
    }
}

fn serialize_extension_columns(values: &[E4]) -> Vec<BF> {
    let mut serialized = vec![BF::ZERO; values.len() * EXT4_DEGREE];
    for (row, value) in values.iter().enumerate() {
        let coeffs = extension_field_into_base_coeffs::<BF, E4>(*value);
        for (column, coeff) in coeffs.into_iter().enumerate() {
            serialized[column * values.len() + row] = coeff;
        }
    }

    serialized
}

fn decode_leaf_values(leafs: &[BF], values_per_leaf: usize) -> Vec<E4> {
    assert_eq!(leafs.len(), values_per_leaf * EXT4_DEGREE);
    let mut result = Vec::with_capacity(values_per_leaf);
    for value_index in 0..values_per_leaf {
        let mut coeffs = [BF::ZERO; EXT4_DEGREE];
        for column in 0..EXT4_DEGREE {
            coeffs[column] = leafs[value_index * EXT4_DEGREE + column];
        }
        result.push(extension_field_from_base_coeffs::<BF, E4>(coeffs));
    }

    result
}

#[cfg(test)]
fn decode_packed_coset_values(values: &[BF], leaf_count: usize, values_per_leaf: usize) -> Vec<E4> {
    assert_eq!(values.len(), leaf_count * values_per_leaf * EXT4_DEGREE);
    let mut result = vec![E4::ZERO; leaf_count * values_per_leaf];
    let log_values_per_leaf = values_per_leaf.trailing_zeros();
    for leaf_index in 0..leaf_count {
        for value_slot in 0..values_per_leaf {
            let mut coeffs = [BF::ZERO; EXT4_DEGREE];
            for column in 0..EXT4_DEGREE {
                coeffs[column] =
                    values[(value_slot * EXT4_DEGREE + column) * leaf_count + leaf_index];
            }
            let src_row =
                leaf_index + bitreverse_index(value_slot, log_values_per_leaf) * leaf_count;
            result[src_row] = extension_field_from_base_coeffs::<BF, E4>(coeffs);
        }
    }

    result
}

fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::alloc::Global;

    use era_cudart::memory::memory_copy_async;
    use fft::{bitreverse_enumeration_inplace, domain_generator_for_size, Twiddles};
    use field::Field;
    use prover::gkr::prover::stages::stage1::ColumnMajorCosetBoundTracePart;
    use prover::gkr::whir::{ColumnMajorExtensionOracleForCoset, ColumnMajorExtensionOracleForLDE};
    use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor};
    use worker::Worker;

    use super::GpuWhirExtensionOracle;
    use crate::primitives::field::{BF, E4};
    use crate::prover::test_utils::make_test_context;

    fn sample_monomial_coeffs(size: usize) -> Vec<E4> {
        (0..size)
            .map(|idx| {
                let base = idx as u32 + 1;
                E4::from_array_of_base([
                    BF::new(base),
                    BF::new(base + 11),
                    BF::new(base + 29),
                    BF::new(base + 47),
                ])
            })
            .collect()
    }

    fn compute_column_major_lde_from_monomial_form_for_test(
        monomial_coeffs: &[E4],
        twiddles: &Twiddles<BF, Global>,
        lde_factor: usize,
    ) -> Vec<(Box<[E4]>, BF)> {
        let trace_len_log2 = monomial_coeffs.len().trailing_zeros() as usize;
        let next_root =
            domain_generator_for_size::<BF>(((1 << trace_len_log2) * lde_factor) as u64);
        let root_powers =
            fft::materialize_powers_serial_starting_with_one::<BF, Global>(next_root, lde_factor);
        let selected_twiddles = &twiddles.forward_twiddles[..(1 << (trace_len_log2 - 1))];

        (0..lde_factor)
            .map(|i| {
                let mut evals = monomial_coeffs.to_vec();
                let offset = root_powers[i];
                if i != 0 {
                    fft::distribute_powers_serial(&mut evals[..], BF::ONE, offset);
                }
                bitreverse_enumeration_inplace(&mut evals[..]);
                fft::naive::serial_ct_ntt_bitreversed_to_natural(
                    &mut evals[..],
                    trace_len_log2 as u32,
                    selected_twiddles,
                );
                (evals.into_boxed_slice(), offset)
            })
            .collect()
    }

    fn cpu_extension_oracle_from_monomial_form(
        monomial_coeffs: &[E4],
        twiddles: &Twiddles<BF, Global>,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        worker: &Worker,
    ) -> ColumnMajorExtensionOracleForLDE<BF, E4, DefaultTreeConstructor> {
        let cosets = compute_column_major_lde_from_monomial_form_for_test(
            monomial_coeffs,
            twiddles,
            lde_factor,
        );
        let trace_len_log2 = monomial_coeffs.len().trailing_zeros() as usize;
        let mut wrapped_cosets = Vec::with_capacity(cosets.len());
        for (column, offset) in cosets.iter() {
            wrapped_cosets.push(ColumnMajorExtensionOracleForCoset {
                values_normal_order: ColumnMajorCosetBoundTracePart {
                    column: column.clone().into(),
                    offset: *offset,
                },
            });
        }
        let source: Vec<_> = wrapped_cosets
            .iter()
            .map(|coset| vec![&coset.values_normal_order.column[..]])
            .collect();
        let source_ref: Vec<_> = source.iter().map(|entry| &entry[..]).collect();
        let tree =
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::construct_from_cosets::<
                E4,
                Global,
            >(
                &source_ref,
                values_per_leaf,
                tree_cap_size,
                true,
                true,
                false,
                worker,
            );

        ColumnMajorExtensionOracleForLDE {
            cosets: wrapped_cosets,
            tree,
            values_per_leaf,
            trace_len_log2,
        }
    }

    #[test]
    fn recursive_oracle_lde_matches_cpu() {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let monomial_coeffs = sample_monomial_coeffs(1 << 6);
        let twiddles = Twiddles::<BF, Global>::new(monomial_coeffs.len(), &worker);
        let cpu =
            cpu_extension_oracle_from_monomial_form(&monomial_coeffs, &twiddles, 4, 4, 4, &worker);
        let gpu = GpuWhirExtensionOracle::from_monomial_coeffs(&monomial_coeffs, 4, 4, 4, &context)
            .unwrap();

        for coset_index in 0..4 {
            assert_eq!(
                gpu.copy_coset_values(coset_index, &context),
                cpu.cosets[coset_index].values_normal_order.column.to_vec(),
                "coset {} diverged",
                coset_index
            );
        }
    }

    #[test]
    fn recursive_oracle_caps_and_queries_match_cpu() {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let monomial_coeffs = sample_monomial_coeffs(1 << 5);
        let twiddles = Twiddles::<BF, Global>::new(monomial_coeffs.len(), &worker);
        let cpu =
            cpu_extension_oracle_from_monomial_form(&monomial_coeffs, &twiddles, 4, 2, 4, &worker);
        let mut gpu =
            GpuWhirExtensionOracle::from_monomial_coeffs(&monomial_coeffs, 4, 2, 4, &context)
                .unwrap();

        assert_eq!(
            gpu.get_tree_cap(),
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(&cpu.tree)
        );

        for query_index in [0usize, 1, 7, 13] {
            let (cpu_coset_index, cpu_values, cpu_query) = cpu.query_for_folded_index(query_index);
            let (gpu_coset_index, gpu_values, gpu_query) =
                gpu.query_for_folded_index(query_index, &context).unwrap();

            assert_eq!(
                gpu_coset_index, cpu_coset_index,
                "query {} uses an unexpected coset mapping",
                query_index
            );
            assert_eq!(
                gpu_values, cpu_values,
                "query {} leaf values diverged",
                query_index
            );
            assert_eq!(gpu_query.index, cpu_query.index);
            assert_eq!(
                gpu_query.leaf_values_concatenated,
                cpu_query.leaf_values_concatenated
            );
            assert_eq!(gpu_query.path, cpu_query.path);
        }
    }

    #[test]
    fn scheduled_recursive_oracle_caps_and_queries_match_cpu() {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let monomial_coeffs = sample_monomial_coeffs(1 << 5);
        let twiddles = Twiddles::<BF, Global>::new(monomial_coeffs.len(), &worker);
        let cpu =
            cpu_extension_oracle_from_monomial_form(&monomial_coeffs, &twiddles, 4, 2, 4, &worker);

        let mut monomial_coeffs_device = context
            .alloc(
                monomial_coeffs.len(),
                crate::allocator::tracker::AllocationPlacement::BestFit,
            )
            .unwrap();
        memory_copy_async(
            &mut monomial_coeffs_device,
            &monomial_coeffs,
            context.get_exec_stream(),
        )
        .unwrap();

        let mut gpu = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
            &monomial_coeffs_device,
            4,
            2,
            4,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        assert_eq!(
            gpu.get_tree_cap(),
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(&cpu.tree)
        );

        for query_index in [0usize, 1, 7, 13] {
            let (_cpu_coset_index, cpu_values, cpu_query) = cpu.query_for_folded_index(query_index);

            let mut host_query_index = unsafe { context.alloc_host_uninit_slice::<u32>(1) };
            unsafe {
                host_query_index.get_mut_accessor().get_mut()[0] = query_index as u32;
            }
            let scheduled_query = gpu
                .schedule_query_for_folded_index_from_host(host_query_index, &context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let (gpu_values, gpu_query) = scheduled_query.decode_with_index(query_index);

            assert_eq!(
                gpu_values, cpu_values,
                "query {} leaf values diverged",
                query_index
            );
            assert_eq!(gpu_query.index, cpu_query.index);
            assert_eq!(
                gpu_query.leaf_values_concatenated,
                cpu_query.leaf_values_concatenated
            );
            assert_eq!(gpu_query.path, cpu_query.path);
        }
    }
}
