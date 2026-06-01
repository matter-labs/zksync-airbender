pub(crate) mod fold;
pub(crate) mod kernels;

#[cfg(test)]
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

#[cfg(test)]
use crate::allocator::tracker::AllocationPlacement;
#[cfg(test)]
use crate::ops::blake2s::Digest;
#[cfg(test)]
use crate::primitives::callbacks::Callbacks;
#[cfg(test)]
use crate::primitives::context::HostAllocation;
use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixImpl};
#[cfg(test)]
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::field::{BF, E4};
use crate::prover::trace::holder::{TraceHolder, TreesCacheMode, PARTIAL_TREE_REDUCTION_LAYERS};
use crate::prover::ProverContext;
use crate::upstream::FieldExtension;

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;

/// Where the WHIR oracle's unified Merkle cap should land after its per-coset
/// trees are committed.
///
/// - `OwnAllocation` — the trace holder allocates a private `DeviceAllocation<Digest>`
///   and stores it on `unified_device_cap` (legacy path used by tests and by
///   the base/initial WHIR oracle construction).
/// - `Slab(...)` — the cap is gathered directly into a caller-supplied device
///   slice (typically a `whir.intermediate[round].cap` slab subrange), and
///   `unified_device_cap` stays `None`. Downstream readers must source the
///   cap from the slab.
enum CapTarget<'a> {
    /// Constructed only by the cfg(test) helper `schedule_from_device_monomial_coeffs`
    /// (legacy own-cap path). Production code always uses [`Self::Slab`].
    #[allow(dead_code)]
    OwnAllocation,
    Slab(&'a mut era_cudart::slice::DeviceSlice<u32>),
}

pub(crate) struct GpuWhirExtensionOracle {
    trace_holder: TraceHolder<BF>,
    /// Read only by cfg(test) query helpers and the cfg(test) recursive-decode
    /// path. Production code never reads this field, but its construction is
    /// shared with the test helpers, so the field remains.
    #[allow(dead_code)]
    values_per_leaf: usize,
    lde_factor: usize,
    #[allow(dead_code)]
    trace_len_log2: usize,
    packed_leaf_count: usize,
}

/// Holds the retired oracle's trace holder (and therefore its unified device
/// cap) alive on a downstream keepalive vector so scheduled D2H or D2D ops
/// reading the cap remain valid until `prove()`'s `is_finished_event`
/// completes.
pub(crate) struct GpuWhirExtensionOracleKeepalive {
    _trace_holder: TraceHolder<BF>,
}

#[cfg(test)]
pub(crate) struct GpuWhirScheduledExtensionQuery {
    pub(crate) index: usize,
    pub(crate) coset_index: usize,
    // Keeps index-fill and query-index callbacks alive until the stream executes them.
    _callbacks: Callbacks<'static>,
    leafs: HostAllocation<[BF]>,
    merkle_paths: HostAllocation<[Digest]>,
    values_per_leaf: usize,
}

impl GpuWhirExtensionOracle {
    fn recursive_tree_cache_mode(
        total_leaf_count_log2: u32,
        log_tree_cap_size: u32,
    ) -> TreesCacheMode {
        if total_leaf_count_log2 > PARTIAL_TREE_REDUCTION_LAYERS + log_tree_cap_size {
            TreesCacheMode::CachePartial
        } else {
            TreesCacheMode::CacheFull
        }
    }

    #[cfg(test)]
    pub(crate) fn schedule_from_device_monomial_coeffs(
        monomial_coeffs: &impl DeviceMatrixImpl<BF>,
        trace_len: usize,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::from_device_monomial_coeffs_impl(
            monomial_coeffs,
            trace_len,
            lde_factor,
            values_per_leaf,
            tree_cap_size,
            CapTarget::OwnAllocation,
            context,
        )
    }

    /// Variant of `schedule_from_device_monomial_coeffs` that writes the
    /// unified Merkle cap directly into a caller-supplied device slice
    /// (typically a slab subrange exposed by `ProofLayout`). The constructed
    /// oracle's `trace_holder.unified_device_cap` stays `None` — downstream
    /// readers must source the cap from `cap_dst_u32`. Intermediate WHIR
    /// oracles in the production fold path use this variant to fuse the cap
    /// gather with the slab commit, eliminating the per-round D2D copy.
    pub(crate) fn schedule_from_device_monomial_coeffs_into_slab(
        monomial_coeffs: &impl DeviceMatrixImpl<BF>,
        trace_len: usize,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        cap_dst_u32: &mut era_cudart::slice::DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::from_device_monomial_coeffs_impl(
            monomial_coeffs,
            trace_len,
            lde_factor,
            values_per_leaf,
            tree_cap_size,
            CapTarget::Slab(cap_dst_u32),
            context,
        )
    }

    fn from_device_monomial_coeffs_impl(
        monomial_coeffs: &impl DeviceMatrixImpl<BF>,
        trace_len: usize,
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        cap_target: CapTarget<'_>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(!monomial_coeffs.slice().is_empty());
        assert!(monomial_coeffs.slice().len().is_power_of_two());
        assert!(lde_factor.is_power_of_two());
        assert!(values_per_leaf.is_power_of_two());
        assert!(tree_cap_size.is_power_of_two());
        assert!(
            lde_factor > 1,
            "recursive WHIR oracles require LDE factor > 1"
        );

        // let trace_len = monomial_coeffs.len();
        let trace_len_log2 = trace_len.trailing_zeros() as usize;
        let log_lde_factor = lde_factor.trailing_zeros() as u32;
        let log_values_per_leaf = values_per_leaf.trailing_zeros() as u32;
        let log_tree_cap_size = tree_cap_size.trailing_zeros();
        assert!(trace_len_log2 >= log_values_per_leaf as usize);
        let packed_leaf_count = trace_len / values_per_leaf;
        let packed_leaf_count_log2 = packed_leaf_count.trailing_zeros();
        let total_leaf_count_log2 = packed_leaf_count_log2 + log_lde_factor;
        let trees_cache_mode =
            Self::recursive_tree_cache_mode(total_leaf_count_log2, log_tree_cap_size);

        // let mut serialized_coeffs_device =
        //     context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
        // serialize_whir_e4_columns(monomial_coeffs, &mut serialized_coeffs_device, stream)?;
        // {
        //     let mut coeffs_matrix = DeviceMatrixMut::new(&mut serialized_coeffs_device, trace_len);
        //     bit_reverse_in_place(&mut coeffs_matrix, stream)?;
        // }

        let stream = context.get_exec_stream();
        let mut trace_holder = TraceHolder::new(
            total_leaf_count_log2,
            0,
            0,
            log_tree_cap_size,
            EXT4_DEGREE * values_per_leaf,
            trees_cache_mode,
            context,
        )?;
        // Multi-coset NTT writes the natural multi-coset evaluations directly
        // into the WHIR oracle's cosets backing. The previous pipeline used a
        // separate `natural_coset_values` temp and then `pack_rows_for_whir_leaves`
        // — both gone. The new blake-leaves-from-NTT kernel (invoked via
        // `commit_all_into_from_ntt`) reads the natural layout in place.
        let monomial_coeffs_slice = monomial_coeffs.slice();
        let monomial_coeffs_stride = monomial_coeffs.stride();
        let device_properties = context.get_device_properties();
        let inputs_matrix =
            DeviceMatrixChunk::new(monomial_coeffs_slice, monomial_coeffs_stride, 0, trace_len);
        {
            let cosets_backing = trace_holder.get_uninit_consolidated_cosets_mut();
            crate::ops::ntt::bitreversed_monomials_to_natural_evals_multi_coset(
                &inputs_matrix,
                cosets_backing,
                trace_len_log2,
                log_lde_factor as usize,
                0,
                lde_factor,
                EXT4_DEGREE,
                false,
                stream,
                device_properties,
            )?;
        }
        trace_holder.mark_cosets_materialized();
        match cap_target {
            CapTarget::OwnAllocation => {
                trace_holder.commit_all_from_ntt(
                    trace_len_log2 as u32,
                    log_lde_factor,
                    log_values_per_leaf,
                    EXT4_DEGREE,
                    context,
                )?;
            }
            CapTarget::Slab(dst_u32) => {
                trace_holder.commit_all_into_from_ntt(
                    dst_u32,
                    trace_len_log2 as u32,
                    log_lde_factor,
                    log_values_per_leaf,
                    EXT4_DEGREE,
                    context,
                )?;
            }
        }

        Ok(Self {
            trace_holder,
            values_per_leaf,
            lde_factor,
            trace_len_log2,
            packed_leaf_count,
        })
    }

    pub(crate) fn lde_factor(&self) -> usize {
        self.lde_factor
    }

    /// Hands the oracle's device unified cap (with the trace holder that
    /// owns it) to the caller as a keepalive. Used by query-emitting paths
    /// that retire the oracle but still need its cap to survive scheduled
    /// downstream reads.
    pub(crate) fn into_host_keepalive(self) -> GpuWhirExtensionOracleKeepalive {
        let Self { trace_holder, .. } = self;
        GpuWhirExtensionOracleKeepalive {
            _trace_holder: trace_holder,
        }
    }

    /// Phase 4 (WHIR-on-device): batch-gather all `device_query_indexes` of one
    /// round directly into the slab's intermediate `query_indices` /
    /// `query_leaves` / `query_paths` ranges. The tree-index kernel writes
    /// straight into the slab `query_indices` range — no temp buffer, no D2D.
    /// The trace_holder is constructed with `log_lde_factor = 0`, so
    /// `tree_index == query_index` (identity) and the slab-resident indices
    /// can be reused as the gather kernels' lookup inputs.
    pub(crate) fn schedule_query_for_folded_indexes_to_slab(
        &mut self,
        device_query_indexes: &era_cudart::slice::DeviceSlice<u32>,
        slab_indices_dst: &mut era_cudart::slice::DeviceSlice<u32>,
        slab_leaves_dst_bf: &mut era_cudart::slice::DeviceSlice<BF>,
        slab_paths_dst: &mut era_cudart::slice::DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let stream = context.get_exec_stream();
        let num_queries = device_query_indexes.len();
        let log_lde_factor = self.lde_factor.trailing_zeros();
        assert!(self.packed_leaf_count.is_power_of_two());
        let packed_leaf_count_log2 = self.packed_leaf_count.trailing_zeros();
        assert_eq!(slab_indices_dst.len(), num_queries);
        // Write tree-indexes directly into the slab `query_indices` range.
        // With `log_lde_factor == 0` the kernel collapses to the identity
        // (tree_index == query_index); the kernel handles both cases for
        // symmetry. The slab range is exclusively written here on
        // `exec_stream`, then read by the gather kernels below, so the
        // subsequent shared reborrow is sound.
        crate::ops::blake2s::query_index_to_tree_index(
            device_query_indexes,
            slab_indices_dst,
            log_lde_factor,
            packed_leaf_count_log2,
            stream,
        )?;
        // Reborrow as a shared view. The gather kernels take a `&DeviceSlice`
        // (read-only) and run after the kernel above on the same stream, so
        // they observe the tree-indexes that were just written.
        let slab_indices_view: &era_cudart::slice::DeviceSlice<u32> = slab_indices_dst;
        // Recursive WHIR trace holders use `log_lde_factor = 0`, so only
        // coset 0 exists; the consolidated gather kernels resolve every
        // query into that single coset (lde_mask == 0).
        let log_values_per_leaf = self.values_per_leaf.trailing_zeros();
        let natural_log_lde_factor = log_lde_factor;
        const LOG_SRC_COLS_PER_COSET: u32 = 2; // log2(EXT4_DEGREE)
        self.trace_holder.schedule_query_leaves_into_from_ntt(
            slab_indices_view,
            slab_leaves_dst_bf,
            self.trace_len_log2 as u32,
            natural_log_lde_factor,
            log_values_per_leaf,
            LOG_SRC_COLS_PER_COSET,
            context,
        )?;
        self.trace_holder
            .schedule_query_merkle_paths_into_from_ntt(
                slab_indices_view,
                slab_paths_dst,
                self.trace_len_log2 as u32,
                natural_log_lde_factor,
                log_values_per_leaf,
                LOG_SRC_COLS_PER_COSET,
                context,
            )?;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn schedule_query_for_folded_index_from_host(
        &mut self,
        query_index: &HostAllocation<[u32]>,
        context: &ProverContext,
    ) -> CudaResult<GpuWhirScheduledExtensionQuery> {
        let mut callbacks = Callbacks::new();
        let mut tree_index_host = unsafe { context.alloc_host_uninit_slice(1) };
        let tree_index_accessor = tree_index_host.get_mut_accessor();
        let query_index_accessor = query_index.get_accessor();
        let lde_factor = self.lde_factor;
        let packed_leaf_count = self.packed_leaf_count;
        callbacks.schedule(
            move || unsafe {
                // See `schedule_query_for_folded_index` above: value and path lookups share
                // the tree index, matching CPU's
                // `ColumnMajorExtensionOracleForLDE::query_for_folded_index`.
                let index = query_index_accessor.get()[0] as usize;
                let coset_index = index & (lde_factor - 1);
                let internal_index = index / lde_factor;
                let coset_dest_index =
                    bitreverse_index(coset_index, lde_factor.trailing_zeros() as u32);
                tree_index_accessor.get_mut()[0] =
                    (coset_dest_index * packed_leaf_count + internal_index) as u32;
            },
            context.get_exec_stream(),
        )?;
        let mut device_tree_index = context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut device_tree_index,
            &tree_index_host,
            context.get_exec_stream(),
        )?;
        drop(tree_index_host);
        // Use the NTT-aware query path (same reason as `schedule_query_for_folded_index`).
        let leaf_len = self.values_per_leaf * EXT4_DEGREE;
        let mut d_leafs = context.alloc(leaf_len, AllocationPlacement::BestFit)?;
        {
            let natural_log_lde_factor = self.lde_factor.trailing_zeros();
            let log_values_per_leaf = self.values_per_leaf.trailing_zeros();
            const LOG_SRC_COLS_PER_COSET: u32 = 2; // log2(EXT4_DEGREE)
            self.trace_holder.schedule_query_leaves_into_from_ntt(
                &device_tree_index,
                &mut d_leafs[..],
                self.trace_len_log2 as u32,
                natural_log_lde_factor,
                log_values_per_leaf,
                LOG_SRC_COLS_PER_COSET,
                context,
            )?;
        }
        let stream_ref = context.get_exec_stream();
        let mut value_query = unsafe { context.alloc_host_uninit_slice(leaf_len) };
        memory_copy_async(&mut value_query, &d_leafs[..], stream_ref)?;
        let path_query = {
            let natural_log_lde_factor = self.lde_factor.trailing_zeros();
            let log_values_per_leaf = self.values_per_leaf.trailing_zeros();
            const LOG_SRC_COLS_PER_COSET: u32 = 2;
            self.trace_holder.get_query_merkle_paths_from_ntt(
                &device_tree_index,
                self.trace_len_log2 as u32,
                natural_log_lde_factor,
                log_values_per_leaf,
                LOG_SRC_COLS_PER_COSET,
                context,
            )?
        };
        Ok(GpuWhirScheduledExtensionQuery {
            index: 0,
            coset_index: 0,
            _callbacks: callbacks,
            leafs: value_query,
            merkle_paths: path_query,
            values_per_leaf: self.values_per_leaf,
        })
    }
}

#[cfg(test)]
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
    use prover::merkle_trees::{
        ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, MerkleTreeCapVarLength,
    };
    use prover::utils::extension_field_from_base_coeffs;
    use serial_test::serial;
    use worker::Worker;

    use super::*;
    use crate::primitives::static_host::alloc_static_pinned_box_from_slice;
    use crate::prover::test_utils::make_test_context;
    use crate::prover::trace::holder::TreesHolder;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) struct GpuWhirExtensionQuery {
        pub(crate) index: usize,
        pub(crate) leaf_values_concatenated: Vec<E4>,
        pub(crate) path: Vec<Digest>,
    }

    impl GpuWhirScheduledExtensionQuery {
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

    pub(crate) fn e4_coeffs_to_vectorized(coeffs: &[E4]) -> Vec<BF> {
        let trace_len = coeffs.len();
        let mut vectorized_coeffs = vec![BF::default(); 4 * trace_len];
        for i in 0..trace_len {
            let coeff = coeffs[i];
            let bf_coeffs = [coeff.c0.c0, coeff.c0.c1, coeff.c1.c0, coeff.c1.c1];
            for j in 0..4 {
                vectorized_coeffs[i + j * trace_len] = bf_coeffs[j];
            }
        }
        vectorized_coeffs
    }

    impl GpuWhirExtensionOracle {
        pub(crate) fn from_monomial_coeffs(
            monomial_coeffs: &[E4],
            lde_factor: usize,
            values_per_leaf: usize,
            tree_cap_size: usize,
            context: &ProverContext,
        ) -> CudaResult<Self> {
            let trace_len = monomial_coeffs.len();
            let mut bitreversed_monomial_coeffs = monomial_coeffs.to_vec();
            bitreverse_enumeration_inplace(&mut bitreversed_monomial_coeffs);
            let vectorized_monomial_coeffs = e4_coeffs_to_vectorized(&bitreversed_monomial_coeffs);
            let mut monomial_coeffs_device_alloc = context.alloc(
                vectorized_monomial_coeffs.len(),
                AllocationPlacement::BestFit,
            )?;
            let stream = context.get_exec_stream();
            let host = alloc_static_pinned_box_from_slice(&vectorized_monomial_coeffs[..])?;
            memory_copy_async(&mut monomial_coeffs_device_alloc, &host[..], stream)?;
            let monomial_coeffs_device =
                DeviceMatrix::new(&monomial_coeffs_device_alloc, trace_len);
            Self::from_device_monomial_coeffs(
                &monomial_coeffs_device,
                trace_len,
                lde_factor,
                values_per_leaf,
                tree_cap_size,
                context,
            )
        }

        pub(crate) fn from_device_monomial_coeffs(
            monomial_coeffs: &impl DeviceMatrixImpl<BF>,
            trace_len: usize,
            lde_factor: usize,
            values_per_leaf: usize,
            tree_cap_size: usize,
            context: &ProverContext,
        ) -> CudaResult<Self> {
            let oracle = Self::from_device_monomial_coeffs_impl(
                monomial_coeffs,
                trace_len,
                lde_factor,
                values_per_leaf,
                tree_cap_size,
                CapTarget::OwnAllocation,
                context,
            )?;
            context.get_exec_stream().synchronize()?;
            Ok(oracle)
        }

        pub(crate) fn schedule_query_for_folded_index(
            &mut self,
            index: usize,
            context: &ProverContext,
        ) -> CudaResult<GpuWhirScheduledExtensionQuery> {
            assert!(
                index < (1usize << self.trace_len_log2) * self.lde_factor / self.values_per_leaf
            );

            let coset_index = index & (self.lde_factor - 1);
            let internal_index = index / self.lde_factor;
            let coset_dest_index =
                bitreverse_index(coset_index, self.lde_factor.trailing_zeros() as u32);
            // tree_index matches CPU `ColumnMajorExtensionOracleForLDE::query_for_folded_index`
            // (prover/src/gkr/whir/mod.rs). The extension oracle trace holder stores leaves in
            // this order, so both value and path lookups go through the same index.
            let tree_index = coset_dest_index * self.packed_leaf_count + internal_index;

            let mut callbacks = Callbacks::new();
            let mut host_tree_index = unsafe { context.alloc_host_uninit_slice(1) };
            let ti_accessor = host_tree_index.get_mut_accessor();
            callbacks.schedule(
                move || unsafe { ti_accessor.get_mut()[0] = tree_index as u32 },
                context.get_exec_stream(),
            )?;
            let mut device_tree_index = context.alloc(1, AllocationPlacement::BestFit)?;
            memory_copy_async(
                &mut device_tree_index,
                &host_tree_index,
                context.get_exec_stream(),
            )?;
            drop(host_tree_index);
            // Use the NTT-aware query path: the trace holder's cosets backing
            // now holds the natural multi-coset NTT output, which `get_query_leafs`
            // (packed-layout reader) would misinterpret. Switch to the new
            // `schedule_query_leaves_into_from_ntt` path used by production.
            let leaf_len = self.values_per_leaf * EXT4_DEGREE;
            let mut d_leafs = context.alloc(leaf_len, AllocationPlacement::BestFit)?;
            {
                let natural_log_lde_factor = self.lde_factor.trailing_zeros();
                let log_values_per_leaf = self.values_per_leaf.trailing_zeros();
                const LOG_SRC_COLS_PER_COSET: u32 = 2; // log2(EXT4_DEGREE)
                self.trace_holder.schedule_query_leaves_into_from_ntt(
                    &device_tree_index,
                    &mut d_leafs[..],
                    self.trace_len_log2 as u32,
                    natural_log_lde_factor,
                    log_values_per_leaf,
                    LOG_SRC_COLS_PER_COSET,
                    context,
                )?;
            }
            let stream_ref = context.get_exec_stream();
            let mut value_query = unsafe { context.alloc_host_uninit_slice(leaf_len) };
            memory_copy_async(&mut value_query, &d_leafs[..], stream_ref)?;
            let path_query = {
                let natural_log_lde_factor = self.lde_factor.trailing_zeros();
                let log_values_per_leaf = self.values_per_leaf.trailing_zeros();
                const LOG_SRC_COLS_PER_COSET: u32 = 2;
                self.trace_holder.get_query_merkle_paths_from_ntt(
                    &device_tree_index,
                    self.trace_len_log2 as u32,
                    natural_log_lde_factor,
                    log_values_per_leaf,
                    LOG_SRC_COLS_PER_COSET,
                    context,
                )?
            };
            Ok(GpuWhirScheduledExtensionQuery {
                index: tree_index,
                coset_index,
                _callbacks: callbacks,
                leafs: value_query,
                merkle_paths: path_query,
                values_per_leaf: self.values_per_leaf,
            })
        }

        /// Reads back the unified device cap synchronously and returns it as a
        /// single-coset `MerkleTreeCapVarLength`. Test-only helper — production
        /// paths should consume the cap as `unified_device_cap()` and avoid
        /// host blocking.
        pub(crate) fn get_tree_cap(
            &self,
            context: &ProverContext,
        ) -> CudaResult<MerkleTreeCapVarLength> {
            self.trace_holder.read_full_cap_synchronously(context)
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

        fn copy_coset_values(&self, coset_index: usize, context: &ProverContext) -> Vec<E4> {
            // The backing now holds the natural multi-coset NTT output.
            // Layout: column-major matrix with `trace_len` rows and
            // `lde_factor * EXT4_DEGREE` columns. Column
            // `coset * EXT4_DEGREE + bf_comp` holds BF component `bf_comp`
            // of coset `coset` — cosets in natural (non-bit-reversed) order.
            let trace_len = self.packed_leaf_count * self.values_per_leaf;
            let full_trace = self.trace_holder.get_consolidated_cosets();
            let mut host = vec![BF::ZERO; full_trace.len()];
            memory_copy_async(&mut host, full_trace, context.get_exec_stream()).unwrap();
            context.get_exec_stream().synchronize().unwrap();
            (0..trace_len)
                .map(|pos| {
                    let mut coeffs = [BF::ZERO; EXT4_DEGREE];
                    for bf_comp in 0..EXT4_DEGREE {
                        coeffs[bf_comp] =
                            host[(coset_index * EXT4_DEGREE + bf_comp) * trace_len + pos];
                    }
                    extension_field_from_base_coeffs::<BF, E4>(coeffs)
                })
                .collect()
        }
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

    fn assert_recursive_oracle_caps_and_queries_match_cpu(
        monomial_coeffs: &[E4],
        values_per_leaf: usize,
        expected_partial_cache: bool,
    ) {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let twiddles = Twiddles::<BF, Global>::new(monomial_coeffs.len(), &worker);
        let cpu = cpu_extension_oracle_from_monomial_form(
            monomial_coeffs,
            &twiddles,
            4,
            values_per_leaf,
            4,
            &worker,
        );
        let mut gpu = GpuWhirExtensionOracle::from_monomial_coeffs(
            monomial_coeffs,
            4,
            values_per_leaf,
            4,
            &context,
        )
        .unwrap();

        match (&gpu.trace_holder.trees, expected_partial_cache) {
            (TreesHolder::Partial(_), true) | (TreesHolder::Full(_), false) => {}
            _ => panic!("unexpected recursive cache mode"),
        }

        assert_eq!(
            gpu.get_tree_cap(&context).unwrap(),
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(&cpu.tree)
        );

        let query_indexes = [
            0usize,
            1,
            7,
            (monomial_coeffs.len() * 4 / values_per_leaf) / 2,
            (monomial_coeffs.len() * 4 / values_per_leaf) - 1,
        ];
        for query_index in query_indexes {
            let (cpu_coset_index, cpu_values, cpu_query) = cpu.query_for_folded_index(query_index);
            let (gpu_coset_index, gpu_values, gpu_query) =
                gpu.query_for_folded_index(query_index, &context).unwrap();

            assert_eq!(
                gpu_coset_index, cpu_coset_index,
                "query {query_index} coset mismatch"
            );
            assert_eq!(gpu_values, cpu_values, "query {query_index} leaf mismatch");
            assert_eq!(gpu_query.index, cpu_query.index);
            assert_eq!(
                gpu_query.leaf_values_concatenated,
                cpu_query.leaf_values_concatenated
            );
            assert_eq!(gpu_query.path, cpu_query.path);
        }
    }

    #[test]
    #[serial]
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
    #[serial]
    fn recursive_oracle_caps_and_queries_match_cpu() {
        let monomial_coeffs = sample_monomial_coeffs(1 << 5);
        assert_recursive_oracle_caps_and_queries_match_cpu(&monomial_coeffs, 2, false);
    }

    #[test]
    #[serial]
    fn recursive_oracle_large_partial_cache_matches_cpu() {
        let monomial_coeffs = sample_monomial_coeffs(1 << 8);
        assert_recursive_oracle_caps_and_queries_match_cpu(&monomial_coeffs, 2, true);
    }

    #[test]
    #[serial]
    fn scheduled_recursive_oracle_caps_and_queries_match_cpu() {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let monomial_coeffs = sample_monomial_coeffs(1 << 5);
        let twiddles = Twiddles::<BF, Global>::new(monomial_coeffs.len(), &worker);
        let cpu =
            cpu_extension_oracle_from_monomial_form(&monomial_coeffs, &twiddles, 4, 2, 4, &worker);
        let trace_len = monomial_coeffs.len();

        let mut bitreversed_monomial_coeffs = monomial_coeffs.to_vec();
        bitreverse_enumeration_inplace(&mut bitreversed_monomial_coeffs);
        let monomial_coeffs_vectorized = e4_coeffs_to_vectorized(&bitreversed_monomial_coeffs);
        let mut monomial_coeffs_device = context
            .alloc(
                trace_len * super::EXT4_DEGREE,
                crate::allocator::tracker::AllocationPlacement::BestFit,
            )
            .unwrap();
        memory_copy_async(
            &mut monomial_coeffs_device,
            &monomial_coeffs_vectorized,
            context.get_exec_stream(),
        )
        .unwrap();
        let monomial_coeffs_device_matrix =
            super::DeviceMatrix::new(&monomial_coeffs_device, trace_len);

        let mut gpu = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
            &monomial_coeffs_device_matrix,
            trace_len,
            4,
            2,
            4,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        assert_eq!(
            gpu.get_tree_cap(&context).unwrap(),
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(&cpu.tree)
        );

        for query_index in [0usize, 1, 7, 13] {
            let (_cpu_coset_index, cpu_values, cpu_query) = cpu.query_for_folded_index(query_index);

            let mut host_query_index = unsafe { context.alloc_host_uninit_slice::<u32>(1) };
            let mut h2d_callbacks = Callbacks::new();
            let host_query_index_accessor = host_query_index.get_mut_accessor();
            h2d_callbacks
                .schedule(
                    move || unsafe {
                        host_query_index_accessor.get_mut()[0] = query_index as u32;
                    },
                    context.get_exec_stream(),
                )
                .unwrap();
            let scheduled_query = gpu
                .schedule_query_for_folded_index_from_host(&host_query_index, &context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            // `decode_with_index` needs the *tree* index (the order leaves are
            // stored in), not the *folded* query_index. Mirror the computation
            // in `schedule_query_for_folded_index` so it matches CPU's
            // `cpu_query.index`.
            let coset_index = query_index & (gpu.lde_factor - 1);
            let internal_index = query_index / gpu.lde_factor;
            let coset_dest_index =
                super::bitreverse_index(coset_index, gpu.lde_factor.trailing_zeros());
            let tree_index = coset_dest_index * gpu.packed_leaf_count + internal_index;
            let (gpu_values, gpu_query) = scheduled_query.decode_with_index(tree_index);

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
    #[serial]
    fn recursive_oracle_cache_mode_branch_selection() {
        let context = make_test_context(256, 32);
        let small = sample_monomial_coeffs(1 << 5);
        let large = sample_monomial_coeffs(1 << 8);

        let small_oracle =
            GpuWhirExtensionOracle::from_monomial_coeffs(&small, 4, 2, 4, &context).unwrap();
        let large_oracle =
            GpuWhirExtensionOracle::from_monomial_coeffs(&large, 4, 2, 4, &context).unwrap();

        assert!(matches!(
            small_oracle.trace_holder.trees,
            TreesHolder::Full(_)
        ));
        assert!(matches!(
            large_oracle.trace_holder.trees,
            TreesHolder::Partial(_)
        ));
    }

    #[test]
    #[serial]
    fn recursive_query_leaf_and_path_helpers_match_combined_queries() {
        let context = make_test_context(256, 32);
        let monomial_coeffs = sample_monomial_coeffs(1 << 8);
        let mut oracle =
            GpuWhirExtensionOracle::from_monomial_coeffs(&monomial_coeffs, 4, 2, 4, &context)
                .unwrap();

        for query_index in [0usize, 1, 17, 63, 127, 255] {
            let coset_index = query_index & (oracle.lde_factor - 1);
            let internal_index = query_index / oracle.lde_factor;
            let stage1_coset_index =
                super::bitreverse_index(coset_index, oracle.lde_factor.trailing_zeros() as u32);
            let logical_row_index = stage1_coset_index * oracle.packed_leaf_count + internal_index;

            let mut value_index = context
                .alloc(1, crate::allocator::tracker::AllocationPlacement::BestFit)
                .unwrap();
            let mut path_index = context
                .alloc(1, crate::allocator::tracker::AllocationPlacement::BestFit)
                .unwrap();
            memory_copy_async(
                &mut value_index,
                &[logical_row_index as u32],
                context.get_exec_stream(),
            )
            .unwrap();
            memory_copy_async(
                &mut path_index,
                &[query_index as u32],
                context.get_exec_stream(),
            )
            .unwrap();

            let combined_leafs = oracle
                .trace_holder
                .get_leafs_and_merkle_paths(0, &value_index, &context)
                .unwrap()
                .leafs;
            let separate_leafs = oracle
                .trace_holder
                .get_query_leafs(0, &value_index, &context)
                .unwrap();
            let combined_paths = oracle
                .trace_holder
                .get_leafs_and_merkle_paths(0, &path_index, &context)
                .unwrap()
                .merkle_paths;
            let separate_paths = oracle
                .trace_holder
                .get_query_merkle_paths(0, &path_index, &context)
                .unwrap();

            context.get_exec_stream().synchronize().unwrap();
            assert_eq!(
                unsafe { separate_leafs.get_accessor().get() },
                unsafe { combined_leafs.get_accessor().get() },
                "query {query_index} leaf helper diverged"
            );
            assert_eq!(
                unsafe { separate_paths.get_accessor().get() },
                unsafe { combined_paths.get_accessor().get() },
                "query {query_index} path helper diverged"
            );
        }
    }
}
