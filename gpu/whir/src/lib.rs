#![cfg_attr(test, feature(allocator_api))]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
#![allow(clippy::mut_from_ref)]
// `no_cuda` gates out every GPU test body, leaving their helpers and imports dead
// by construction. That mode only ever compiles, so this is not a real finding.
#![cfg_attr(no_cuda, allow(dead_code, unused_imports))]

pub mod fold;
pub(crate) mod fused_commit;
pub(crate) mod in_domain;
pub(crate) mod kernels;
mod oracle_commit;
pub mod pow;
pub(crate) mod upstream;

#[cfg(test)]
mod test_utils;

#[cfg(test)]
gpu_core::force_serial_libtest!();

use era_cudart::result::CudaResult;

use crate::upstream::FieldExtension;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixImpl};
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{
    TraceHolder, TreesCacheMode, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS,
};

#[cfg(test)]
use crate::upstream::{extension_field_from_base_coeffs, Field, MerkleTreeCapVarLength};
use era_cudart::memory::memory_copy_async;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
#[cfg(test)]
use gpu_core::primitives::{
    context::HostAllocation, device_structures::DeviceMatrix,
    static_host::alloc_static_pinned_box_from_slice,
};
#[cfg(test)]
use gpu_hash::blake2s::Digest;

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;
const LOG_SRC_COLS_PER_COSET: u32 = EXT4_DEGREE.trailing_zeros();
const _: () = assert!(EXT4_DEGREE.is_power_of_two());

/// Where the WHIR oracle's unified Merkle cap should land after its per-coset
/// trees are committed.
///
/// - `Slab(...)` — the cap is gathered directly into a caller-supplied device
///   slice (typically a `whir.intermediate[round].cap` slab subrange), and
///   `unified_device_cap` stays `None`. Downstream readers must source the
///   cap from the slab.
enum CapTarget<'a> {
    #[cfg(test)]
    OwnAllocation,
    Slab(&'a mut era_cudart::slice::DeviceSlice<u32>),
}

enum OracleValues {
    Coefficients,
    Recomputed(gpu_core::primitives::context::DeviceAllocation<BF>),
}

pub(crate) struct GpuWhirExtensionOracle {
    trace_holder: TraceHolder<BF>,
    values_per_leaf: usize,
    lde_factor: usize,
    trace_len_log2: u32,
    packed_leaf_count: usize,
    values: OracleValues,
}

#[cfg(test)]
type HostQueryOutputs = (HostAllocation<[BF]>, HostAllocation<[Digest]>);

impl GpuWhirExtensionOracle {
    /// Constructs the coefficient oracle and writes the
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

        let trace_len_log2 = trace_len.trailing_zeros();
        let log_lde_factor = lde_factor.trailing_zeros();
        let log_values_per_leaf = values_per_leaf.trailing_zeros();
        let log_tree_cap_size = tree_cap_size.trailing_zeros();
        assert!(trace_len_log2 >= log_values_per_leaf);
        let packed_leaf_count = trace_len / values_per_leaf;
        let packed_leaf_count_log2 = packed_leaf_count.trailing_zeros();
        let total_leaf_count_log2 = packed_leaf_count_log2 + log_lde_factor;
        assert!(
            total_leaf_count_log2 > PARTIAL_TREE_REDUCTION_LAYERS + log_tree_cap_size,
            "recursive WHIR commitments require a partial tree",
        );
        let fused_coefficients = fused_commit::supported(trace_len_log2, log_values_per_leaf);
        assert!(
            fused_coefficients || matches!((trace_len_log2, log_values_per_leaf), (14..=23, 5)),
            "unsupported recursive WHIR coefficient shape: log_n={trace_len_log2}, log_v={log_values_per_leaf}",
        );

        // Reinterpret bitreverse-N coefficients as V bitreverse-(N/V)
        // residue polynomials per BF limb. The leaf reader's bit-reversed
        // slot lookup restores natural residue order.
        let make_holder = if fused_coefficients {
            TraceHolder::new_tree_only
        } else {
            TraceHolder::new_commitment_only
        };
        let mut trace_holder = make_holder(
            total_leaf_count_log2,
            0,
            0,
            log_tree_cap_size,
            EXT4_DEGREE * values_per_leaf,
            TreesCacheMode::CachePartial,
            context,
        )?;
        // Retained oracles release the relabel scratch after all its readers
        // have been scheduled on exec. Fused oracles keep it for query reconstruction.
        let monomial_coeffs_slice = monomial_coeffs.slice();
        let monomial_coeffs_stride = monomial_coeffs.stride();
        let stream = context.get_exec_stream();
        let mut bitreversed_coeffs: gpu_core::primitives::context::DeviceAllocation<BF> =
            context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
        for column in 0..EXT4_DEGREE {
            let src_start = column * monomial_coeffs_stride;
            memory_copy_async(
                &mut bitreversed_coeffs[column * trace_len..(column + 1) * trace_len],
                &monomial_coeffs_slice[src_start..src_start + trace_len],
                stream,
            )?;
        }
        {
            let mut bitreversed_matrix =
                DeviceMatrixMut::new(&mut bitreversed_coeffs[..], trace_len);
            gpu_ops::bit_reverse::bit_reverse_in_place::<BF>(&mut bitreversed_matrix, stream)?;
        }
        let inputs_matrix = DeviceMatrixChunk::new(
            &bitreversed_coeffs[..],
            packed_leaf_count,
            0,
            packed_leaf_count,
        );

        match cap_target {
            #[cfg(test)]
            CapTarget::OwnAllocation => {
                let mut unified_cap = context.alloc(
                    tree_cap_size,
                    gpu_core::allocator::tracker::AllocationPlacement::BestFit,
                )?;
                let cap_dst_u32 = unsafe {
                    era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                        unified_cap.as_mut_ptr() as *mut u32,
                        tree_cap_size * gpu_hash::blake2s::STATE_SIZE,
                    )
                };
                oracle_commit::schedule_recursive_oracle_commit(
                    &mut trace_holder,
                    &inputs_matrix,
                    cap_dst_u32,
                    trace_len_log2,
                    log_lde_factor,
                    log_values_per_leaf,
                    EXT4_DEGREE,
                    fused_coefficients,
                    context,
                )?;
                trace_holder.install_unified_device_cap(unified_cap);
            }
            CapTarget::Slab(dst_u32) => {
                oracle_commit::schedule_recursive_oracle_commit(
                    &mut trace_holder,
                    &inputs_matrix,
                    dst_u32,
                    trace_len_log2,
                    log_lde_factor,
                    log_values_per_leaf,
                    EXT4_DEGREE,
                    fused_coefficients,
                    context,
                )?;
            }
        }
        if !fused_coefficients {
            trace_holder.mark_cosets_materialized();
        }

        Ok(Self {
            trace_holder,
            values_per_leaf,
            lde_factor,
            trace_len_log2,
            packed_leaf_count,
            values: if fused_coefficients {
                OracleValues::Recomputed(bitreversed_coeffs)
            } else {
                OracleValues::Coefficients
            },
        })
    }

    pub(crate) fn lde_factor(&self) -> usize {
        self.lde_factor
    }

    /// Refresh symbolic terms from this round's coefficient oracle. Retained
    /// oracles only gather values. Recomputed oracles evaluate the selected
    /// coefficient leaves directly, without hashing or constructing paths.
    pub(crate) fn schedule_in_domain_leaves(
        &mut self,
        folded_indexes: &era_cudart::slice::DeviceSlice<u32>,
        leaves: &mut era_cudart::slice::DeviceSlice<E4>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(leaves.len(), folded_indexes.len() * self.values_per_leaf);
        let log_v = self.values_per_leaf.trailing_zeros();
        let log_c = self.lde_factor.trailing_zeros();
        let mut tree_indexes = context.alloc(folded_indexes.len(), AllocationPlacement::BestFit)?;
        gpu_hash::blake2s::query_index_to_tree_index(
            folded_indexes,
            &mut tree_indexes,
            log_c,
            self.packed_leaf_count.trailing_zeros(),
            context.get_exec_stream(),
        )?;
        if let OracleValues::Recomputed(coeffs) = &self.values {
            return in_domain::leaves_from_monomials(
                coeffs,
                context.ntt_device_context().whir_leaf_transform_params(),
                self.trace_len_log2,
                log_c,
                log_v,
                &tree_indexes,
                leaves,
                context.get_exec_stream(),
            );
        }
        // E4 is four consecutive BF limbs; the destination remains exclusively
        // owned here until the queued gather has written every leaf slot.
        let leaves_bf = unsafe {
            era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                leaves.as_mut_ptr() as *mut BF,
                leaves.len() * EXT4_DEGREE,
            )
        };
        self.trace_holder.schedule_query_leaves_into_from_ntt(
            &tree_indexes,
            leaves_bf,
            self.trace_len_log2,
            log_c,
            log_v,
            LOG_SRC_COLS_PER_COSET,
            context,
        )
    }

    fn schedule_query_leaves_and_paths_into_from_ntt(
        &mut self,
        tree_indexes: &era_cudart::slice::DeviceSlice<u32>,
        leaves_dst: &mut era_cudart::slice::DeviceSlice<BF>,
        paths_dst: &mut era_cudart::slice::DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let queries_count = tree_indexes.len();
        let log_values_per_leaf = self.values_per_leaf.trailing_zeros();
        let log_lde_factor = self.lde_factor.trailing_zeros();
        let layers_count = self.trace_holder.log_domain_size
            - self.trace_holder.log_rows_per_leaf
            - (self.trace_holder.log_tree_cap_size - self.trace_holder.log_lde_factor);
        assert_eq!(
            leaves_dst.len(),
            queries_count * self.values_per_leaf * EXT4_DEGREE,
        );
        assert_eq!(
            paths_dst.len(),
            queries_count * layers_count as usize * gpu_hash::blake2s::STATE_SIZE,
        );

        if let OracleValues::Recomputed(coefficients) = &self.values {
            let TreesHolder::Partial(tree) = &self.trace_holder.trees else {
                unreachable!("recomputed WHIR oracles require a partial tree")
            };
            return fused_commit::query(
                coefficients,
                tree,
                tree_indexes,
                leaves_dst,
                paths_dst,
                self.trace_len_log2,
                log_lde_factor,
                log_values_per_leaf,
                self.trace_holder.log_tree_cap_size,
                context.ntt_device_context().whir_leaf_transform_params(),
                context.get_exec_stream(),
            );
        }

        self.trace_holder.schedule_query_leaves_into_from_ntt(
            tree_indexes,
            leaves_dst,
            self.trace_len_log2,
            log_lde_factor,
            log_values_per_leaf,
            LOG_SRC_COLS_PER_COSET,
            context,
        )?;
        self.trace_holder.schedule_query_merkle_paths_into_from_ntt(
            tree_indexes,
            paths_dst,
            self.trace_len_log2,
            log_lde_factor,
            log_values_per_leaf,
            LOG_SRC_COLS_PER_COSET,
            context,
        )
    }

    /// batch-gather all `device_query_indexes` of one
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
        gpu_hash::blake2s::query_index_to_tree_index(
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
        self.schedule_query_leaves_and_paths_into_from_ntt(
            slab_indices_view,
            slab_leaves_dst_bf,
            slab_paths_dst,
            context,
        )
    }

    #[cfg(test)]
    fn schedule_query_outputs_to_host(
        &mut self,
        tree_indexes: &era_cudart::slice::DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<HostQueryOutputs> {
        let queries_count = tree_indexes.len();
        let leaf_len = queries_count * self.values_per_leaf * EXT4_DEGREE;
        let layers_count = self.trace_holder.log_domain_size
            - self.trace_holder.log_rows_per_leaf
            - (self.trace_holder.log_tree_cap_size - self.trace_holder.log_lde_factor);
        let paths_len = queries_count * layers_count as usize;
        let mut device_leaves = context.alloc(leaf_len, AllocationPlacement::BestFit)?;
        let mut device_paths: gpu_core::primitives::context::DeviceAllocation<Digest> =
            context.alloc(paths_len, AllocationPlacement::BestFit)?;
        let device_paths_u32 = unsafe {
            era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                device_paths.as_mut_ptr() as *mut u32,
                paths_len * gpu_hash::blake2s::STATE_SIZE,
            )
        };
        self.schedule_query_leaves_and_paths_into_from_ntt(
            tree_indexes,
            &mut device_leaves,
            device_paths_u32,
            context,
        )?;

        let stream = context.get_exec_stream();
        let mut leaves = unsafe { context.alloc_host_uninit_slice(leaf_len) };
        let mut paths = unsafe { context.alloc_host_uninit_slice(paths_len) };
        memory_copy_async(&mut leaves, &device_leaves, stream)?;
        memory_copy_async(&mut paths, &device_paths, stream)?;
        Ok((leaves, paths))
    }
}

#[cfg(test)]
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
    #[cfg(test)]
    pub(crate) fn from_monomial_coeffs(
        monomial_coeffs: &[E4],
        lde_factor: usize,
        values_per_leaf: usize,
        tree_cap_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let trace_len = monomial_coeffs.len();
        let vectorized_monomial_coeffs = e4_coeffs_to_vectorized(monomial_coeffs);
        let mut monomial_coeffs_device_alloc = context.alloc(
            vectorized_monomial_coeffs.len(),
            AllocationPlacement::BestFit,
        )?;
        let stream = context.get_exec_stream();
        let host = alloc_static_pinned_box_from_slice(&vectorized_monomial_coeffs[..])?;
        memory_copy_async(&mut monomial_coeffs_device_alloc, &host[..], stream)?;
        let monomial_coeffs_device = DeviceMatrix::new(&monomial_coeffs_device_alloc, trace_len);
        let oracle = Self::from_device_monomial_coeffs_impl(
            &monomial_coeffs_device,
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

    #[cfg(test)]
    pub(crate) fn get_tree_cap(
        &self,
        context: &ProverContext,
    ) -> CudaResult<MerkleTreeCapVarLength> {
        self.trace_holder.read_full_cap_synchronously(context)
    }
}

#[cfg(test)]
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
