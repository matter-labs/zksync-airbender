//! H2D transfer of a memory Merkle cap. Per-coset host caps are packed into a
//! contiguous host buffer in bit-reversed coset order and staged into a
//! matching device allocation on `h2d_stream`. A commitment's persisted
//! partial trees use their own pooled pinned source in natural coset order.

use era_cudart::slice::CudaSlice;
use execution_prover_model::allocator::PooledHostBuffer;
use fft::GoodAllocator;
use std::alloc::Global;
use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::result::CudaResult;

use crate::trace::holder::{bitreverse_index, TraceHolder};
use crate::upstream::{BaseCommitmentGeometry, BaseOracleRole, MerkleTreeCapVarLength};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;

/// Natural coset order and the device stride: live nodes in builder order,
/// followed by a zeroed cap-sized unwritten suffix.
pub const PARTIAL_TREES_LAYOUT_VERSION: u32 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialTreesGeometry {
    pub log_domain_size: u32,
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
    pub reduction_layers: u32,
    pub columns_count: usize,
}

impl PartialTreesGeometry {
    /// Geometry of `holder`'s cached partial trees at its resolved depth.
    pub fn of_holder<T>(holder: &TraceHolder<T>) -> Self {
        Self {
            log_domain_size: holder.commitment_log_domain_size(),
            log_lde_factor: holder.log_lde_factor,
            log_rows_per_leaf: holder.log_rows_per_leaf,
            log_tree_cap_size: holder.log_tree_cap_size,
            reduction_layers: holder.partial_tree_reduction_layers(),
            columns_count: holder.committed_columns_count(),
        }
    }

    pub fn cosets_count(&self) -> usize {
        1 << self.log_lde_factor
    }

    /// Digests per coset in the device tree backing.
    pub fn coset_stride(&self) -> usize {
        1 << (self.log_domain_size - self.reduction_layers + 1 - self.log_rows_per_leaf)
    }

    pub fn coset_cap_len(&self) -> usize {
        1 << (self.log_tree_cap_size - self.log_lde_factor)
    }

    /// Nodes the builder writes per coset: every level up to the coset's cap.
    pub fn coset_live_len(&self) -> usize {
        self.coset_stride() - self.coset_cap_len()
    }
}

/// Host copy of a commitment's partial trees in `PARTIAL_TREES_LAYOUT_VERSION`.
pub struct PartialTrees<A: GoodAllocator = Global> {
    pub layout_version: u32,
    pub geometry: PartialTreesGeometry,
    pub nodes: PooledHostBuffer<Digest, A>,
}

/// Rejects persisted trees that do not belong to a commitment of `expected`
/// geometry with these natural-order per-coset caps.
pub fn validate_partial_trees<A: GoodAllocator>(
    trees: &PartialTrees<A>,
    expected: &PartialTreesGeometry,
    memory_tree_caps: &[MerkleTreeCapVarLength],
) {
    assert_eq!(
        trees.layout_version, PARTIAL_TREES_LAYOUT_VERSION,
        "unsupported partial-tree layout version"
    );
    assert_eq!(
        &trees.geometry, expected,
        "partial-tree geometry differs from the proof's"
    );
    let live = expected.coset_live_len();
    assert_eq!(
        trees.nodes.len(),
        expected.cosets_count() * expected.coset_stride(),
        "partial-tree payload length mismatch"
    );
    assert_eq!(
        memory_tree_caps.len(),
        expected.cosets_count(),
        "memory tree caps must contain one entry per coset",
    );
    let cap_len = expected.coset_cap_len();
    for (coset, (nodes, cap)) in trees
        .nodes
        .chunks_exact(expected.coset_stride())
        .zip(memory_tree_caps)
        .enumerate()
    {
        assert!(
            nodes[live - cap_len..live] == cap.cap[..],
            "partial tree of coset {coset} does not end in that coset's cap"
        );
    }
}

pub struct GpuGKRMemoryCapHost {
    base_geometry: BaseCommitmentGeometry,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order, matching the device-side cap.
    pub(crate) unified_tree_cap: Vec<Digest>,
    /// Persisted partial trees in the device layout: natural coset order,
    /// `coset_stride` digests per coset, the unwritten suffix zeroed.
    pub(crate) partial_trees: Option<(
        PartialTreesGeometry,
        Arc<dyn CudaSlice<Digest> + Send + Sync>,
    )>,
}

impl GpuGKRMemoryCapHost {
    /// Packs naturally ordered per-coset caps into one bit-reversed cap bound
    /// to the producing commitment geometry.
    pub fn from_per_coset_caps_for_geometry(
        caps: &[MerkleTreeCapVarLength],
        geometry: BaseCommitmentGeometry,
    ) -> Self {
        let log_lde_factor = geometry.lde_factor().trailing_zeros();
        let log_tree_cap_size = geometry.cap_size().trailing_zeros();
        let lde_factor = geometry.lde_factor();
        let cap_size = geometry.cap_size();
        assert_eq!(
            caps.len(),
            lde_factor,
            "memory tree caps must contain one entry per coset"
        );
        let empty = geometry.oracle(BaseOracleRole::Memory).physical_columns() == 0;
        let per_coset = if empty { 0 } else { cap_size / lde_factor };
        for (index, cap) in caps.iter().enumerate() {
            assert_eq!(
                cap.cap.len(),
                per_coset,
                "memory tree cap[{index}] length mismatch"
            );
        }
        let mut unified_tree_cap = Vec::with_capacity(if empty { 0 } else { cap_size });
        for stage1_pos in 0..lde_factor {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
            unified_tree_cap.extend_from_slice(&caps[natural_coset_index].cap);
        }
        Self {
            base_geometry: geometry,
            log_lde_factor,
            log_tree_cap_size,
            unified_tree_cap,
            partial_trees: None,
        }
    }

    /// A memory cap serves only proofs of the geometry it was produced for.
    pub fn validate_for_geometry(&self, geometry: &BaseCommitmentGeometry) {
        assert_eq!(
            self.base_geometry, *geometry,
            "memory cap producing geometry mismatch"
        );
    }

    /// `from_per_coset_caps` plus the commitment's persisted partial trees,
    /// validated against `expected` and the caps before anything is allocated.
    pub fn from_per_coset_caps_and_partial_trees<A: GoodAllocator + 'static>(
        memory_tree_caps: &[MerkleTreeCapVarLength],
        geometry: BaseCommitmentGeometry,
        expected: PartialTreesGeometry,
        trees: PartialTrees<A>,
    ) -> Self {
        validate_partial_trees(&trees, &expected, memory_tree_caps);
        let mut host = Self::from_per_coset_caps_for_geometry(memory_tree_caps, geometry);
        assert_eq!(
            expected.log_domain_size,
            geometry.message_size_log2() as u32
        );
        assert_eq!(
            expected.log_lde_factor,
            geometry.lde_factor().trailing_zeros()
        );
        assert_eq!(
            expected.log_rows_per_leaf,
            geometry.values_per_leaf().trailing_zeros()
        );
        assert_eq!(
            expected.log_tree_cap_size,
            geometry.cap_size().trailing_zeros()
        );
        assert_eq!(
            expected.columns_count,
            geometry.oracle(BaseOracleRole::Memory).physical_columns()
        );
        host.partial_trees = Some((expected, Arc::new(trees.nodes)));
        host
    }
}

pub struct GpuGKRMemoryCapTransfer<'a> {
    pub host: Arc<GpuGKRMemoryCapHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    partial_trees: Option<DeviceAllocation<Digest>>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryCapTransfer<'a> {
    pub fn new(host: Arc<GpuGKRMemoryCapHost>, context: &ProverContext) -> CudaResult<Self> {
        let cap_size = host.unified_tree_cap.len();
        let unified_device_cap = context.alloc::<Digest>(cap_size, AllocationPlacement::BestFit)?;
        let partial_trees = host
            .partial_trees
            .as_ref()
            .map(|(_, slab)| context.alloc::<Digest>(slab.len(), AllocationPlacement::BestFit))
            .transpose()?;
        Ok(Self {
            host,
            unified_device_cap,
            partial_trees,
            _marker: PhantomData,
        })
    }

    /// Stages the small unified cap.
    pub fn stage_transfer(&mut self, transfer: &mut Transfer<'a>) {
        transfer.stage(&self.host.unified_tree_cap, &mut self.unified_device_cap);
    }

    /// Submit after all small values are staged; the source survives through finish().
    pub fn schedule_partial_tree_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if let Some(device) = self.partial_trees.as_mut() {
            let (_, source) = self.host.partial_trees.as_ref().unwrap();
            transfer.schedule(Arc::clone(source), device, context)?;
        }
        Ok(())
    }

    pub fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        &self.unified_device_cap
    }

    /// Hands the transferred partial trees to the holder that opens them.
    pub fn take_partial_trees(
        &mut self,
    ) -> Option<(PartialTreesGeometry, DeviceAllocation<Digest>)> {
        let device = self.partial_trees.take()?;
        let (geometry, _) = self.host.partial_trees.as_ref().unwrap();
        Some((*geometry, device))
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    const GEOMETRY: PartialTreesGeometry = PartialTreesGeometry {
        log_domain_size: 8,
        log_lde_factor: 2,
        log_rows_per_leaf: 1,
        log_tree_cap_size: 3,
        reduction_layers: 5,
        columns_count: 3,
    };

    fn trees_and_caps() -> (PartialTrees, Vec<MerkleTreeCapVarLength>) {
        let live = GEOMETRY.coset_live_len();
        let stride = GEOMETRY.coset_stride();
        let mut nodes = vec![Digest::default(); GEOMETRY.cosets_count() * stride];
        for (coset, dst) in nodes.chunks_exact_mut(stride).enumerate() {
            for (i, value) in dst[..live].iter_mut().enumerate() {
                *value = [(coset * live + i) as u32 + 1; 8];
            }
        }
        let caps = nodes
            .chunks_exact(stride)
            .map(|coset| MerkleTreeCapVarLength {
                cap: coset[live - GEOMETRY.coset_cap_len()..live].to_vec(),
            })
            .collect();
        let nodes = PooledHostBuffer::new(nodes, crossbeam_channel::unbounded().0);
        let trees = PartialTrees {
            layout_version: PARTIAL_TREES_LAYOUT_VERSION,
            geometry: GEOMETRY,
            nodes,
        };
        (trees, caps)
    }

    #[test]
    fn cpu_partial_trees_validate_the_device_stride() {
        assert_eq!((GEOMETRY.coset_stride(), GEOMETRY.coset_live_len()), (8, 6));
        let (trees, caps) = trees_and_caps();
        validate_partial_trees(&trees, &GEOMETRY, &caps);
        let (stride, live) = (GEOMETRY.coset_stride(), GEOMETRY.coset_live_len());
        for (coset, dst) in trees.nodes.chunks_exact(stride).enumerate() {
            let expected: Vec<_> = (0..live)
                .map(|i| [(coset * live + i) as u32 + 1; 8])
                .collect();
            assert_eq!(&dst[..live], &expected, "coset {coset} live nodes");
            assert!(
                dst[live..]
                    .iter()
                    .all(|digest| *digest == Digest::default()),
                "coset {coset} padding"
            );
        }
    }
}
