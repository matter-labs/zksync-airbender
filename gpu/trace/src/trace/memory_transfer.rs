//! H2D transfer of a memory Merkle cap. Per-coset host caps are packed into a
//! contiguous host buffer in bit-reversed coset order and staged into a
//! matching device allocation on `h2d_stream`. A commitment's persisted
//! partial trees are staged the same way, in natural coset order.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::trace::decoder::DecoderTableTransfer;
use crate::trace::holder::{bitreverse_index, TraceHolder};
use crate::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::MerkleTreeCapVarLength;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;

/// The only partial-tree layout: natural coset order; per coset its live nodes
/// in builder order, the bottom stored level first and the coset's cap slots
/// last. The cap-sized unwritten suffix of each device stride is not part of it.
pub const PARTIAL_TREES_LAYOUT_VERSION: u32 = 1;

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
            log_domain_size: holder.log_domain_size,
            log_lde_factor: holder.log_lde_factor,
            log_rows_per_leaf: holder.log_rows_per_leaf,
            log_tree_cap_size: holder.log_tree_cap_size,
            reduction_layers: holder.partial_tree_reduction_layers(),
            columns_count: holder.columns_count,
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
pub struct PartialTrees {
    pub layout_version: u32,
    pub geometry: PartialTreesGeometry,
    pub nodes: Vec<Digest>,
}

/// Rejects persisted trees that do not belong to a commitment of `expected`
/// geometry with these natural-order per-coset caps.
pub fn validate_partial_trees(
    trees: &PartialTrees,
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
        expected.cosets_count() * live,
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
        .chunks_exact(live)
        .zip(memory_tree_caps)
        .enumerate()
    {
        assert!(
            nodes[live - cap_len..] == cap.cap[..],
            "partial tree of coset {coset} does not end in that coset's cap"
        );
    }
}

pub struct GpuGKRMemoryTransferHost {
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order, matching the device-side cap.
    pub(crate) unified_tree_cap: Vec<Digest>,
    /// Persisted partial trees in the device layout: natural coset order,
    /// `coset_stride` digests per coset, the unwritten suffix zeroed.
    pub(crate) partial_trees: Option<(PartialTreesGeometry, Vec<Digest>)>,
}

impl GpuGKRMemoryTransferHost {
    /// Packs naturally ordered per-coset caps into one bit-reversed cap.
    /// `log_lde_factor` specifies the number of cosets; `log_tree_cap_size`
    /// specifies the total cap size across all cosets.
    pub fn from_per_coset_caps(
        memory_tree_caps: &[MerkleTreeCapVarLength],
        log_lde_factor: u32,
        log_tree_cap_size: u32,
    ) -> Self {
        let lde_factor = 1usize << log_lde_factor;
        assert_eq!(
            memory_tree_caps.len(),
            lde_factor,
            "memory tree caps must contain one entry per coset",
        );
        let cap_size = 1usize << log_tree_cap_size;
        let per_coset = cap_size >> log_lde_factor;
        let mut unified_tree_cap = Vec::with_capacity(cap_size);
        for stage1_pos in 0..lde_factor {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
            let src = &memory_tree_caps[natural_coset_index].cap;
            assert_eq!(
                src.len(),
                per_coset,
                "memory tree cap[{natural_coset_index}] length mismatch",
            );
            unified_tree_cap.extend_from_slice(src);
        }
        Self {
            log_lde_factor,
            log_tree_cap_size,
            unified_tree_cap,
            partial_trees: None,
        }
    }

    /// `from_per_coset_caps` plus the commitment's persisted partial trees,
    /// validated against `expected` and the caps before anything is allocated.
    pub fn from_per_coset_caps_and_partial_trees(
        memory_tree_caps: &[MerkleTreeCapVarLength],
        expected: PartialTreesGeometry,
        trees: &PartialTrees,
    ) -> Self {
        validate_partial_trees(trees, &expected, memory_tree_caps);
        let mut host = Self::from_per_coset_caps(
            memory_tree_caps,
            expected.log_lde_factor,
            expected.log_tree_cap_size,
        );
        let mut slab = vec![Digest::default(); expected.cosets_count() * expected.coset_stride()];
        write_device_layout(&expected, &trees.nodes, &mut slab);
        host.partial_trees = Some((expected, slab));
        host
    }
}

/// Spreads the live nodes over the device stride and zeroes every unwritten slot.
fn write_device_layout(geometry: &PartialTreesGeometry, nodes: &[Digest], dst: &mut [Digest]) {
    let live = geometry.coset_live_len();
    for (dst, src) in dst
        .chunks_exact_mut(geometry.coset_stride())
        .zip(nodes.chunks_exact(live))
    {
        dst[..live].copy_from_slice(src);
        dst[live..].fill(Digest::default());
    }
}

pub struct GpuGKRMemoryTransfer<'a> {
    pub host: Arc<GpuGKRMemoryTransferHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    partial_trees: Option<DeviceAllocation<Digest>>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryTransfer<'a> {
    pub fn new(host: Arc<GpuGKRMemoryTransferHost>, context: &ProverContext) -> CudaResult<Self> {
        let cap_size = 1usize << host.log_tree_cap_size;
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

    /// Stages the unified cap and the persisted partial trees, if any.
    pub fn stage_transfer(&mut self, transfer: &mut Transfer<'a>) {
        transfer.stage(&self.host.unified_tree_cap, &mut self.unified_device_cap);
        if let Some(device) = self.partial_trees.as_mut() {
            let (_, slab) = self.host.partial_trees.as_ref().unwrap();
            transfer.stage(slab, device);
        }
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

// ---------------------------------------------------------------------------
// GpuGKRCommitMemoryTransfer
// ---------------------------------------------------------------------------

/// Input transfers for `commit_memory_from_transfers`: decoder,
/// inits-and-teardowns, and tracing data share one transfer fence.
pub struct GpuGKRCommitMemoryTransfer<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRCommitMemoryTransfer<'a, A> {
    pub fn new(
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
        tracing_data: Option<TracingDataTransfer<'a, A>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
        })
    }

    pub fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(it) = self.inits_and_teardowns.as_mut() {
            it.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(td) = self.tracing_data.as_mut() {
            td.schedule_transfer(&mut self.transfer, context)?;
        }
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
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
        let nodes: Vec<Digest> = (0..GEOMETRY.cosets_count() * live)
            .map(|i| [i as u32 + 1; 8])
            .collect();
        let caps = nodes
            .chunks_exact(live)
            .map(|coset| MerkleTreeCapVarLength {
                cap: coset[live - GEOMETRY.coset_cap_len()..].to_vec(),
            })
            .collect();
        let trees = PartialTrees {
            layout_version: PARTIAL_TREES_LAYOUT_VERSION,
            geometry: GEOMETRY,
            nodes,
        };
        (trees, caps)
    }

    #[test]
    fn cpu_partial_trees_validate_and_spread_over_the_device_stride() {
        assert_eq!((GEOMETRY.coset_stride(), GEOMETRY.coset_live_len()), (8, 6));
        let (trees, caps) = trees_and_caps();
        validate_partial_trees(&trees, &GEOMETRY, &caps);
        let (stride, live) = (GEOMETRY.coset_stride(), GEOMETRY.coset_live_len());
        let mut device = vec![[u32::MAX; 8]; GEOMETRY.cosets_count() * stride];
        write_device_layout(&GEOMETRY, &trees.nodes, &mut device);
        for (coset, (dst, src)) in device
            .chunks_exact(stride)
            .zip(trees.nodes.chunks_exact(live))
            .enumerate()
        {
            assert_eq!(&dst[..live], src, "coset {coset} live nodes");
            assert!(
                dst[live..]
                    .iter()
                    .all(|digest| *digest == Digest::default()),
                "coset {coset} padding"
            );
        }
    }

    #[test]
    #[should_panic(expected = "unsupported partial-tree layout version")]
    fn cpu_partial_trees_reject_an_unknown_layout() {
        let (mut trees, caps) = trees_and_caps();
        trees.layout_version += 1;
        validate_partial_trees(&trees, &GEOMETRY, &caps);
    }

    #[test]
    fn cpu_partial_trees_reject_every_geometry_field() {
        let (trees, caps) = trees_and_caps();
        let mutations: [fn(&mut PartialTreesGeometry); 6] = [
            |g| g.log_domain_size += 1,
            |g| g.log_lde_factor -= 1,
            |g| g.log_rows_per_leaf += 1,
            |g| g.log_tree_cap_size += 1,
            |g| g.reduction_layers += 1,
            |g| g.columns_count += 1,
        ];
        for (index, mutate) in mutations.into_iter().enumerate() {
            let mut expected = GEOMETRY;
            mutate(&mut expected);
            let message =
                std::panic::catch_unwind(|| validate_partial_trees(&trees, &expected, &caps))
                    .expect_err("a geometry mismatch must be rejected");
            let message = message.downcast_ref::<String>().unwrap();
            assert!(
                message.contains("partial-tree geometry differs from the proof's"),
                "field {index}: {message}"
            );
        }
    }

    #[test]
    #[should_panic(expected = "partial-tree payload length mismatch")]
    fn cpu_partial_trees_reject_a_short_payload() {
        let (mut trees, caps) = trees_and_caps();
        trees.nodes.pop();
        validate_partial_trees(&trees, &GEOMETRY, &caps);
    }

    #[test]
    #[should_panic(expected = "partial tree of coset 3 does not end in that coset's cap")]
    fn cpu_partial_trees_reject_a_foreign_cap() {
        let (trees, mut caps) = trees_and_caps();
        caps[3].cap[1][0] ^= 1;
        validate_partial_trees(&trees, &GEOMETRY, &caps);
    }
}
