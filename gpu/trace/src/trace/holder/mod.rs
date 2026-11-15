use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use crate::upstream::{BaseCommitmentGeometry, BaseOracleRole, MerkleTreeCapVarLength};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::ProverContext;

#[doc(hidden)]
pub const PARTIAL_TREE_REDUCTION_LAYERS: u32 = gpu_core::primitives::utils::LOG_WARP_SIZE;

#[doc(hidden)]
pub const MAX_PARTIAL_TREE_REDUCTION_LAYERS: u32 =
    gpu_hash::blake2s::MAX_PARTIAL_TREE_REDUCTION_LAYERS;

#[doc(hidden)]
pub fn assert_partial_tree_reduction_layers(requested: u32) {
    assert!(
        (PARTIAL_TREE_REDUCTION_LAYERS..=MAX_PARTIAL_TREE_REDUCTION_LAYERS).contains(&requested),
        "partial-tree reduction layers {requested} outside {PARTIAL_TREE_REDUCTION_LAYERS}..={MAX_PARTIAL_TREE_REDUCTION_LAYERS}"
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialTreePolicy {
    pub setup: u32,
    pub memory: u32,
    pub witness: u32,
}

impl PartialTreePolicy {
    pub const DEFAULT: Self = Self::uniform(PARTIAL_TREE_REDUCTION_LAYERS);

    pub const fn uniform(reduction_layers: u32) -> Self {
        Self {
            setup: reduction_layers,
            memory: reduction_layers,
            witness: reduction_layers,
        }
    }
}

impl Default for PartialTreePolicy {
    fn default() -> Self {
        Self::DEFAULT
    }
}

#[doc(hidden)]
pub fn resolve_partial_tree_reduction_layers(
    requested: u32,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
) -> u32 {
    assert_partial_tree_reduction_layers(requested);
    let log_coset_cap = log_tree_cap_size
        .checked_sub(log_lde_factor)
        .expect("partial trees require log_tree_cap_size >= log_lde_factor");
    let available = log_domain_size
        .checked_sub(log_rows_per_leaf + log_coset_cap)
        .expect("partial trees require log_domain_size >= log_rows_per_leaf + log_coset_cap");
    let resolved = requested.min(available);
    assert!(
        resolved >= PARTIAL_TREE_REDUCTION_LAYERS,
        "partial tree needs {PARTIAL_TREE_REDUCTION_LAYERS} reduction layers below the coset cap, only {available} available"
    );
    resolved
}

#[doc(hidden)]
#[derive(Copy, Clone)]
pub enum TreesCacheMode {
    CacheNone,
    CachePartial,
    CacheFull,
}

/// `PerCoset` and `InPlace` require `log_domain_size` in `20..=24`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OpeningStrategy {
    #[default]
    AllCosets,
    PerCoset,
    InPlace,
}

/// `PerCoset` and `InPlace` require `log_domain_size` in `20..=24`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WitnessCommitmentStrategy {
    #[default]
    AllCosets,
    PerCoset,
    InPlace,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WitnessPostCommitStorage {
    RawEvaluations,
    RawAndMonomials,
    #[default]
    RawAndCosets,
}

pub(crate) enum CosetsHolder<T> {
    Full(DeviceAllocation<T>),
    None(std::marker::PhantomData<T>),
}

#[doc(hidden)]
pub enum TreesHolder {
    Full(DeviceAllocation<Digest>),
    Partial(DeviceAllocation<Digest>),
    None,
}

#[doc(hidden)]
pub struct TraceHolder<T> {
    /// Logical GKR dimensions; commitment readers use the committed getters.
    pub log_domain_size: u32,
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
    pub columns_count: usize,
    pub(crate) base_geometry: Option<(BaseCommitmentGeometry, BaseOracleRole)>,
    partial_tree_reduction_layers: u32,
    pub(crate) raw_hypercube_evals: Option<std::sync::Arc<DeviceAllocation<T>>>,
    pub(crate) cosets_materialized: bool,
    pub(crate) opening_raw: Option<DeviceAllocation<T>>,
    pub(crate) opening_monomials: Option<DeviceAllocation<T>>,
    pub(crate) defer_opening: bool,
    pub(crate) opening_policy: OpeningStrategy,
    pub(crate) cosets: CosetsHolder<T>,
    pub trees: TreesHolder,
    /// Device-resident, contiguous Merkle cap of length `1 << log_tree_cap_size`,
    /// laid out in canonical bit-reversed coset order (`stage1_pos = 0..lde_factor`,
    /// reading from `coset[bitreverse(stage1_pos)]`). Populated by `commit_all`
    /// or supplied through `install_unified_device_cap`.
    pub unified_device_cap: Option<DeviceAllocation<Digest>>,
}

impl<T> TraceHolder<T> {
    pub fn commitment_log_domain_size(&self) -> u32 {
        self.base_geometry
            .as_ref()
            .map_or(self.log_domain_size, |(geometry, _)| {
                u32::try_from(geometry.message_size_log2()).expect("message log2 exceeds u32")
            })
    }

    pub fn committed_columns_count(&self) -> usize {
        self.base_geometry
            .as_ref()
            .map_or(self.columns_count, |(geometry, role)| {
                geometry.oracle(*role).physical_columns()
            })
    }

    pub(crate) fn is_empty_base_oracle(&self) -> bool {
        self.base_geometry.is_some() && self.committed_columns_count() == 0
    }
}

impl<T> TraceHolder<T> {
    pub fn install_partial_trees(&mut self, context: &ProverContext) -> CudaResult<()> {
        assert!(
            matches!(self.trees, TreesHolder::None),
            "install_partial_trees requires TreesHolder::None"
        );
        assert!(
            self.unified_device_cap.is_none() && !self.cosets_materialized,
            "install_partial_trees requires an uncommitted trace"
        );
        self.trees = TreesHolder::Partial(allocate_trees(
            1usize << self.log_lde_factor,
            self.commitment_log_domain_size() - self.partial_tree_reduction_layers(),
            self.log_rows_per_leaf,
            context,
        )?);
        Ok(())
    }

    pub fn partial_tree_reduction_layers(&self) -> u32 {
        resolve_partial_tree_reduction_layers(
            self.partial_tree_reduction_layers,
            self.commitment_log_domain_size(),
            self.log_lde_factor,
            self.log_rows_per_leaf,
            self.log_tree_cap_size,
        )
    }

    pub(crate) fn allocate_partial_tree_scratch(
        &self,
        context: &ProverContext,
    ) -> CudaResult<Option<DeviceAllocation<Digest>>> {
        if self.partial_tree_reduction_layers() == PARTIAL_TREE_REDUCTION_LAYERS {
            return Ok(None);
        }
        let leaves = 1usize << (self.commitment_log_domain_size() - self.log_rows_per_leaf);
        context
            .alloc(
                leaves >> PARTIAL_TREE_REDUCTION_LAYERS,
                AllocationPlacement::BestFit,
            )
            .map(Some)
    }

    pub fn new(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let raw_hypercube_evals = std::sync::Arc::new(context.alloc(
            columns_count << log_domain_size,
            AllocationPlacement::Bottom,
        )?);
        Self::new_with_raw_backing(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            trees_cache_mode,
            partial_tree_reduction_layers,
            Some(raw_hypercube_evals),
            true,
            context,
        )
    }

    /// Allocates commitment storage for an external scheduler that writes the
    /// cosets directly. No raw hypercube values are allocated; this holder
    /// cannot rematerialize released cosets from raw values.
    pub fn new_commitment_only(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::new_with_raw_backing(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            trees_cache_mode,
            partial_tree_reduction_layers,
            None,
            true,
            context,
        )
    }

    /// Allocates only tree storage. The external commitment scheduler owns the
    /// source values and must reconstruct openings without this holder's cosets.
    /// Public for the fused recursive commitment scheduler in `gpu_whir`.
    pub fn new_tree_only(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::new_with_raw_backing(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            trees_cache_mode,
            partial_tree_reduction_layers,
            None,
            false,
            context,
        )
    }

    fn new_with_raw_backing(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        raw_hypercube_evals: Option<std::sync::Arc<DeviceAllocation<T>>>,
        allocate_coset_backing: bool,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let instances_count = 1usize << log_lde_factor;
        let cosets = if allocate_coset_backing {
            CosetsHolder::Full(allocate_cosets(
                instances_count,
                log_domain_size,
                columns_count,
                context,
            )?)
        } else {
            CosetsHolder::None(std::marker::PhantomData)
        };
        assert_partial_tree_reduction_layers(partial_tree_reduction_layers);
        let trees = match trees_cache_mode {
            TreesCacheMode::CacheNone => TreesHolder::None,
            TreesCacheMode::CachePartial => TreesHolder::Partial(allocate_trees(
                instances_count,
                log_domain_size
                    - resolve_partial_tree_reduction_layers(
                        partial_tree_reduction_layers,
                        log_domain_size,
                        log_lde_factor,
                        log_rows_per_leaf,
                        log_tree_cap_size,
                    ),
                log_rows_per_leaf,
                context,
            )?),
            TreesCacheMode::CacheFull => TreesHolder::Full(allocate_trees(
                instances_count,
                log_domain_size,
                log_rows_per_leaf,
                context,
            )?),
        };
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            partial_tree_reduction_layers,
            raw_hypercube_evals,
            base_geometry: None,
            cosets_materialized: false,
            opening_raw: None,
            opening_monomials: None,
            defer_opening: false,
            opening_policy: OpeningStrategy::AllCosets,
            cosets,
            trees,
            unified_device_cap: None,
        })
    }

    /// Creates a trace holder that allocates only the hypercube evaluation buffer and
    /// (optionally) tree storage, but defers coset allocation until `ensure_cosets_materialized`.
    #[doc(hidden)]
    pub fn new_without_cosets(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::new_without_cosets_padded(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            0,
            trees_cache_mode,
            partial_tree_reduction_layers,
            context,
        )
    }

    /// Rounds raw backing up to groups of `2^pad_columns_to_log2` columns,
    /// zeroing the tail on exec before a producer can fork onto another stream.
    /// Logical readers and writers retain their original prefix view.
    #[allow(clippy::too_many_arguments)]
    pub fn new_without_cosets_padded(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        pad_columns_to_log2: u32,
        trees_cache_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let instances_count = 1usize << log_lde_factor;
        let padding = 1usize
            .checked_shl(pad_columns_to_log2)
            .expect("raw column padding shift overflow");
        let rows = 1usize
            .checked_shl(log_domain_size)
            .expect("raw trace size shift overflow");
        let allocated_columns = columns_count
            .checked_next_multiple_of(padding)
            .expect("padded column count overflow");
        let allocation_len = allocated_columns
            .checked_mul(rows)
            .expect("padded raw element count overflow");
        let logical_len = columns_count
            .checked_mul(rows)
            .expect("logical raw element count overflow");
        let mut backing = context.alloc(allocation_len, AllocationPlacement::Bottom)?;
        if allocated_columns > columns_count {
            let tail = &mut backing[logical_len..];
            memory_set_async(
                // SAFETY: the exclusive byte view covers only padding owned by this allocation.
                unsafe { tail.transmute_mut::<u8>() },
                0,
                context.get_exec_stream(),
            )?;
        }
        let raw_hypercube_evals = std::sync::Arc::new(backing);
        assert_partial_tree_reduction_layers(partial_tree_reduction_layers);
        let trees = match trees_cache_mode {
            TreesCacheMode::CacheNone => TreesHolder::None,
            TreesCacheMode::CachePartial => TreesHolder::Partial(allocate_trees(
                instances_count,
                log_domain_size
                    - resolve_partial_tree_reduction_layers(
                        partial_tree_reduction_layers,
                        log_domain_size,
                        log_lde_factor,
                        log_rows_per_leaf,
                        log_tree_cap_size,
                    ),
                log_rows_per_leaf,
                context,
            )?),
            TreesCacheMode::CacheFull => TreesHolder::Full(allocate_trees(
                instances_count,
                log_domain_size,
                log_rows_per_leaf,
                context,
            )?),
        };
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            partial_tree_reduction_layers,
            raw_hypercube_evals: Some(raw_hypercube_evals),
            base_geometry: None,
            cosets_materialized: false,
            opening_raw: None,
            opening_monomials: None,
            defer_opening: false,
            opening_policy: OpeningStrategy::AllCosets,
            cosets: CosetsHolder::None(std::marker::PhantomData),
            trees,
            unified_device_cap: None,
        })
    }

    /// Returns the unified device cap populated by `commit_all` or
    /// supplied through `install_unified_device_cap`.
    #[doc(hidden)]
    pub fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        self.unified_device_cap
            .as_ref()
            .expect("unified device cap must be materialized before access")
    }

    /// Installs a private unified cap after an external scheduler has filled it.
    #[doc(hidden)]
    pub fn install_unified_device_cap(&mut self, cap: DeviceAllocation<Digest>) {
        assert_eq!(cap.len(), 1usize << self.log_tree_cap_size);
        assert!(
            self.unified_device_cap.is_none(),
            "unified device cap was already installed",
        );
        self.unified_device_cap = Some(cap);
    }

    /// Installs partial trees transferred from this oracle's commitment, so the
    /// openings read them instead of rebuilding every coset's tree.
    pub fn install_transferred_partial_trees(
        &mut self,
        geometry: crate::trace::memory_cap::PartialTreesGeometry,
        trees: DeviceAllocation<Digest>,
    ) {
        assert!(
            matches!(self.trees, TreesHolder::None),
            "install_transferred_partial_trees requires TreesHolder::None"
        );
        assert!(
            !self.cosets_materialized && self.columns_count != 0,
            "install_transferred_partial_trees requires an unmaterialized, non-empty oracle"
        );
        assert_eq!(
            geometry,
            crate::trace::memory_cap::PartialTreesGeometry::of_holder(self),
            "transferred partial trees differ from this oracle's geometry"
        );
        assert_eq!(
            trees.len(),
            geometry.cosets_count() * geometry.coset_stride()
        );
        self.trees = TreesHolder::Partial(trees);
    }

    #[doc(hidden)]
    pub fn get_hypercube_evals(&self) -> &DeviceSlice<T> {
        let len = self.columns_count << self.log_domain_size;
        &self.padded_hypercube_evals()[..len]
    }

    /// Complete raw backing, including the zeroed columns used by packed readers.
    pub fn padded_hypercube_evals(&self) -> &DeviceSlice<T> {
        self.raw_hypercube_evals
            .as_ref()
            .expect("raw hypercube values are unavailable for this holder")
    }

    pub fn get_uninit_hypercube_evals_mut(&mut self) -> &mut DeviceSlice<T> {
        self.cosets_materialized = false;
        let len = self.columns_count << self.log_domain_size;
        &mut std::sync::Arc::get_mut(
            self.raw_hypercube_evals
                .as_mut()
                .expect("raw hypercube values are unavailable for this holder"),
        )
        .expect("raw hypercube allocation must not be shared while being initialized")[..len]
    }

    pub fn raw_hypercube_backing(&self) -> std::sync::Arc<DeviceAllocation<T>> {
        std::sync::Arc::clone(
            self.raw_hypercube_evals
                .as_ref()
                .expect("raw hypercube values are unavailable for this holder"),
        )
    }

    /// Consumes the raw representation after its last readers have been
    /// enqueued. The returned allocation can be converted to an opening
    /// representation or released when materialized cosets suffice.
    ///
    /// Panics if another owner still holds the backing.
    pub fn take_raw_hypercube_backing(&mut self) -> DeviceAllocation<T> {
        let backing = self
            .raw_hypercube_evals
            .take()
            .expect("raw hypercube values are unavailable for this holder");
        std::sync::Arc::try_unwrap(backing).unwrap_or_else(|_| {
            panic!("raw hypercube backing must be exclusively owned at the opening handoff")
        })
    }

    /// Defer LDE materialization until queries. Requires raw backing and no
    /// materialized cosets; configure before `finish_raw_batching`.
    pub fn defer_materialization_until_queries(&mut self, policy: OpeningStrategy) {
        if self.base_geometry.is_some() && policy == OpeningStrategy::InPlace {
            assert!(
                matches!(self.trees, TreesHolder::None | TreesHolder::Partial(_)),
                "in-place openings require partial or uncached trees"
            );
        }
        if self.base_geometry.is_some() && policy == OpeningStrategy::PerCoset {
            assert!(
                matches!(self.trees, TreesHolder::None | TreesHolder::Partial(_)),
                "geometry-backed PerCoset openings require partial or uncached trees"
            );
        }
        assert!(!self.cosets_materialized);
        assert!(self.raw_hypercube_evals.is_some());
        self.defer_opening = true;
        self.opening_policy = policy;
    }

    pub fn opening_policy(&self) -> OpeningStrategy {
        self.opening_policy
    }

    pub fn are_cosets_materialized(&self) -> bool {
        self.cosets_materialized
    }

    /// Release coset storage after its last readers have been enqueued on exec.
    /// Raw backing, cached trees, and the unified cap are kept.
    /// `ensure_cosets_materialized` can regenerate cosets if raw evaluations or
    /// monomials remain available. A commitment-only holder cannot regenerate them.
    pub fn release_cosets(&mut self) {
        self.cosets = CosetsHolder::None(std::marker::PhantomData);
        self.cosets_materialized = false;
    }

    pub fn mark_cosets_materialized(&mut self) {
        self.cosets_materialized = true;
    }

    #[doc(hidden)]
    pub fn get_coset_evaluations(&self, coset_index: usize) -> &DeviceSlice<T> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        assert!(
            self.cosets_materialized,
            "coset evaluations must be materialized before access"
        );
        match &self.cosets {
            CosetsHolder::Full(backing) => {
                let stride = self.committed_columns_count() << self.commitment_log_domain_size();
                &backing[coset_index * stride..(coset_index + 1) * stride]
            }
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        }
    }

    pub fn get_evaluations(&self) -> &DeviceSlice<T> {
        self.get_coset_evaluations(0)
    }

    /// Returns the single consolidated cosets backing as one device slice in
    /// coset-major order: `backing[coset_index * stride .. (coset_index + 1) * stride]`
    /// is the slice for coset `coset_index`, where `stride = columns_count << log_domain_size`.
    pub fn get_consolidated_cosets(&self) -> &DeviceSlice<T> {
        match &self.cosets {
            CosetsHolder::Full(backing) => backing,
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        }
    }

    /// Returns per-coset segment length in digests for the current trees variant.
    /// `None` if no trees are allocated.
    pub(crate) fn per_coset_tree_len(&self) -> Option<usize> {
        match &self.trees {
            TreesHolder::Full(_) => {
                Some(1usize << (self.commitment_log_domain_size() + 1 - self.log_rows_per_leaf))
            }
            TreesHolder::Partial(_) => {
                let partial_log_domain =
                    self.commitment_log_domain_size() - self.partial_tree_reduction_layers();
                Some(1usize << (partial_log_domain + 1 - self.log_rows_per_leaf))
            }
            TreesHolder::None => None,
        }
    }

    pub fn get_uninit_tree_mut(&mut self, coset_index: usize) -> Option<&mut DeviceSlice<Digest>> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        let per_coset = self.per_coset_tree_len()?;
        match &mut self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => {
                Some(&mut backing[coset_index * per_coset..(coset_index + 1) * per_coset])
            }
            TreesHolder::None => None,
        }
    }

    /// Returns disjoint mutable views of the unmaterialized consolidated
    /// coset storage and tree storage for an external commit scheduler.
    pub fn get_uninit_cosets_and_tree_mut(&mut self) -> (&mut DeviceSlice<T>, &mut TreesHolder) {
        assert!(
            !self.cosets_materialized,
            "cosets are already marked materialized",
        );
        let cosets = match &mut self.cosets {
            CosetsHolder::Full(backing) => &mut backing[..],
            CosetsHolder::None(_) => panic!("cosets storage is not allocated"),
        };
        (cosets, &mut self.trees)
    }

    /// Shared-borrow per-coset tree slice. Returns the subrange of the
    /// consolidated tree backing belonging to `coset_index`, or `None` if
    /// trees aren't allocated.
    pub(crate) fn get_tree_slice(&self, coset_index: usize) -> Option<&DeviceSlice<Digest>> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        let per_coset = self.per_coset_tree_len()?;
        match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => {
                Some(&backing[coset_index * per_coset..(coset_index + 1) * per_coset])
            }
            TreesHolder::None => None,
        }
    }

    /// Returns the single consolidated tree backing as one device slice in
    /// coset-major order. `None` if trees aren't allocated.
    pub fn get_consolidated_tree(&self) -> Option<&DeviceSlice<Digest>> {
        match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => Some(backing),
            TreesHolder::None => None,
        }
    }
}

pub(crate) fn allocate_cosets<T>(
    instances_count: usize,
    log_domain_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    let per_coset_len = columns_count << log_domain_size;
    let total = instances_count * per_coset_len;
    context.alloc(total, AllocationPlacement::Bottom)
}

pub(crate) fn allocate_tree(
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<Digest>> {
    let size = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    context.alloc(size, AllocationPlacement::Bottom)
}

#[doc(hidden)]
pub fn allocate_trees(
    instances_count: usize,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<Digest>> {
    let per_coset_len = 1usize << (log_domain_size + 1 - log_rows_per_leaf);
    let total = instances_count * per_coset_len;
    context.alloc(total, AllocationPlacement::Bottom)
}

pub(crate) fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

impl<T> TraceHolder<T> {
    /// Reads the unified device cap into a host `MerkleTreeCapVarLength`.
    /// Synchronizes the exec stream before returning.
    #[doc(hidden)]
    pub fn read_full_cap_synchronously(
        &self,
        context: &ProverContext,
    ) -> CudaResult<MerkleTreeCapVarLength> {
        let device_cap = self.unified_device_cap();
        let cap_size = device_cap.len();
        debug_assert_eq!(
            cap_size,
            if self.is_empty_base_oracle() {
                0
            } else {
                1usize << self.log_tree_cap_size
            }
        );
        if cap_size == 0 {
            return Ok(MerkleTreeCapVarLength { cap: Vec::new() });
        }
        let stream = context.get_exec_stream();
        let mut host = vec![Digest::default(); cap_size];
        memory_copy_async(host.as_mut_slice(), device_cap, stream)?;
        stream.synchronize()?;
        Ok(MerkleTreeCapVarLength { cap: host })
    }

    /// Reads the unified device cap into per-coset host caps in bit-reversed
    /// coset order. Synchronizes the exec stream before returning.
    #[doc(hidden)]
    pub fn read_per_coset_caps_synchronously(
        &self,
        context: &ProverContext,
    ) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
        let lde_factor = 1usize << self.log_lde_factor;
        let full = self.read_full_cap_synchronously(context)?.cap;
        debug_assert_eq!(full.len() % lde_factor, 0);
        let per_coset = full.len() / lde_factor;
        Ok((0..lde_factor)
            .map(|stage1_pos| MerkleTreeCapVarLength {
                cap: full[stage1_pos * per_coset..(stage1_pos + 1) * per_coset].to_vec(),
            })
            .collect())
    }
}
