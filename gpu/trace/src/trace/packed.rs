use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_hash::keccak256::{
    append_top_paths, build_top_tree, gather_tree_cap, launch_coset_query_plan,
    retained_layer_offset, Digest,
};
use gpu_ntt::proth120::{
    dispatch, hypercube_evals_to_monomials_chunked, pack_hypercubes_to_monomials, SuffixShape,
    TwiddleDescriptor,
};
use gpu_prover_context::ProverContext;

use crate::upstream::ProverConfig;

use super::holder::{
    assert_partial_tree_reduction_layers, TraceHolder, MAX_PARTIAL_TREE_REDUCTION_LAYERS,
};
use super::sink::{
    commit_coset, commit_coset_scratch_lens, has_leaf_sink, has_open_sink, open_coset_slot,
    open_coset_slot_scratch_lens, OpenQueries, OpenSlot, SinkMode,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedCommitConfig {
    pub log_lde_factor: u32,
    pub log_values_per_leaf: u32,
    pub cap_log: u32,
    pub skip_bottom: u32,
}

impl PackedCommitConfig {
    pub fn from_prover_config(config: &ProverConfig, requested_skip_bottom: u32) -> Self {
        assert_partial_tree_reduction_layers(requested_skip_bottom);
        assert!(
            config.pack_log2() > 0,
            "PackedCommitConfig requires a packed ProverConfig"
        );
        let log_packed = config
            .trace_len_log2
            .checked_add(config.pack_log2())
            .and_then(|log| u32::try_from(log).ok())
            .expect("PackedCommitConfig: packed domain log overflow");
        assert!(
            config.lde_factor().is_power_of_two(),
            "PackedCommitConfig: lde_factor must be a power of two"
        );
        assert!(
            config.base_oracles_values_per_leaf().is_power_of_two(),
            "PackedCommitConfig: values_per_leaf must be a power of two"
        );
        assert!(
            config.cap_size.is_power_of_two(),
            "PackedCommitConfig: cap_size must be a power of two"
        );
        let log_values_per_leaf = config.base_oracles_values_per_leaf().trailing_zeros();
        let h = log_packed
            .checked_sub(log_values_per_leaf)
            .expect("PackedCommitConfig: values_per_leaf exceeds the packed domain");
        Self {
            log_lde_factor: config.lde_factor().trailing_zeros(),
            log_values_per_leaf,
            cap_log: config.cap_size.trailing_zeros(),
            skip_bottom: h.min(requested_skip_bottom),
        }
    }
}

pub struct PackedCosetRecomputeOracle<T> {
    log_rows: u32,
    pack_log2: u32,
    columns: usize,
    packed_columns: usize,
    raw: Option<TraceHolder<T>>,
    monomials: Option<DeviceAllocation<T>>,
    committed: Option<PackedTreeState>,
}

struct PackedTreeState {
    cfg: PackedCommitConfig,
    data: Option<PackedTreeData>,
    cap: DeviceAllocation<Digest>,
}

struct PackedTreeData {
    retained: DeviceAllocation<Digest>,
    roots: DeviceAllocation<Digest>,
    top_nodes: DeviceAllocation<Digest>,
}

fn pow2(log: u32) -> usize {
    1usize
        .checked_shl(log)
        .expect("PackedCosetRecomputeOracle: shift overflow")
}

fn product(a: usize, b: usize) -> usize {
    a.checked_mul(b)
        .expect("PackedCosetRecomputeOracle: length overflow")
}

fn assert_disjoint<A, B>(left: &DeviceSlice<A>, right: &DeviceSlice<B>, message: &str) {
    let left_start = left.as_ptr() as usize;
    let right_start = right.as_ptr() as usize;
    let left_end = left_start
        .checked_add(product(left.len(), size_of::<A>()))
        .expect("PackedCosetRecomputeOracle: pointer extent overflow");
    let right_end = right_start
        .checked_add(product(right.len(), size_of::<B>()))
        .expect("PackedCosetRecomputeOracle: pointer extent overflow");
    assert!(
        left_start == left_end
            || right_start == right_end
            || left_end <= right_start
            || right_end <= left_start,
        "PackedCosetRecomputeOracle: {message}"
    );
}

pub fn retained_len(log_leaves: u32, skip_bottom: u32) -> usize {
    assert!(
        skip_bottom <= log_leaves && skip_bottom <= MAX_PARTIAL_TREE_REDUCTION_LAYERS,
        "PackedCosetRecomputeOracle: skip_bottom exceeds min({MAX_PARTIAL_TREE_REDUCTION_LAYERS}, log_leaves)"
    );
    retained_layer_offset(log_leaves, skip_bottom, log_leaves)
        .checked_add(1)
        .expect("PackedCosetRecomputeOracle: retained length overflow")
}

pub fn coset_root_offset(log_leaves: u32, skip_bottom: u32) -> usize {
    retained_len(log_leaves, skip_bottom) - 1
}

// The touched-coset plan of the round-0 queries (`launch_coset_query_plan`), built once per proof
// and shared by the base and the setup openings (same queries and log_lde): openings run one gated
// slot per query, exactly `count` of them active.
pub struct CosetQueryPlan {
    pub touched: DeviceAllocation<u32>,
    pub active: DeviceAllocation<u32>,
    pub count: DeviceAllocation<u32>,
    pub log_lde: u32,
}

impl CosetQueryPlan {
    pub fn new(
        queries: &DeviceSlice<u32>,
        log_lde: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut touched = context.alloc(queries.len(), AllocationPlacement::BestFit)?;
        let mut active = context.alloc(queries.len(), AllocationPlacement::BestFit)?;
        let mut count = context.alloc(1, AllocationPlacement::BestFit)?;
        launch_coset_query_plan(
            queries,
            log_lde,
            &mut touched,
            &mut active,
            &mut count,
            context.get_exec_stream(),
        )?;
        Ok(Self {
            touched,
            active,
            count,
            log_lde,
        })
    }

    pub fn slots(&self) -> usize {
        self.touched.len()
    }
}

pub fn opening_path_len(log_packed: u32, cfg: &PackedCommitConfig) -> usize {
    let h = log_packed
        .checked_sub(cfg.log_values_per_leaf)
        .expect("PackedCosetRecomputeOracle: values_per_leaf exceeds the packed domain");
    h.checked_add(cfg.log_lde_factor)
        .and_then(|depth| depth.checked_sub(cfg.cap_log))
        .expect("PackedCosetRecomputeOracle: invalid opening depth") as usize
}

impl<T> PackedCosetRecomputeOracle<T> {
    pub fn log_rows(&self) -> u32 {
        self.log_rows
    }
    pub fn pack_log2(&self) -> u32 {
        self.pack_log2
    }
    pub fn log_packed(&self) -> u32 {
        self.log_rows + self.pack_log2
    }
    pub fn columns(&self) -> usize {
        self.columns
    }
    pub fn packed_columns(&self) -> usize {
        self.packed_columns
    }
    pub fn config(&self) -> Option<PackedCommitConfig> {
        self.committed.as_ref().map(|state| state.cfg)
    }
    pub fn raw(&self) -> &TraceHolder<T> {
        self.raw
            .as_ref()
            .expect("PackedCosetRecomputeOracle: raw after release_raw")
    }
    pub fn raw_mut(&mut self) -> &mut TraceHolder<T> {
        self.raw
            .as_mut()
            .expect("PackedCosetRecomputeOracle: raw_mut after release_raw")
    }
    pub fn release_raw(&mut self) {
        self.raw = None;
    }
    pub fn monomials(&self) -> &DeviceSlice<T> {
        self.monomials
            .as_ref()
            .expect("PackedCosetRecomputeOracle: monomials after release_commitment_state")
    }
    pub fn cap_digests(&self) -> &DeviceSlice<Digest> {
        &self
            .committed
            .as_ref()
            .expect("PackedCosetRecomputeOracle: cap before commit")
            .cap
    }
    pub fn cap(&self) -> &DeviceSlice<u32> {
        unsafe { self.cap_digests().transmute() }
    }
    pub fn release_commitment_state(&mut self) {
        let state = self
            .committed
            .as_mut()
            .expect("PackedCosetRecomputeOracle: release_commitment_state before commit");
        state.data = None;
        self.monomials = None;
    }
}

impl PackedCosetRecomputeOracle<PR> {
    fn allocate_monomials(
        raw: TraceHolder<PR>,
        pack_log2: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let log_rows = raw.log_domain_size;
        let log_packed = log_rows
            .checked_add(pack_log2)
            .filter(|log| (8..=26).contains(log))
            .expect("PackedCosetRecomputeOracle: log_rows + pack_log2 outside 8..=26");
        let columns = raw.columns_count;
        assert!(
            columns != 0,
            "PackedCosetRecomputeOracle: columns must be nonzero"
        );
        assert_eq!(
            raw.get_hypercube_evals().len(),
            product(columns, pow2(log_rows)),
            "PackedCosetRecomputeOracle: holder/column mismatch"
        );
        let packed_columns = columns.div_ceil(pow2(pack_log2));
        u32::try_from(packed_columns)
            .expect("PackedCosetRecomputeOracle: packed column count exceeds u32");
        let monomials = context.alloc(
            product(packed_columns, pow2(log_packed)),
            AllocationPlacement::Bottom,
        )?;
        Ok(Self {
            log_rows,
            pack_log2,
            columns,
            packed_columns,
            raw: Some(raw),
            monomials: Some(monomials),
            committed: None,
        })
    }

    pub fn pack_from_columns(
        raw: TraceHolder<PR>,
        pack_log2: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut oracle = Self::allocate_monomials(raw, pack_log2, context)?;
        let packed_rows = pow2(oracle.log_packed());
        let raw = oracle.raw.as_ref().unwrap();
        let stream = context.get_exec_stream();
        let mut output = DeviceMatrixMut::new(oracle.monomials.as_mut().unwrap(), packed_rows);
        if (raw.padded_hypercube_evals().len() >> raw.log_domain_size)
            == oracle.packed_columns << pack_log2
        {
            let input = DeviceMatrix::new(raw.padded_hypercube_evals(), packed_rows);
            let _r = scoped_range(Some("ab"), "pack.mobius");
            let l2 = context.get_device_properties().l2_cache_size_bytes;
            hypercube_evals_to_monomials_chunked(&input, &mut output, l2, stream)?;
        } else {
            let input = DeviceMatrix::new(raw.get_hypercube_evals(), pow2(oracle.log_rows));
            pack_hypercubes_to_monomials(&input, &mut output, pack_log2, stream)?;
        }
        Ok(oracle)
    }

    fn allocate_tree(
        &self,
        cfg: PackedCommitConfig,
        context: &ProverContext,
    ) -> CudaResult<PackedTreeState> {
        let log_packed = self.log_packed();
        let log_domain = log_packed
            .checked_add(cfg.log_lde_factor)
            .expect("PackedCosetRecomputeOracle: domain log overflow");
        assert!(
            log_domain <= gpu_ntt::proth120::LOG_MAX_DOMAIN,
            "PackedCosetRecomputeOracle: packed LDE domain exceeds the Proth120 NTT domain"
        );
        assert!(
            cfg.cap_log <= cfg.log_lde_factor,
            "PackedCosetRecomputeOracle: cap_log exceeds log_lde_factor"
        );
        let h = log_packed
            .checked_sub(cfg.log_values_per_leaf)
            .expect("PackedCosetRecomputeOracle: values_per_leaf exceeds the packed domain");
        let per_coset = retained_len(h, cfg.skip_bottom);
        let cosets = pow2(cfg.log_lde_factor);
        let cap_len = pow2(cfg.cap_log);
        let retained = context.alloc(product(cosets, per_coset), AllocationPlacement::Bottom)?;
        let roots = context.alloc(cosets, AllocationPlacement::Bottom)?;
        let top_nodes = context.alloc(cosets - cap_len, AllocationPlacement::Bottom)?;
        let cap = context.alloc(cap_len, AllocationPlacement::BestFit)?;
        Ok(PackedTreeState {
            cfg,
            data: Some(PackedTreeData {
                retained,
                roots,
                top_nodes,
            }),
            cap,
        })
    }

    pub fn from_uploaded(
        raw: TraceHolder<PR>,
        pack_log2: u32,
        cfg: PackedCommitConfig,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut oracle = Self::allocate_monomials(raw, pack_log2, context)?;
        oracle.committed = Some(oracle.allocate_tree(cfg, context)?);
        Ok(oracle)
    }

    pub fn uninit_monomials_mut(&mut self) -> &mut DeviceSlice<PR> {
        self.monomials
            .as_mut()
            .expect("PackedCosetRecomputeOracle: monomials after release_commitment_state")
    }

    fn tree_data_mut(&mut self) -> &mut PackedTreeData {
        self.committed
            .as_mut()
            .expect("PackedCosetRecomputeOracle: tree before commit")
            .data
            .as_mut()
            .expect("PackedCosetRecomputeOracle: tree after release_commitment_state")
    }

    pub fn uninit_retained_mut(&mut self) -> &mut DeviceSlice<Digest> {
        &mut self.tree_data_mut().retained
    }
    pub fn uninit_roots_mut(&mut self) -> &mut DeviceSlice<Digest> {
        &mut self.tree_data_mut().roots
    }
    pub fn uninit_top_nodes_mut(&mut self) -> &mut DeviceSlice<Digest> {
        &mut self.tree_data_mut().top_nodes
    }
    pub fn uninit_cap_mut(&mut self) -> &mut DeviceSlice<Digest> {
        &mut self
            .committed
            .as_mut()
            .expect("PackedCosetRecomputeOracle: cap before commit")
            .cap
    }

    pub fn commit(
        &mut self,
        cfg: &PackedCommitConfig,
        twiddles: TwiddleDescriptor,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.committed.is_none(),
            "PackedCosetRecomputeOracle: already committed"
        );
        let mut state = self.allocate_tree(*cfg, context)?;
        let data = state.data.as_mut().unwrap();
        let h = self.log_packed() - cfg.log_values_per_leaf;
        let per_coset = retained_len(h, cfg.skip_bottom);
        let mut scratch = context.alloc(self.monomials().len(), AllocationPlacement::Top)?;
        let plan = dispatch(
            self.log_packed(),
            self.packed_columns,
            cfg.log_values_per_leaf,
            cfg.skip_bottom,
            context.get_device_properties().l2_cache_size_bytes,
        );
        let shape = SuffixShape::new(
            &plan,
            self.log_packed(),
            cfg.log_values_per_leaf,
            cfg.skip_bottom,
            self.packed_columns as u32,
        );
        assert!(
            shape.skip_bottom >= 8 && has_leaf_sink(&shape, &SinkMode::Commit),
            "PackedCosetRecomputeOracle: commitment requires the wrap sink"
        );
        let (tiles_len, nodes_len, node_scratch_len) = commit_coset_scratch_lens(&plan, &shape);
        let mut tiles = context.alloc(tiles_len, AllocationPlacement::BestFit)?;
        let mut nodes = context.alloc(nodes_len, AllocationPlacement::BestFit)?;
        let mut node_scratch = context.alloc(node_scratch_len, AllocationPlacement::BestFit)?;
        let stream = context.get_exec_stream();
        for k in 0..pow2(cfg.log_lde_factor) {
            let base = product(k, per_coset);
            commit_coset(
                twiddles,
                self.monomials(),
                &plan,
                &shape,
                k as u32,
                self.log_packed() + cfg.log_lde_factor,
                &mut scratch,
                &mut tiles,
                &mut nodes,
                &mut node_scratch,
                &mut data.retained[base..base + per_coset],
                stream,
            )?;
            let physical = if cfg.log_lde_factor == 0 {
                0
            } else {
                k.reverse_bits() >> (usize::BITS - cfg.log_lde_factor)
            };
            let root = base + coset_root_offset(h, cfg.skip_bottom);
            memory_copy_async(
                &mut data.roots[physical..physical + 1],
                &data.retained[root..root + 1],
                stream,
            )?;
        }
        let _r = scoped_range(Some("ab"), "packed.commit.top");
        build_top_tree(&data.roots, cfg.cap_log, &mut data.top_nodes, stream)?;
        gather_tree_cap(
            &data.roots,
            &data.top_nodes,
            cfg.cap_log,
            &mut state.cap,
            stream,
        )?;
        drop(_r);
        drop(node_scratch);
        drop(nodes);
        drop(tiles);
        drop(scratch);
        self.committed = Some(state);
        Ok(())
    }

    pub fn open_queries(
        &self,
        plan: &CosetQueryPlan,
        queries: &DeviceSlice<u32>,
        leaves: &mut DeviceSlice<PR>,
        paths: &mut DeviceSlice<Digest>,
        tree_indexes: &mut DeviceSlice<u32>,
        twiddles: TwiddleDescriptor,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let state = self
            .committed
            .as_ref()
            .expect("PackedCosetRecomputeOracle: open_queries before commit");
        let data = state
            .data
            .as_ref()
            .expect("PackedCosetRecomputeOracle: open_queries after release_commitment_state");
        let cfg = state.cfg;
        let log_packed = self.log_packed();
        let h = log_packed - cfg.log_values_per_leaf;
        let count = queries.len();
        assert!(
            count > 0,
            "PackedCosetRecomputeOracle: wrap openings require queries"
        );
        assert_eq!(
            leaves.len(),
            product(
                product(count, pow2(cfg.log_values_per_leaf)),
                self.packed_columns
            ),
            "PackedCosetRecomputeOracle: leaves.len() == Q * 2^log_values_per_leaf * packed_columns"
        );
        assert_eq!(
            paths.len(),
            product(count, opening_path_len(log_packed, &cfg)),
            "PackedCosetRecomputeOracle: paths.len() == Q * D"
        );
        assert_eq!(
            tree_indexes.len(),
            count,
            "PackedCosetRecomputeOracle: tree_indexes.len() == Q"
        );
        assert_disjoint(leaves, paths, "leaves/paths overlap");
        assert_disjoint(leaves, tree_indexes, "leaves/tree_indexes overlap");
        assert_disjoint(paths, tree_indexes, "paths/tree_indexes overlap");

        let per_coset = retained_len(h, cfg.skip_bottom);
        let mut scratch = context.alloc(self.monomials().len(), AllocationPlacement::Top)?;
        let stream = context.get_exec_stream();
        assert_eq!(
            plan.log_lde, cfg.log_lde_factor,
            "PackedCosetRecomputeOracle: query plan LDE differs"
        );
        assert_eq!(
            plan.slots(),
            count,
            "PackedCosetRecomputeOracle: query plan slot count differs"
        );
        let dispatched = dispatch(
            log_packed,
            self.packed_columns,
            cfg.log_values_per_leaf,
            cfg.skip_bottom,
            context.get_device_properties().l2_cache_size_bytes,
        );
        let shape = SuffixShape::new(
            &dispatched,
            log_packed,
            cfg.log_values_per_leaf,
            cfg.skip_bottom,
            self.packed_columns as u32,
        );
        assert!(
            has_open_sink(&shape),
            "PackedCosetRecomputeOracle: wrap openings require the sink"
        );

        let (tiles_len, nodes_len) = open_coset_slot_scratch_lens(&dispatched, &shape);
        let mut tiles = context.alloc(tiles_len, AllocationPlacement::BestFit)?;
        let mut nodes = context.alloc(nodes_len, AllocationPlacement::BestFit)?;
        let mut open = OpenQueries {
            queries,
            log_lde: cfg.log_lde_factor,
            cap_log: cfg.cap_log,
            leaves: &mut *leaves,
            paths: &mut *paths,
        };
        for s in 0..plan.slots() {
            let _r = scoped_range(Some("ab"), "packed.open.slot");
            open_coset_slot(
                twiddles,
                self.monomials(),
                &dispatched,
                &shape,
                OpenSlot {
                    coset: &plan.touched[s..s + 1],
                    active: &plan.active[s..s + 1],
                },
                log_packed + cfg.log_lde_factor,
                &data.retained,
                per_coset,
                &mut open,
                &mut scratch,
                &mut tiles,
                &mut nodes,
                stream,
            )?;
        }
        drop(nodes);
        drop(tiles);

        let _r = scoped_range(Some("ab"), "packed.open.top");
        append_top_paths(
            &data.roots,
            &data.top_nodes,
            cfg.log_lde_factor,
            cfg.cap_log,
            h,
            queries,
            paths,
            tree_indexes,
            stream,
        )?;
        drop(_r);
        drop(scratch);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::holder::{TreesCacheMode, PARTIAL_TREE_REDUCTION_LAYERS};
    use era_cudart::memory::memory_copy_async;
    use field::Field;
    use gpu_prover_context::ProverContextConfig;

    fn holder(
        log_rows: u32,
        columns: usize,
        pad: u32,
        values: &[PR],
        context: &ProverContext,
    ) -> TraceHolder<PR> {
        let mut raw = TraceHolder::new_without_cosets_padded(
            log_rows,
            1,
            0,
            0,
            columns,
            pad,
            TreesCacheMode::CacheNone,
            PARTIAL_TREE_REDUCTION_LAYERS,
            context,
        )
        .unwrap();
        assert_eq!(raw.get_hypercube_evals().len(), columns << log_rows);
        assert_eq!(
            (raw.padded_hypercube_evals().len() >> raw.log_domain_size),
            columns.next_multiple_of(1 << pad)
        );
        memory_copy_async(
            raw.get_uninit_hypercube_evals_mut(),
            values,
            context.get_exec_stream(),
        )
        .unwrap();
        raw
    }

    #[test]
    fn pr_pack_from_padded_columns_matches_gather() {
        let context = ProverContext::new(&ProverContextConfig {
            device_allocation_blocks_count: Some(256),
            host_allocator_blocks_count: 256,
            ..Default::default()
        })
        .unwrap();
        let stream = context.get_exec_stream();
        let mut state = 0x9120_2201_u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (u128::from(state) << 64 | u128::from(state.rotate_left(29))) % PR::ORDER
        };
        for (log_rows, columns, pack_log2) in [(15, 96, 3), (15, 10, 3)] {
            let values: Vec<PR> = (0..columns << log_rows).map(|_| PR::new(next())).collect();
            let padded = PackedCosetRecomputeOracle::pack_from_columns(
                holder(log_rows, columns, pack_log2, &values, &context),
                pack_log2,
                &context,
            )
            .unwrap();
            let gathered = PackedCosetRecomputeOracle::pack_from_columns(
                holder(log_rows, columns, 0, &values, &context),
                pack_log2,
                &context,
            )
            .unwrap();
            let download = |oracle: &PackedCosetRecomputeOracle<PR>| {
                let mut host = vec![PR::ZERO; oracle.monomials().len()];
                memory_copy_async(&mut host, oracle.monomials(), stream).unwrap();
                stream.synchronize().unwrap();
                host
            };
            assert!(
                download(&padded) == download(&gathered),
                "padded pack differs at log_rows {log_rows} columns {columns} pack {pack_log2}"
            );
            let mut raw_back = vec![PR::ZERO; values.len()];
            memory_copy_async(&mut raw_back, padded.raw().get_hypercube_evals(), stream).unwrap();
            stream.synchronize().unwrap();
            assert!(raw_back == values, "raw columns changed by the pack");
        }
    }
}
