use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_hash::keccak256::{
    append_top_paths, build_partial_coset_tree, build_partial_coset_tree_with_scratch,
    build_top_tree, gather_leaves_for_queries_single_coset,
    gather_merkle_paths_partial_for_queries_single_coset, gather_tree_cap,
    partial_coset_tree_scratch_len, retained_layer_offset, Digest,
};
use gpu_ntt::proth120::{
    dispatch, has_reference_finish, lde_coset, lde_coset_slot, lde_finish_reference,
    pack_hypercubes_to_monomials, CosetSource, ScaleArgs,
};
use gpu_ops::powers::get_powers_by_val;
use gpu_prover_context::ProverContext;

use crate::upstream::{domain_generator_for_size, ProverConfig};

use super::holder::{
    assert_partial_tree_reduction_layers, TraceHolder, MAX_PARTIAL_TREE_REDUCTION_LAYERS,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedCommitConfig {
    pub log_lde_factor: u32,
    pub log_values_per_leaf: u32,
    pub cap_log: u32,
    pub skip_bottom: u32,
}

impl PackedCommitConfig {
    pub fn from_prover_config(
        config: &ProverConfig,
        log_packed: u32,
        requested_skip_bottom: u32,
    ) -> Self {
        assert_partial_tree_reduction_layers(requested_skip_bottom);
        assert!(
            config.lde_factor.is_power_of_two(),
            "PackedCommitConfig: lde_factor must be a power of two"
        );
        assert!(
            config.base_oracles_values_per_leaf.is_power_of_two(),
            "PackedCommitConfig: values_per_leaf must be a power of two"
        );
        assert!(
            config.cap_size.is_power_of_two(),
            "PackedCommitConfig: cap_size must be a power of two"
        );
        let log_values_per_leaf = config.base_oracles_values_per_leaf.trailing_zeros();
        let h = log_packed
            .checked_sub(log_values_per_leaf)
            .expect("PackedCommitConfig: values_per_leaf exceeds the packed domain");
        Self {
            log_lde_factor: config.lde_factor.trailing_zeros(),
            log_values_per_leaf,
            cap_log: config.cap_size.trailing_zeros(),
            skip_bottom: h.min(requested_skip_bottom),
        }
    }

    pub fn same_protocol_geometry(&self, other: &Self) -> bool {
        self.log_lde_factor == other.log_lde_factor
            && self.log_values_per_leaf == other.log_values_per_leaf
            && self.cap_log == other.cap_log
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
    offsets: DeviceAllocation<PR>,
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
        let input = DeviceMatrix::new(
            oracle.raw.as_ref().unwrap().get_hypercube_evals(),
            pow2(oracle.log_rows),
        );
        let mut output = DeviceMatrixMut::new(oracle.monomials.as_mut().unwrap(), packed_rows);
        pack_hypercubes_to_monomials(&input, &mut output, pack_log2, context.get_exec_stream())?;
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
            log_domain <= context.proth120_ntt_device_context().log_max_domain(),
            "PackedCosetRecomputeOracle: packed LDE domain exceeds context.log_max_domain()"
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
        let mut offsets = context.alloc(cosets, AllocationPlacement::Bottom)?;
        let root = domain_generator_for_size::<PR>(
            u64::try_from(pow2(log_domain))
                .expect("PackedCosetRecomputeOracle: domain exceeds u64"),
        );
        get_powers_by_val(root, 0, &mut offsets, context.get_exec_stream())?;
        let retained = context.alloc(product(cosets, per_coset), AllocationPlacement::Bottom)?;
        let roots = context.alloc(cosets, AllocationPlacement::Bottom)?;
        let top_nodes = context.alloc(cosets - cap_len, AllocationPlacement::Bottom)?;
        let cap = context.alloc(cap_len, AllocationPlacement::BestFit)?;
        Ok(PackedTreeState {
            cfg,
            data: Some(PackedTreeData {
                offsets,
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

    #[allow(clippy::too_many_arguments)]
    fn recompute_into(
        monomials: &DeviceSlice<PR>,
        offsets: &DeviceSlice<PR>,
        log_packed: u32,
        packed_columns: usize,
        cfg: &PackedCommitConfig,
        coset: u32,
        dst: &mut DeviceSlice<PR>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            (coset as usize) < offsets.len(),
            "PackedCosetRecomputeOracle: coset out of bounds"
        );
        let rows = pow2(log_packed);
        let len = product(packed_columns, rows);
        assert_eq!(
            monomials.len(),
            len,
            "PackedCosetRecomputeOracle: monomial length mismatch"
        );
        assert_eq!(
            dst.len(),
            len,
            "PackedCosetRecomputeOracle: recompute_coset destination length mismatch"
        );
        let ctx = context.proth120_ntt_device_context();
        let stream = context.get_exec_stream();
        let plan = dispatch(
            log_packed,
            packed_columns,
            cfg.log_values_per_leaf,
            cfg.skip_bottom,
        )
        .and_then(|shape| shape.prefix)
        .filter(has_reference_finish);
        if let Some(plan) = plan {
            let scale = ScaleArgs {
                coset: CosetSource::Constant(coset),
                log_domain: log_packed + cfg.log_lde_factor,
            };
            lde_coset_slot(ctx, monomials, dst, packed_columns, &plan, scale, stream)?;
            return lde_finish_reference(ctx, dst, packed_columns, &plan, stream);
        }
        let input = DeviceMatrix::new(monomials, rows);
        let mut output = DeviceMatrixMut::new(dst, rows);
        lde_coset(
            ctx,
            &input,
            &mut output,
            &offsets[coset as usize..coset as usize + 1],
            stream,
        )
    }

    pub fn recompute_coset(
        &self,
        coset: u32,
        dst: &mut DeviceSlice<PR>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let state = self
            .committed
            .as_ref()
            .expect("PackedCosetRecomputeOracle: recompute_coset before commit");
        let data = state
            .data
            .as_ref()
            .expect("PackedCosetRecomputeOracle: recompute_coset after release_commitment_state");
        Self::recompute_into(
            self.monomials(),
            &data.offsets,
            self.log_packed(),
            self.packed_columns,
            &state.cfg,
            coset,
            dst,
            context,
        )
    }

    pub fn commit(&mut self, cfg: &PackedCommitConfig, context: &ProverContext) -> CudaResult<()> {
        assert!(
            self.committed.is_none(),
            "PackedCosetRecomputeOracle: already committed"
        );
        let mut state = self.allocate_tree(*cfg, context)?;
        let data = state.data.as_mut().unwrap();
        let h = self.log_packed() - cfg.log_values_per_leaf;
        let per_coset = retained_len(h, cfg.skip_bottom);
        let mut scratch = context.alloc(self.monomials().len(), AllocationPlacement::Top)?;
        let tree_scratch_len = partial_coset_tree_scratch_len(
            self.log_packed(),
            cfg.log_values_per_leaf,
            cfg.skip_bottom,
        );
        let mut tree_scratch: Option<DeviceAllocation<Digest>> = if tree_scratch_len == 0 {
            None
        } else {
            Some(context.alloc(tree_scratch_len, AllocationPlacement::BestFit)?)
        };
        let stream = context.get_exec_stream();
        for k in 0..data.offsets.len() {
            {
                let _r = scoped_range(Some("ab"), "packed.commit.prefix");
                Self::recompute_into(
                    self.monomials(),
                    &data.offsets,
                    self.log_packed(),
                    self.packed_columns,
                    cfg,
                    k as u32,
                    &mut scratch,
                    context,
                )?;
            }
            let _r = scoped_range(Some("ab"), "packed.commit.suffix");
            let base = product(k, per_coset);
            let retained = &mut data.retained[base..base + per_coset];
            match tree_scratch.as_mut() {
                None => build_partial_coset_tree(
                    &scratch,
                    self.log_packed(),
                    cfg.log_values_per_leaf,
                    self.packed_columns as u32,
                    cfg.skip_bottom,
                    retained,
                    stream,
                )?,
                Some(tree_scratch) => build_partial_coset_tree_with_scratch(
                    &scratch,
                    self.log_packed(),
                    cfg.log_values_per_leaf,
                    self.packed_columns as u32,
                    cfg.skip_bottom,
                    retained,
                    tree_scratch,
                    stream,
                )?,
            }
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
        drop(tree_scratch);
        drop(scratch);
        self.committed = Some(state);
        Ok(())
    }

    pub fn open_queries(
        &self,
        queries: &DeviceSlice<u32>,
        leaves: &mut DeviceSlice<PR>,
        paths: &mut DeviceSlice<Digest>,
        tree_indexes: &mut DeviceSlice<u32>,
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
        if count == 0 {
            return Ok(());
        }
        let per_coset = retained_len(h, cfg.skip_bottom);
        let mut scratch = context.alloc(self.monomials().len(), AllocationPlacement::Top)?;
        let stream = context.get_exec_stream();
        for k in 0..data.offsets.len() {
            let _r = scoped_range(Some("ab"), "packed.open.slot");
            self.recompute_coset(k as u32, &mut scratch, context)?;
            gather_leaves_for_queries_single_coset(
                &scratch,
                k as u32,
                cfg.log_lde_factor,
                log_packed,
                cfg.log_values_per_leaf,
                queries,
                leaves,
                stream,
            )?;
            let base = product(k, per_coset);
            gather_merkle_paths_partial_for_queries_single_coset(
                &scratch,
                k as u32,
                cfg.log_lde_factor,
                log_packed,
                cfg.log_values_per_leaf,
                cfg.cap_log,
                cfg.skip_bottom,
                &data.retained[base..base + per_coset],
                queries,
                paths,
                stream,
            )?;
        }
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
mod cpu_tests {
    use super::*;
    use field::Field;
    use std::alloc::Global;

    #[test]
    fn cpu_packed_layout_formulas() {
        let wrap = PackedCommitConfig {
            log_lde_factor: 7,
            log_values_per_leaf: 1,
            cap_log: 3,
            skip_bottom: 10,
        };
        assert_eq!(opening_path_len(24, &wrap), 27);
        assert_eq!(retained_len(23, 10), 2 * ((1usize << 23) >> 10) - 1);
        for (log_packed, h) in [(26, 24), (16, 14)] {
            let cfg = PackedCommitConfig {
                log_lde_factor: 5,
                log_values_per_leaf: 2,
                cap_log: 3,
                skip_bottom: 5,
            };
            assert_eq!(retained_len(h, 5), 2 * ((1usize << h) >> 5) - 1);
            assert_eq!(coset_root_offset(h, 5), retained_len(h, 5) - 1);
            assert_eq!(opening_path_len(log_packed, &cfg), (h + 2) as usize);
            for q in [0u32, 31, 32, (1 << (h + 5)) - 1] {
                let k = q & 31;
                let j = q >> 5;
                let tree_index = (k.reverse_bits() >> 27) as usize * pow2(h) + j as usize;
                assert_eq!(
                    tree_index,
                    fft::bitreverse_index(k as usize, 5) * pow2(h) + j as usize
                );
            }
        }
        assert_eq!(retained_len(4, 4), 1);
        assert_eq!(coset_root_offset(4, 4), 0);
        assert_eq!(retained_len(4, 0), 31);
    }

    #[test]
    fn cpu_coset_offsets_match_cpu_formula() {
        for log_domain in [21, 31] {
            let root = domain_generator_for_size::<PR>(pow2(log_domain) as u64);
            let host_root =
                fft::domain_generator_for_size::<field::Proth120>(pow2(log_domain) as u64);
            assert_eq!(root.0, host_root.0);
            let expected = fft::materialize_powers_serial_starting_with_one::<PR, Global>(root, 32);
            for (k, offset) in expected.iter().enumerate() {
                assert_eq!(root.pow(k as u32).0, offset.0);
            }
            let mut order_check = root;
            order_check.exp_power_of_2(log_domain as usize);
            assert_eq!(order_check, PR::ONE);
            let mut half_order = root;
            half_order.exp_power_of_2(log_domain as usize - 1);
            assert_ne!(half_order, PR::ONE);
        }
    }
}
