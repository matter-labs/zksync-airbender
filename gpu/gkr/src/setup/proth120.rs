use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_hash::keccak256::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};

use crate::upstream::{CpuGKRSetup, MerkleTreeCapVarLength};

pub struct L1WrapSetupHost {
    pub log_rows: u32,
    pub columns_count: usize,
    pub pack_log2: u32,
    pub cfg: PackedCommitConfig,
    raw_hypercube_evals: Arc<StaticPinnedBox<PR>>,
    packed_monomials: Arc<StaticPinnedBox<PR>>,
    retained: Arc<StaticPinnedBox<Digest>>,
    pub(crate) roots: Arc<StaticPinnedBox<Digest>>,
    top_nodes: Arc<StaticPinnedBox<Digest>>,
    cap: Arc<StaticPinnedBox<Digest>>,
}

fn copy_to_pinned<T: Copy>(
    source: &DeviceSlice<T>,
    context: &ProverContext,
) -> CudaResult<StaticPinnedBox<T>> {
    let host = alloc_static_pinned_box_uninit(source.len().max(1))?;
    if source.is_empty() {
        let mut empty = host.into_vec();
        empty.clear();
        return Ok(empty.into_boxed_slice());
    }
    let mut host = host;
    memory_copy_async(&mut host[..], source, context.get_exec_stream())?;
    Ok(host)
}

impl L1WrapSetupHost {
    pub fn precompute(
        setup: &CpuGKRSetup<PR>,
        pack_log2: u32,
        cfg: PackedCommitConfig,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let columns_count = setup.hypercube_evals.len();
        assert!(
            columns_count != 0,
            "L1WrapSetupHost: setup columns must be nonzero"
        );
        let rows = setup.hypercube_evals[0].len();
        assert!(
            rows.is_power_of_two(),
            "L1WrapSetupHost: setup rows must be a power of two"
        );
        let log_rows = rows.trailing_zeros();
        log_rows
            .checked_add(pack_log2)
            .filter(|log| (8..=26).contains(log))
            .expect("L1WrapSetupHost: log_rows + pack_log2 outside 8..=26");
        let len = columns_count
            .checked_mul(rows)
            .expect("L1WrapSetupHost: setup length overflow");
        let mut raw_hypercube_evals = alloc_static_pinned_box_uninit(len)?;
        for (column, destination) in setup
            .hypercube_evals
            .iter()
            .zip(raw_hypercube_evals.chunks_mut(rows))
        {
            assert_eq!(
                column.len(),
                rows,
                "L1WrapSetupHost: setup column length mismatch"
            );
            destination.copy_from_slice(column.as_ref());
        }
        let mut raw = TraceHolder::new_without_cosets(
            log_rows,
            cfg.log_lde_factor,
            cfg.log_values_per_leaf,
            cfg.cap_log,
            columns_count,
            TreesCacheMode::CacheNone,
            context,
        )?;
        memory_copy_async(
            raw.get_uninit_hypercube_evals_mut(),
            &raw_hypercube_evals[..],
            context.get_exec_stream(),
        )?;
        let mut oracle = PackedCosetRecomputeOracle::pack_from_columns(raw, pack_log2, context)?;
        oracle.commit(&cfg, context)?;
        let packed_monomials = copy_to_pinned(oracle.monomials(), context)?;
        let retained = copy_to_pinned(oracle.uninit_retained_mut(), context)?;
        let roots = copy_to_pinned(oracle.uninit_roots_mut(), context)?;
        let top_nodes = copy_to_pinned(oracle.uninit_top_nodes_mut(), context)?;
        let cap = copy_to_pinned(oracle.cap_digests(), context)?;
        context.get_exec_stream().synchronize()?;
        Ok(Self {
            log_rows,
            columns_count,
            pack_log2,
            cfg,
            raw_hypercube_evals: Arc::new(raw_hypercube_evals),
            packed_monomials: Arc::new(packed_monomials),
            retained: Arc::new(retained),
            roots: Arc::new(roots),
            top_nodes: Arc::new(top_nodes),
            cap: Arc::new(cap),
        })
    }

    pub fn cap(&self) -> MerkleTreeCapVarLength {
        MerkleTreeCapVarLength {
            cap: self.cap.to_vec(),
        }
    }
}

/// The job keeps `Arc<L1WrapSetupHost>` and the `Transfer` callbacks alive until `finish()`.
pub struct PackedSetupSource<'a> {
    pub host: Arc<L1WrapSetupHost>,
    oracle: PackedCosetRecomputeOracle<PR>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> PackedSetupSource<'a> {
    pub fn new(host: Arc<L1WrapSetupHost>, context: &ProverContext) -> CudaResult<Self> {
        let raw = TraceHolder::new_without_cosets(
            host.log_rows,
            host.cfg.log_lde_factor,
            host.cfg.log_values_per_leaf,
            host.cfg.cap_log,
            host.columns_count,
            TreesCacheMode::CacheNone,
            context,
        )?;
        let oracle =
            PackedCosetRecomputeOracle::from_uploaded(raw, host.pack_log2, host.cfg, context)?;
        Ok(Self {
            host,
            oracle,
            _marker: PhantomData,
        })
    }

    /// The caller records allocation before transfer, records transfer completion, and joins before consumption or drop.
    pub fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.ensure_allocated(context)?;
        let stream = context.get_h2d_stream();
        memory_copy_async(
            self.oracle.raw_mut().get_uninit_hypercube_evals_mut(),
            &self.host.raw_hypercube_evals[..],
            stream,
        )?;
        memory_copy_async(
            self.oracle.uninit_monomials_mut(),
            &self.host.packed_monomials[..],
            stream,
        )?;
        memory_copy_async(
            self.oracle.uninit_retained_mut(),
            &self.host.retained[..],
            stream,
        )?;
        memory_copy_async(self.oracle.uninit_roots_mut(), &self.host.roots[..], stream)?;
        if !self.host.top_nodes.is_empty() {
            memory_copy_async(
                self.oracle.uninit_top_nodes_mut(),
                &self.host.top_nodes[..],
                stream,
            )?;
        }
        memory_copy_async(self.oracle.uninit_cap_mut(), &self.host.cap[..], stream)?;
        Ok(())
    }

    pub fn recompute_coset(
        &self,
        coset: u32,
        dst: &mut DeviceSlice<PR>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.oracle.recompute_coset(coset, dst, context)
    }

    pub fn open_queries(
        &self,
        queries: &DeviceSlice<u32>,
        leaves: &mut DeviceSlice<PR>,
        paths: &mut DeviceSlice<Digest>,
        tree_indexes: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.oracle
            .open_queries(queries, leaves, paths, tree_indexes, context)
    }

    pub fn cap(&self) -> &DeviceSlice<u32> {
        self.oracle.cap()
    }
    pub fn raw(&self) -> &TraceHolder<PR> {
        self.oracle.raw()
    }
    pub fn release_raw(&mut self) {
        self.oracle.release_raw();
    }
    pub fn release_commitment_state(&mut self) {
        self.oracle.release_commitment_state();
    }
    pub fn oracle(&self) -> &PackedCosetRecomputeOracle<PR> {
        &self.oracle
    }
}
