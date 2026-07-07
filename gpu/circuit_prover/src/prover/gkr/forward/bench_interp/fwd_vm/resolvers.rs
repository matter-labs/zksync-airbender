//! Task 2 (G-CPU, spec §7): the host-side bridge from real GPU prover data
//! (`CircuitFixture`) to the CPU fwd-VM interpreter. D2H copies every column,
//! mapping array, and setup table a compiled layer reads, then implements the
//! four dag_ir resolver traits + `PeekResolver` over those host copies so
//! `interpret_layer_row_with_peeks` runs on real data — the first-ever run of
//! the fwd VM on prover data. Semantics-only: a mismatch vs the flat-produced
//! storage columns is a lowering/challenge/peek bug, not a kernel bug (later
//! tasks reuse `read_place_to_gkr_address` / `HostSnapshot` / `flat_root_value`).
//!
//! Bench/test host code: D2H copies synchronize immediately (blocking is fine
//! here — this is NOT production scheduling code).

use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use field::{Field, FieldExtension, PrimeField};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{
    Bf, ChallengeKey, ChallengePower, ChallengeRef, ChallengeResolver, DagLayer, Ext,
    LookupResolver, LookupValueKind, PermutationSlot, RangeWidth, ReadPlace, ReadResolver,
    Resolvers, RootId, SinkKind, SourceKind, VirtualSetupKind, VirtualSetupResolver,
};
use gkr_eval_isa::fwd::context::{CompiledLayer, ForwardAction, RootOutput};
use gkr_eval_isa::fwd::peek::{validate_special_bindings, PeekError, PeekResolver};
use gkr_eval_isa::fwd::source::{SpecialDescriptor, SpecialStrategy};

use super::super::fixture::{CircuitFixture, CircuitKeepalive};
use super::compile::{read_place_to_gkr_address, FwdVmCircuit};
use crate::prover::gkr::stage1::GpuGKRStage1Output;
use crate::prover::ProverContext;

// ── field helpers ─────────────────────────────────────────────────────────────

#[inline]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

/// `base^power` per the DAG-IR convention (`One` = power 1, `Static(p)` = power
/// p, so `Static(0)` = 1). `alpha^j`, `rho^p`, etc. resolve through this.
fn pow_of(base: Ext, power: &ChallengePower) -> Ext {
    let p = match power {
        ChallengePower::One => 1u32,
        ChallengePower::Static(p) => *p,
    };
    base.pow(p)
}

/// Map a `PermutationSlot` to its linearization-challenge index
/// (`cs/src/definitions/constants.rs:15-20` `PERMUTATION_ARGUMENT_CHALLENGE_POWERS_*_IDX`,
/// matching `lower.rs`'s ADDR_LOW..VAL_HIGH = 0..5 convention).
fn perm_role(slot: &PermutationSlot) -> usize {
    match slot {
        PermutationSlot::AddressLow => 0,
        PermutationSlot::AddressHigh => 1,
        PermutationSlot::TimestampLow => 2,
        PermutationSlot::TimestampHigh => 3,
        PermutationSlot::ValueLow => 4,
        PermutationSlot::ValueHigh => 5,
    }
}

/// Per-row value of a virtual-setup base column, byte-for-byte the device
/// `gkr_virtual_base_value` switch (== `materialize_virtual_setup_column`'s
/// per-row body, `fixture.rs:1195`).
fn virtual_setup_value(kind: &VirtualSetupKind, row: usize) -> Bf {
    let row = row as u32;
    let ts_bits: u32 = crate::upstream::TIMESTAMP_COLUMNS_NUM_BITS;
    let v = match kind {
        VirtualSetupKind::RangeCheck16Bits => {
            if row < (1u32 << 16) {
                row
            } else {
                0
            }
        }
        VirtualSetupKind::RangeCheckTimestamp => {
            if row < (1u32 << ts_bits) {
                row
            } else {
                0
            }
        }
        VirtualSetupKind::InitsAndTeardownsLow => (row << 2) & 0xffff,
        VirtualSetupKind::InitsAndTeardownsHigh => row >> 14,
    };
    Bf::from_u32_with_reduction(v)
}

// ── D2H helpers (bench-simple: copy + synchronize) ────────────────────────────

fn d2h_bf(ptr: *const u8, t: usize, ctx: &ProverContext) -> Vec<Bf> {
    let mut host = vec![Bf::ZERO; t];
    // SAFETY: `ptr` is a resident bf column of >= t elements (a storage poly);
    // the read is stream-ordered and synchronized before the host slice is read.
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr as *const Bf, t) };
    memory_copy_async(&mut host, slice, ctx.get_exec_stream()).unwrap();
    ctx.get_exec_stream().synchronize().unwrap();
    host
}

fn d2h_ext(ptr: *const u8, t: usize, ctx: &ProverContext) -> Vec<Ext> {
    let mut host = vec![Ext::ZERO; t];
    // SAFETY: `ptr` is a resident e4 column of >= t elements; stream-ordered.
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr as *const Ext, t) };
    memory_copy_async(&mut host, slice, ctx.get_exec_stream()).unwrap();
    ctx.get_exec_stream().synchronize().unwrap();
    host
}

fn d2h_u32(slice: &DeviceSlice<u32>, ctx: &ProverContext) -> Vec<u32> {
    let n = slice.len();
    let mut host = vec![0u32; n];
    memory_copy_async(&mut host, &slice[0..n], ctx.get_exec_stream()).unwrap();
    ctx.get_exec_stream().synchronize().unwrap();
    host
}

pub(crate) fn fixture_stage1(fixture: &CircuitFixture) -> &GpuGKRStage1Output {
    match &fixture.keepalive {
        CircuitKeepalive::Unrolled { stage1, .. } => stage1,
        CircuitKeepalive::Delegation(keepalive) => &keepalive.stage1,
    }
}

// ── SinkKind → GKRAddress (flat destination of a materialized root) ────────────

fn sink_to_addr(kind: &SinkKind) -> GKRAddress {
    match *kind {
        SinkKind::Inner { layer, offset } => GKRAddress::InnerLayer { layer, offset },
        SinkKind::Cache { layer, offset } => GKRAddress::Cached { layer, offset },
        SinkKind::Scratch { slot } => GKRAddress::ScratchSpace(slot),
        SinkKind::Export { slot } => panic!(
            "sink_to_addr: Export sink (slot {slot}) has no GKRAddress; not produced by these \
             circuits' lowering"
        ),
    }
}

/// The flat-storage destination address of a non-skipped root: a `CopyAlias`
/// action's `dst_addr`, else the root's `materialize` sink.
pub(crate) fn root_flat_addr(layer: &DagLayer, cl: &CompiledLayer, rid: RootId) -> GKRAddress {
    if let Some(ForwardAction::CopyAlias { dst_addr, .. }) = cl.ctx.actions.get(&rid) {
        return *dst_addr;
    }
    let sink = layer.roots[rid.0 as usize]
        .materialize
        .as_ref()
        .unwrap_or_else(|| panic!("root_flat_addr: root {rid:?} has no materialize sink"));
    sink_to_addr(&sink.kind)
}

// ── HostSnapshot ──────────────────────────────────────────────────────────────

/// A D2H'd column: base (`Bf`) or extension (`Ext`) elements, `trace_len` long.
pub(crate) enum HostColumn {
    Base(Vec<Bf>),
    Ext(Vec<Ext>),
}

/// Per-(circuit,layer) host copies of every value a compiled layer reads or
/// writes, plus the special peek arrays. The explicit capture-set union
/// (codex plan-F5): (a) every read column; (b) special arrays (mapping / setup
/// table / decoder predicate / fill); (c) the flat root DESTINATION column of
/// every non-skipped root (incl. Smem-rooted — the G-CPU golden); (d) alias
/// source AND destination columns. Resolvers must never touch a column outside
/// this set (they panic if they do).
pub(crate) struct HostSnapshot {
    pub(crate) columns: BTreeMap<GKRAddress, HostColumn>,
    /// `preprocessed_generic_lookup` — the `VectorizedLookupSetup` cache out,
    /// E4 (`setup/mod.rs:398-404`: `generic_lookup: Option<DeviceAllocation<E>>`).
    pub(crate) generic_lookup: Vec<Ext>,
    pub(crate) generic_lookup_len: usize,
    /// Per-set index columns (u32), keyed by `set_index`.
    range_check_mappings: BTreeMap<usize, Vec<u32>>,
    timestamp_mappings: BTreeMap<usize, Vec<u32>>,
    generic_mappings: BTreeMap<usize, Vec<u32>>,
    decoder_mapping: Option<Vec<u32>>,
    /// Decoder execute-predicate address (its column lives in `columns`).
    decoder_pred_addr: Option<GKRAddress>,
    /// `device_decoder_lookup_fill_value` host value (E4; via `bench_challenges`).
    decoder_fill: Ext,
    pub(crate) trace_len: usize,
}

fn capture_column(
    columns: &mut BTreeMap<GKRAddress, HostColumn>,
    fixture: &CircuitFixture,
    addr: GKRAddress,
) {
    if columns.contains_key(&addr) {
        return;
    }
    let (is_e4, ptr) = fixture.storage_column(addr).unwrap_or_else(|| {
        panic!("HostSnapshot capture: address {addr:?} not resident in post-capture storage")
    });
    let t = fixture.trace_len;
    let ctx = fixture.context();
    let col = if is_e4 {
        HostColumn::Ext(d2h_ext(ptr, t, ctx))
    } else {
        HostColumn::Base(d2h_bf(ptr, t, ctx))
    };
    columns.insert(addr, col);
}

impl HostSnapshot {
    /// Build the per-layer snapshot (spec §6.1). D2H is synchronous.
    pub(crate) fn capture_for_layer(
        fixture: &CircuitFixture,
        cl: &CompiledLayer,
        layer: &DagLayer,
    ) -> HostSnapshot {
        let mut snap = HostSnapshot {
            columns: BTreeMap::new(),
            generic_lookup: Vec::new(),
            generic_lookup_len: 0,
            range_check_mappings: BTreeMap::new(),
            timestamp_mappings: BTreeMap::new(),
            generic_mappings: BTreeMap::new(),
            decoder_mapping: None,
            decoder_pred_addr: None,
            decoder_fill: Ext::ZERO,
            trace_len: fixture.trace_len,
        };

        // (a) every read column the layer's sources reference. VirtualSetup
        //     sources have no resident buffer (materialized per row), so they are
        //     not captured here.
        for src in &layer.sources {
            if let SourceKind::Read { place } = &src.kind {
                let addr = read_place_to_gkr_address(place, &fixture.compiled_circuit);
                capture_column(&mut snap.columns, fixture, addr);
            }
        }

        // (c) flat root DESTINATION column for every non-skipped root, and
        // (d) alias source + destination columns.
        for (rid, _out) in &cl.root_outputs {
            let addr = root_flat_addr(layer, cl, *rid);
            capture_column(&mut snap.columns, fixture, addr);
            if let Some(ForwardAction::CopyAlias { src_addr, dst_addr }) = cl.ctx.actions.get(rid) {
                capture_column(&mut snap.columns, fixture, *src_addr);
                capture_column(&mut snap.columns, fixture, *dst_addr);
            }
        }

        // (b) special peek arrays — only what the compiled descriptors reference.
        if cl.ctx.specials.len() > 0 {
            let stage1 = fixture_stage1(fixture);
            let ctx = fixture.context();
            for d in cl.ctx.specials.iter() {
                match &d.strategy {
                    SpecialStrategy::PeekSingleColumn { set_index, width } => match width {
                        RangeWidth::Bits16 => {
                            snap.range_check_mappings.entry(*set_index).or_insert_with(|| {
                                d2h_u32(stage1.lookup_mappings.range_check_mapping(*set_index), ctx)
                            });
                        }
                        RangeWidth::Timestamp => {
                            snap.timestamp_mappings.entry(*set_index).or_insert_with(|| {
                                d2h_u32(stage1.lookup_mappings.timestamp_mapping(*set_index), ctx)
                            });
                        }
                    },
                    SpecialStrategy::PeekAggregate { set_index } => {
                        snap.generic_mappings.entry(*set_index).or_insert_with(|| {
                            d2h_u32(stage1.lookup_mappings.generic_mapping(*set_index), ctx)
                        });
                        snap.ensure_generic_lookup(fixture);
                    }
                    SpecialStrategy::PeekSetup => {
                        snap.ensure_generic_lookup(fixture);
                    }
                    SpecialStrategy::PeekDecoder { predicate, .. } => {
                        if snap.decoder_mapping.is_none() {
                            let m = stage1.lookup_mappings.decoder_mapping().unwrap_or_else(|| {
                                panic!("PeekDecoder present but stage1 has no decoder mapping")
                            });
                            snap.decoder_mapping = Some(d2h_u32(m, ctx));
                        }
                        snap.ensure_generic_lookup(fixture);
                        let pred_addr =
                            read_place_to_gkr_address(predicate, &fixture.compiled_circuit);
                        capture_column(&mut snap.columns, fixture, pred_addr);
                        snap.decoder_pred_addr = Some(pred_addr);
                        snap.decoder_fill = fixture.bench_challenges().decoder_fill;
                    }
                    // VirtualSetup is resolver-computed (`virtual_setup_value`) — it
                    // reads nothing, so there is no peek array to D2H-capture.
                    SpecialStrategy::VirtualSetup { .. } => {}
                }
            }
        }

        snap
    }

    fn ensure_generic_lookup(&mut self, fixture: &CircuitFixture) {
        if self.generic_lookup_len == 0 && self.generic_lookup.is_empty() {
            let (ptr, len) = fixture.setup_table();
            self.generic_lookup = d2h_ext(ptr, len as usize, fixture.context());
            self.generic_lookup_len = len as usize;
        }
    }

    /// Value of captured column `addr` at `row`, lifted to `Ext`.
    pub(crate) fn column_value(&self, addr: GKRAddress, row: usize) -> Ext {
        match self.columns.get(&addr) {
            Some(HostColumn::Base(v)) => lift(v[row]),
            Some(HostColumn::Ext(v)) => v[row],
            None => panic!("HostSnapshot: value requested for uncaptured column {addr:?}"),
        }
    }

    fn range_check_mapping(&self, set_index: usize) -> &[u32] {
        self.range_check_mappings
            .get(&set_index)
            .unwrap_or_else(|| panic!("HostSnapshot: range-check mapping set {set_index} not captured"))
    }

    fn timestamp_mapping(&self, set_index: usize) -> &[u32] {
        self.timestamp_mappings
            .get(&set_index)
            .unwrap_or_else(|| panic!("HostSnapshot: timestamp mapping set {set_index} not captured"))
    }

    fn generic_mapping(&self, set_index: usize) -> &[u32] {
        self.generic_mappings
            .get(&set_index)
            .unwrap_or_else(|| panic!("HostSnapshot: generic mapping set {set_index} not captured"))
    }

    fn decoder_mapping(&self) -> &[u32] {
        self.decoder_mapping
            .as_deref()
            .unwrap_or_else(|| panic!("HostSnapshot: decoder mapping not captured"))
    }

    fn generic_lookup_at(&self, index: usize) -> Ext {
        *self
            .generic_lookup
            .get(index)
            .unwrap_or_else(|| panic!("HostSnapshot: generic_lookup index {index} out of range"))
    }

    /// The flat golden for `rid` at `row`: the resident storage column at the
    /// root's materialized `GKRAddress` (alias roots resolve through the aliased
    /// destination). This is the G-CPU golden the VM output is compared against.
    pub(crate) fn flat_root_value(
        &self,
        _fixture: &CircuitFixture,
        c: &FwdVmCircuit,
        li: usize,
        rid: RootId,
        _out: &RootOutput,
        row: usize,
    ) -> Ext {
        let layer = &c.dag.layers[li];
        let cl = &c.compiled.layers[li];
        let addr = root_flat_addr(layer, cl, rid);
        self.column_value(addr, row)
    }
}

// ── HostStorageResolvers ──────────────────────────────────────────────────────

/// The four dag_ir resolver traits + `PeekResolver`, backed by a `HostSnapshot`
/// (reads/peeks) and the fixture's captured challenges.
pub(crate) struct HostStorageResolvers<'a> {
    snap: &'a HostSnapshot,
    fixture: &'a CircuitFixture,
}

impl<'a> HostStorageResolvers<'a> {
    pub(crate) fn new(snap: &'a HostSnapshot, fixture: &'a CircuitFixture) -> Self {
        Self { snap, fixture }
    }

    /// Bundle `&self` as all four resolver trait objects for the interpreter.
    pub(crate) fn resolvers(&self) -> Resolvers<'_> {
        Resolvers {
            read: self,
            lookup: self,
            virtual_setup: self,
            challenge: self,
        }
    }
}

impl ReadResolver for HostStorageResolvers<'_> {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        let addr = read_place_to_gkr_address(place, &self.fixture.compiled_circuit);
        self.snap.column_value(addr, row)
    }
}

impl LookupResolver for HostStorageResolvers<'_> {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        _evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        // Only the SP1 Fold path / `eval_layer_root` oracle call this; the G-CPU
        // gate runs `interpret_layer_row_with_peeks` (SP2) and the SP2 validator
        // uses its own IdentityLookupResolver, so this is inert here. Implemented
        // for the base-field range/timestamp legs; E4-valued legs panic loudly.
        match kind {
            LookupValueKind::RangeCheck16Index => {
                Bf::from_u32_with_reduction(self.snap.range_check_mapping(set_index)[row])
            }
            LookupValueKind::TimestampIndex => {
                Bf::from_u32_with_reduction(self.snap.timestamp_mapping(set_index)[row])
            }
            LookupValueKind::GenericColumn { .. } | LookupValueKind::DecoderColumn { .. } => {
                panic!(
                    "HostStorageResolvers::lookup: E4-valued lookup leg reached the base-field \
                     resolver (kind {kind:?}); unexpected for the G-CPU gate"
                )
            }
        }
    }
}

impl VirtualSetupResolver for HostStorageResolvers<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        virtual_setup_value(kind, row)
    }
}

/// The SAME `ChallengeRef` -> concrete `Ext` mapping the G-CPU gate (Task 2)
/// uses, factored out so Task 3's device challenge-bank lowering sources
/// challenge values from one place (spec §5: "the SAME mapping"). Any change
/// to how a challenge resolves must land here once, for both call sites.
pub(crate) fn challenge_value(fixture: &CircuitFixture, r: &ChallengeRef) -> Ext {
    let base = match &r.key {
        ChallengeKey::LookupMultiplicative => fixture.lookup_alpha,
        ChallengeKey::LookupAdditive => fixture.lookup_additive_part,
        ChallengeKey::PermutationAdditive => {
            fixture.external_challenges.permutation_argument_additive_part
        }
        ChallengeKey::PermutationLinearization(slot) => {
            fixture.external_challenges.permutation_argument_linearization_challenges
                [perm_role(slot)]
        }
        ChallengeKey::ConstraintAggregation => panic!(
            "challenge_value: ConstraintAggregation is not sourced for these circuits' forward \
             programs (no materialized constraint roots): {r:?}"
        ),
    };
    pow_of(base, &r.power)
}

impl ChallengeResolver for HostStorageResolvers<'_> {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        challenge_value(self.fixture, r)
    }
}

impl PeekResolver for HostStorageResolvers<'_> {
    fn peek(
        &self,
        desc: &SpecialDescriptor,
        row: usize,
        _r: &Resolvers<'_>,
    ) -> Result<Ext, PeekError> {
        let snap = self.snap;
        Ok(match &desc.strategy {
            SpecialStrategy::PeekSingleColumn { set_index, width } => {
                let idx = match width {
                    RangeWidth::Bits16 => snap.range_check_mapping(*set_index)[row],
                    RangeWidth::Timestamp => snap.timestamp_mapping(*set_index)[row],
                };
                lift(Bf::from_u32_with_reduction(idx))
            }
            SpecialStrategy::PeekAggregate { set_index } => {
                let i = snap.generic_mapping(*set_index)[row] as usize;
                snap.generic_lookup_at(i)
            }
            SpecialStrategy::PeekSetup => {
                snap.generic_lookup.get(row).copied().unwrap_or(Ext::ZERO)
            }
            SpecialStrategy::PeekDecoder { fill: _, .. } => {
                let pred_addr = snap
                    .decoder_pred_addr
                    .expect("PeekDecoder without a captured predicate address");
                if snap.column_value(pred_addr, row) != Ext::ZERO {
                    let i = snap.decoder_mapping()[row] as usize;
                    snap.generic_lookup_at(i)
                } else {
                    // FillSource::DecoderLookupFill — the only variant.
                    snap.decoder_fill
                }
            }
            // Resolver-computed base value, byte-identical to the device
            // `SD_VIRTUAL` path (`gkr_virtual_base_value`); reads no snapshot array.
            SpecialStrategy::VirtualSetup { kind } => lift(virtual_setup_value(kind, row)),
        })
    }
}

// ── test helpers ──────────────────────────────────────────────────────────────

/// Sampled rows for the gate: first/second/mid/last (copy of the stage3 helper
/// `gkr_eval_isa/tests/common/mod.rs:143`).
pub(crate) fn sample_rows(n: usize) -> Vec<usize> {
    if n == 0 {
        return vec![];
    }
    let mut rows = vec![0usize, 1, n / 2, n - 1];
    rows.retain(|&r| r < n);
    rows.sort_unstable();
    rows.dedup();
    rows
}

/// SP2 differential pre-gate on real data (spec §6): drive
/// `validate_special_bindings` (coverage checks + `peek == query-fold` for every
/// referenced descriptor) at the sampled rows. Panics on any binding failure.
pub(crate) fn validate_bindings_sampled(
    cl: &CompiledLayer,
    layer: &DagLayer,
    peek: &dyn PeekResolver,
    r: &Resolvers<'_>,
    rows: &[usize],
) {
    validate_special_bindings(cl, layer, rows, r, peek)
        .unwrap_or_else(|e| panic!("SP2 binding validation failed: {e:?}"));
}
