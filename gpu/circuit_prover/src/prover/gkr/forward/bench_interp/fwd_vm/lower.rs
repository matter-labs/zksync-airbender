//! Task 3: `InterpDesc3` lowering — the fwd-VM `CompiledLayer` program +
//! per-(slot,col) column table + specials + smem-rooted outputs, bound to a
//! real `CircuitFixture`'s production storage. Host-only (no kernel launch;
//! that is Task 4). `gkr_eval_isa`/`cs` are dev-dependencies here (the module
//! is `cfg(all(test, feature = "bench"))`), so `crate::upstream` does not
//! apply — see `bench_interp/fwd_vm/compile.rs:1-5`.
//!
//! Output isolation (spec §4/§10, codex finding F1): a `(slot, col)`
//! materialized THIS layer never gets a read/write pointer into the
//! flat-produced `GpuGKRStorage`. Instead it gets a fresh, poison-filled,
//! interp-owned device column used as BOTH `col_read_ptr` and
//! `col_write_ptr` — an in-memory overlay. This is safe only because the
//! compiled program never legitimately reads such a pair before its own
//! `GlobalMaterialize` write (checked statically below, spec §4 guarantee).

use std::collections::{BTreeMap, BTreeSet};
use std::ptr;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use field::{Field, FieldExtension, PrimeField};

use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::dag_ir::{ChallengeRef, DagLayer, RangeWidth, ReadPlace, RootId};

use gkr_eval_isa::fwd::binding::BackingKey;
use gkr_eval_isa::fwd::context::{CompiledLayer, ForwardAction, OutputCell, RootOutput};
use gkr_eval_isa::fwd::isa::{DstLine, Instr, OperandField, OperandLine};
use gkr_eval_isa::fwd::source::SpecialStrategy;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::ProverContext;

use super::super::fixture::{materialize_virtual_setup_column, CircuitFixture};
use super::super::{InterpResidency, BENCH_INTERP_PROGRAM_LDC_LANES};
use super::compile::{encoded_lanes, read_place_to_gkr_address, FwdVmCircuit};
use super::resolvers::{challenge_value, fixture_stage1, root_flat_addr};

/// Poison bit pattern interp-owned output columns are filled with before the
/// (never-run-in-this-task) kernel would overwrite them via its
/// `GlobalMaterialize` writes. A read that reaches this value is either a
/// static-check bug in this file, or (structurally impossible, per the
/// read-before-write assertion below) a genuine poison read.
const POISON_U32: u32 = 0x5EED_DEAD;

/// Host mirror of the (not-yet-written) `interp_desc3` CUDA ABI (Task 4).
/// Keep field order identical to the `.cu` once it exists.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct InterpDesc3 {
    // program
    pub program_ldg: *const u16, // null when LDC
    pub program_lanes: u32,
    pub n_instr: u32,
    // per-(slot,col) column table (codex spec-F2 + plan-F4): entry for (slot,col) is
    // col_base[slot] + col; col_base has 17 entries (prefix sums, col_base[16] = total =
    // end sentinel) so the kernel bounds-checks col < col_base[slot+1] - col_base[slot]
    // and sets error_flag on violation instead of reading a neighbor slot's region
    // (v2 precedent: col_base length n_matrix_slots+1, interp_v2_gpu.rs:29-35).
    pub col_base: [u32; 17],
    pub col_read_ptr: *const *const u8,
    pub col_is_e4: *const u8, // 0 = Bf column, 1 = E4 column
    pub col_write_ptr: *const *mut u8, // null unless (slot,col) materialized this layer (codex spec-F1)
    // banks — lengths REQUIRED (codex plan-F3): kernel must fail closed (error_flag) on
    // an out-of-range Ldc index, mirroring ChallengeBanks::get / ConstBank::get bounds
    // checks (source.rs:27,:46-49; interp.rs UnknownConst/UnknownChallenge errors).
    pub consts: *const BF,
    pub n_consts: u32,
    pub const_challenge: *const E4,
    pub n_const_challenge: u32,
    pub arg_challenge: *const E4,
    pub n_arg_challenge: u32,
    // specials (parallel arrays, v2 pattern). Value channel is E4 (codex plan-F1):
    // production generic_lookup and decoder fill are DeviceAllocation<E4>
    // (setup/mod.rs:398-404), NOT base-field.
    pub n_descs: u32,
    pub desc_kind: *const u8, // 0=SingleColumn 1=Aggregate 2=Setup 3=Decoder
    pub desc_mapping: *const *const u32,
    pub desc_table: *const *const E4, // generic lookup table (Aggregate/Setup/Decoder)
    pub desc_table_len: *const u32,   // zero-pad boundary (Setup) / bounds (Aggregate/Decoder)
    pub desc_mask: *const *const BF,  // decoder predicate column (base field)
    pub desc_fill: *const E4,         // decoder fill VALUES (per desc, E4)
    pub desc_param: *const u32,       // width/set params as needed
    // smem-rooted outputs written in the epilogue
    pub n_outs: u32,
    pub out_cell: *const u16,
    pub out_ptr: *const *mut u8,
    pub out_is_e4: *const u8,
    // geometry
    pub budget: u32,
    pub count: u32,
    pub error_flag: *mut u32,
}

/// ABI size guard: `InterpDesc3` (Rust) must stay layout-identical to
/// `interp_desc3` (CUDA, `native/bench/gkr_fwd_vm.cu`) — a silent field-layout
/// drift between the two sides corrupts device memory. Paired with the
/// `static_assert(sizeof(interp_desc3) == 264, ...)` on the CUDA side; if the
/// two sides ever disagree on N, that is a real ABI bug, not a number to
/// reconcile by picking two different values.
const _: () = assert!(core::mem::size_of::<InterpDesc3>() == 264);

/// Every `DeviceAllocation` an `InterpDesc3`'s raw pointers borrow into, kept
/// alive for the lifetime of `FwdVmDeviceSetup`.
struct FwdVmKeepalive {
    _lanes_dev: DeviceAllocation<u16>,
    _consts_dev: DeviceAllocation<BF>,
    _const_challenge_dev: DeviceAllocation<E4>,
    _arg_challenge_dev: DeviceAllocation<E4>,
    _col_read_dev: DeviceAllocation<u64>,
    _col_write_dev: DeviceAllocation<u64>,
    _col_is_e4_dev: DeviceAllocation<u8>,
    _desc_kind_dev: DeviceAllocation<u8>,
    _desc_mapping_dev: DeviceAllocation<u64>,
    _desc_table_dev: DeviceAllocation<u64>,
    _desc_table_len_dev: DeviceAllocation<u32>,
    _desc_mask_dev: DeviceAllocation<u64>,
    _desc_fill_dev: DeviceAllocation<E4>,
    _desc_param_dev: DeviceAllocation<u32>,
    _out_cell_dev: DeviceAllocation<u16>,
    _out_ptr_dev: DeviceAllocation<u64>,
    _out_is_e4_dev: DeviceAllocation<u8>,
    _err_dev: DeviceAllocation<u32>,
    /// Interp-owned poison-filled overlay columns, one per materialized
    /// `(slot, col)` this layer (codex finding F1, output isolation). Raw
    /// u32-backed so a single `Vec` covers both Bf (1 word/row) and E4 (4
    /// words/row) columns.
    _poison_bufs: Vec<DeviceAllocation<u32>>,
    /// Materialized virtual-setup base columns (no resident production
    /// buffer; synthesized here exactly like `materialize_virtual_setup_column`
    /// callers elsewhere in this bench harness).
    _virtual_setup_bufs: Vec<DeviceAllocation<BF>>,
    /// Interp-owned poison-filled overlay columns for smem-rooted outputs
    /// (codex finding F1, output isolation): the epilogue kernel (Task 4)
    /// writes here, never into flat/production storage. Raw u32-backed for
    /// the same reason as `_poison_bufs`.
    _smem_out_bufs: Vec<DeviceAllocation<u32>>,
}

pub(crate) struct FwdVmDeviceSetup {
    pub desc: InterpDesc3,
    pub lanes: Vec<u16>,
    pub residency: InterpResidency,
    /// Flat/production storage pointer for each smem-rooted output, in the
    /// same order as `desc.out_cell`/`desc.out_ptr` — the GOLDEN comparison
    /// target Task 4's G-DEV compares the interp-owned `out_ptr` write
    /// against. NEVER handed to the device as a write target (output
    /// isolation, codex F1); host-only bookkeeping.
    pub out_golden_ptr: Vec<u64>,
    _keepalive: FwdVmKeepalive,
}

// ── small host-side helpers ─────────────────────────────────────────────────

fn alloc_upload<T: Copy>(context: &ProverContext, host: &[T]) -> DeviceAllocation<T> {
    let mut dev: DeviceAllocation<T> =
        context.alloc(host.len().max(1), AllocationPlacement::Top).unwrap();
    if !host.is_empty() {
        memory_copy_async(&mut dev[0..host.len()], host, context.get_exec_stream()).unwrap();
    }
    dev
}

/// D2H a raw device array back to host for the G-PTR re-derivation compare.
/// Generic over any POD `T` (u8/u16/u32/u64/E4) — `fill` seeds the host
/// buffer before the copy (no `Default` bound: `E4` has none).
fn d2h_raw<T: Copy>(ptr: *const T, n: usize, ctx: &ProverContext, fill: T) -> Vec<T> {
    if n == 0 {
        return Vec::new();
    }
    assert!(!ptr.is_null(), "d2h_raw: null pointer for a non-empty ({n}) array");
    let mut host = vec![fill; n];
    // SAFETY: caller-provided `ptr`/`n` describe a resident device array of at
    // least `n` `T`s (every call site below sources them from a table this
    // module itself uploaded with exactly that length).
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr, n) };
    memory_copy_async(&mut host, slice, ctx.get_exec_stream()).unwrap();
    ctx.get_exec_stream().synchronize().unwrap();
    host
}

/// Every `OperandLine` an instruction reads, paired with the field width the
/// instruction declares for it (an instruction's own field applies to all its
/// read operands — mirrors `gkr_eval_isa::fwd::interp::resolve`'s callers).
fn instr_operand_fields(instr: &Instr) -> Vec<(OperandLine, OperandField)> {
    match instr {
        Instr::Add { field, operands, .. } => operands.iter().map(|o| (*o, *field)).collect(),
        Instr::Mul { field, operands, .. } => operands.iter().map(|o| (*o, *field)).collect(),
        Instr::Fma { field_lhs, field_rhs, pairs, .. } => pairs
            .iter()
            .flat_map(|(l, r)| [(*l, *field_lhs), (*r, *field_rhs)])
            .collect(),
        Instr::Mov { field, src, .. } => src.iter().map(|s| (*s, *field)).collect(),
    }
}

fn note_col(max_col: &mut [Option<u16>; 16], slot: u8, col: u16) {
    let s = slot as usize;
    max_col[s] = Some(max_col[s].map_or(col, |m| m.max(col)));
}

/// Per-layer usage of the `(slot, col)` Global address space: the highest
/// column index touched per slot (for `col_base` sizing), the operand field
/// every non-materialized read declares (for the storage `is_e4` cross-check),
/// and the `(slot,col) -> field` map of every `GlobalMaterialize` destination
/// (the materialized/overlay set).
struct GlobalUsage {
    max_col: [Option<u16>; 16],
    read_field: BTreeMap<(u8, u16), OperandField>,
    materialized: BTreeMap<(u8, u16), OperandField>,
}

/// Walk `cl.program.instrs` once, collecting `GlobalUsage`, then cross-check
/// the derived materialized set against `cl.root_outputs`' `RootOutput::
/// Cell(Global)` entries (spec §5 build rule: the two sources must agree
/// exactly — `materialize_if_root` in the compiler always emits both
/// together, so a divergence here is a lowering bug, not a legitimate case).
fn collect_global_usage(cl: &CompiledLayer) -> GlobalUsage {
    let mut max_col: [Option<u16>; 16] = [None; 16];
    let mut read_field: BTreeMap<(u8, u16), OperandField> = BTreeMap::new();
    let mut materialized: BTreeMap<(u8, u16), OperandField> = BTreeMap::new();

    for instr in &cl.program.instrs {
        for (op, field) in instr_operand_fields(instr) {
            if let OperandLine::Global { slot, col } = op {
                note_col(&mut max_col, slot, col);
                match read_field.get(&(slot, col)) {
                    Some(&prev) => assert_eq!(
                        prev, field,
                        "fwd-VM lowering: (slot {slot}, col {col}) read with inconsistent \
                         operand fields ({prev:?} vs {field:?})"
                    ),
                    None => {
                        read_field.insert((slot, col), field);
                    }
                }
            }
        }
        if let Instr::Mov { dst: Some(DstLine::GlobalMaterialize { slot, col }), field, .. } =
            instr
        {
            note_col(&mut max_col, *slot, *col);
            materialized.insert((*slot, *col), *field);
        }
    }

    let mut root_global: BTreeSet<(u8, u16)> = BTreeSet::new();
    for (_, out) in &cl.root_outputs {
        if let RootOutput::Cell(OutputCell::Global { slot, col }) = out {
            root_global.insert((*slot, *col));
        }
    }
    let materialized_keys: BTreeSet<(u8, u16)> = materialized.keys().copied().collect();
    assert_eq!(
        materialized_keys, root_global,
        "fwd-VM lowering: GlobalMaterialize dsts {materialized_keys:?} and RootOutput::\
         Cell(Global) roots {root_global:?} disagree on the materialized (slot,col) set"
    );

    GlobalUsage { max_col, read_field, materialized }
}

/// Static read-before-write check (spec §4 guarantee): every program-order
/// Global read of a materialized `(slot,col)` must be preceded by its own
/// `GlobalMaterialize` write. This is what makes it sound to hand the SAME
/// poison-filled overlay buffer to both `col_read_ptr` and `col_write_ptr`.
fn assert_read_before_write(cl: &CompiledLayer, materialized: &BTreeMap<(u8, u16), OperandField>) {
    let mut written: BTreeSet<(u8, u16)> = BTreeSet::new();
    for instr in &cl.program.instrs {
        for (op, _field) in instr_operand_fields(instr) {
            if let OperandLine::Global { slot, col } = op {
                if materialized.contains_key(&(slot, col)) {
                    assert!(
                        written.contains(&(slot, col)),
                        "fwd-VM lowering: Global read of materialized (slot {slot}, col {col}) \
                         precedes its GlobalMaterialize write in program order — poison-overlay \
                         read-before-write invariant violated (spec §4)"
                    );
                }
            }
        }
        if let Instr::Mov { dst: Some(DstLine::GlobalMaterialize { slot, col }), .. } = instr {
            written.insert((*slot, *col));
        }
    }
}

/// Inverse of `gkr_eval_isa::fwd::binding::read_place_to_backing` + `super::
/// compile::read_place_to_gkr_address`, composed for a `BackingTable` slot's
/// key: the flat `GKRAddress` a non-materialized `(slot,col)` reads from.
/// `None` for `VirtualSetup` (no resident backing; materialized separately).
fn backing_key_col_to_gkr_address(key: &BackingKey, col: u16) -> Option<GKRAddress> {
    let c = col as usize;
    Some(match key {
        BackingKey::BaseLayerMemory => GKRAddress::BaseLayerMemory(c),
        BackingKey::BaseLayerWitness => GKRAddress::BaseLayerWitness(c),
        BackingKey::Setup => GKRAddress::Setup(c),
        BackingKey::Scratch => GKRAddress::ScratchSpace(c),
        BackingKey::LayerOutput { layer } => GKRAddress::InnerLayer { layer: *layer, offset: c },
        BackingKey::CacheOutput { layer } => GKRAddress::Cached { layer: *layer, offset: c },
        BackingKey::VirtualSetup { .. } => return None,
    })
}

/// `VirtualSetupKind` (dag_ir) -> `VirtualSetupPoly` (the `GKRAddress`-space
/// enum `materialize_virtual_setup_column` takes). Same four variants; kept as
/// an explicit `match` (not a transmute) so a future added variant fails to
/// compile here instead of silently misrouting.
fn virtual_setup_kind_to_poly(
    kind: &cs::gkr_compiler::dag_ir::VirtualSetupKind,
) -> VirtualSetupPoly {
    use cs::gkr_compiler::dag_ir::VirtualSetupKind as K;
    match kind {
        K::RangeCheck16Bits => VirtualSetupPoly::RangeCheck16Bits,
        K::RangeCheckTimestamp => VirtualSetupPoly::RangeCheckTimestamp,
        K::InitsAndTeardownsLow => VirtualSetupPoly::InitsAndTeardownsLow,
        K::InitsAndTeardownsHigh => VirtualSetupPoly::InitsAndTeardownsHigh,
    }
}

fn poison_words(t: usize, is_e4: bool) -> Vec<u32> {
    vec![POISON_U32; if is_e4 { t * 4 } else { t }]
}

// ── build ────────────────────────────────────────────────────────────────────

/// Build the `InterpDesc3` device lowering for one real-fixture (circuit,
/// layer) point. Every raw pointer either targets `fixture`'s resident
/// production storage (non-materialized reads) or a fresh interp-owned
/// device allocation kept alive in the returned setup (materialized overlay
/// columns, virtual-setup materializations, banks, desc/out tables).
pub(crate) fn build_fwd_vm_device_setup(
    fixture: &CircuitFixture,
    c: &FwdVmCircuit,
    layer_idx: usize,
) -> FwdVmDeviceSetup {
    let cl = &c.compiled.layers[layer_idx];
    let layer = &c.dag.layers[layer_idx];
    let ctx = &cl.ctx;
    let context = fixture.context();
    let t = fixture.trace_len;

    // Capacity (spec plan-F3): backing slots are bounded to 16 by
    // `BackingTable::intern` itself (compile_circuit would already have
    // failed otherwise), but assert here too rather than silently truncate.
    assert!(
        ctx.backings.backing(16).is_none(),
        "L{layer_idx}: more than 16 backing slots (MAX_SLOTS violated)"
    );

    let usage = collect_global_usage(cl);
    assert_read_before_write(cl, &usage.materialized);

    // ----- col_base: prefix sums over the 16 fixed slots. -----
    let mut col_base = [0u32; 17];
    for s in 0..16u8 {
        let width = match ctx.backings.backing(s) {
            Some(_) => usage.max_col[s as usize]
                .unwrap_or_else(|| panic!("L{layer_idx}: slot {s} has a backing but no observed column"))
                as u32
                + 1,
            None => 0,
        };
        col_base[s as usize + 1] = col_base[s as usize] + width;
    }
    let total_cols = col_base[16] as usize;

    // ----- per-(slot,col) column table. -----
    let mut col_read_host = vec![0u64; total_cols];
    let mut col_write_host = vec![0u64; total_cols];
    let mut col_is_e4_host = vec![0u8; total_cols];
    let mut poison_bufs: Vec<DeviceAllocation<u32>> = Vec::new();
    let mut virtual_setup_bufs: Vec<DeviceAllocation<BF>> = Vec::new();

    for s in 0..16u8 {
        let Some(key) = ctx.backings.backing(s) else { continue };
        let Some(max_c) = usage.max_col[s as usize] else { continue };
        for col in 0..=max_c {
            let idx = (col_base[s as usize] + col as u32) as usize;
            let pair = (s, col);
            if let Some(&field) = usage.materialized.get(&pair) {
                // Materialized this layer: interp-owned poison overlay, never
                // a pointer into flat/production storage (output isolation).
                let is_e4 = field == OperandField::Ext;
                let words = poison_words(t, is_e4);
                let dev = alloc_upload(context, &words);
                let raw = dev.as_ptr() as u64;
                col_read_host[idx] = raw;
                col_write_host[idx] = raw;
                col_is_e4_host[idx] = is_e4 as u8;
                poison_bufs.push(dev);
                continue;
            }
            match key {
                BackingKey::VirtualSetup { kind } => {
                    let poly = virtual_setup_kind_to_poly(kind);
                    let host = materialize_virtual_setup_column(poly, t);
                    let dev = alloc_upload(context, &host);
                    col_read_host[idx] = dev.as_ptr() as u64;
                    col_is_e4_host[idx] = 0; // virtual-setup polys are base-field
                    virtual_setup_bufs.push(dev);
                }
                _ => {
                    let addr = backing_key_col_to_gkr_address(key, col)
                        .expect("non-VirtualSetup backing key must resolve to a GKRAddress");
                    let (is_e4, p) = fixture.storage_column(addr).unwrap_or_else(|| {
                        panic!(
                            "L{layer_idx}: (slot {s}, col {col}) addr {addr:?} not resident in \
                             post-capture storage"
                        )
                    });
                    if let Some(&declared) = usage.read_field.get(&pair) {
                        let expect_e4 = declared == OperandField::Ext;
                        assert_eq!(
                            expect_e4, is_e4,
                            "L{layer_idx}: (slot {s}, col {col}) addr {addr:?} field mismatch — \
                             program declares {declared:?}, storage_column reports is_e4={is_e4}"
                        );
                    }
                    col_read_host[idx] = p as u64;
                    col_is_e4_host[idx] = is_e4 as u8;
                }
            }
        }
    }

    let col_read_dev = alloc_upload(context, &col_read_host);
    let col_write_dev = alloc_upload(context, &col_write_host);
    let col_is_e4_dev = alloc_upload(context, &col_is_e4_host);

    // ----- constant + challenge banks. -----
    let consts_host: Vec<BF> =
        ctx.consts.values().iter().map(|&v| BF::from_u32_with_reduction(v)).collect();
    let consts_dev = alloc_upload(context, &consts_host);

    let const_challenge_host = collect_challenge_bank(
        fixture,
        ctx,
        gkr_eval_isa::fwd::isa::LdcSub::ConstChallenge,
    );
    let arg_challenge_host =
        collect_challenge_bank(fixture, ctx, gkr_eval_isa::fwd::isa::LdcSub::ArgChallenge);
    let const_challenge_dev = alloc_upload(context, &const_challenge_host);
    let arg_challenge_dev = alloc_upload(context, &arg_challenge_host);

    // ----- specials. -----
    let stage1 = fixture_stage1(fixture);
    let (setup_ptr, setup_len) = fixture.setup_table();
    let specials: Vec<_> = ctx.specials.iter().collect();
    let n_descs = specials.len();
    let mut desc_kind = vec![0u8; n_descs];
    let mut desc_mapping = vec![0u64; n_descs];
    let mut desc_table = vec![0u64; n_descs];
    let mut desc_table_len = vec![0u32; n_descs];
    let mut desc_mask = vec![0u64; n_descs];
    let mut desc_fill = vec![Field::ZERO; n_descs];
    let mut desc_param = vec![0u32; n_descs];

    for (d, desc) in specials.iter().enumerate() {
        match &desc.strategy {
            SpecialStrategy::PeekSingleColumn { set_index, width } => {
                desc_kind[d] = 0;
                let map_ptr = match width {
                    RangeWidth::Bits16 => stage1.lookup_mappings.range_check_mapping(*set_index).as_ptr(),
                    RangeWidth::Timestamp => {
                        stage1.lookup_mappings.timestamp_mapping(*set_index).as_ptr()
                    }
                };
                desc_mapping[d] = map_ptr as u64;
                desc_param[d] = match width {
                    RangeWidth::Bits16 => 0,
                    RangeWidth::Timestamp => 1,
                };
            }
            SpecialStrategy::PeekAggregate { set_index } => {
                desc_kind[d] = 1;
                desc_mapping[d] = stage1.lookup_mappings.generic_mapping(*set_index).as_ptr() as u64;
                desc_table[d] = setup_ptr as u64;
                desc_table_len[d] = setup_len;
            }
            SpecialStrategy::PeekSetup => {
                desc_kind[d] = 2;
                desc_table[d] = setup_ptr as u64;
                desc_table_len[d] = setup_len;
            }
            SpecialStrategy::PeekDecoder { predicate, .. } => {
                desc_kind[d] = 3;
                let mapping = stage1.lookup_mappings.decoder_mapping().unwrap_or_else(|| {
                    panic!("L{layer_idx}: PeekDecoder present but stage1 has no decoder mapping")
                });
                desc_mapping[d] = mapping.as_ptr() as u64;
                desc_table[d] = setup_ptr as u64;
                desc_table_len[d] = setup_len;
                let pred_addr = read_place_to_gkr_address(predicate, &fixture.compiled_circuit);
                let (is_e4_pred, pred_ptr) = fixture.storage_column(pred_addr).unwrap_or_else(|| {
                    panic!("L{layer_idx}: decoder predicate {pred_addr:?} not resident")
                });
                assert!(
                    !is_e4_pred,
                    "L{layer_idx}: decoder predicate column must be base-field, got e4 for \
                     {pred_addr:?}"
                );
                desc_mask[d] = pred_ptr as u64;
                desc_fill[d] = fixture.bench_challenges().decoder_fill;
            }
        }
    }

    let desc_kind_dev = alloc_upload(context, &desc_kind);
    let desc_mapping_dev = alloc_upload(context, &desc_mapping);
    let desc_table_dev = alloc_upload(context, &desc_table);
    let desc_table_len_dev = alloc_upload(context, &desc_table_len);
    let desc_mask_dev = alloc_upload(context, &desc_mask);
    let desc_fill_dev = alloc_upload(context, &desc_fill);
    let desc_param_dev = alloc_upload(context, &desc_param);

    // ----- smem-rooted outputs (epilogue writes here). Output isolation
    // (spec §4/§10, codex F1): out_ptr NEVER points into flat/production
    // storage. Each output gets a fresh, poison-filled, interp-owned column
    // (same treatment as the `GlobalMaterialize` overlay above); the flat
    // destination (`addr`/`p`) is resolved only to serve as the GOLDEN
    // comparison target for Task 4's G-DEV, kept in `out_golden_ptr`. -----
    let mut out_cell_host: Vec<u16> = Vec::new();
    let mut out_ptr_host: Vec<u64> = Vec::new();
    let mut out_is_e4_host: Vec<u8> = Vec::new();
    let mut out_golden_ptr_host: Vec<u64> = Vec::new();
    let mut smem_out_bufs: Vec<DeviceAllocation<u32>> = Vec::new();
    for (rid, out) in &cl.root_outputs {
        if let RootOutput::Cell(OutputCell::Smem(cell)) = out {
            let addr = root_flat_addr(layer, cl, *rid);
            let (is_e4, p) = fixture.storage_column(addr).unwrap_or_else(|| {
                panic!("L{layer_idx}: smem-rooted output root {rid:?} addr {addr:?} not resident")
            });
            let words = poison_words(t, is_e4);
            let dev = alloc_upload(context, &words);
            out_cell_host.push(*cell);
            out_ptr_host.push(dev.as_ptr() as u64);
            out_is_e4_host.push(is_e4 as u8);
            out_golden_ptr_host.push(p as u64);
            smem_out_bufs.push(dev);
        }
    }
    let n_outs = out_cell_host.len();
    let out_cell_dev = alloc_upload(context, &out_cell_host);
    let out_ptr_dev = alloc_upload(context, &out_ptr_host);
    let out_is_e4_dev = alloc_upload(context, &out_is_e4_host);

    // ----- program lanes (LDG pointer; a caller wanting LDC residency should
    // `upload_bench_program_to_constant(&setup.lanes)` and null this field —
    // Task 3 does not launch a kernel, so it always populates the LDG form). -----
    let lanes = encoded_lanes(cl);
    let lanes_dev = alloc_upload(context, &lanes);

    let mut err_dev: DeviceAllocation<u32> = alloc_upload(context, &[0u32]);

    context.get_exec_stream().synchronize().unwrap();

    let desc = InterpDesc3 {
        program_ldg: lanes_dev.as_ptr(),
        program_lanes: lanes.len() as u32,
        n_instr: cl.program.instrs.len() as u32,
        col_base,
        col_read_ptr: col_read_dev.as_ptr() as *const *const u8,
        col_is_e4: col_is_e4_dev.as_ptr(),
        col_write_ptr: col_write_dev.as_ptr() as *const *mut u8,
        consts: consts_dev.as_ptr(),
        n_consts: consts_host.len() as u32,
        const_challenge: const_challenge_dev.as_ptr(),
        n_const_challenge: const_challenge_host.len() as u32,
        arg_challenge: arg_challenge_dev.as_ptr(),
        n_arg_challenge: arg_challenge_host.len() as u32,
        n_descs: n_descs as u32,
        desc_kind: if n_descs == 0 { ptr::null() } else { desc_kind_dev.as_ptr() },
        desc_mapping: if n_descs == 0 {
            ptr::null()
        } else {
            desc_mapping_dev.as_ptr() as *const *const u32
        },
        desc_table: if n_descs == 0 {
            ptr::null()
        } else {
            desc_table_dev.as_ptr() as *const *const E4
        },
        desc_table_len: if n_descs == 0 { ptr::null() } else { desc_table_len_dev.as_ptr() },
        desc_mask: if n_descs == 0 {
            ptr::null()
        } else {
            desc_mask_dev.as_ptr() as *const *const BF
        },
        desc_fill: if n_descs == 0 { ptr::null() } else { desc_fill_dev.as_ptr() },
        desc_param: if n_descs == 0 { ptr::null() } else { desc_param_dev.as_ptr() },
        n_outs: n_outs as u32,
        out_cell: if n_outs == 0 { ptr::null() } else { out_cell_dev.as_ptr() },
        out_ptr: if n_outs == 0 { ptr::null() } else { out_ptr_dev.as_ptr() as *const *mut u8 },
        out_is_e4: if n_outs == 0 { ptr::null() } else { out_is_e4_dev.as_ptr() },
        budget: cl.budget as u32,
        count: t as u32,
        error_flag: err_dev.as_mut_ptr(),
    };

    FwdVmDeviceSetup {
        desc,
        lanes,
        residency: InterpResidency::Ldg,
        out_golden_ptr: out_golden_ptr_host,
        _keepalive: FwdVmKeepalive {
            _lanes_dev: lanes_dev,
            _consts_dev: consts_dev,
            _const_challenge_dev: const_challenge_dev,
            _arg_challenge_dev: arg_challenge_dev,
            _col_read_dev: col_read_dev,
            _col_write_dev: col_write_dev,
            _col_is_e4_dev: col_is_e4_dev,
            _desc_kind_dev: desc_kind_dev,
            _desc_mapping_dev: desc_mapping_dev,
            _desc_table_dev: desc_table_dev,
            _desc_table_len_dev: desc_table_len_dev,
            _desc_mask_dev: desc_mask_dev,
            _desc_fill_dev: desc_fill_dev,
            _desc_param_dev: desc_param_dev,
            _out_cell_dev: out_cell_dev,
            _out_ptr_dev: out_ptr_dev,
            _out_is_e4_dev: out_is_e4_dev,
            _err_dev: err_dev,
            _poison_bufs: poison_bufs,
            _virtual_setup_bufs: virtual_setup_bufs,
            _smem_out_bufs: smem_out_bufs,
        },
    }
}

/// Enumerate a `ChallengeBanks` channel to concrete `E4` values via the
/// SHARED `challenge_value` mapping (Task 2's `HostStorageResolvers::
/// challenge` calls the same function). `ChallengeBanks` exposes no length
/// accessor, so probe `get(sub, idx)` upward from 0 until it returns `None`
/// — the bank is a dense `Vec` internally (`intern` always pushes), so this
/// terminates exactly at the real length.
fn collect_challenge_bank(
    fixture: &CircuitFixture,
    ctx: &gkr_eval_isa::fwd::context::DagForwardContext,
    sub: gkr_eval_isa::fwd::isa::LdcSub,
) -> Vec<E4> {
    let mut out = Vec::new();
    let mut idx = 0u16;
    while let Some(r) = ctx.challenges.get(sub, idx) {
        out.push(challenge_value(fixture, r));
        idx += 1;
    }
    out
}

// ── G-PTR (spec §7): structural re-derivation gate ──────────────────────────

/// Re-derive every pointer/flag `build_fwd_vm_device_setup` produced, NOT by
/// trusting `setup.desc`'s own tables, and cross-check against the ACTUAL
/// device array contents read back (D2H) plus a freshly-queried
/// `fixture.storage_column`. This shares its address-derivation helpers
/// (`collect_global_usage`, `backing_key_col_to_gkr_address`) with the
/// builder, so it is a consistency gate against device contents +
/// `fixture`/`c`, not a fully independent re-derivation — semantic misrouting
/// of the SAME shared derivation would be caught by G-CPU/G-DEV, not here.
/// This is the structural soundness gate for Task 3's output-isolation +
/// pointer-wiring claims.
pub(crate) fn assert_gptr(
    fixture: &CircuitFixture,
    c: &FwdVmCircuit,
    layer_idx: usize,
    setup: &FwdVmDeviceSetup,
) {
    let cl = &c.compiled.layers[layer_idx];
    let layer = &c.dag.layers[layer_idx];
    let ctx = &cl.ctx;
    let context = fixture.context();

    let usage = collect_global_usage(cl);

    // ----- col_base re-derivation. -----
    let mut col_base = [0u32; 17];
    for s in 0..16u8 {
        let width = match ctx.backings.backing(s) {
            Some(_) => usage.max_col[s as usize].map(|m| m as u32 + 1).unwrap_or(0),
            None => 0,
        };
        col_base[s as usize + 1] = col_base[s as usize] + width;
    }
    assert_eq!(col_base, setup.desc.col_base, "L{layer_idx}: col_base mismatch");
    let total_cols = col_base[16] as usize;
    assert!(
        ctx.backings.backing(16).is_none(),
        "L{layer_idx}: capacity violated — a 17th backing slot exists (MAX_SLOTS=16)"
    );

    // ----- column table re-derivation, compared against the DEVICE contents. -----
    let read_back_read =
        d2h_raw::<u64>(setup.desc.col_read_ptr as *const u64, total_cols, context, 0u64);
    let read_back_write =
        d2h_raw::<u64>(setup.desc.col_write_ptr as *const u64, total_cols, context, 0u64);
    let read_back_e4 = d2h_raw::<u8>(setup.desc.col_is_e4, total_cols, context, 0u8);

    for s in 0..16u8 {
        let Some(key) = ctx.backings.backing(s) else { continue };
        let Some(max_c) = usage.max_col[s as usize] else {
            panic!("L{layer_idx}: slot {s} has a backing but no observed column usage");
        };
        for col in 0..=max_c {
            let idx = (col_base[s as usize] + col as u32) as usize;
            let pair = (s, col);
            if let Some(&field) = usage.materialized.get(&pair) {
                let expect_e4 = field == OperandField::Ext;
                assert_ne!(
                    read_back_write[idx], 0,
                    "L{layer_idx}: (slot {s}, col {col}) materialized but write ptr is null"
                );
                assert_eq!(
                    read_back_read[idx], read_back_write[idx],
                    "L{layer_idx}: (slot {s}, col {col}) overlay read/write ptr mismatch"
                );
                assert_eq!(
                    (read_back_e4[idx] != 0),
                    expect_e4,
                    "L{layer_idx}: (slot {s}, col {col}) overlay is_e4 mismatch"
                );
                // Output isolation: never the production storage pointer.
                if let Some(addr) = backing_key_col_to_gkr_address(key, col) {
                    if let Some((_, storage_ptr)) = fixture.storage_column(addr) {
                        assert_ne!(
                            read_back_read[idx], storage_ptr as u64,
                            "L{layer_idx}: (slot {s}, col {col}) overlay read ptr equals \
                             PRODUCTION storage ptr — output isolation violated"
                        );
                    }
                }
            } else {
                match key {
                    BackingKey::VirtualSetup { .. } => {
                        assert_eq!(
                            read_back_write[idx], 0,
                            "L{layer_idx}: virtual-setup (slot {s}, col {col}) must not be \
                             writable"
                        );
                        assert_ne!(
                            read_back_read[idx], 0,
                            "L{layer_idx}: virtual-setup (slot {s}, col {col}) read ptr is null"
                        );
                        assert_eq!(
                            read_back_e4[idx], 0,
                            "L{layer_idx}: virtual-setup (slot {s}, col {col}) must be base-field"
                        );
                    }
                    _ => {
                        let addr = backing_key_col_to_gkr_address(key, col)
                            .expect("non-VirtualSetup backing key must resolve to a GKRAddress");
                        let (is_e4, p) = fixture.storage_column(addr).unwrap_or_else(|| {
                            panic!("L{layer_idx}: (slot {s}, col {col}) addr {addr:?} not resident")
                        });
                        assert_eq!(
                            read_back_read[idx], p as u64,
                            "L{layer_idx}: (slot {s}, col {col}) read ptr != storage_column({addr:?})"
                        );
                        assert_eq!(
                            (read_back_e4[idx] != 0),
                            is_e4,
                            "L{layer_idx}: (slot {s}, col {col}) is_e4 != storage_column({addr:?})"
                        );
                        assert_eq!(
                            read_back_write[idx], 0,
                            "L{layer_idx}: (slot {s}, col {col}) non-materialized but has a \
                             write ptr"
                        );
                    }
                }
            }
        }
    }

    // ----- specials re-derivation. -----
    let stage1 = fixture_stage1(fixture);
    let (setup_ptr, setup_len) = fixture.setup_table();
    let specials: Vec<_> = ctx.specials.iter().collect();
    let n_descs = specials.len();
    assert_eq!(n_descs as u32, setup.desc.n_descs, "L{layer_idx}: n_descs mismatch");
    if n_descs > 0 {
        let kind_back = d2h_raw::<u8>(setup.desc.desc_kind, n_descs, context, 0u8);
        let mapping_back = d2h_raw::<u64>(setup.desc.desc_mapping as *const u64, n_descs, context, 0u64);
        let table_back = d2h_raw::<u64>(setup.desc.desc_table as *const u64, n_descs, context, 0u64);
        let table_len_back = d2h_raw::<u32>(setup.desc.desc_table_len, n_descs, context, 0u32);
        let mask_back = d2h_raw::<u64>(setup.desc.desc_mask as *const u64, n_descs, context, 0u64);
        let fill_back = d2h_raw::<E4>(setup.desc.desc_fill, n_descs, context, Field::ZERO);
        let param_back = d2h_raw::<u32>(setup.desc.desc_param, n_descs, context, 0u32);

        for (d, desc) in specials.iter().enumerate() {
            match &desc.strategy {
                SpecialStrategy::PeekSingleColumn { set_index, width } => {
                    assert_eq!(kind_back[d], 0, "L{layer_idx}: desc {d} kind");
                    let expect_ptr = match width {
                        RangeWidth::Bits16 => {
                            stage1.lookup_mappings.range_check_mapping(*set_index).as_ptr()
                        }
                        RangeWidth::Timestamp => {
                            stage1.lookup_mappings.timestamp_mapping(*set_index).as_ptr()
                        }
                    } as u64;
                    assert_eq!(mapping_back[d], expect_ptr, "L{layer_idx}: desc {d} mapping ptr");
                    assert_eq!(table_back[d], 0, "L{layer_idx}: desc {d} table must be null");
                    assert_eq!(mask_back[d], 0, "L{layer_idx}: desc {d} mask must be null");
                    assert_eq!(fill_back[d], Field::ZERO, "L{layer_idx}: desc {d} fill must be zero");
                    let expect_param = match width {
                        RangeWidth::Bits16 => 0,
                        RangeWidth::Timestamp => 1,
                    };
                    assert_eq!(param_back[d], expect_param, "L{layer_idx}: desc {d} param");
                }
                SpecialStrategy::PeekAggregate { set_index } => {
                    assert_eq!(kind_back[d], 1, "L{layer_idx}: desc {d} kind");
                    assert_eq!(
                        mapping_back[d],
                        stage1.lookup_mappings.generic_mapping(*set_index).as_ptr() as u64,
                        "L{layer_idx}: desc {d} mapping ptr"
                    );
                    assert_eq!(table_back[d], setup_ptr as u64, "L{layer_idx}: desc {d} table ptr");
                    assert_eq!(table_len_back[d], setup_len, "L{layer_idx}: desc {d} table len");
                }
                SpecialStrategy::PeekSetup => {
                    assert_eq!(kind_back[d], 2, "L{layer_idx}: desc {d} kind");
                    assert_eq!(table_back[d], setup_ptr as u64, "L{layer_idx}: desc {d} table ptr");
                    assert_eq!(table_len_back[d], setup_len, "L{layer_idx}: desc {d} table len");
                    assert_eq!(mapping_back[d], 0, "L{layer_idx}: desc {d} mapping must be null");
                }
                SpecialStrategy::PeekDecoder { predicate, .. } => {
                    assert_eq!(kind_back[d], 3, "L{layer_idx}: desc {d} kind");
                    let expect_mapping =
                        stage1.lookup_mappings.decoder_mapping().unwrap().as_ptr() as u64;
                    assert_eq!(mapping_back[d], expect_mapping, "L{layer_idx}: desc {d} mapping ptr");
                    assert_eq!(table_back[d], setup_ptr as u64, "L{layer_idx}: desc {d} table ptr");
                    let pred_addr = read_place_to_gkr_address(predicate, &fixture.compiled_circuit);
                    let (is_e4_pred, pred_ptr) = fixture.storage_column(pred_addr).unwrap();
                    assert!(!is_e4_pred, "L{layer_idx}: desc {d} predicate must be base-field");
                    assert_eq!(mask_back[d], pred_ptr as u64, "L{layer_idx}: desc {d} mask ptr");
                    assert_eq!(
                        fill_back[d],
                        fixture.bench_challenges().decoder_fill,
                        "L{layer_idx}: desc {d} fill value"
                    );
                }
            }
        }
    }

    // ----- smem-rooted outputs re-derivation. Output isolation (spec §4,
    // codex F1): out_ptr must be the interp-owned poison column, NEVER the
    // flat storage_column pointer — the flat destination survives only
    // host-side in `setup.out_golden_ptr` (Task 4's G-DEV golden). -----
    let mut expected: Vec<(RootId, u16)> = Vec::new();
    for (rid, out) in &cl.root_outputs {
        if let RootOutput::Cell(OutputCell::Smem(cell)) = out {
            expected.push((*rid, *cell));
        }
    }
    assert_eq!(expected.len() as u32, setup.desc.n_outs, "L{layer_idx}: n_outs mismatch");
    assert_eq!(
        expected.len(),
        setup.out_golden_ptr.len(),
        "L{layer_idx}: out_golden_ptr length mismatch"
    );
    assert_eq!(
        expected.len(),
        setup._keepalive._smem_out_bufs.len(),
        "L{layer_idx}: _smem_out_bufs length mismatch"
    );
    if !expected.is_empty() {
        let cell_back = d2h_raw::<u16>(setup.desc.out_cell, expected.len(), context, 0u16);
        let ptr_back = d2h_raw::<u64>(setup.desc.out_ptr as *const u64, expected.len(), context, 0u64);
        let e4_back = d2h_raw::<u8>(setup.desc.out_is_e4, expected.len(), context, 0u8);
        for (i, (rid, cell)) in expected.iter().enumerate() {
            assert_eq!(cell_back[i], *cell, "L{layer_idx}: out {i} cell");
            let addr = root_flat_addr(layer, cl, *rid);
            let (is_e4, p) = fixture.storage_column(addr).unwrap();
            // Isolation: the device write target is NOT production storage.
            assert_ne!(
                ptr_back[i], p as u64,
                "L{layer_idx}: out {i} ptr aliases storage_column({addr:?}) — output isolation \
                 violated (codex F1)"
            );
            // The device write target IS the interp-owned poison column.
            assert_eq!(
                ptr_back[i],
                setup._keepalive._smem_out_bufs[i].as_ptr() as u64,
                "L{layer_idx}: out {i} ptr != interp-owned _smem_out_bufs[{i}]"
            );
            // The flat destination is preserved host-side as the golden.
            assert_eq!(
                setup.out_golden_ptr[i], p as u64,
                "L{layer_idx}: out {i} out_golden_ptr != storage_column({addr:?})"
            );
            assert_eq!((e4_back[i] != 0), is_e4, "L{layer_idx}: out {i} is_e4");
        }
        // Poison spot-check: no kernel has run yet, so the first lanes of the
        // first interp-owned output buffer must still hold the poison pattern.
        let buf0 = &setup._keepalive._smem_out_bufs[0];
        let probe = buf0.len().min(8);
        let lanes_back = d2h_raw::<u32>(buf0.as_ptr(), probe, context, 0u32);
        for (j, w) in lanes_back.iter().enumerate() {
            assert_eq!(
                *w, POISON_U32,
                "L{layer_idx}: out 0 poison lane {j} = {w:#010x}, expected {POISON_U32:#010x}"
            );
        }
    }

    // ----- program size sanity. -----
    assert_eq!(
        setup.desc.n_instr as usize,
        cl.program.instrs.len(),
        "L{layer_idx}: n_instr mismatch"
    );
    assert_eq!(
        setup.desc.program_lanes as usize,
        setup.lanes.len(),
        "L{layer_idx}: program_lanes mismatch vs setup.lanes"
    );
    assert!(!setup.desc.program_ldg.is_null(), "L{layer_idx}: program_ldg is null");
}

// ── G-DEV + G-ALIAS (spec §7): device interpreter bit-exact vs flat ──────────

/// D2H a device column and lift to `E4` per row (Bf columns lift via
/// `from_base`, so a Bf/E4 width difference between the interp overlay and the
/// flat storage still compares by VALUE).
fn d2h_col_lifted(ptr: u64, is_e4: bool, t: usize, ctx: &ProverContext) -> Vec<E4> {
    if is_e4 {
        d2h_raw::<E4>(ptr as *const E4, t, ctx, Field::ZERO)
    } else {
        d2h_raw::<BF>(ptr as *const BF, t, ctx, Field::ZERO)
            .into_iter()
            .map(<E4 as FieldExtension<BF>>::from_base)
            .collect()
    }
}

fn compare_columns(label: &str, got: &[E4], want: &[E4]) -> Result<(), String> {
    for (row, (g, w)) in got.iter().zip(want.iter()).enumerate() {
        if g != w {
            return Err(format!("{label} row {row}: interp {g:?} != flat {w:?}"));
        }
    }
    Ok(())
}

/// Run the fwd-VM kernel on one real-fixture (circuit, layer) point and gate it
/// (spec §7):
///
/// - **G-DEV** (all-row bit-exact): every interp-owned output column — the
///   smem-rooted epilogue columns AND the materialized `(slot,col)` overlay
///   columns — equals the flat-produced reference column, every row.
/// - **G-ALIAS** (codex spec-F5): for each `CopyAlias` action, the aliased
///   source column equals the flat destination column, every row
///   (pointer-equality shortcut when both resolve to the same device pointer).
///
/// Both residencies run against fresh poison-filled setups, so a stale LDG
/// result cannot mask an LDC no-op; LDC is skipped only if the program exceeds
/// the 28 KB constant array (never for add_sub, per the Task 1 probe).
pub(crate) fn run_gdev_layer(
    fixture: &CircuitFixture,
    c: &FwdVmCircuit,
    layer_idx: usize,
) -> Result<(), String> {
    let cl = &c.compiled.layers[layer_idx];
    let context = fixture.context();
    let t = fixture.trace_len;
    let usage = collect_global_usage(cl);

    // G-ALIAS is residency-independent (alias roots carry zero program lanes —
    // the kernel never touches these columns); check once.
    for (rid, out) in &cl.root_outputs {
        if let RootOutput::Alias(_) = out {
            let Some(ForwardAction::CopyAlias { src_addr, dst_addr }) = cl.ctx.actions.get(rid)
            else {
                return Err(format!("L{layer_idx}: alias root {rid:?} has no CopyAlias action"));
            };
            let (se4, sp) = fixture
                .storage_column(*src_addr)
                .ok_or_else(|| format!("L{layer_idx}: alias src {src_addr:?} not resident"))?;
            let (de4, dp) = fixture
                .storage_column(*dst_addr)
                .ok_or_else(|| format!("L{layer_idx}: alias dst {dst_addr:?} not resident"))?;
            if sp == dp {
                continue; // same device pointer: trivially aliased
            }
            let src = d2h_col_lifted(sp as u64, se4, t, context);
            let dst = d2h_col_lifted(dp as u64, de4, t, context);
            compare_columns(
                &format!("L{layer_idx} G-ALIAS root {rid:?} ({src_addr:?} -> {dst_addr:?})"),
                &src,
                &dst,
            )?;
        }
    }

    for residency in [InterpResidency::Ldg, InterpResidency::Ldc] {
        let mut setup = build_fwd_vm_device_setup(fixture, c, layer_idx);
        if residency == InterpResidency::Ldc {
            let fits = super::super::upload_bench_program_to_constant(&setup.lanes)
                .map_err(|e| format!("L{layer_idx} [Ldc] constant upload: {e:?}"))?;
            if !fits {
                // Corpus-wide this never triggers (max observed 10911/14336
                // lanes), so an unexpected non-fit would otherwise silently
                // halve LDC residency coverage with no trace in the output.
                eprintln!(
                    "[fwd_vm G-DEV] WARNING: layer {layer_idx} program {} lanes exceeds LDC {BENCH_INTERP_PROGRAM_LDC_LANES} — skipping LDC residency",
                    setup.lanes.len()
                );
                continue; // program exceeds the 28 KB constant array
            }
            setup.desc.program_ldg = ptr::null();
        }

        super::launch_fwd_vm(&setup.desc, residency, context)
            .map_err(|e| format!("L{layer_idx} [{residency:?}] launch: {e:?}"))?;
        context
            .get_exec_stream()
            .synchronize()
            .map_err(|e| format!("L{layer_idx} [{residency:?}] sync: {e:?}"))?;

        // Fail-closed gate: the kernel must have raised no FWDVM_ERR_* bit.
        let err = d2h_raw::<u32>(setup.desc.error_flag as *const u32, 1, context, 0u32)[0];
        if err != 0 {
            return Err(format!("L{layer_idx} [{residency:?}]: kernel error_flag = {err:#x}"));
        }

        // G-DEV part 1: smem-rooted epilogue outputs vs their flat goldens
        // (index-aligned with out_ptr/out_is_e4, lower.rs build order).
        let n_outs = setup.desc.n_outs as usize;
        if n_outs > 0 {
            let ptr_back = d2h_raw::<u64>(setup.desc.out_ptr as *const u64, n_outs, context, 0u64);
            let e4_back = d2h_raw::<u8>(setup.desc.out_is_e4, n_outs, context, 0u8);
            for i in 0..n_outs {
                let is_e4 = e4_back[i] != 0;
                let got = d2h_col_lifted(ptr_back[i], is_e4, t, context);
                let want = d2h_col_lifted(setup.out_golden_ptr[i], is_e4, t, context);
                compare_columns(
                    &format!("L{layer_idx} [{residency:?}] G-DEV smem-out {i}"),
                    &got,
                    &want,
                )?;
            }
        }

        // G-DEV part 2: materialized (slot,col) overlay columns vs the flat
        // columns at the same backing address.
        let total_cols = setup.desc.col_base[16] as usize;
        let read_back =
            d2h_raw::<u64>(setup.desc.col_read_ptr as *const u64, total_cols, context, 0u64);
        for (&(slot, col), &field) in &usage.materialized {
            let idx = (setup.desc.col_base[slot as usize] + col as u32) as usize;
            let overlay_e4 = field == OperandField::Ext;
            let key = cl
                .ctx
                .backings
                .backing(slot)
                .unwrap_or_else(|| panic!("L{layer_idx}: no backing for slot {slot}"));
            let addr = backing_key_col_to_gkr_address(key, col)
                .expect("materialized (slot,col) must map to a GKRAddress");
            let (flat_e4, flat_ptr) = fixture.storage_column(addr).ok_or_else(|| {
                format!("L{layer_idx}: materialized {addr:?} not resident in flat storage")
            })?;
            let got = d2h_col_lifted(read_back[idx], overlay_e4, t, context);
            let want = d2h_col_lifted(flat_ptr as u64, flat_e4, t, context);
            compare_columns(
                &format!(
                    "L{layer_idx} [{residency:?}] G-DEV overlay (slot {slot}, col {col}) {addr:?}"
                ),
                &got,
                &want,
            )?;
        }
    }

    Ok(())
}
