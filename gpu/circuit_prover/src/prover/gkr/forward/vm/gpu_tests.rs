//! Task 10: the fwd-VM v2 GPU bit-exact parity gate — the authoritative value
//! gate for the v2 wire format, descriptor lowering, and both CUDA kernels.
//!
//! For each of the 3 GPU circuits, every compiled layer:
//! 1. Build the REAL prover fixture (`bench_interp::fixture::CircuitFixture` —
//!    the production forward preamble + a capturing flat pass, so the
//!    consolidated storage matrices, stage-1 mapping arenas, generic-lookup
//!    table, and decoder fill slot are all the true production buffers).
//! 2. Compile via the production stage-3 chain (committed b16 schedule) and
//!    lower via `lower_layer_desc` with a resolver over the REAL
//!    `GpuGKRStorage` consolidated matrices (true per-column `(base, stride)`).
//! 3. Launch `ab_gkr_fwd_vm_validate_kernel`; assert `error_flag == 0`.
//! 4. Compare every materialized column bit-exactly against the FLAT PRODUCTION
//!    forward outputs — the same storage the flat/generated forward codegen
//!    wrote during the capturing pass, snapshotted D2H BEFORE the VM runs.
//! 5. Launch the release `ab_gkr_fwd_vm_s4_kernel`, same comparison (proves
//!    the VALIDATE/release split changes nothing).
//!
//! Oracle isolation: the v2 kernel writes `GlobalMaterialize` columns DIRECTLY
//! into the production storage matrices (`base[slot] + col * stride`), i.e.
//! into the very columns the flat oracle produced. The gate therefore
//! snapshots each materialized column to host FIRST (the immutable oracle),
//! then overwrites the device column with a poison pattern before EVERY
//! launch, so a kernel that silently writes nothing (or misses a column)
//! compares poison-vs-oracle and fails. A passing kernel leaves the storage
//! bit-identical to the flat values, so later layers still read correct
//! inputs.
//!
//! Gated `cfg(all(test, feature = "bench"))` because the harness it mines
//! (`CircuitFixture`, the compile chain, `challenge_value`) lives in the
//! bench-gated `bench_interp` tree; the production `vm/` code itself and its
//! CPU-only tests (`vm/tests.rs`) stay ungated. The kernels under test are
//! production symbols (`fwd_vm.cu` compiles unconditionally), not bench ones.
//!
//! Tests are exempt from the `crate::upstream` import rule (AGENTS.md).

use std::collections::BTreeSet;
use std::mem::size_of;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;

use cs::definitions::GKRAddress;
use gkr_eval_isa::fwd::compile::layer_needs_compile;
use gkr_eval_isa::fwd::context::{CompiledLayer, OutputCell, RootOutput};
use gkr_eval_isa::fwd::isa::{DstLine, Instr, LdcSub};

use super::desc::CONST_CHALLENGE_CAP;
use super::lower::{
    lower_layer_desc, read_place_to_gkr_address, FwdVmHeaderInputs, ResolvedColumn,
};
use super::{launch_fwd_vm_s4, launch_fwd_vm_validate, upload_const_challenges};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::forward::bench_interp::fixture::CircuitFixture;
use crate::prover::gkr::forward::bench_interp::fwd_vm::compile::{
    load_fwd_vm_circuit, FwdVmCircuit,
};
use crate::prover::gkr::forward::bench_interp::fwd_vm::resolvers::challenge_value;
use crate::prover::gkr::forward::bench_interp::fwd_vm::resolvers::fixture_stage1;
use crate::prover::ProverContext;

/// Poison bit pattern written over every materialized destination column
/// before each launch: a lazy/no-op kernel compares poison-vs-oracle and
/// fails instead of vacuously passing on stale flat values.
const POISON_U32: u32 = 0x5EED_DEAD;

// ── raw word transfers (test-only: blocking D2H/H2D is fine here) ────────────

fn d2h_words(ptr: *const u32, n: usize, ctx: &ProverContext) -> Vec<u32> {
    let mut host = vec![0u32; n];
    // SAFETY: `ptr` is a resident storage column of at least `n` u32 words
    // (t rows × 1 (BF) or 4 (E4) words, from `storage_column`).
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr, n) };
    memory_copy_async(&mut host, slice, ctx.get_exec_stream()).unwrap();
    ctx.get_exec_stream().synchronize().unwrap();
    host
}

fn h2d_words(ptr: *mut u32, words: &[u32], ctx: &ProverContext) {
    // SAFETY: as `d2h_words`, mutable: the gate owns the fixture and poisons
    // only columns it snapshotted first.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(ptr, words.len()) };
    memory_copy_async(slice, words, ctx.get_exec_stream()).unwrap();
    ctx.get_exec_stream().synchronize().unwrap();
}

// ── production storage resolver (the Task-9 seam, wired to the real thing) ───

/// Resolve a flat `GKRAddress` to its REAL consolidated-matrix column: the
/// storage poly view's backing allocation is the matrix (`matrix_base`), the
/// view's `offset`/`len` give the column pointer and the inter-column stride
/// (`views.rs`: column `poly_idx` at `offset = poly_idx << log2_stride`,
/// `len = 1 << log2_stride`). Soundness does not hinge on `len` being the
/// "true" stride: the lowering re-derives `matrix_col = (ptr - base) / stride`
/// and the kernel reads `base + matrix_col * stride` — exact by construction —
/// with off-stride / collision / geometry mismatches all hard lowering errors.
pub(crate) fn resolve_storage_column(
    fixture: &CircuitFixture,
    addr: GKRAddress,
) -> Option<ResolvedColumn> {
    if let Some(p) = fixture.storage.try_get_base_poly(addr) {
        return Some(ResolvedColumn {
            is_e4: false,
            ptr: p.as_ptr() as *const u8,
            matrix_base: p.backing.as_ptr() as *mut u8,
            stride_bytes: (p.len * size_of::<BF>()) as u32,
        });
    }
    fixture
        .storage
        .try_get_ext_poly(addr)
        .map(|p| ResolvedColumn {
            is_e4: true,
            ptr: p.as_ptr() as *const u8,
            matrix_base: p.backing.as_ptr() as *mut u8,
            stride_bytes: (p.len * size_of::<E4>()) as u32,
        })
}

/// Per-layer header inputs from the REAL prover buffers: the 3 stage-1 mapping
/// arenas (column-major, column stride = trace_len), the decoder mapping
/// column (`num_generic_sets`), the shared α-folded generic-lookup table, and
/// the production 1-element `device_decoder_lookup_fill_value` slot.
pub(crate) fn build_header(fixture: &CircuitFixture) -> FwdVmHeaderInputs {
    let stage1 = fixture_stage1(fixture);
    let m = &stage1.lookup_mappings;
    assert_eq!(
        m.trace_len, fixture.trace_len,
        "mapping-arena column stride != trace_len"
    );
    let forward_setup = fixture.keepalive.forward_setup();
    let (table_ptr, table_len) = fixture.setup_table();
    FwdVmHeaderInputs {
        mapping_arena: [
            if m.has_generic_family() {
                m.generic_family().as_ptr()
            } else {
                std::ptr::null()
            },
            if m.has_range_check_16() {
                m.range_check_16().as_ptr()
            } else {
                std::ptr::null()
            },
            if m.has_timestamp() {
                m.timestamp().as_ptr()
            } else {
                std::ptr::null()
            },
        ],
        decoder_mapping_col: m
            .has_decoder
            .then(|| u16::try_from(m.num_generic_sets).expect("num_generic_sets exceeds u16")),
        table: table_ptr as *const E4,
        table_len,
        fill: forward_setup.decoder_lookup_fill_value_device().as_ptr(),
        count: fixture.trace_len as u32,
    }
}

// ── materialized destination set + flat-oracle snapshot ──────────────────────

/// One materialized destination column: the dense `(slot, col)` its
/// `GlobalMaterialize` writes, the flat storage address behind it, the raw
/// device pointer, its field width, and the host snapshot of the flat oracle
/// values (captured BEFORE any VM launch).
struct MaterializedColumn {
    slot: u8,
    col: u16,
    addr: GKRAddress,
    ptr: *mut u32,
    is_e4: bool,
    oracle: Vec<u32>,
}

/// Collect every `GlobalMaterialize` destination of the compiled program
/// (dense `(slot, col)` domain), cross-check the set against the compiler's
/// `RootOutput::Cell(Global)` roots (the two are emitted together — a
/// divergence is a harness/compiler bug), resolve each through the backing
/// table's reverse map to its flat address, and snapshot the flat oracle.
fn snapshot_materialized(
    fixture: &CircuitFixture,
    cl: &CompiledLayer,
    layer_idx: usize,
) -> Vec<MaterializedColumn> {
    let mut dsts: BTreeSet<(u8, u16)> = BTreeSet::new();
    for instr in &cl.program.instrs {
        if let Instr::Mov {
            dst: Some(DstLine::GlobalMaterialize { slot, col }),
            ..
        } = instr
        {
            dsts.insert((*slot, *col));
        }
    }
    let mut root_globals: BTreeSet<(u8, u16)> = BTreeSet::new();
    for (_, out) in &cl.root_outputs {
        if let RootOutput::Cell(OutputCell::Global { slot, col }) = out {
            root_globals.insert((*slot, *col));
        }
    }
    assert_eq!(
        dsts, root_globals,
        "L{layer_idx}: GlobalMaterialize dsts and RootOutput::Cell(Global) roots disagree"
    );

    let t = fixture.trace_len;
    let ctx = fixture.context();
    dsts.into_iter()
        .map(|(slot, col)| {
            let place = cl
                .ctx
                .backings
                .slot_col_to_read_place(slot, col)
                .unwrap_or_else(|| {
                    panic!("L{layer_idx}: materialized (slot {slot}, col {col}) has no reverse map")
                });
            let addr = read_place_to_gkr_address(&place);
            let (is_e4, ptr) = fixture.storage_column(addr).unwrap_or_else(|| {
                panic!("L{layer_idx}: materialized {addr:?} not resident in flat storage")
            });
            let words = if is_e4 { 4 * t } else { t };
            let oracle = d2h_words(ptr as *const u32, words, ctx);
            MaterializedColumn {
                slot,
                col,
                addr,
                ptr: ptr as *mut u32,
                is_e4,
                oracle,
            }
        })
        .collect()
}

fn poison_columns(fixture: &CircuitFixture, cols: &[MaterializedColumn]) {
    let ctx = fixture.context();
    for c in cols {
        h2d_words(c.ptr, &vec![POISON_U32; c.oracle.len()], ctx);
    }
}

/// Bit-exact comparison of every materialized column against its flat-oracle
/// snapshot; panics with circuit/layer/kernel/column + first divergent row.
fn assert_columns_match(
    fixture: &CircuitFixture,
    cols: &[MaterializedColumn],
    stem: &str,
    layer_idx: usize,
    kernel: &str,
) -> usize {
    let ctx = fixture.context();
    let mut words_checked = 0usize;
    for c in cols {
        let got = d2h_words(c.ptr as *const u32, c.oracle.len(), ctx);
        if let Some(w) = got.iter().zip(c.oracle.iter()).position(|(g, o)| g != o) {
            let row = if c.is_e4 { w / 4 } else { w };
            panic!(
                "{stem} L{layer_idx} [{kernel}]: (slot {}, col {}) {:?} diverges at row {row} \
                 (word {w}): vm {:#010x} != flat {:#010x}{}",
                c.slot,
                c.col,
                c.addr,
                got[w],
                c.oracle[w],
                if got[w] == POISON_U32 {
                    " (vm word is POISON — column never written)"
                } else {
                    ""
                },
            );
        }
        words_checked += got.len();
    }
    words_checked
}

// ── the gate ──────────────────────────────────────────────────────────────────

/// Values of the layer's `ConstChallenge` bank, via the SAME `ChallengeRef`
/// mapping the flat fixture/G-CPU harness uses (`challenge_value`).
pub(crate) fn const_challenge_values(fixture: &CircuitFixture, cl: &CompiledLayer) -> Vec<E4> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(r) = cl.ctx.challenges.get(LdcSub::ConstChallenge, i as u16) {
        out.push(challenge_value(fixture, r));
        i += 1;
        assert!(i <= CONST_CHALLENGE_CAP, "const-challenge bank exceeds cap");
    }
    out
}

/// Run the full v2 parity gate for one circuit: every compiled layer, both
/// kernels (VALIDATE first — its `error_flag` separates malformed-program/desc
/// bugs from value bugs — then the release s4 instantiation).
pub(crate) fn run_vm_parity(stem: &str) {
    let fixture = CircuitFixture::build(stem);
    let c: FwdVmCircuit = load_fwd_vm_circuit(stem);
    let context = fixture.context();
    assert_eq!(c.compiled.budget, 16, "{stem}: committed corpus budget");
    let header = build_header(&fixture);

    let mut layers_gated = 0usize;
    let mut cols_checked = 0usize;
    let mut words_checked = 0usize;
    for (li, layer) in c.dag.layers.iter().enumerate() {
        if !layer_needs_compile(c.sched.layers[li].units.is_empty(), layer) {
            continue;
        }
        let cl = &c.compiled.layers[li];

        // Production lowering against the REAL consolidated storage matrices.
        let resolve = |addr: GKRAddress| resolve_storage_column(&fixture, addr);
        let challenge = |r: &_| challenge_value(&fixture, r);
        let setup = lower_layer_desc(cl, &header, &resolve, &challenge, None)
            .unwrap_or_else(|e| panic!("{stem} L{li}: lower_layer_desc failed: {e:?}"));
        assert!(
            setup.desc.program_ldg.is_null(),
            "{stem} L{li}: corpus program unexpectedly overflowed inline cap"
        );
        upload_const_challenges(&const_challenge_values(&fixture, cl), context)
            .unwrap_or_else(|e| panic!("{stem} L{li}: const-challenge upload: {e:?}"));

        // Flat oracle snapshot BEFORE any VM launch (the kernel writes into
        // the very storage columns the flat pass produced).
        let cols = snapshot_materialized(&fixture, cl, li);
        assert!(
            !cols.is_empty(),
            "{stem} L{li}: no materialized columns — vacuous"
        );

        let mut err_dev: DeviceAllocation<u32> =
            context.alloc(1, AllocationPlacement::Top).unwrap();
        memory_copy_async(&mut err_dev[0..1], &[0u32], context.get_exec_stream()).unwrap();

        // ── VALIDATE kernel: fail-closed flag, then bit-exact columns. ──
        poison_columns(&fixture, &cols);
        launch_fwd_vm_validate(&setup, cl.budget as u32, err_dev.as_mut_ptr(), context)
            .unwrap_or_else(|e| panic!("{stem} L{li}: validate launch: {e:?}"));
        context.get_exec_stream().synchronize().unwrap();
        let err = d2h_words(err_dev.as_ptr(), 1, context)[0];
        assert_eq!(
            err, 0,
            "{stem} L{li}: VALIDATE kernel error_flag = {err:#x} (malformed program/desc — \
             a different bug class than a value mismatch)"
        );
        words_checked += assert_columns_match(&fixture, &cols, stem, li, "validate");

        // ── Release s4 kernel: same oracle, fresh poison. ──
        poison_columns(&fixture, &cols);
        launch_fwd_vm_s4(&setup, cl.budget as u32, context)
            .unwrap_or_else(|e| panic!("{stem} L{li}: s4 launch: {e:?}"));
        context.get_exec_stream().synchronize().unwrap();
        words_checked += assert_columns_match(&fixture, &cols, stem, li, "s4");

        cols_checked += cols.len();
        layers_gated += 1;
        eprintln!(
            "[fwdvm-v2-parity] {stem} L{li}: {} materialized columns bit-exact (validate + s4)",
            cols.len()
        );
    }
    assert!(
        layers_gated > 0,
        "{stem}: no compiled layers gated — vacuous"
    );
    eprintln!(
        "[fwdvm-v2-parity] {stem}: {layers_gated} layers, {cols_checked} columns, \
         {words_checked} words bit-exact across both kernels"
    );
}

#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_v2_parity_add_sub() {
    run_vm_parity("add_sub_lui_auipc_mop");
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_v2_parity_bigint() {
    run_vm_parity("bigint_with_extended_control");
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_v2_parity_blake2() {
    run_vm_parity("blake2_with_extended_control");
}
