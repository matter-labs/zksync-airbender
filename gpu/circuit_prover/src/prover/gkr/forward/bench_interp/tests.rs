use super::lower::{
    lincomb_bf, lower_payloads, lower_program, mem_tuple_affine, output_widths, payload_dst_e4,
    payload_kind_shape, vec_lookup_affine, BenchChallenges, LoweredPayloads, LoweredProgram,
};
use super::{
    launch_bench_fwd_interp, upload_bench_program_to_constant, InterpDesc, InterpResidency,
};

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResultWrap;
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::cudaGetSymbolAddress;
use field::Field;
use serial_test::serial;
use std::ffi::c_void;
use std::ptr;

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn bench_stub_kernel_roundtrip() {
    use super::launch_bench_fwd_interp_smoke;

    let context = make_test_context(256, 32);
    let count = 256usize;
    let values = (0..count as u32).map(BF::new).collect::<Vec<_>>();

    let mut src_dev = context.alloc(count, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut src_dev, &values, context.get_exec_stream()).unwrap();
    let mut dst_dev = context.alloc(count, AllocationPlacement::Top).unwrap();

    launch_bench_fwd_interp_smoke(src_dev.as_ptr(), dst_dev.as_mut_ptr(), count, &context).unwrap();

    let mut host = vec![BF::ZERO; count];
    memory_copy_async(&mut host, &dst_dev, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(host, values);
}

// ---------------------------------------------------------------------------
// FULL GPU<->CPU interpreter parity on synthetic staged sources (Task 4).
//
// The CPU interpreter treats NativeK payloads as uninterpreted functions
// (sentinels for caches); here the TRUE values are computed on the host —
// `mirror_gate` / `mirror_cache` below mirror each device routine's math and
// double as the payload-ABI documentation — fed to the CPU run as cache
// sentinels, and compared against the GPU's real payload-routine outputs:
// every payload dst column, the cache alias cells (via the cell-file dump),
// and the program outputs.
// ---------------------------------------------------------------------------

use cs::gkr_compiler::codegen_ir::{CacheKind, CodegenCache, CodegenGate, CodegenLayer, GateKind};
use gkr_design_space::import::load_circuit;
use gkr_eval_isa::compiler::fwd::{
    compile_forward, fwd_eligible, CompiledForward, FwdParams, PayloadRecord,
};
use gkr_eval_isa::eval_ref::{lift, random_row, Bf, Ext, RowAssignment};
use gkr_eval_isa::interp::{execute, ExecResult, StagedSources};
use gkr_eval_isa::isa::Op;
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::panic::{catch_unwind, AssertUnwindSafe};

const PARITY_TRACE_LEN: usize = 1024;

/// Replicated from gkr_eval_isa/tests/oracle_forward_native.rs:35-40 (Task 6
/// of the stage-3 plan consolidates both copies into a test_support module).
fn base_part(v: Ext) -> Bf {
    use field::FieldExtension;
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    assert!(
        coeffs[1..].iter().all(|c| c.is_zero()),
        "bf source holds non-base value"
    );
    coeffs[0]
}

fn rand_bf(rng: &mut StdRng) -> Bf {
    use field::PrimeField;
    Bf::from_u32_with_reduction(rng.random::<u32>())
}

fn rand_e4(rng: &mut StdRng) -> Ext {
    use field::FieldExtension;
    <Ext as FieldExtension<Bf>>::from_coeffs([
        rand_bf(rng),
        rand_bf(rng),
        rand_bf(rng),
        rand_bf(rng),
    ])
}

fn mont(c: u32) -> Bf {
    use field::PrimeField;
    Bf::from_u32_with_reduction(c)
}

/// Random nonzero challenge set, mirrored to the GPU payload records and
/// `ab_gkr_lookup_gamma_consts`. `Ext` and the crate's `E4` are the same
/// type (BabyBearExt4), so the values flow into `BenchChallenges` directly.
fn random_challenges(rng: &mut StdRng) -> BenchChallenges {
    BenchChallenges {
        gamma: rand_e4(rng),
        alpha: rand_e4(rng),
        perm_challenges: std::array::from_fn(|_| rand_e4(rng)),
        perm_additive: rand_e4(rng),
        decoder_fill: rand_e4(rng),
    }
}

/// Test-owned synthetic inputs the IR lanes do not carry: the decoder
/// execute-predicate value (constant-fill bf column on device) and the
/// VectorizedLookupSetup table value (constant-fill e4 column on device).
struct SyntheticExtras {
    exec_val: Bf,
    setup_value: Ext,
}

// ---------------------------------------------------------------------------
// Gamma constants upload: the bench routines read the production
// `__constant__ ab_gkr_lookup_gamma_consts` (flat.cuh:5). Pattern from
// generated_layer0_parity.rs `set_const_e4`.
// ---------------------------------------------------------------------------

extern "C" {
    static ab_gkr_lookup_gamma_consts: [E4; 3];
}

fn set_gamma_consts(ch: &BenchChallenges, context: &ProverContext) {
    let mut device_ptr: *mut c_void = ptr::null_mut();
    // SAFETY: ab_gkr_lookup_gamma_consts is a valid __constant__ e4[3]
    // defined in native/prover/gkr/forward/flat_layer.cu (always linked).
    unsafe {
        cudaGetSymbolAddress(
            &mut device_ptr,
            &ab_gkr_lookup_gamma_consts as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_lookup_gamma_consts");
    // SAFETY: the constant storage holds exactly 3 E4 elements.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(device_ptr as *mut E4, 3) };
    memory_copy_async(slice, &ch.gamma_consts()[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
}

// ---------------------------------------------------------------------------
// Host mirror of the device payload routines. Operand values arrive in
// canonical lane order (`payload_operands` = `gate_kind_input_nodes`, MQ expr
// lane dropped), lifted to Ext exactly like the CPU interpreter's NativeFire
// vals; bf-typed device routines (e.g. gkr_eval_lookup_base_pair_v2) compute
// the same values in the base subring, so Ext math here is the reference.
// ---------------------------------------------------------------------------

fn ext_mul(a: Ext, b: Ext) -> Ext {
    let mut r = a;
    r.mul_assign(&b);
    r
}

fn ext_add(a: Ext, b: Ext) -> Ext {
    let mut r = a;
    r.add_assign(&b);
    r
}

fn ext_sub(a: Ext, b: Ext) -> Ext {
    let mut r = a;
    r.sub_assign(&b);
    r
}

/// `constant + sum_k coeffs[k] * vals[k]` — the device `eval_affine_e4`.
fn affine_eval((constant, coeffs): (Ext, Vec<Ext>), vals: &[Ext]) -> Ext {
    assert_eq!(coeffs.len(), vals.len(), "affine arity mismatch");
    let mut acc = constant;
    for (c, v) in coeffs.iter().zip(vals) {
        acc.add_assign(&ext_mul(*c, *v));
    }
    acc
}

/// Mirror of every GATE routine the kernel dispatches (kind->routine table in
/// native/bench/gkr_fwd_interp.cu). Returns one value per dst slot.
fn mirror_gate(
    g: &CodegenGate,
    vals: &[Ext],
    ch: &BenchChallenges,
    extras: &SyntheticExtras,
) -> Vec<Ext> {
    let gamma = ch.gamma;
    let sh = |v: Ext| ext_add(v, gamma); // the routines' `E::add(x, gamma)` shift
    match &g.kind {
        // gkr_eval_product (lookup_helpers.cuh:217).
        GateKind::TrivialProduct { .. } | GateKind::InitialGrandProductFromCaches { .. } => {
            vec![ext_mul(vals[0], vals[1])]
        }
        // gkr_eval_mask_identity (lookup_helpers.cuh:219-223): (v-1)*m + 1;
        // lanes [input(v), mask(m)].
        GateKind::MaskIntoIdentityProduct { .. } => {
            let r = ext_mul(ext_sub(vals[0], Ext::ONE), vals[1]);
            vec![ext_add(r, Ext::ONE)]
        }
        // gkr_eval_lookup_pair (lookup_helpers.cuh:229): num = a*d + c*b,
        // den = b*d; lanes [a, b, c, d] = input[0] ++ input[1].
        GateKind::AggregateLookupRationalPair { .. } => {
            let (a, b, c, d) = (vals[0], vals[1], vals[2], vals[3]);
            vec![ext_add(ext_mul(a, d), ext_mul(c, b)), ext_mul(b, d)]
        }
        // gkr_eval_lookup_base_pair_v2 / gkr_eval_lookup_ext_pair
        // (lookup_helpers.cuh:242/250): num = (b+g)+(d+g), den = (b+g)(d+g).
        GateKind::LookupPairFromMaterializedBaseInputs { .. }
        | GateKind::LookupPairFromMaterializedVectorInputs { .. } => {
            let (b, d) = (sh(vals[0]), sh(vals[1]));
            vec![ext_add(b, d), ext_mul(b, d)]
        }
        // gkr_eval_lookup_base_minus_multiplicity[_v2] (lookup_helpers.cuh:268/276):
        // num = (d+g) - c*(b+g), den = (b+g)(d+g); lanes [input(b), setup0(c), setup1(d)].
        GateKind::LookupFromMaterializedBaseInputWithSetup { .. }
        | GateKind::LookupFromMaterializedVectorInputWithSetup { .. } => {
            let (b, c, d) = (sh(vals[0]), vals[1], sh(vals[2]));
            vec![ext_sub(d, ext_mul(c, b)), ext_mul(b, d)]
        }
        // gkr_eval_lookup_cached_dens_and_setup (lookup_helpers.cuh:313):
        // num = a*(d+g) - c*(b+g), den = (b+g)(d+g); lanes [a, b, c, d].
        GateKind::LookupWithCachedDensAndSetup { .. } => {
            let (a, b, c, d) = (vals[0], sh(vals[1]), vals[2], sh(vals[3]));
            vec![ext_sub(ext_mul(a, d), ext_mul(c, b)), ext_mul(b, d)]
        }
        // gkr_eval_lookup_unbalanced (lookup_helpers.cuh:300): num = a*(d+g)+b,
        // den = b*(d+g); lanes [input0(a), input1(b), remainder(d)].
        GateKind::LookupUnbalancedPairWithMaterializedBaseInputs { .. }
        | GateKind::LookupUnbalancedPairWithMaterializedVectorInputs { .. } => {
            let (a, b, d) = (vals[0], vals[1], sh(vals[2]));
            vec![ext_add(ext_mul(a, d), b), ext_mul(b, d)]
        }
        // Alpha-folded affine form (emit_vectorized_lookup math), value-injected.
        GateKind::MaterializedVectorLookupInput { input } => {
            let mut v = affine_eval(vec_lookup_affine(&input.columns, ch), vals);
            if input.lookup_set_index == usize::MAX && extras.exec_val.is_zero() {
                v = ch.decoder_fill;
            }
            vec![v]
        }
        // Factored flat form: sum_q a_q * (sum_s c_qs * b_qs) + sum_l c_l * v_l
        // + constant; lane cursor pairs with payload_operands order.
        GateKind::MaxQuadratic { flat, .. } => {
            let mut acc = lift(mont(flat.constant));
            let mut cur = 0usize;
            for (_a, terms) in &flat.quadratic {
                let a = vals[cur];
                cur += 1;
                let mut inner = Ext::ZERO;
                for &(c, _b) in terms {
                    inner.add_assign(&ext_mul(lift(mont(c)), vals[cur]));
                    cur += 1;
                }
                acc.add_assign(&ext_mul(a, inner));
            }
            for &(c, _a) in &flat.linear {
                acc.add_assign(&ext_mul(lift(mont(c)), vals[cur]));
                cur += 1;
            }
            assert_eq!(cur, vals.len(), "MQ mirror lane walk");
            vec![acc]
        }
        other => panic!(
            "mirror_gate: kind outside the census: {:?}",
            std::mem::discriminant(other)
        ),
    }
}

/// Mirror of every CACHE routine (gkr_forward_cache switch arms,
/// lookup_helpers.cuh:39-83, in their IR/value-injected form).
fn mirror_cache(
    c: &CodegenCache,
    vals: &[Ext],
    ch: &BenchChallenges,
    extras: &SyntheticExtras,
) -> Ext {
    match &c.kind {
        // bf lincomb (emit_lincomb_base) == production setup_values[mapping[gid]].
        CacheKind::SingleColumnLookup { column, .. } => {
            let (constant, coeffs) = lincomb_bf(column);
            affine_eval(
                (lift(constant), coeffs.into_iter().map(lift).collect()),
                vals,
            )
        }
        // Alpha-folded tuple + decoder fill select (lookup_helpers.cuh:58-69).
        CacheKind::VectorizedLookup {
            columns,
            lookup_set_index,
        } => {
            let v = affine_eval(vec_lookup_affine(columns, ch), vals);
            if *lookup_set_index == usize::MAX && extras.exec_val.is_zero() {
                ch.decoder_fill
            } else {
                v
            }
        }
        // Challenge-folded affine form (gkr_forward_cache_memory_tuple).
        CacheKind::MemoryTuple { descriptor } => {
            affine_eval(mem_tuple_affine(descriptor, ch), vals)
        }
        // generic_lookup[gid] gather; the synthetic table is constant-fill so
        // the row-independent mirror value is exact (lookup_helpers.cuh:70-74).
        CacheKind::VectorizedLookupSetup => extras.setup_value,
    }
}

/// True cache values in dependency order (a cache operand may alias another
/// cache's out-cell; `ensure_cache` fires producers first, so plain recursion
/// over `cached_alias` terminates).
fn node_value(
    node: usize,
    layer: &CodegenLayer,
    cf: &CompiledForward,
    row: &RowAssignment,
    ch: &BenchChallenges,
    extras: &SyntheticExtras,
    memo: &mut Vec<Option<Ext>>,
) -> Ext {
    if let Some(&ci) = cf.cached_alias.get(&node) {
        return cache_value(ci as usize, layer, cf, row, ch, extras, memo);
    }
    if let cs::gkr_compiler::codegen_ir::ExprNode::Constant(c) = &layer.arena.nodes[node] {
        return lift(mont(*c));
    }
    row.leaf_vals[node].expect("leaf without a staged value")
}

fn cache_value(
    ci: usize,
    layer: &CodegenLayer,
    cf: &CompiledForward,
    row: &RowAssignment,
    ch: &BenchChallenges,
    extras: &SyntheticExtras,
    memo: &mut Vec<Option<Ext>>,
) -> Ext {
    if let Some(v) = memo[ci] {
        return v;
    }
    let nodes = cf.payload_operands[ci].clone();
    let vals: Vec<Ext> = nodes
        .iter()
        .map(|&n| node_value(n, layer, cf, row, ch, extras, memo))
        .collect();
    let v = match &cf.payloads[ci] {
        PayloadRecord::Cache(c) => mirror_cache(c, &vals, ch, extras),
        PayloadRecord::Gate(_) => unreachable!("payload {ci} in cache range is a gate"),
    };
    memo[ci] = Some(v);
    v
}

// ---------------------------------------------------------------------------
// Payload dst-buffer layout. Built over the UNFILTERED payload enumeration so
// the equal-work (MaxQuadratic-filtered) row shares the exact buffer layout —
// the filtered run must leave the MQ columns untouched (asserted).
// ---------------------------------------------------------------------------

fn unfiltered_records(layer: &CodegenLayer) -> Vec<PayloadRecord> {
    let mut recs: Vec<PayloadRecord> = layer
        .caches
        .iter()
        .map(|c| PayloadRecord::Cache(c.clone()))
        .collect();
    recs.extend(
        layer
            .gates
            .iter()
            .chain(&layer.gates_external)
            .filter(|g| fwd_eligible(g))
            .map(|g| PayloadRecord::Gate(g.clone())),
    );
    recs
}

struct PayloadDstLayout {
    /// Per unfiltered record: per dst slot j -> (e4, packed column index).
    slots: Vec<Vec<(bool, usize)>>,
    n_bf_cols: usize,
    n_e4_cols: usize,
    /// Unfiltered record indices that are MaxQuadratic gates (the columns the
    /// equal-work row must leave untouched).
    mq_records: Vec<usize>,
}

fn build_dst_layout(records: &[PayloadRecord]) -> PayloadDstLayout {
    let (mut n_bf, mut n_e4) = (0usize, 0usize);
    let mut slots = Vec::with_capacity(records.len());
    let mut mq_records = Vec::new();
    for (r, rec) in records.iter().enumerate() {
        let (_, n_dsts, _) = payload_kind_shape(rec);
        let mut per = Vec::with_capacity(n_dsts);
        for j in 0..n_dsts {
            let e4 = payload_dst_e4(rec, j);
            let col = if e4 { &mut n_e4 } else { &mut n_bf };
            per.push((e4, *col));
            *col += 1;
        }
        slots.push(per);
        if matches!(rec, PayloadRecord::Gate(g) if matches!(g.kind, GateKind::MaxQuadratic { .. }))
        {
            mq_records.push(r);
        }
    }
    PayloadDstLayout {
        slots,
        n_bf_cols: n_bf,
        n_e4_cols: n_e4,
        mq_records,
    }
}

/// cf payload index -> unfiltered record index (replays the equal-work filter).
fn payload_record_map(layer: &CodegenLayer, cf: &CompiledForward, exclude_mq: bool) -> Vec<usize> {
    let mut map: Vec<usize> = (0..layer.caches.len()).collect();
    let mut r = layer.caches.len();
    for g in layer.gates.iter().chain(&layer.gates_external) {
        if !fwd_eligible(g) {
            continue;
        }
        if !(exclude_mq && matches!(g.kind, GateKind::MaxQuadratic { .. })) {
            map.push(r);
        }
        r += 1;
    }
    assert_eq!(map.len(), cf.payloads.len(), "payload->record map size");
    map
}

// ---------------------------------------------------------------------------
// Parity point construction + checks.
// ---------------------------------------------------------------------------

fn alloc_upload<T>(context: &ProverContext, host: &[T]) -> DeviceAllocation<T> {
    let mut dev: DeviceAllocation<T> = context
        .alloc(host.len().max(1), AllocationPlacement::Top)
        .unwrap();
    if !host.is_empty() {
        memory_copy_async(&mut dev[0..host.len()], host, context.get_exec_stream()).unwrap();
    }
    dev
}

struct ParityPoint<'a> {
    context: &'a ProverContext,
    label: String,
    cf: CompiledForward,
    cpu: ExecResult,
    lowered: LoweredProgram,
    /// Mirror outputs per cf payload (one value per dst slot).
    expected: Vec<Vec<Ext>>,
    /// cf payload idx -> unfiltered record idx; layout over the records.
    record_map: Vec<usize>,
    layout: PayloadDstLayout,
    // Device allocations backing the lowered pointers (kept alive for the
    // duration of the launches; test code, synchronous by design).
    _src_bf_dev: DeviceAllocation<Bf>,
    _src_e4_dev: DeviceAllocation<Ext>,
    out_bf_dev: DeviceAllocation<Bf>,
    out_e4_dev: DeviceAllocation<Ext>,
    /// (slot j, e4, column index within the bf/e4 output buffer).
    out_slots: Vec<(u16, bool, usize)>,
    payload_bf_dev: DeviceAllocation<Bf>,
    payload_e4_dev: DeviceAllocation<Ext>,
    _pred_dev: DeviceAllocation<Bf>,
    _setup_dev: DeviceAllocation<Ext>,
    payload_bytes_dev: DeviceAllocation<Ext>,
    payload_offsets_dev: DeviceAllocation<u32>,
    lanes_dev: DeviceAllocation<u16>,
    consts_dev: DeviceAllocation<BF>,
    sources_tbl_dev: DeviceAllocation<u64>,
    outputs_tbl_dev: DeviceAllocation<u64>,
    output_e4_dev: DeviceAllocation<u32>,
    /// [native_fired, error_flag].
    debug_dev: DeviceAllocation<u32>,
    /// Final cell-file dump, layout [c * t + row], budget_cells x t.
    debug_cells_dev: DeviceAllocation<Bf>,
}

fn build_parity_point<'a>(
    context: &'a ProverContext,
    label: String,
    layer: &CodegenLayer,
    cf: CompiledForward,
    exclude_mq: bool,
    seed: u64,
) -> ParityPoint<'a> {
    let t = PARITY_TRACE_LEN;
    let mut rng = StdRng::seed_from_u64(seed);

    let ch = random_challenges(&mut rng);
    let extras = SyntheticExtras {
        // Alternate the decoder predicate so both select branches get GPU
        // coverage across the sweep (a random bf is almost never zero). The
        // budgets {32, 64} flip seed bits 5/6, so bit 6 alternates per budget.
        exec_val: if (seed >> 6) & 1 == 0 {
            Bf::ZERO
        } else {
            Bf::ONE
        },
        setup_value: rand_e4(&mut rng),
    };

    // CPU reference: random staged row; cache sentinels are the TRUE cache
    // values (computed by the host mirror in dependency order), so the CPU
    // cell file / downstream operand values match the GPU's real-value runs.
    let row = random_row(&layer.arena.nodes, &mut rng);
    let mut memo: Vec<Option<Ext>> = vec![None; layer.caches.len()];
    let cache_outs: Vec<Ext> = (0..layer.caches.len())
        .map(|ci| cache_value(ci, layer, &cf, &row, &ch, &extras, &mut memo))
        .collect();
    let src = StagedSources {
        bf: cf
            .source_map
            .bf
            .iter()
            .map(|&n| base_part(row.leaf_vals[n].unwrap()))
            .collect(),
        e4: cf
            .source_map
            .e4
            .iter()
            .map(|&n| row.leaf_vals[n].unwrap())
            .collect(),
        cache_outs: cache_outs.clone(),
    };
    let cpu = execute(&cf.program, &src);

    // Mirror the payload outputs from the fired operand values. Gates fire
    // exactly once; cache (re-)fires must reproduce the staged sentinel —
    // this pins mirror/staging consistency before any GPU comparison.
    let mut expected: Vec<Option<Vec<Ext>>> = vec![None; cf.payloads.len()];
    for fire in &cpu.native_trace {
        let p = fire.payload as usize;
        let outs = match &cf.payloads[p] {
            PayloadRecord::Gate(g) => mirror_gate(g, &fire.vals, &ch, &extras),
            PayloadRecord::Cache(c) => {
                let v = mirror_cache(c, &fire.vals, &ch, &extras);
                assert_eq!(
                    v, cache_outs[p],
                    "{label}: cache {p} mirror vs staged sentinel"
                );
                vec![v]
            }
        };
        match &expected[p] {
            Some(prev) => assert_eq!(prev, &outs, "{label}: refire output diverged"),
            None => expected[p] = Some(outs),
        }
    }
    let expected: Vec<Vec<Ext>> = expected
        .into_iter()
        .enumerate()
        .map(|(p, o)| o.unwrap_or_else(|| panic!("{label}: payload {p} never fired")))
        .collect();

    // GPU staging: every row of a source column holds the same staged value.
    let mut bf_host = vec![Bf::ZERO; src.bf.len() * t];
    for (i, &v) in src.bf.iter().enumerate() {
        bf_host[i * t..(i + 1) * t].fill(v);
    }
    let mut e4_host = vec![Ext::ZERO; src.e4.len() * t];
    for (i, &v) in src.e4.iter().enumerate() {
        e4_host[i * t..(i + 1) * t].fill(v);
    }
    let src_bf_dev = alloc_upload(context, &bf_host);
    let src_e4_dev = alloc_upload(context, &e4_host);

    // Program output columns, zeroed, packed per width; slot -> column index.
    let widths = output_widths(&cf.program);
    let mut out_slots = Vec::new();
    let (mut n_out_bf, mut n_out_e4) = (0usize, 0usize);
    for &(j, _node) in &cf.outputs {
        let e4 = widths[j as usize].expect("cf.outputs slot never written");
        let col = if e4 { &mut n_out_e4 } else { &mut n_out_bf };
        out_slots.push((j, e4, *col));
        *col += 1;
    }
    let out_bf_dev = alloc_upload(context, &vec![Bf::ZERO; n_out_bf * t]);
    let out_e4_dev = alloc_upload(context, &vec![Ext::ZERO; n_out_e4 * t]);

    let lowered = lower_program(
        &cf,
        |i| unsafe { src_bf_dev.as_ptr().add(i * t) } as *const u8,
        |i| unsafe { src_e4_dev.as_ptr().add(i * t) } as *const u8,
        |j| {
            let (_, e4, col) = *out_slots
                .iter()
                .find(|&&(jj, ..)| jj == j)
                .expect("unknown output slot");
            let ptr = if e4 {
                (unsafe { out_e4_dev.as_ptr().add(col * t) }) as *mut u8
            } else {
                (unsafe { out_bf_dev.as_ptr().add(col * t) }) as *mut u8
            };
            (ptr, e4)
        },
    );

    // Payload dst buffers over the UNFILTERED layout (shared between the
    // equal-work and production-shape rows).
    let records = unfiltered_records(layer);
    let layout = build_dst_layout(&records);
    let record_map = payload_record_map(layer, &cf, exclude_mq);
    let payload_bf_dev = alloc_upload(context, &vec![Bf::ZERO; layout.n_bf_cols * t]);
    let payload_e4_dev = alloc_upload(context, &vec![Ext::ZERO; layout.n_e4_cols * t]);
    let pred_dev = alloc_upload(context, &vec![extras.exec_val; t]);
    let setup_dev = alloc_upload(context, &vec![extras.setup_value; t]);

    let lp: LoweredPayloads = lower_payloads(
        &cf,
        &layer.arena.nodes,
        |p, _rec, j| {
            let (e4, col) = layout.slots[record_map[p]][j];
            if e4 {
                (unsafe { payload_e4_dev.as_ptr().add(col * t) }) as *mut u8
            } else {
                (unsafe { payload_bf_dev.as_ptr().add(col * t) }) as *mut u8
            }
        },
        |_p, _rec| pred_dev.as_ptr() as *const u8,
        |_ci| (setup_dev.as_ptr() as *const u8, t as u32),
        &ch,
    );
    println!(
        "{label}: payload table {} bytes / {} records",
        lp.bytes.len(),
        lp.offsets.len()
    );

    // Upload the record bytes via an E4-backed allocation so the device base
    // is 16B-aligned (the e4 record fields are reinterpret-cast loads).
    let mut padded = lp.bytes.clone();
    while padded.len() % 16 != 0 {
        padded.push(0);
    }
    let bytes_e4: Vec<Ext> = padded
        .chunks_exact(16)
        // SAFETY: Ext is a plain 16-byte POD (4 Montgomery u32 limbs).
        .map(|c| unsafe { std::ptr::read_unaligned(c.as_ptr() as *const Ext) })
        .collect();
    let payload_bytes_dev = alloc_upload(context, &bytes_e4);
    let payload_offsets_dev = alloc_upload(context, &lp.offsets);

    // Upload the gamma staging triple exactly as production's prelude does.
    set_gamma_consts(&ch, context);

    let lanes_dev = alloc_upload(context, &lowered.lanes);
    let consts_dev = alloc_upload(context, &lowered.consts);
    let sources_host: Vec<u64> = lowered.source_ptrs.iter().map(|&p| p as u64).collect();
    let sources_tbl_dev = alloc_upload(context, &sources_host);
    let outputs_host: Vec<u64> = lowered.output_ptrs.iter().map(|&p| p as u64).collect();
    let outputs_tbl_dev = alloc_upload(context, &outputs_host);
    let output_e4_dev = alloc_upload(context, &lowered.output_e4);
    let debug_dev = alloc_upload(context, &[0u32; 2][..]);
    let debug_cells_dev = alloc_upload(context, &vec![Bf::ZERO; lowered.budget_cells as usize * t]);

    ParityPoint {
        context,
        label,
        cf,
        cpu,
        lowered,
        expected,
        record_map,
        layout,
        _src_bf_dev: src_bf_dev,
        _src_e4_dev: src_e4_dev,
        out_bf_dev,
        out_e4_dev,
        out_slots,
        payload_bf_dev,
        payload_e4_dev,
        _pred_dev: pred_dev,
        _setup_dev: setup_dev,
        payload_bytes_dev,
        payload_offsets_dev,
        lanes_dev,
        consts_dev,
        sources_tbl_dev,
        outputs_tbl_dev,
        output_e4_dev,
        debug_dev,
        debug_cells_dev,
    }
}

impl ParityPoint<'_> {
    fn run_and_check(&mut self, residency: InterpResidency) {
        let context = self.context;
        let t = PARITY_TRACE_LEN;
        let label = format!("{} [{:?}]", self.label, residency);

        // Reset outputs, payload dst buffers and debug counters (the LDC pass
        // reruns on the same buffers; a stale value passing the compare would
        // prove nothing).
        let n_out_bf: usize = self.out_slots.iter().filter(|s| !s.1).count();
        let n_out_e4: usize = self.out_slots.iter().filter(|s| s.1).count();
        if n_out_bf > 0 {
            memory_copy_async(
                &mut self.out_bf_dev[0..n_out_bf * t],
                &vec![Bf::ZERO; n_out_bf * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        if n_out_e4 > 0 {
            memory_copy_async(
                &mut self.out_e4_dev[0..n_out_e4 * t],
                &vec![Ext::ZERO; n_out_e4 * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        if self.layout.n_bf_cols > 0 {
            memory_copy_async(
                &mut self.payload_bf_dev[0..self.layout.n_bf_cols * t],
                &vec![Bf::ZERO; self.layout.n_bf_cols * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        if self.layout.n_e4_cols > 0 {
            memory_copy_async(
                &mut self.payload_e4_dev[0..self.layout.n_e4_cols * t],
                &vec![Ext::ZERO; self.layout.n_e4_cols * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        memory_copy_async(
            &mut self.debug_dev,
            &[0u32; 2][..],
            context.get_exec_stream(),
        )
        .unwrap();
        let n_cells = self.lowered.budget_cells as usize;
        memory_copy_async(
            &mut self.debug_cells_dev,
            &vec![Bf::ZERO; n_cells * t],
            context.get_exec_stream(),
        )
        .unwrap();

        let program_ldg = match residency {
            InterpResidency::Ldg => self.lanes_dev.as_ptr(),
            InterpResidency::Ldc => std::ptr::null(),
        };
        let desc = InterpDesc {
            program_ldg,
            program_lanes: self.lowered.lanes.len() as u32,
            n_instr: self.lowered.n_instr,
            sources: self.sources_tbl_dev.as_ptr() as *const *const u8,
            n_sources_bf: self.lowered.n_sources_bf,
            outputs: self.outputs_tbl_dev.as_ptr() as *const *mut u8,
            output_e4: self.output_e4_dev.as_ptr(),
            consts: self.consts_dev.as_ptr(),
            budget_cells: self.lowered.budget_cells,
            count: t as u32,
            native_fired: self.debug_dev.as_mut_ptr(),
            error_flag: unsafe { self.debug_dev.as_mut_ptr().add(1) },
            debug_cells: self.debug_cells_dev.as_mut_ptr() as *mut BF,
            payloads: self.payload_bytes_dev.as_ptr() as *const u8,
            payload_offsets: self.payload_offsets_dev.as_ptr(),
        };
        launch_bench_fwd_interp(&desc, residency, context).unwrap();

        let mut out_bf_host = vec![Bf::ZERO; n_out_bf * t];
        if n_out_bf > 0 {
            memory_copy_async(
                &mut out_bf_host,
                &self.out_bf_dev[0..n_out_bf * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let mut out_e4_host = vec![Ext::ZERO; n_out_e4 * t];
        if n_out_e4 > 0 {
            memory_copy_async(
                &mut out_e4_host,
                &self.out_e4_dev[0..n_out_e4 * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let mut pay_bf_host = vec![Bf::ZERO; self.layout.n_bf_cols * t];
        if self.layout.n_bf_cols > 0 {
            memory_copy_async(
                &mut pay_bf_host,
                &self.payload_bf_dev[0..self.layout.n_bf_cols * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let mut pay_e4_host = vec![Ext::ZERO; self.layout.n_e4_cols * t];
        if self.layout.n_e4_cols > 0 {
            memory_copy_async(
                &mut pay_e4_host,
                &self.payload_e4_dev[0..self.layout.n_e4_cols * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let mut cells_host = vec![Bf::ZERO; n_cells * t];
        memory_copy_async(
            &mut cells_host,
            &self.debug_cells_dev,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut debug_host = [0u32; 2];
        memory_copy_async(
            &mut debug_host[..],
            &self.debug_dev,
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        assert_eq!(debug_host[1], 0, "{label}: kernel reported INTERP_ERR bits");

        // NativeK fire accounting: once per (NativeK instruction, active thread).
        let n_native = self
            .cf
            .program
            .instrs
            .iter()
            .filter(|i| i.op == Op::NativeK)
            .count() as u32;
        assert_eq!(
            debug_host[0],
            n_native * t as u32,
            "{label}: native_fired counter (expected {n_native} NativeK x {t} threads)"
        );

        // Cell-file parity: the kernel dumps its FINAL smem cell file; the CPU
        // file now holds REAL cache values (the test stages true sentinels),
        // so this checks the alias-cell writes of every cache payload.
        assert_eq!(
            self.cpu.final_cells.len(),
            n_cells,
            "{label}: CPU cell-file length vs lowered budget_cells"
        );
        for row in [0usize, t - 1] {
            for c in 0..n_cells {
                assert_eq!(
                    cells_host[c * t + row],
                    self.cpu.final_cells[c],
                    "{label}: cell {c} row {row}"
                );
            }
        }

        // Payload dst columns: rows 0 and t-1 must equal the host mirror.
        for (p, outs) in self.expected.iter().enumerate() {
            let slots = &self.layout.slots[self.record_map[p]];
            assert_eq!(slots.len(), outs.len(), "{label}: payload {p} dst count");
            for (j, (&(e4, col), want)) in slots.iter().zip(outs).enumerate() {
                for row in [0usize, t - 1] {
                    if e4 {
                        assert_eq!(
                            pay_e4_host[col * t + row],
                            *want,
                            "{label}: payload {p} dst {j} (e4) row {row}"
                        );
                    } else {
                        assert_eq!(
                            pay_bf_host[col * t + row],
                            base_part(*want),
                            "{label}: payload {p} dst {j} (bf) row {row}"
                        );
                    }
                }
            }
        }

        // Equal-work row: the filtered-out MaxQuadratic dst columns must stay
        // untouched (all-zero) — nothing in the program may write them.
        let covered: std::collections::HashSet<usize> = self.record_map.iter().copied().collect();
        for &r in &self.layout.mq_records {
            if covered.contains(&r) {
                continue; // production-shape row computes MQ normally
            }
            for &(e4, col) in &self.layout.slots[r] {
                assert!(!e4, "MaxQuadratic dst is a bf column by contract");
                assert!(
                    pay_bf_host[col * t..(col + 1) * t]
                        .iter()
                        .all(|v| v.is_zero()),
                    "{label}: filtered MaxQuadratic record {r} dst column written"
                );
            }
        }

        // Program outputs: rows 0 and t-1 must equal the CPU interpreter's
        // result (empty corpus-wide for forward programs; assertion kept).
        for &(j, e4, col) in &self.out_slots {
            let cpu_v = self.cpu.outputs[j as usize]
                .unwrap_or_else(|| panic!("{label}: CPU never wrote output {j}"));
            for row in [0usize, t - 1] {
                if e4 {
                    let gpu_v = out_e4_host[col * t + row];
                    assert_eq!(gpu_v, cpu_v, "{label}: e4 output {j} row {row}");
                } else {
                    let gpu_v = out_bf_host[col * t + row];
                    assert_eq!(gpu_v, base_part(cpu_v), "{label}: bf output {j} row {row}");
                }
            }
        }
        // Slots absent from cf.outputs are never written on either side: the
        // lowering left them null (and asserts the program agrees); the CPU
        // result must be None for them.
        for (j, v) in self.cpu.outputs.iter().enumerate() {
            if !self.out_slots.iter().any(|&(jj, ..)| jj as usize == j) {
                assert!(
                    v.is_none(),
                    "{label}: CPU wrote output {j} the lowering skipped"
                );
            }
        }
    }
}

#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn interp_full_parity() {
    let context = make_test_context(256, 32);
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for (ci, circuit) in [
        "add_sub_lui_auipc_mop",
        "bigint_with_extended_control",
        "blake2_with_extended_control",
    ]
    .into_iter()
    .enumerate()
    {
        let c = load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
        let layer = &c.circuit.layers[0];
        let graph = &c.graphs[0];
        let mut compiled_any = false;
        for budget in [32usize, 64] {
            // bigint at the top budget also runs the equal-work
            // (MaxQuadratic-filtered) row with the SAME seed: the mirror
            // values of every surviving payload coincide, and the MQ dst
            // columns must stay untouched. add_sub/blake2 have zero
            // fwd-eligible MaxQuadratic gates (rows coincide).
            let filter_rows: &[bool] = if circuit == "bigint_with_extended_control" && budget == 64
            {
                &[false, true]
            } else {
                &[false]
            };
            for &exclude_mq in filter_rows {
                let params = FwdParams {
                    budget_cells: budget,
                    leaf_cache: true,
                    exclude_max_quadratic: exclude_mq,
                };
                // Tight budgets can be GENUINELY infeasible (mandatory
                // cache-cell operands exceeding the budget) — skip with a
                // recorded marker.
                let cf = match catch_unwind(AssertUnwindSafe(|| {
                    compile_forward(layer, graph, params)
                })) {
                    Ok(cf) => cf,
                    Err(_) => {
                        println!("SKIP {circuit} L0 budget {budget}: compile_forward infeasible");
                        continue;
                    }
                };
                compiled_any = true;
                if exclude_mq {
                    let n_mq = unfiltered_records(layer)
                        .iter()
                        .filter(|r| {
                            matches!(r, PayloadRecord::Gate(g)
                                if matches!(g.kind, GateKind::MaxQuadratic { .. }))
                        })
                        .count();
                    assert!(n_mq > 0, "{circuit}: filtered row without MQ gates");
                }
                let label = format!(
                    "{circuit} L0 budget {budget}{}",
                    if exclude_mq { " [equal-work]" } else { "" }
                );
                // Same seed for the filtered and unfiltered bigint points:
                // identical staged row + challenges => identical mirrors.
                let seed = 0x57A6_E3u64 ^ ((ci as u64) << 32) ^ budget as u64;
                let mut point =
                    build_parity_point(&context, label.clone(), layer, cf, exclude_mq, seed);
                point.run_and_check(InterpResidency::Ldg);
                if upload_bench_program_to_constant(&point.lowered.lanes).unwrap() {
                    point.run_and_check(InterpResidency::Ldc);
                } else {
                    println!(
                        "SKIP {label} LDC: program {} lanes exceeds the 28KB constant array",
                        point.lowered.lanes.len()
                    );
                }
            }
        }
        assert!(
            compiled_any,
            "{circuit}: no budget compiled — spurious-panic check"
        );
    }
}
