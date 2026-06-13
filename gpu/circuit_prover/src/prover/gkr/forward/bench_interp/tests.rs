use super::lower::{
    lower_payloads, lower_program, output_widths, payload_dst_e4, payload_kind_shape,
    BenchChallenges, LoweredPayloads, LoweredProgram,
};
use super::{
    launch_bench_fwd_interp, upload_bench_program_to_constant, BenchThreads, InterpDesc,
    InterpResidency,
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

use cs::definitions::gkr::RamWordRepresentation;
use cs::gkr_compiler::codegen_ir::{
    CacheKind, CodegenCache, CodegenGate, CodegenLayer, GateKind, LinearComb, MemTupleDescriptor,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict as AddrSpace, CompiledAddressStrict as Addr,
    CompiledMemoryTimestamp as Ts,
};
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

// ---------------------------------------------------------------------------
// Independent host evaluators for the affine payload kinds. Per the Task 4.5
// review, the affine kinds must NOT reuse lower.rs's coefficient folds (host
// expected and device bytes both derived from the same fold => a fold bug
// corrupts both sides identically and the parity passes vacuously). These
// recompute the expected value directly from the raw IR + challenges + operand
// values, applying alpha^k / challenge roles at EVALUATION time — a structurally
// different decomposition from lower::{vec_lookup_affine, mem_tuple_affine,
// lincomb_bf}, while remaining mathematically equivalent to the (correct) folds.
// ---------------------------------------------------------------------------

// Challenge roles into perm_challenges[6] (cs/src/definitions/constants.rs).
// The role->index convention is fixed; the field->role mapping below is the
// independently-rewritten part (review: closes the fold-circularity gap).
const R_ADDR_LOW: usize = 0;
const R_ADDR_HIGH: usize = 1;
const R_TS_LOW: usize = 2;
const R_TS_HIGH: usize = 3;
const R_VAL_LOW: usize = 4;
const R_VAL_HIGH: usize = 5;

/// `sum_k alpha^k * (col_k.constant + sum_j col_k.terms[j].coeff * vals[lane])`,
/// applying alpha to each column's full sum at eval time (independent of
/// lower::vec_lookup_affine, which pre-folds alpha into per-lane coeffs).
fn indep_vec_lookup(columns: &[LinearComb], ch: &BenchChallenges, vals: &[Ext]) -> Ext {
    let mut acc = Ext::ZERO;
    let mut lane = 0usize;
    for (k, col) in columns.iter().enumerate() {
        let mut col_val = lift(mont(col.constant));
        for &(coeff, _node) in &col.terms {
            col_val.add_assign(&ext_mul(lift(mont(coeff)), vals[lane]));
            lane += 1;
        }
        acc.add_assign(&ext_mul(ch.alpha_pow(k), col_val));
    }
    assert_eq!(lane, vals.len(), "indep vec-lookup lane walk");
    acc
}

/// `col.constant + sum_j col.terms[j].coeff * vals[j]` in the base subring (lifted).
fn indep_lincomb(column: &LinearComb, vals: &[Ext]) -> Ext {
    assert_eq!(column.terms.len(), vals.len(), "indep lincomb lane walk");
    let mut acc = lift(mont(column.constant));
    for (&(coeff, _node), &v) in column.terms.iter().zip(vals) {
        acc.add_assign(&ext_mul(lift(mont(coeff)), v));
    }
    acc
}

/// Memory-tuple value computed inline from the descriptor: perm_additive +
/// address-space term + sum_role chal[role] * (lane value or constant), walking
/// dependencies() order and applying the challenge at eval time. Mirrors the
/// VALUE semantics of gkr_forward_cache_memory_tuple / cache_relation.rs (NOT
/// lower::mem_tuple_affine's coefficient construction).
fn indep_mem_tuple(mt: &MemTupleDescriptor, ch: &BenchChallenges, vals: &[Ext]) -> Ext {
    let d = &mt.descriptor;
    let chal = |role: usize| ch.perm_challenges[role];
    let mut acc = ch.perm_additive;
    let mut lane = 0usize;

    match d.address_space {
        AddrSpace::Constant(c) => {
            acc.add_assign(&lift(mont(c)));
        }
        AddrSpace::IsRam(_) => {
            acc.add_assign(&vals[lane]); // value += col  (coeff ONE)
            lane += 1;
        }
        AddrSpace::IsRegister(_) => {
            acc.add_assign(&Ext::ONE);
            let mut neg = Ext::ONE;
            neg.negate();
            acc.add_assign(&ext_mul(neg, vals[lane])); // value += 1 - col
            lane += 1;
        }
    }

    match &d.address {
        Addr::ConstantU16(c) => {
            acc.add_assign(&ext_mul(chal(R_ADDR_LOW), lift(mont(*c as u32))));
        }
        Addr::Constant(c) => {
            acc.add_assign(&ext_mul(chal(R_ADDR_LOW), lift(mont(*c))));
        }
        Addr::U16Space(_) => {
            acc.add_assign(&ext_mul(chal(R_ADDR_LOW), vals[lane]));
            lane += 1;
        }
        Addr::U32Space(_) => {
            acc.add_assign(&ext_mul(chal(R_ADDR_LOW), vals[lane]));
            lane += 1;
            acc.add_assign(&ext_mul(chal(R_ADDR_HIGH), vals[lane]));
            lane += 1;
        }
        Addr::U32SpaceSpecialIndirect {
            low_dynamic_offset,
            low_offset,
            ..
        } => {
            acc.add_assign(&ext_mul(chal(R_ADDR_LOW), vals[lane]));
            lane += 1;
            acc.add_assign(&ext_mul(chal(R_ADDR_HIGH), vals[lane]));
            lane += 1;
            if let Some((dyn_coeff, _)) = low_dynamic_offset {
                let c = ext_mul(chal(R_ADDR_LOW), lift(mont(*dyn_coeff as u32)));
                acc.add_assign(&ext_mul(c, vals[lane]));
                lane += 1;
            }
            acc.add_assign(&ext_mul(chal(R_ADDR_LOW), lift(mont(*low_offset))));
        }
        other => panic!("indep mem-tuple address {other:?} unsupported"),
    }

    match d.timestamp {
        Ts::Zero => {}
        Ts::Normal(_) => {
            acc.add_assign(&ext_mul(chal(R_TS_LOW), vals[lane]));
            lane += 1;
            acc.add_assign(&ext_mul(chal(R_TS_LOW), lift(mont(d.timestamp_offset))));
            acc.add_assign(&ext_mul(chal(R_TS_HIGH), vals[lane]));
            lane += 1;
        }
    }

    match d.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(_) => {
            acc.add_assign(&ext_mul(chal(R_VAL_LOW), vals[lane]));
            lane += 1;
            acc.add_assign(&ext_mul(chal(R_VAL_HIGH), vals[lane]));
            lane += 1;
        }
        RamWordRepresentation::U8Limbs(_) => panic!("indep mem-tuple U8Limbs unsupported"),
    }

    assert_eq!(lane, vals.len(), "indep mem-tuple lane walk");
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
        // Vector-lookup value recomputed independently from the raw columns +
        // challenges (review: was circular via lower::vec_lookup_affine).
        GateKind::MaterializedVectorLookupInput { input } => {
            let mut v = indep_vec_lookup(&input.columns, ch, vals);
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
        // bf lincomb recomputed independently from the raw column (review: was
        // circular via lower::lincomb_bf) == production setup_values[mapping[gid]].
        CacheKind::SingleColumnLookup { column, .. } => indep_lincomb(column, vals),
        // Vector-lookup tuple recomputed independently (review: was circular via
        // lower::vec_lookup_affine) + decoder fill select (lookup_helpers.cuh:58-69).
        CacheKind::VectorizedLookup {
            columns,
            lookup_set_index,
        } => {
            let v = indep_vec_lookup(columns, ch, vals);
            if *lookup_set_index == usize::MAX && extras.exec_val.is_zero() {
                ch.decoder_fill
            } else {
                v
            }
        }
        // Memory-tuple value recomputed independently from the descriptor
        // (review: was circular via lower::mem_tuple_affine).
        CacheKind::MemoryTuple { descriptor } => indep_mem_tuple(descriptor, ch, vals),
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

/// Does this layer carry a decoder-select payload (a `VectorizedLookup` cache
/// or `MaterializedVectorLookupInput` gate with the formal `usize::MAX` set
/// index)? Used to assert both decoder-select branches get exercised.
fn layer_has_decoder_payload(layer: &CodegenLayer) -> bool {
    layer.caches.iter().any(|c| {
        matches!(&c.kind,
        CacheKind::VectorizedLookup { lookup_set_index, .. } if *lookup_set_index == usize::MAX)
    }) || layer
        .gates
        .iter()
        .chain(&layer.gates_external)
        .filter(|g| fwd_eligible(g))
        .any(|g| {
            matches!(&g.kind, GateKind::MaterializedVectorLookupInput { input }
                if input.lookup_set_index == usize::MAX)
        })
}

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

    // Non-vacuity: a covered MaxQuadratic payload must produce a nonzero mirror
    // value, else the dst compare against a zero reference would be vacuous.
    let mq_set: std::collections::HashSet<usize> = layout.mq_records.iter().copied().collect();
    let mut mq_covered = false;
    let mut mq_nonzero = false;
    for (p, outs) in expected.iter().enumerate() {
        if mq_set.contains(&record_map[p]) {
            mq_covered = true;
            if outs.iter().any(|v| !v.is_zero()) {
                mq_nonzero = true;
            }
        }
    }
    assert!(
        !mq_covered || mq_nonzero,
        "{label}: all covered MaxQuadratic mirrors are zero — vacuous compare, reseed"
    );

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
        launch_bench_fwd_interp(&desc, residency, BenchThreads::T128, context).unwrap();

        let out_bf_host = readback_packed(&self.out_bf_dev, n_out_bf, t, context);
        let out_e4_host = readback_packed(&self.out_e4_dev, n_out_e4, t, context);
        let pay_bf_host = readback_packed(&self.payload_bf_dev, self.layout.n_bf_cols, t, context);
        let pay_e4_host = readback_packed(&self.payload_e4_dev, self.layout.n_e4_cols, t, context);
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
    // Decoder-select branch coverage: both the affine/exec branch (exec_val != 0)
    // and the fill branch (exec_val == 0) must actually run, else a skipped
    // budget silently drops a branch while the test still passes.
    let (mut decoder_present, mut decoder_exec_seen, mut decoder_fill_seen) = (false, false, false);
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
                // Record which decoder-select branch this point exercised (the
                // exec_val derives from the same seed: build_parity_point sets it
                // to ONE when bit 6 is set, else ZERO).
                if layer_has_decoder_payload(layer) {
                    decoder_present = true;
                    if (seed >> 6) & 1 == 1 {
                        decoder_exec_seen = true;
                    } else {
                        decoder_fill_seen = true;
                    }
                }
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
    assert!(
        !decoder_present || (decoder_exec_seen && decoder_fill_seen),
        "decoder-select coverage incomplete: exec_seen={decoder_exec_seen} fill_seen={decoder_fill_seen} — a budget was likely skipped"
    );
}

// ===========================================================================
// Task 5: real-circuit per-layer fixture builder.
// ===========================================================================

use super::fixture::{
    assert_layer_consistency, build_add_sub_circuit_fixture, relation_output_addrs, CircuitFixture,
    LayerFixture, STAGE3_CIRCUITS,
};

/// 5.1 — CPU-only representation-consistency precheck (spec §6.0). For each of
/// the 3 circuits, the codegen-IR JSON and the prover-side artifact must agree
/// per layer on cache count, cache-out address set, output address population,
/// and source-column set. Non-ignored (CPU only).
#[test]
fn stage3_layer_consistency_precheck() {
    for circuit in STAGE3_CIRCUITS {
        assert_layer_consistency(circuit);
    }
}

/// Read every output column the layer produces back to host bytes, in address
/// order. Each entry is `(addr, e4, raw little-endian bytes)`. Uses the
/// panic-robust `relation_output_addrs` (not `layer.outputs()`, which the
/// upstream `dump_outputs` catch-all panics on for constraint gates).
#[cfg(not(no_cuda))]
fn read_layer_outputs(
    fixture: &super::fixture::CircuitFixture,
    layer_idx: usize,
) -> Vec<(crate::upstream::GKRAddress, bool, Vec<u8>)> {
    use crate::upstream::GKRAddress;
    use std::collections::BTreeSet;
    let context = fixture.context();
    let layer = &fixture.compiled_circuit.layers[layer_idx];
    let mut output_set: BTreeSet<GKRAddress> = BTreeSet::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        output_set.extend(relation_output_addrs(&gate.enforced_relation));
    }
    let outputs: Vec<GKRAddress> = output_set.into_iter().collect();
    let mut result = Vec::new();
    for addr in outputs {
        if let Some(poly) = fixture.storage.try_get_ext_poly(addr) {
            let mut host = vec![E4::ZERO; poly.len()];
            // SAFETY: poly.as_ptr() is a valid device E4 column of poly.len().
            let slice = unsafe { DeviceSlice::from_raw_parts(poly.as_ptr(), poly.len()) };
            memory_copy_async(&mut host, slice, context.get_exec_stream()).unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let bytes = host
                .iter()
                .flat_map(|v| {
                    let limbs: [u32; 4] = unsafe { std::mem::transmute(*v) };
                    limbs.into_iter().flat_map(u32::to_le_bytes)
                })
                .collect();
            result.push((addr, true, bytes));
        } else if let Some(poly) = fixture.storage.try_get_base_poly(addr) {
            let mut host = vec![BF::ZERO; poly.len()];
            // SAFETY: poly.as_ptr() is a valid device BF column of poly.len().
            let slice = unsafe { DeviceSlice::from_raw_parts(poly.as_ptr(), poly.len()) };
            memory_copy_async(&mut host, slice, context.get_exec_stream()).unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let bytes = host.iter().flat_map(|v| v.0.to_le_bytes()).collect();
            result.push((addr, false, bytes));
        }
    }
    result
}

/// 5.3 — Fixture smoke test (`#[ignore]`, GPU). Build the add_sub forward
/// fixture, replay every layer's captured `flat_launches` twice, and assert the
/// per-layer output columns are bytewise identical across the two replays
/// (replayability). Also asserts the 5.1 precheck passes for add_sub.
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn stage3_add_sub_fixture_smoke() {
    // 5.1 precheck for the smoke-test circuit (CPU; cheap, run first).
    assert_layer_consistency("add_sub_lui_auipc_mop");

    let fixture = build_add_sub_circuit_fixture();
    assert!(!fixture.layers.is_empty(), "fixture has no layers");

    let context = fixture.context();
    for layer in &fixture.layers {
        // A meaningful smoke layer must have at least one replayable launch.
        let replayable = layer
            .flat_launches
            .iter()
            .filter(|l| !matches!(l, super::fixture::FlatLaunch::MaterializeSingle))
            .count();
        if replayable == 0 {
            continue;
        }

        fixture.replay_layer(layer.layer_idx).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let first = read_layer_outputs(&fixture, layer.layer_idx);

        fixture.replay_layer(layer.layer_idx).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let second = read_layer_outputs(&fixture, layer.layer_idx);

        assert_eq!(
            first.len(),
            second.len(),
            "layer {}: output column count diverged across replays",
            layer.layer_idx
        );
        for ((a_addr, a_e4, a_bytes), (b_addr, b_e4, b_bytes)) in first.iter().zip(second.iter()) {
            assert_eq!(
                a_addr, b_addr,
                "layer {}: output address order",
                layer.layer_idx
            );
            assert_eq!(
                a_e4, b_e4,
                "layer {}: output width {a_addr:?}",
                layer.layer_idx
            );
            assert_eq!(
                a_bytes, b_bytes,
                "layer {}: output {a_addr:?} diverged across replays (non-replayable launch)",
                layer.layer_idx
            );
        }
        println!(
            "layer {}: {} replayable launches, {} output columns identical across 2 replays",
            layer.layer_idx,
            replayable,
            first.len()
        );
    }
}

// ===========================================================================
// Task 6.B: real-fixture interpreter device-compare parity (spec §6.1 step 4c).
//
// For each of the 3 stage-3 circuits at layer 0 (and any other feasible layers),
// at each feasible budget: (i) replay the layer's flat launches into storage,
// (ii) read the flat-produced dst/output references from storage (MaxQuadratic
// dsts read from the hydrated scratch reference), (iii) lower the interpreter
// program + payloads with the REAL resolvers (sources -> resident storage
// columns, dsts/outputs -> FRESH packed buffers) + the fixture's real
// `bench_challenges()`, (iv) run the interpreter and assert its dst/output
// columns equal the flat reference at rows 0 and trace_len-1. The gamma consts
// are ALREADY staged on device by the flat preamble — NOT re-staged here.
// ===========================================================================

/// Read back a packed column buffer (`n_cols * t` elements, layout `col*t+row`)
/// to host, skipping the copy when there are no columns. Shared by both parity
/// harnesses' readback (the `if n_cols > 0 { memory_copy_async(..) }` pattern).
fn readback_packed<T: Field>(
    dev: &DeviceSlice<T>,
    n_cols: usize,
    t: usize,
    context: &ProverContext,
) -> Vec<T> {
    let mut host = vec![T::ZERO; n_cols * t];
    if n_cols > 0 {
        memory_copy_async(&mut host, &dev[0..n_cols * t], context.get_exec_stream()).unwrap();
    }
    host
}

/// Read `t` elements from a raw device column pointer to host (bf or e4).
#[cfg(not(no_cuda))]
fn read_device_column_bf(ptr: *const u8, t: usize, context: &ProverContext) -> Vec<Bf> {
    let mut host = vec![Bf::ZERO; t];
    // SAFETY: `ptr` is a resident bf column of >= t elements (storage poly or
    // hydrated scratch); the read is stream-ordered, host buffer matches len.
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr as *const Bf, t) };
    memory_copy_async(&mut host, slice, context.get_exec_stream()).unwrap();
    host
}

#[cfg(not(no_cuda))]
fn read_device_column_e4(ptr: *const u8, t: usize, context: &ProverContext) -> Vec<Ext> {
    let mut host = vec![Ext::ZERO; t];
    // SAFETY: `ptr` is a resident e4 column of >= t elements; stream-ordered.
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr as *const Ext, t) };
    memory_copy_async(&mut host, slice, context.get_exec_stream()).unwrap();
    host
}

/// The interpreter side of a real-fixture point, fully resident on device and
/// ready to launch: the `InterpDesc` plus every backing allocation kept alive
/// for the launch's lifetime. Shared by the device-compare gate (c) and the
/// 6.C-2 timing path. The compare-only flat references are NOT built here.
///
/// `count` is the element count the buffers are sized for and the desc reports;
/// the device columns the sources point into are real-trace-sized, so a
/// `count < trace_len` reads/writes only a prefix (capped timing, spec §6.2(A)).
#[cfg(not(no_cuda))]
pub(super) struct InterpDeviceSetup {
    pub(super) desc: InterpDesc,
    pub(super) lanes: Vec<u16>,
    /// cf payload p, dst j -> (e4, packed column index). For the compare.
    pub(super) pay_slots: Vec<Vec<(bool, usize)>>,
    pub(super) n_pay_bf: usize,
    pub(super) n_pay_e4: usize,
    /// (slot j, e4, packed column index). For the compare.
    pub(super) out_slots: Vec<(u16, bool, usize)>,
    pub(super) n_out_bf: usize,
    pub(super) n_out_e4: usize,
    pub(super) n_instr: u32,
    pub(super) payload_bytes: usize,
    pub(super) program_bytes: usize,
    // Backing allocations: dropped (freed) when the setup is dropped; every raw
    // pointer in `desc` and the read-back columns refer into these.
    _virtual_src: std::collections::BTreeMap<usize, DeviceAllocation<Bf>>,
    out_bf_dev: DeviceAllocation<Bf>,
    out_e4_dev: DeviceAllocation<Ext>,
    pay_bf_dev: DeviceAllocation<Bf>,
    pay_e4_dev: DeviceAllocation<Ext>,
    _payload_bytes_dev: DeviceAllocation<Ext>,
    _payload_offsets_dev: DeviceAllocation<u32>,
    _lanes_dev: DeviceAllocation<u16>,
    _consts_dev: DeviceAllocation<BF>,
    _sources_tbl_dev: DeviceAllocation<u64>,
    _outputs_tbl_dev: DeviceAllocation<u64>,
    _output_e4_dev: DeviceAllocation<u32>,
    debug_dev: DeviceAllocation<u32>,
    _debug_cells_dev: DeviceAllocation<Bf>,
}

/// Build the interpreter device side for one real-fixture point: materialize
/// virtual-setup source columns, allocate fresh packed dst/output buffers, lower
/// the program + payloads against the fixture's resolvers, and upload everything
/// into an `InterpDesc`. Sized for `count` elements. The returned `desc` has
/// `debug_cells`/`native_fired` populated (debug_dev[0] = native_fired,
/// debug_dev[1] = error_flag); timing callers null them via
/// `setup.timing_desc()`.
#[cfg(not(no_cuda))]
pub(super) fn build_interp_device_setup(
    fixture: &CircuitFixture,
    layer: &LayerFixture,
    cf: &gkr_eval_isa::compiler::fwd::CompiledForward,
    cg_layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    count: usize,
) -> InterpDeviceSetup {
    use super::fixture::{
        materialize_virtual_setup_column, resolve_decoder_pred, resolve_source,
        source_virtual_setup,
    };
    let arena = &cg_layer.arena.nodes;
    let context = fixture.context();
    let t = count;
    let ch = fixture.bench_challenges();
    let decoder_pred_addr = fixture.decoder_predicate_address();

    // Virtual-setup bf source columns have NO resident device buffer;
    // materialize each (byte-for-byte the device formula) and upload.
    let mut virtual_src: std::collections::BTreeMap<usize, DeviceAllocation<Bf>> =
        std::collections::BTreeMap::new();
    for i in 0..cf.source_map.bf.len() {
        if let Some(poly) = source_virtual_setup(cf, arena, i) {
            let col = materialize_virtual_setup_column(poly, t);
            virtual_src.insert(i, alloc_upload(context, &col));
        }
    }
    context.get_exec_stream().synchronize().unwrap();

    // Fresh interpreter dst buffers, packed per width (the interpreter writes
    // here, NOT into storage, so flat references stay intact).
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

    let mut pay_slots: Vec<Vec<(bool, usize)>> = Vec::with_capacity(cf.payloads.len());
    let (mut n_pay_bf, mut n_pay_e4) = (0usize, 0usize);
    for rec in &cf.payloads {
        let (_, n_dsts, _) = payload_kind_shape(rec);
        let mut per = Vec::with_capacity(n_dsts);
        for j in 0..n_dsts {
            let e4 = payload_dst_e4(rec, j);
            let col = if e4 { &mut n_pay_e4 } else { &mut n_pay_bf };
            per.push((e4, *col));
            *col += 1;
        }
        pay_slots.push(per);
    }
    let pay_bf_dev = alloc_upload(context, &vec![Bf::ZERO; n_pay_bf * t]);
    let pay_e4_dev = alloc_upload(context, &vec![Ext::ZERO; n_pay_e4 * t]);

    // Lower: sources -> resident storage columns; outputs/dsts -> fresh packed
    // buffers; decoder pred -> storage predicate column; setup table -> forward
    // setup's generic_lookup buffer.
    let lowered = lower_program(
        cf,
        |i| {
            if let Some(dev) = virtual_src.get(&i) {
                dev.as_ptr() as *const u8
            } else {
                resolve_source(layer, &fixture.storage, cf, cg_layer, i, false)
            }
        },
        |i| resolve_source(layer, &fixture.storage, cf, cg_layer, i, true),
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

    let (setup_ptr, setup_len) = fixture.setup_table();
    let lp: LoweredPayloads = lower_payloads(
        cf,
        arena,
        |p, _rec, j| {
            let (e4, col) = pay_slots[p][j];
            if e4 {
                (unsafe { pay_e4_dev.as_ptr().add(col * t) }) as *mut u8
            } else {
                (unsafe { pay_bf_dev.as_ptr().add(col * t) }) as *mut u8
            }
        },
        |_p, _rec| resolve_decoder_pred(layer, &fixture.storage, decoder_pred_addr),
        |_ci| (setup_ptr, setup_len),
        &ch,
    );

    // Upload program + payloads. Record bytes go into an E4-backed (16B-aligned)
    // allocation — the device reader does reinterpret-cast e4 loads.
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
    let lanes_dev = alloc_upload(context, &lowered.lanes);
    let consts_dev = alloc_upload(context, &lowered.consts);
    let sources_host: Vec<u64> = lowered.source_ptrs.iter().map(|&p| p as u64).collect();
    let sources_tbl_dev = alloc_upload(context, &sources_host);
    let outputs_host: Vec<u64> = lowered.output_ptrs.iter().map(|&p| p as u64).collect();
    let outputs_tbl_dev = alloc_upload(context, &outputs_host);
    let output_e4_dev = alloc_upload(context, &lowered.output_e4);
    let mut debug_dev = alloc_upload(context, &[0u32; 2][..]);
    let n_cells = lowered.budget_cells as usize;
    let mut debug_cells_dev = alloc_upload(context, &vec![Bf::ZERO; n_cells.max(1) * t]);
    context.get_exec_stream().synchronize().unwrap();

    let desc = InterpDesc {
        program_ldg: lanes_dev.as_ptr(),
        program_lanes: lowered.lanes.len() as u32,
        n_instr: lowered.n_instr,
        sources: sources_tbl_dev.as_ptr() as *const *const u8,
        n_sources_bf: lowered.n_sources_bf,
        outputs: outputs_tbl_dev.as_ptr() as *const *mut u8,
        output_e4: output_e4_dev.as_ptr(),
        consts: consts_dev.as_ptr(),
        budget_cells: lowered.budget_cells,
        count: t as u32,
        native_fired: debug_dev.as_mut_ptr(),
        error_flag: unsafe { debug_dev.as_mut_ptr().add(1) },
        debug_cells: debug_cells_dev.as_mut_ptr() as *mut BF,
        payloads: payload_bytes_dev.as_ptr() as *const u8,
        payload_offsets: payload_offsets_dev.as_ptr(),
    };

    InterpDeviceSetup {
        desc,
        lanes: lowered.lanes.clone(),
        pay_slots,
        n_pay_bf,
        n_pay_e4,
        out_slots,
        n_out_bf,
        n_out_e4,
        n_instr: lowered.n_instr,
        payload_bytes: lp.bytes.len(),
        program_bytes: lowered.lanes.len() * 2 + lowered.consts.len() * 4,
        _virtual_src: virtual_src,
        out_bf_dev,
        out_e4_dev,
        pay_bf_dev,
        pay_e4_dev,
        _payload_bytes_dev: payload_bytes_dev,
        _payload_offsets_dev: payload_offsets_dev,
        _lanes_dev: lanes_dev,
        _consts_dev: consts_dev,
        _sources_tbl_dev: sources_tbl_dev,
        _outputs_tbl_dev: outputs_tbl_dev,
        _output_e4_dev: output_e4_dev,
        debug_dev,
        _debug_cells_dev: debug_cells_dev,
    }
}

#[cfg(not(no_cuda))]
impl InterpDeviceSetup {
    /// A copy of the desc with the debug sinks nulled (`debug_cells` and
    /// `native_fired`) — the timing-run form (spec §6.2: no cell dump, no fire
    /// counter in the timed loop). `error_flag` stays wired so a faulting launch
    /// still surfaces.
    pub(super) fn timing_desc(&self) -> InterpDesc {
        let mut d = self.desc;
        d.debug_cells = std::ptr::null_mut();
        d.native_fired = std::ptr::null_mut();
        d
    }
}

/// Lower + run + device-compare one (circuit, layer, budget) point against the
/// flat references already resident in storage. This is the body of harness
/// gate (c): on the FIRST mismatch (non-zero `error_flag`, wrong `native_fired`
/// count, vacuous comparison set, or any dst/output row divergence) it returns
/// `Err(reason)`; a full pass returns `Ok(())`. The sole caller is `run_point`'s
/// gate (c) (`harness.rs`), which itself maps the `Err(reason)` into a recorded
/// `PointResult::Failed` rather than panicking.
///
/// Builds the interpreter side via `build_interp_device_setup` (shared with the
/// 6.C-2 timing path) at the full `trace_len`, then reads back the interpreter
/// dst/output columns and compares them to the flat references.
#[cfg(not(no_cuda))]
pub(super) fn run_real_fixture_parity_point(
    fixture: &CircuitFixture,
    layer: &LayerFixture,
    cf: &gkr_eval_isa::compiler::fwd::CompiledForward,
    cg_layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    label: &str,
) -> Result<(), String> {
    use super::fixture::resolve_output;
    let arena = &cg_layer.arena.nodes;
    let context = fixture.context();
    let t = fixture.trace_len;

    // (ii) Flat references: per payload dst (and per program output), the
    // resident POST-CAPTURE storage column. Read from `fixture.storage` (every
    // layer's flat outputs + hydrated scratch are bound) so a MaxQuadratic gate
    // dst at `InnerLayer { layer: L+1 }` — never produced flat-side — resolves to
    // the hydrated witness-stage scratch value (spec §6.1 step 2). The kind-
    // implied e4 width is cross-checked against the storage column's width.
    let payload_refs: Vec<Vec<(bool, Vec<Bf>, Vec<Ext>)>> = cf
        .payloads
        .iter()
        .enumerate()
        .map(|(p, rec)| {
            let (_, n_dsts, _) = payload_kind_shape(rec);
            (0..n_dsts)
                .map(|j| {
                    let want_e4 = payload_dst_e4(rec, j);
                    let (e4, ptr) = fixture.payload_dst_reference(cf, p, j);
                    assert_eq!(
                        e4, want_e4,
                        "{label}: payload {p} dst {j} storage width vs kind width"
                    );
                    if e4 {
                        (true, Vec::new(), read_device_column_e4(ptr, t, context))
                    } else {
                        (false, read_device_column_bf(ptr, t, context), Vec::new())
                    }
                })
                .collect()
        })
        .collect();
    let output_refs: Vec<(u16, bool, Vec<Bf>, Vec<Ext>)> = cf
        .outputs
        .iter()
        .map(|&(j, _)| {
            let (_, e4) = resolve_output(layer, &fixture.storage, cf, cg_layer, j);
            let node = cf.outputs.iter().find(|&&(jj, _)| jj == j).unwrap().1;
            let addr = match arena[node] {
                cs::gkr_compiler::codegen_ir::ExprNode::Place { addr, .. } => addr,
                ref other => panic!("{label}: output slot {j} node is not a Place: {other:?}"),
            };
            let (_, ptr) = fixture
                .storage_column(addr)
                .unwrap_or_else(|| panic!("{label}: output {j} addr {addr:?} not resident"));
            if e4 {
                (j, true, Vec::new(), read_device_column_e4(ptr, t, context))
            } else {
                (j, false, read_device_column_bf(ptr, t, context), Vec::new())
            }
        })
        .collect();
    context.get_exec_stream().synchronize().unwrap();

    // (iii) Build the interpreter side (materialize virtual-setup columns, fresh
    // packed dst/output buffers, lower + upload, build the desc) at the full
    // trace_len, then launch LDG/128 (gate (c) is LDG-only; the fairness configs
    // exercise the same lowering through the timing path).
    let setup = build_interp_device_setup(fixture, layer, cf, cg_layer, t);
    println!(
        "{label}: payload table {} bytes / {} records, {} program lanes",
        setup.payload_bytes,
        setup.pay_slots.iter().map(|p| p.len()).sum::<usize>(),
        setup.lanes.len(),
    );
    launch_bench_fwd_interp(
        &setup.desc,
        InterpResidency::Ldg,
        BenchThreads::T128,
        context,
    )
    .unwrap();

    // (iv) Read interpreter dsts/outputs back and compare to the flat reference.
    let (pay_slots, out_slots) = (&setup.pay_slots, &setup.out_slots);
    let pay_bf_host = readback_packed(&setup.pay_bf_dev, setup.n_pay_bf, t, context);
    let pay_e4_host = readback_packed(&setup.pay_e4_dev, setup.n_pay_e4, t, context);
    let out_bf_host = readback_packed(&setup.out_bf_dev, setup.n_out_bf, t, context);
    let out_e4_host = readback_packed(&setup.out_e4_dev, setup.n_out_e4, t, context);
    let mut debug_host = [0u32; 2];
    memory_copy_async(
        &mut debug_host[..],
        &setup.debug_dev,
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    if debug_host[1] != 0 {
        return Err(format!(
            "{label}: kernel reported INTERP_ERR bits {:#x}",
            debug_host[1]
        ));
    }

    // Non-vacuity: there must be SOMETHING to compare, else the per-row loops
    // below run zero iterations and the point "passes" while checking nothing.
    if cf.payloads.is_empty() && cf.outputs.is_empty() {
        return Err(format!(
            "{label}: nothing to compare (empty payloads+outputs)"
        ));
    }

    // NativeK fire accounting (mirrors `run_and_check` / `interp_full_parity`):
    // once per (NativeK instruction, active thread). Proves the kernel actually
    // executed the payload routines rather than no-op'ing past them.
    let n_native = cf
        .program
        .instrs
        .iter()
        .filter(|i| i.op == Op::NativeK)
        .count() as u32;
    if debug_host[0] != n_native * t as u32 {
        return Err(format!(
            "{label}: native_fired counter {} (expected {n_native} NativeK x {t} threads)",
            debug_host[0]
        ));
    }

    // Payload dst columns: rows 0 and t-1 must equal the flat reference.
    let rows = [0usize, t - 1];
    for (p, per) in pay_slots.iter().enumerate() {
        for (j, &(e4, col)) in per.iter().enumerate() {
            let (ref_e4, ref_bf, ref_ext) = &payload_refs[p][j];
            if *ref_e4 != e4 {
                return Err(format!("{label}: payload {p} dst {j} width disagrees"));
            }
            for &row in &rows {
                if e4 {
                    if pay_e4_host[col * t + row] != ref_ext[row] {
                        return Err(format!(
                            "{label}: payload {p} dst {j} (e4) row {row} mismatch vs flat ref"
                        ));
                    }
                } else if pay_bf_host[col * t + row] != ref_bf[row] {
                    return Err(format!(
                        "{label}: payload {p} dst {j} (bf) row {row} mismatch vs flat ref"
                    ));
                }
            }
        }
    }

    // Program outputs (empty corpus-wide for forward programs; assertion kept).
    for &(j, e4, col) in out_slots {
        let (_, _, ref_bf, ref_ext) = output_refs
            .iter()
            .find(|&&(jj, ..)| jj == j)
            .expect("output ref");
        for &row in &rows {
            if e4 {
                if out_e4_host[col * t + row] != ref_ext[row] {
                    return Err(format!(
                        "{label}: e4 output {j} row {row} mismatch vs flat ref"
                    ));
                }
            } else if out_bf_host[col * t + row] != ref_bf[row] {
                return Err(format!(
                    "{label}: bf output {j} row {row} mismatch vs flat ref"
                ));
            }
        }
    }
    println!(
        "{label}: PASS ({} payloads, {} outputs)",
        cf.payloads.len(),
        out_slots.len()
    );
    Ok(())
}

/// 6.C-1 — per-point correctness driver (`#[ignore]`, GPU). Drives `run_point`
/// (the three-gate harness: CPU oracle, structural lowering, device-compare)
/// over all 3 stage-3 circuits × all layers × budgets {32, 64} × filter rows
/// (production-shape always; the equal-work MaxQuadratic-filtered row for bigint
/// at the top budget, per `interp_full_parity`'s logic). Collects every
/// `(label, PointResult)`; asserts every result is `Verified` or `Infeasible`
/// (NONE `Failed`) and at least one `Verified` per circuit. Same coverage the
/// old `stage3_real_fixture_interp_parity` had, now routed through `run_point`.
///
/// Layer/budget grid + filter rows + the `assert_layer_consistency` precheck
/// live HERE (the driver); `run_point` owns the per-point replay + the gates.
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn stage3_run_point_correctness() {
    use super::harness::{run_point, PointParams, PointResult};

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let mut results: Vec<(String, PointResult)> = Vec::new();

    for (ci, circuit) in STAGE3_CIRCUITS.into_iter().enumerate() {
        // CPU precheck first (cheap; catches representation drift).
        assert_layer_consistency(circuit);

        let loaded = load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
        let fixture = CircuitFixture::build(circuit);
        assert!(
            !fixture.layers.is_empty(),
            "{circuit}: fixture has no layers"
        );
        assert_eq!(
            loaded.circuit.layers.len(),
            fixture.compiled_circuit.layers.len(),
            "{circuit}: codegen IR vs artifact layer count"
        );

        // Per-circuit base seed (same scheme `interp_full_parity` uses);
        // `check_layer` mixes in the layer index itself.
        let circuit_seed = 0x57A6_E3u64 ^ ((ci as u64) << 32);

        // Layer 0 is mandatory; include any further layer that has replayable
        // launches (others carry no flat reference for the device-compare).
        let mut circuit_verified = false;
        for layer_idx in 0..fixture.layers.len() {
            let replayable = fixture.layers[layer_idx]
                .flat_launches
                .iter()
                .filter(|l| !matches!(l, super::fixture::FlatLaunch::MaterializeSingle))
                .count();
            if layer_idx != 0 && replayable == 0 {
                continue;
            }

            let cg_layer = &loaded.circuit.layers[layer_idx];
            let graph = &loaded.graphs[layer_idx];
            for budget in [32usize, 64] {
                // Production-shape always; the equal-work row only for bigint at
                // the top budget (matching `interp_full_parity`): add_sub/blake2
                // have zero fwd-eligible MaxQuadratic gates, so the rows coincide.
                let filter_rows: &[bool] =
                    if circuit == "bigint_with_extended_control" && budget == 64 {
                        &[false, true]
                    } else {
                        &[false]
                    };
                for &exclude_mq in filter_rows {
                    let label = format!(
                        "{circuit} L{layer_idx} budget {budget}{}",
                        if exclude_mq { " [equal-work]" } else { "" }
                    );
                    let params = PointParams {
                        budget,
                        exclude_max_quadratic: exclude_mq,
                    };
                    let result = run_point(
                        &fixture,
                        layer_idx,
                        cg_layer,
                        graph,
                        params,
                        circuit_seed,
                        &label,
                    );
                    match &result {
                        PointResult::Verified => circuit_verified = true,
                        PointResult::Infeasible => {
                            println!("INFEASIBLE {label}");
                        }
                        PointResult::Failed { gate, reason } => {
                            println!("FAILED [{gate}] {label}: {reason}");
                        }
                    }
                    results.push((label, result));
                }
            }
        }
        assert!(
            circuit_verified,
            "{circuit}: no point Verified (need >=1 per circuit)"
        );
    }

    // No point may be Failed; report all failures together before panicking.
    let failures: Vec<String> = results
        .iter()
        .filter_map(|(label, r)| match r {
            PointResult::Failed { gate, reason } => Some(format!("[{gate}] {label}: {reason}")),
            _ => None,
        })
        .collect();
    assert!(
        failures.is_empty(),
        "run_point reported {} failed point(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ===========================================================================
// 6.C-2 — verdict A/B timing test (spec §6.2(A), §6.3, §9).
// ===========================================================================

use super::harness::{
    prescan_best_budget, time_point, TimedPoint, BUDGET_GRID, PRESCAN_ITERS, TIMING_COUNT_CAP,
    TIMING_ITERS,
};
use super::report::{AbReport, AbRow, DeviceAttrs, SideTiming};

use super::harness::{compile_feasible, fit_ols, time_interp_smem, RegressionObs};
use super::report::{RegressionBlock, SetBRow, SetCRow, SetDRow};
use super::{
    bench_interp_blocks_per_sm_smem, bench_interp_dynamic_smem_bytes, padded_smem_for_blocks,
    BENCH_INTERP_DEFAULT_SMEM_CAP, BENCH_INTERP_THREADS_PER_BLOCK,
};

/// Count of fwd-eligible MaxQuadratic gates a layer carries (the equal-work
/// filter target). Zero for add_sub/blake2 (rows coincide); positive for bigint.
fn fwd_eligible_mq_count(layer: &CodegenLayer) -> usize {
    layer
        .gates
        .iter()
        .chain(&layer.gates_external)
        .filter(|g| fwd_eligible(g) && matches!(g.kind, GateKind::MaxQuadratic { .. }))
        .count()
}

/// Compile + time ONE (residency, threads) config row of an already-Verified
/// (`budget`, filter) point at `count`, building it into an `AbRow`. The caller
/// pre-scans the config's best-feasible budget (`prescan_best_budget`) and gates
/// it via `run_point` BEFORE calling this, then passes the chosen `budget` in —
/// so timing is recorded ONLY for a gate-Verified point at the EXACT timed
/// budget (spec §6.1.4). This recompiles at that budget for the EXACT timed
/// program's stats (`cf.stats`, filtered for equal-work rows). Returns `None`
/// (with a recorded skip) when the program is not timeable for this config at
/// `budget` (e.g. LDC never fits).
#[allow(clippy::too_many_arguments)]
#[cfg(not(no_cuda))]
fn time_config_row(
    fixture: &CircuitFixture,
    layer_idx: usize,
    cg_layer: &CodegenLayer,
    graph: &gkr_design_space::graph::AnalysisGraph,
    circuit: &str,
    exclude_mq: bool,
    rows_coincide: bool,
    residency: InterpResidency,
    threads: BenchThreads,
    budget: usize,
    count: usize,
    skips: &mut Vec<String>,
) -> Option<AbRow> {
    // Recompile at the chosen budget for the EXACT timed program's stats.
    let cf = compile_forward(
        cg_layer,
        graph,
        FwdParams {
            budget_cells: budget,
            leaf_cache: true,
            exclude_max_quadratic: exclude_mq,
        },
    );
    let layer = &fixture.layers[layer_idx];
    let Some(t): Option<TimedPoint> = time_point(
        fixture, layer_idx, layer, &cf, cg_layer, residency, threads, count,
    ) else {
        skips.push(format!(
            "{circuit} L{layer_idx} {residency:?}/{} budget {budget}: program does not fit constant array",
            threads.threads_per_block(),
        ));
        return None;
    };

    let trace_len = fixture.trace_len;
    let interp_over_flat = if t.flat_median_ms > 0.0 {
        t.interp_median_ms / t.flat_median_ms
    } else {
        f32::INFINITY
    };
    Some(AbRow {
        circuit: circuit.to_string(),
        layer: layer_idx,
        budget,
        residency: format!("{residency:?}"),
        interp_threads: threads.threads_per_block(),
        equal_work: exclude_mq,
        rows_coincide,
        timed_count: count,
        trace_len,
        capped: count < trace_len,
        flat: SideTiming {
            median_ms: t.flat_median_ms,
            min_ms: t.flat_min_ms,
            launches: t.flat_launches,
            iters: TIMING_ITERS,
        },
        interp: SideTiming {
            median_ms: t.interp_median_ms,
            min_ms: t.interp_min_ms,
            launches: 1,
            iters: TIMING_ITERS,
        },
        interp_over_flat,
        interp_smem_bytes: t.interp_smem_bytes,
        interp_blocks_per_sm: t.interp_blocks_per_sm,
        interp_large_smem_optin: t.interp_large_smem_optin,
        program_bytes: t.program_bytes,
        payload_bytes: t.payload_bytes,
        n_instr: t.n_instr,
        instrs: cf.stats.instrs,
        src_reads: cf.stats.src_reads,
        cell_reads: cf.stats.cell_reads,
        cache_refires: cf.stats.cache_refires,
        max_live_cells: cf.stats.max_live_cells,
    })
}

/// 6.C-2 — verdict A/B test (`#[ignore]`, GPU; spec §6.2(A), §6.3, §9). For each
/// of the 3 stage-3 circuits × all layers (L0 + replayable upper layers) ×
/// best-feasible budget × {LDG, LDC-if-fits} × {production-shape, equal-work}:
///
///   1. Pre-scan the budget grid for the best-feasible budget (min interpreter
///      median, N={PRESCAN_ITERS}), including the THREADS=256 fairness config.
///   2. Run the 3 correctness gates (`run_point`) at that budget; only a
///      `Verified` point is timed. `Failed`/`Infeasible` are recorded — never
///      timed (spec §6.1.4).
///   3. Time both sides (flat replay-sum vs single interpreter launch) with CUDA
///      events, N={TIMING_ITERS}, at the capped count `min(trace_len, 1<<20)`.
///   4. Emit the §6.2(A) table to stdout + `.agents/audits/...{md,json}`.
///
/// Filter coincidence (spec §9): add_sub/blake2 have ZERO fwd-eligible
/// MaxQuadratic, so the equal-work row coincides with production — run ONCE,
/// `rows_coincide=true`. Only bigint runs a distinct equal-work row.
///
/// No silent gaps: every set-A point is either timed (a row), or recorded as a
/// Failed/Infeasible point, or a pre-scan/fit skip; the test asserts the union
/// covers the grid and panics on any `Failed`.
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn stage3_fwd_interp_ab() {
    use super::harness::{run_point, PointParams, PointResult};

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let mut rows: Vec<AbRow> = Vec::new();
    let mut skips: Vec<String> = Vec::new();
    let mut failures: Vec<String> = Vec::new();

    for (ci, circuit) in STAGE3_CIRCUITS.into_iter().enumerate() {
        assert_layer_consistency(circuit);
        let loaded = load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
        let fixture = CircuitFixture::build(circuit);
        assert!(
            !fixture.layers.is_empty(),
            "{circuit}: fixture has no layers"
        );

        let circuit_seed = 0x57A6_E3u64 ^ ((ci as u64) << 32);
        // Cross-circuit cap (controller ruling): both sides timed at this count.
        let count = fixture.trace_len.min(TIMING_COUNT_CAP);
        let capped = count < fixture.trace_len;
        println!(
            "{circuit}: trace_len {} -> timed count {count}{}",
            fixture.trace_len,
            if capped { " (capped)" } else { "" }
        );

        for layer_idx in 0..fixture.layers.len() {
            let replayable = fixture.layers[layer_idx].replayable_launch_count();
            if layer_idx != 0 && replayable == 0 {
                continue;
            }
            let cg_layer = &loaded.circuit.layers[layer_idx];
            let graph = &loaded.graphs[layer_idx];

            // Filter shapes: production always; a distinct equal-work row only
            // when the layer has fwd-eligible MaxQuadratic gates (bigint). Else
            // the rows coincide — run production once with rows_coincide=true.
            let mq = fwd_eligible_mq_count(cg_layer);
            let rows_coincide = mq == 0;
            let shapes: &[bool] = if rows_coincide {
                &[false]
            } else {
                &[false, true]
            };

            for &exclude_mq in shapes {
                let shape_str = if exclude_mq {
                    "equal-work"
                } else {
                    "production"
                };
                let configs = [
                    (InterpResidency::Ldg, BenchThreads::T128),
                    (InterpResidency::Ldg, BenchThreads::T256),
                    (InterpResidency::Ldc, BenchThreads::T128),
                ];

                // (1) Pre-scan EACH config for its own best-feasible budget (min
                // interpreter median over the grid). The configs may land on
                // DIFFERENT budgets, so the exact budget that will be TIMED
                // varies per config — each one must be gated at its own budget.
                let mut config_budgets: Vec<(InterpResidency, BenchThreads, Option<usize>)> =
                    Vec::with_capacity(configs.len());
                for (residency, threads) in configs {
                    let chosen = prescan_best_budget(
                        &fixture, layer_idx, cg_layer, graph, exclude_mq, residency, threads, count,
                    )
                    .map(|p| p.budget);
                    if chosen.is_none() {
                        skips.push(format!(
                            "{circuit} L{layer_idx} {residency:?}/{} {shape_str}: no feasible+timeable budget in grid {BUDGET_GRID:?}",
                            threads.threads_per_block(),
                        ));
                    }
                    config_budgets.push((residency, threads, chosen));
                }

                // (2) Gate EVERY distinct (budget, filter) that WILL be timed —
                // the union of the configs' chosen budgets (spec §6.1.4). A single
                // LDG/128 `run_point` at (budget, filter) certifies all configs
                // timed at that same point: the lowered program is identical
                // across residencies (LDC just uploads the same program to
                // `__constant__`) and the kernel body is block-size-agnostic. The
                // map memoizes the verdict so each budget is gated (and
                // device-compared) at most ONCE per (layer, filter).
                let mut gated: std::collections::BTreeMap<usize, PointResult> =
                    std::collections::BTreeMap::new();
                for budget in config_budgets
                    .iter()
                    .filter_map(|&(_, _, b)| b)
                    .collect::<std::collections::BTreeSet<usize>>()
                {
                    let label = format!(
                        "{circuit} L{layer_idx} budget {budget}{}",
                        if exclude_mq { " [equal-work]" } else { "" }
                    );
                    let result = run_point(
                        &fixture,
                        layer_idx,
                        cg_layer,
                        graph,
                        PointParams {
                            budget,
                            exclude_max_quadratic: exclude_mq,
                        },
                        circuit_seed,
                        &label,
                    );
                    // Record a non-Verified verdict at a TIMED budget right here —
                    // no silent gap: the budget's configs are then skipped below.
                    match &result {
                        PointResult::Verified => {}
                        PointResult::Infeasible => {
                            skips.push(format!(
                                "{label}: INFEASIBLE (run_point) — timed budget skipped"
                            ));
                        }
                        PointResult::Failed { gate, reason } => {
                            failures.push(format!("[{gate}] {label}: {reason}"));
                        }
                    }
                    gated.insert(budget, result);
                }

                // (3) Time each config row ONLY at its gate-Verified budget
                // (LDG/128 verdict, LDG/256 §9 fairness, LDC/128 where it fits).
                // A config whose chosen budget did not Verify is skipped here; its
                // verdict is already recorded in `failures`/`skips` above.
                for (residency, threads, chosen) in config_budgets {
                    let Some(budget) = chosen else { continue };
                    if !matches!(gated.get(&budget), Some(PointResult::Verified)) {
                        // Failed/Infeasible at this timed budget — recorded above.
                        continue;
                    }
                    if let Some(row) = time_config_row(
                        &fixture,
                        layer_idx,
                        cg_layer,
                        graph,
                        circuit,
                        exclude_mq,
                        rows_coincide,
                        residency,
                        threads,
                        budget,
                        count,
                        &mut skips,
                    ) {
                        println!(
                            "TIMED {circuit} L{layer_idx} {residency:?}/{} {shape_str} budget {budget}: flat {:.4}ms (x{}) interp {:.4}ms => {:.2}x  blk/SM {} smem {}B",
                            threads.threads_per_block(),
                            row.flat.median_ms,
                            row.flat.launches,
                            row.interp.median_ms,
                            row.interp_over_flat,
                            row.interp_blocks_per_sm,
                            row.interp_smem_bytes,
                        );
                        rows.push(row);
                    }
                }
            }
        }
    }

    // Build the report (queried device attrs + rows + skips) and write it.
    let props = {
        // Any built fixture's context exposes device props; rebuild a context-
        // free attr query via the device API directly.
        use era_cudart::device::{device_get_attribute, get_device};
        use era_cudart_sys::CudaDeviceAttr;
        let dev = get_device().unwrap();
        DeviceAttrs {
            max_shared_memory_per_multiprocessor: device_get_attribute(
                CudaDeviceAttr::MaxSharedMemoryPerMultiprocessor,
                dev,
            )
            .unwrap(),
            max_shared_memory_per_block_optin: device_get_attribute(
                CudaDeviceAttr::MaxSharedMemoryPerBlockOptin,
                dev,
            )
            .unwrap(),
            sm_count: device_get_attribute(CudaDeviceAttr::MultiProcessorCount, dev).unwrap()
                as usize,
        }
    };
    let report = AbReport {
        device: props,
        iters_full: TIMING_ITERS,
        iters_prescan: PRESCAN_ITERS,
        rows,
        set_b: Vec::new(),
        set_b_padded_smem_bytes: 0,
        set_c: Vec::new(),
        set_d: Vec::new(),
        regression: None,
        skips: skips.clone(),
    };
    println!("\n{}", report.to_markdown());
    let (md, json) = super::report::write_report(&report);
    println!("wrote report: {} / {}", md.display(), json.display());

    // No silent gaps: every Verified point that pre-scanned a budget produced at
    // least the LDG/128 verdict row. Assert no Failed correctness gate.
    assert!(
        failures.is_empty(),
        "verdict A/B reported {} failed correctness point(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(
        !report.rows.is_empty(),
        "verdict A/B produced no timed rows (every point skipped?)"
    );
    // Each circuit must contribute at least one LDG/128 verdict row.
    for circuit in STAGE3_CIRCUITS {
        assert!(
            report
                .rows
                .iter()
                .any(|r| r.circuit == circuit && r.residency == "Ldg" && r.interp_threads == 128),
            "{circuit}: no LDG/128 verdict row timed"
        );
    }
}

// ===========================================================================
// Task 7 — measurement sets B/C/D + the combined report (spec §6.2(B)/(C)/(D)).
//
// One `#[ignore]` GPU test runs ALL FOUR sets (A verdict + B cost decomposition
// + C occupancy curve + D LDC/LDG) and writes the COMBINED report with the
// exploratory regression. Set A's per-point correctness gating (`run_point`)
// + `stage3_run_point_correctness` anchor correctness; sets B/C/D are TIMING
// sweeps — un-gated swept budgets are annotated `gated = timing-only` (NOT
// device-compared at full trace_len, which would be prohibitive: add_sub
// trace_len = 2^24). Where a swept budget coincides with a set-A gated verdict
// (or the 32/64 anchor), it is marked `gated = yes` and reuses that verdict.
// ===========================================================================

/// Query the three device attrs the sweeps need (mirrors set A's inline query).
#[cfg(not(no_cuda))]
fn query_device_attrs() -> DeviceAttrs {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    let dev = get_device().unwrap();
    DeviceAttrs {
        max_shared_memory_per_multiprocessor: device_get_attribute(
            CudaDeviceAttr::MaxSharedMemoryPerMultiprocessor,
            dev,
        )
        .unwrap(),
        max_shared_memory_per_block_optin: device_get_attribute(
            CudaDeviceAttr::MaxSharedMemoryPerBlockOptin,
            dev,
        )
        .unwrap(),
        sm_count: device_get_attribute(CudaDeviceAttr::MultiProcessorCount, dev).unwrap() as usize,
    }
}

/// Per-point compiler stats for the EXACT timed program (filtered for equal-work
/// rows) — used to fill the set-B row + assemble the regression predictor row.
struct PointStats {
    n_instr: u32,
    instrs: usize,
    src_reads: usize,
    cell_reads: usize,
    cache_refires: usize,
    max_live_cells: usize,
    payload_bytes: usize,
}

/// Build the per-point stats for the EXACT timed program: the compiler's
/// per-point `cf.stats` (filtered for equal-work rows) joined with the lowered
/// program's instruction count + payload-table byte count (from the device
/// setup). Shared by sets B/C and the regression predictor row.
#[cfg(not(no_cuda))]
fn point_stats(cf: &CompiledForward, setup: &InterpDeviceSetup) -> PointStats {
    PointStats {
        n_instr: setup.n_instr,
        instrs: cf.stats.instrs,
        src_reads: cf.stats.src_reads,
        cell_reads: cf.stats.cell_reads,
        cache_refires: cf.stats.cache_refires,
        max_live_cells: cf.stats.max_live_cells,
        payload_bytes: setup.payload_bytes,
    }
}

/// Task 7 combined sweep: sets A/B/C/D + the exploratory regression, written to
/// the combined report. Set A is the verdict (same flow as `stage3_fwd_interp_ab`,
/// run here so the combined report carries it + the no-silent-gaps assert
/// covers it); B/C/D are interpreter-side timing sweeps over the feasible budget
/// grid; the regression is the §6.2(B) secondary "exploratory correlation".
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn stage3_fwd_interp_sweeps() {
    use super::harness::{run_point, PointParams, PointResult};

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let device = query_device_attrs();

    // Set B's CONSTANT padded smem: the largest footprint sustaining 4 blocks/SM
    // at 128 threads (= floor(MaxSharedMemoryPerMultiprocessor/4) rounded to cell
    // granularity), clamped to the per-block opt-in cap so every set-B launch is
    // actually launchable. Occupancy is then held constant across the budget grid
    // — only per-thread work varies (controller decision).
    let per_sm = device.max_shared_memory_per_multiprocessor as usize;
    let optin_cap = device.max_shared_memory_per_block_optin as usize;
    let tpb = BENCH_INTERP_THREADS_PER_BLOCK; // set B is FIXED 128 threads.
    let cell_stride = tpb as usize * std::mem::size_of::<BF>();
    let padded_unclamped = padded_smem_for_blocks(tpb, per_sm, 4);
    // Clamp to the opt-in cap (rounded down to cell granularity) if it would
    // exceed it — document + pick achievable (controller "when to STOP" guard).
    let padded_smem = padded_unclamped.min((optin_cap / cell_stride) * cell_stride);
    println!(
        "set B padded smem: floor({per_sm}/4)={padded_unclamped}B, optin cap {optin_cap}B => using {padded_smem}B \
         ({} cells x {tpb} thr)",
        padded_smem / cell_stride,
    );

    let mut rows: Vec<AbRow> = Vec::new();
    let mut set_b: Vec<SetBRow> = Vec::new();
    let mut set_c: Vec<SetCRow> = Vec::new();
    let mut set_d: Vec<SetDRow> = Vec::new();
    let mut obs: Vec<RegressionObs> = Vec::new();
    let mut skips: Vec<String> = Vec::new();
    let mut failures: Vec<String> = Vec::new();

    // Circuit fixed-effect dummies: one indicator column per circuit beyond the
    // first (the first is folded into the intercept). Predictor layout (design
    // row) the regression builds per observation:
    //   [1.0, dummy_circuit1, dummy_circuit2, n_instr, src_reads, cell_reads,
    //    payload_bytes]
    let n_circuits = STAGE3_CIRCUITS.len();
    let predictor_labels: Vec<String> = {
        let mut v = vec!["intercept".to_string()];
        for c in &STAGE3_CIRCUITS[1..] {
            v.push(format!("circuit[{c}]"));
        }
        v.extend(
            ["n_instr", "src_reads", "cell_reads", "payload_bytes"]
                .iter()
                .map(|s| s.to_string()),
        );
        v
    };

    for (ci, circuit) in STAGE3_CIRCUITS.into_iter().enumerate() {
        assert_layer_consistency(circuit);
        let loaded = load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
        let fixture = CircuitFixture::build(circuit);
        assert!(
            !fixture.layers.is_empty(),
            "{circuit}: fixture has no layers"
        );

        let circuit_seed = 0x57A6_E3u64 ^ ((ci as u64) << 32);
        let count = fixture.trace_len.min(TIMING_COUNT_CAP);
        let capped = count < fixture.trace_len;
        println!(
            "{circuit}: trace_len {} -> timed count {count}{}",
            fixture.trace_len,
            if capped { " (capped)" } else { "" }
        );

        for layer_idx in 0..fixture.layers.len() {
            let replayable = fixture.layers[layer_idx].replayable_launch_count();
            if layer_idx != 0 && replayable == 0 {
                continue;
            }
            let cg_layer = &loaded.circuit.layers[layer_idx];
            let graph = &loaded.graphs[layer_idx];
            let layer = &fixture.layers[layer_idx];

            let mq = fwd_eligible_mq_count(cg_layer);
            let rows_coincide = mq == 0;
            let shapes: &[bool] = if rows_coincide {
                &[false]
            } else {
                &[false, true]
            };

            for &exclude_mq in shapes {
                let shape_str = if exclude_mq {
                    "equal-work"
                } else {
                    "production"
                };

                // ---- Set A (verdict): same flow as stage3_fwd_interp_ab — prescan
                // each config, gate the timed budgets, time the verified rows. The
                // gated-budget set feeds the B/C/D `gated` annotation.
                let configs = [
                    (InterpResidency::Ldg, BenchThreads::T128),
                    (InterpResidency::Ldg, BenchThreads::T256),
                    (InterpResidency::Ldc, BenchThreads::T128),
                ];
                let mut config_budgets: Vec<(InterpResidency, BenchThreads, Option<usize>)> =
                    Vec::with_capacity(configs.len());
                for (residency, threads) in configs {
                    let chosen = prescan_best_budget(
                        &fixture, layer_idx, cg_layer, graph, exclude_mq, residency, threads, count,
                    )
                    .map(|p| p.budget);
                    if chosen.is_none() {
                        skips.push(format!(
                            "{circuit} L{layer_idx} {residency:?}/{} {shape_str}: no feasible+timeable budget in grid {BUDGET_GRID:?}",
                            threads.threads_per_block(),
                        ));
                    }
                    config_budgets.push((residency, threads, chosen));
                }

                let mut gated_budgets: std::collections::BTreeSet<usize> =
                    std::collections::BTreeSet::new();
                for budget in config_budgets
                    .iter()
                    .filter_map(|&(_, _, b)| b)
                    .collect::<std::collections::BTreeSet<usize>>()
                {
                    let label = format!(
                        "{circuit} L{layer_idx} budget {budget}{}",
                        if exclude_mq { " [equal-work]" } else { "" }
                    );
                    let result = run_point(
                        &fixture,
                        layer_idx,
                        cg_layer,
                        graph,
                        PointParams {
                            budget,
                            exclude_max_quadratic: exclude_mq,
                        },
                        circuit_seed,
                        &label,
                    );
                    match &result {
                        PointResult::Verified => {
                            gated_budgets.insert(budget);
                        }
                        PointResult::Infeasible => {
                            skips.push(format!(
                                "{label}: INFEASIBLE (run_point) — timed budget skipped"
                            ));
                        }
                        PointResult::Failed { gate, reason } => {
                            failures.push(format!("[{gate}] {label}: {reason}"));
                        }
                    }
                }

                for (residency, threads, chosen) in config_budgets {
                    let Some(budget) = chosen else { continue };
                    if !gated_budgets.contains(&budget) {
                        continue;
                    }
                    if let Some(row) = time_config_row(
                        &fixture,
                        layer_idx,
                        cg_layer,
                        graph,
                        circuit,
                        exclude_mq,
                        rows_coincide,
                        residency,
                        threads,
                        budget,
                        count,
                        &mut skips,
                    ) {
                        rows.push(row);
                    }
                }

                // The 32/64 budgets are correctness-gated by stage3_run_point_correctness
                // (all circuits/layers/filters); fold them into the gated set so a
                // swept point at 32 or 64 is annotated `gated = yes`.
                gated_budgets.insert(32);
                gated_budgets.insert(64);

                // ---- Sets B & C: sweep BUDGET_GRID ∩ feasible at FIXED LDG/T128.
                // Set B holds the CONSTANT padded smem; set C uses the NATURAL
                // (budget-implied) footprint. One device setup per budget serves
                // both (the lowered program is identical; only the launch's smem
                // size differs).
                for &budget in &BUDGET_GRID {
                    let Some(cf) = compile_feasible(cg_layer, graph, budget, exclude_mq) else {
                        skips.push(format!(
                            "{circuit} L{layer_idx} {shape_str} budget {budget}: compile_forward infeasible (sets B/C)"
                        ));
                        continue;
                    };
                    let gated = gated_budgets.contains(&budget);
                    let setup = build_interp_device_setup(&fixture, layer, &cf, cg_layer, count);
                    let stats = point_stats(&cf, &setup);

                    // Set B: constant padded smem. Skip a budget whose natural
                    // (budget-implied) footprint already exceeds the constant pad —
                    // launching at a smaller pad would let the kernel read past its
                    // block (only possible if the pad was clamped to the optin cap).
                    let natural_for_budget = bench_interp_dynamic_smem_bytes(budget as u32, tpb);
                    if natural_for_budget > padded_smem {
                        skips.push(format!(
                            "{circuit} L{layer_idx} {shape_str} budget {budget}: natural smem {natural_for_budget}B > set-B pad {padded_smem}B — set B point skipped"
                        ));
                    } else if let Some((med, min)) = time_interp_smem(
                        &fixture,
                        &setup,
                        InterpResidency::Ldg,
                        BenchThreads::T128,
                        padded_smem,
                        TIMING_ITERS,
                    ) {
                        let blk = bench_interp_blocks_per_sm_smem(
                            BenchThreads::T128,
                            InterpResidency::Ldg,
                            padded_smem,
                        )
                        .unwrap_or(0);
                        set_b.push(SetBRow {
                            circuit: circuit.to_string(),
                            layer: layer_idx,
                            budget,
                            equal_work: exclude_mq,
                            padded_smem_bytes: padded_smem,
                            blocks_per_sm: blk,
                            interp_median_ms: med,
                            interp_min_ms: min,
                            gated,
                            n_instr: stats.n_instr,
                            instrs: stats.instrs,
                            src_reads: stats.src_reads,
                            cell_reads: stats.cell_reads,
                            cache_refires: stats.cache_refires,
                            max_live_cells: stats.max_live_cells,
                            payload_bytes: stats.payload_bytes,
                        });
                        // Regression observation: response = interp median;
                        // predictors = intercept + circuit dummies + numeric stats.
                        let mut pred = vec![1.0f64];
                        for k in 1..n_circuits {
                            pred.push(if k == ci { 1.0 } else { 0.0 });
                        }
                        pred.push(stats.n_instr as f64);
                        pred.push(stats.src_reads as f64);
                        pred.push(stats.cell_reads as f64);
                        pred.push(stats.payload_bytes as f64);
                        obs.push(RegressionObs {
                            response: med as f64,
                            predictors: pred,
                        });
                    }

                    // Set C: natural (budget-implied) smem.
                    let nat_smem = natural_for_budget;
                    if let Some((med, min)) = time_interp_smem(
                        &fixture,
                        &setup,
                        InterpResidency::Ldg,
                        BenchThreads::T128,
                        nat_smem,
                        TIMING_ITERS,
                    ) {
                        let blk = bench_interp_blocks_per_sm_smem(
                            BenchThreads::T128,
                            InterpResidency::Ldg,
                            nat_smem,
                        )
                        .unwrap_or(0);
                        set_c.push(SetCRow {
                            circuit: circuit.to_string(),
                            layer: layer_idx,
                            budget,
                            equal_work: exclude_mq,
                            natural_smem_bytes: nat_smem,
                            blocks_per_sm: blk,
                            large_smem_optin: nat_smem > BENCH_INTERP_DEFAULT_SMEM_CAP,
                            interp_median_ms: med,
                            interp_min_ms: min,
                            gated,
                        });
                    }
                }

                // ---- Set D: LDC vs LDG at one budget where the program fits the
                // __constant__ array. Pick the smallest feasible grid budget whose
                // program uploads; identical config (LDG/T128, natural smem) on both
                // sides. add_sub L0 fits certainly; bigint checked dynamically.
                for &budget in &BUDGET_GRID {
                    let Some(cf) = compile_feasible(cg_layer, graph, budget, exclude_mq) else {
                        continue;
                    };
                    let setup = build_interp_device_setup(&fixture, layer, &cf, cg_layer, count);
                    // Does the program fit __constant__?
                    if !upload_bench_program_to_constant(&setup.lanes).unwrap() {
                        continue;
                    }
                    fixture.context().get_exec_stream().synchronize().unwrap();
                    let nat_smem = bench_interp_dynamic_smem_bytes(budget as u32, tpb);
                    let Some((ldg_med, ldg_min)) = time_interp_smem(
                        &fixture,
                        &setup,
                        InterpResidency::Ldg,
                        BenchThreads::T128,
                        nat_smem,
                        TIMING_ITERS,
                    ) else {
                        continue;
                    };
                    let Some((ldc_med, ldc_min)) = time_interp_smem(
                        &fixture,
                        &setup,
                        InterpResidency::Ldc,
                        BenchThreads::T128,
                        nat_smem,
                        TIMING_ITERS,
                    ) else {
                        continue;
                    };
                    set_d.push(SetDRow {
                        circuit: circuit.to_string(),
                        layer: layer_idx,
                        budget,
                        equal_work: exclude_mq,
                        threads: tpb,
                        smem_bytes: nat_smem,
                        ldg_median_ms: ldg_med,
                        ldg_min_ms: ldg_min,
                        ldc_median_ms: ldc_med,
                        ldc_min_ms: ldc_min,
                        ldc_over_ldg: if ldg_med > 0.0 {
                            ldc_med / ldg_med
                        } else {
                            f32::INFINITY
                        },
                        gated: gated_budgets.contains(&budget),
                    });
                    println!(
                        "SET-D {circuit} L{layer_idx} {shape_str} budget {budget}: LDG {ldg_med:.4}ms LDC {ldc_med:.4}ms => {:.2}x",
                        if ldg_med > 0.0 { ldc_med / ldg_med } else { f32::INFINITY },
                    );
                    break; // one LDC/LDG comparison per (layer, filter) is enough.
                }
            }
        }
    }

    // ---- The §6.2(B) secondary exploratory regression over all set-B points.
    let regression = build_regression(&obs, &predictor_labels);
    match &regression.error {
        Some(err) => println!("regression: UNESTIMABLE — {err}"),
        None => println!(
            "regression: R^2 {:.4}, n_obs {}, n_coeffs {}, residual dof {}",
            regression.r_squared, regression.n_obs, regression.n_coeffs, regression.residual_dof
        ),
    }

    let report = AbReport {
        device,
        iters_full: TIMING_ITERS,
        iters_prescan: PRESCAN_ITERS,
        rows,
        set_b,
        set_b_padded_smem_bytes: padded_smem,
        set_c,
        set_d,
        regression: Some(regression),
        skips: skips.clone(),
    };
    println!("\n{}", report.to_markdown());
    let (md, json) = super::report::write_report(&report);
    println!(
        "wrote combined report: {} / {}",
        md.display(),
        json.display()
    );

    // No silent gaps for SET A (the controller's 7.4 assert): no Failed gate, at
    // least one LDG/128 verdict row per circuit, sets B/C non-empty.
    assert!(
        failures.is_empty(),
        "sweeps reported {} failed correctness point(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(
        !report.rows.is_empty(),
        "sweeps produced no set-A verdict rows (every point skipped?)"
    );
    for circuit in STAGE3_CIRCUITS {
        assert!(
            report
                .rows
                .iter()
                .any(|r| r.circuit == circuit && r.residency == "Ldg" && r.interp_threads == 128),
            "{circuit}: no LDG/128 verdict row timed (set A)"
        );
    }
    assert!(!report.set_b.is_empty(), "set B produced no rows");
    assert!(!report.set_c.is_empty(), "set C produced no rows");
    assert!(
        !report.set_d.is_empty(),
        "set D produced no LDC/LDG comparison (no program fit __constant__?)"
    );
}

/// Assemble the exploratory regression block from the pooled set-B observations.
/// Drops constant (zero-variance) predictor columns BEFORE the fit so a circuit
/// dummy or numeric stat that never varies in the pool does not force a
/// rank-deficient bail; reports any remaining unestimability honestly. Keeps the
/// label↔coefficient alignment by tracking which columns survived.
fn build_regression(obs: &[RegressionObs], labels: &[String]) -> RegressionBlock {
    if obs.is_empty() {
        return RegressionBlock {
            predictor_labels: labels.to_vec(),
            coefficients: Vec::new(),
            r_squared: 0.0,
            n_obs: 0,
            n_coeffs: labels.len(),
            residual_dof: 0,
            error: Some("no set-B observations to regress".to_string()),
        };
    }
    let p = obs[0].predictors.len();
    // Keep column 0 (intercept) always; drop any other column with no variance.
    let mut keep: Vec<usize> = Vec::new();
    for col in 0..p {
        if col == 0 {
            keep.push(col);
            continue;
        }
        let first = obs[0].predictors[col];
        if obs
            .iter()
            .any(|o| (o.predictors[col] - first).abs() > f64::EPSILON)
        {
            keep.push(col);
        }
    }
    let reduced: Vec<RegressionObs> = obs
        .iter()
        .map(|o| RegressionObs {
            response: o.response,
            predictors: keep.iter().map(|&c| o.predictors[c]).collect(),
        })
        .collect();
    let kept_labels: Vec<String> = keep.iter().map(|&c| labels[c].clone()).collect();

    match fit_ols(&reduced) {
        Ok(fit) => RegressionBlock {
            predictor_labels: kept_labels,
            coefficients: fit.coefficients,
            r_squared: fit.r_squared,
            n_obs: fit.n_obs,
            n_coeffs: fit.n_coeffs,
            residual_dof: fit.residual_dof,
            error: None,
        },
        Err(reason) => RegressionBlock {
            predictor_labels: kept_labels.clone(),
            coefficients: Vec::new(),
            r_squared: 0.0,
            n_obs: reduced.len(),
            n_coeffs: kept_labels.len(),
            residual_dof: reduced.len() as isize - kept_labels.len() as isize,
            error: Some(reason),
        },
    }
}

/// ncu profiling TARGET (`#[ignore]`, GPU). Runs EXACTLY ONE interpreter point —
/// one circuit (env `STAGE3_NCU_CIRCUIT`, default add_sub) at one budget (env
/// `STAGE3_NCU_BUDGET`, default 32), LDG/T128, ONE interpreter launch — so an
/// `ncu` wrapper captures a single clean kernel instance. NOT part of the normal
/// sweep (no report, no grid). Wrap it per `gpu/docs/profiling_ncu.md` "Quick
/// Kernel Mode" + the `circuit_prover` profiling doc; the interpreter kernel
/// symbol is `ab_gkr_bench_fwd_interp_ldg_kernel`. Example (build the bench test
/// binary first, then run UNDER the GPU lock):
///
/// ```bash
/// TEST_BINARY="$(
///   cargo test -p circuit_prover --features bench stage3_fwd_interp_ncu_target \
///     --release --no-run --message-format=json \
///     | python3 .agents/bin/cargo_test_executables.py)"
/// STAGE3_NCU_CIRCUIT=add_sub_lui_auipc_mop STAGE3_NCU_BUDGET=32 \
/// .agents/bin/with_gpu_lock.sh ncu \
///   --set basic \
///   --kernel-name-base demangled \
///   --kernel-name 'regex:ab_gkr_bench_fwd_interp_ldg_kernel' \
///   --launch-count 1 \
///   -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_gkr_interp" \
///   "$TEST_BINARY" \
///   --exact prover::gkr::forward::bench_interp::tests::stage3_fwd_interp_ncu_target \
///   --ignored --nocapture
/// ```
///
/// (No `--nvtx`/`--nvtx-include`: this test issues a single matching launch, so a
/// `--launch-count 1` kernel-name filter is sufficient to isolate it. Output goes
/// to the ignored `target/profiling/ncu/` per `.agents/gpu_work.md`.)
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn stage3_fwd_interp_ncu_target() {
    let circuit =
        std::env::var("STAGE3_NCU_CIRCUIT").unwrap_or_else(|_| STAGE3_CIRCUITS[0].to_string());
    let budget: usize = std::env::var("STAGE3_NCU_BUDGET")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(32);
    assert!(
        STAGE3_CIRCUITS.contains(&circuit.as_str()),
        "STAGE3_NCU_CIRCUIT={circuit} is not a stage-3 circuit ({STAGE3_CIRCUITS:?})"
    );
    println!("ncu target: circuit {circuit} budget {budget} (LDG/T128, one launch)");

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let loaded = load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
    let fixture = CircuitFixture::build(&circuit);
    let layer_idx = 0usize;
    let cg_layer = &loaded.circuit.layers[layer_idx];
    let graph = &loaded.graphs[layer_idx];
    let layer = &fixture.layers[layer_idx];
    let count = fixture.trace_len.min(TIMING_COUNT_CAP);

    let cf = compile_feasible(cg_layer, graph, budget, false)
        .unwrap_or_else(|| panic!("{circuit} L0 budget {budget} infeasible for ncu target"));
    let setup = build_interp_device_setup(&fixture, layer, &cf, cg_layer, count);
    let desc = setup.timing_desc();
    // EXACTLY ONE interpreter launch (the kernel ncu isolates).
    launch_bench_fwd_interp(
        &desc,
        InterpResidency::Ldg,
        BenchThreads::T128,
        fixture.context(),
    )
    .unwrap();
    fixture.context().get_exec_stream().synchronize().unwrap();
    println!("ncu target: one ab_gkr_bench_fwd_interp_ldg_kernel launch complete");
}
