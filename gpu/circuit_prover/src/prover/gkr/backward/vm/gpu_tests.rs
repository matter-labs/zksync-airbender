//! GPU tests for the backward coefficient-term ISA's typed source resolution
//! (design §10).
//!
//! **What is under test.** Task 10 implements source resolution only: the typed
//! R0 BF/E4 endpoint readers, the bounded D0–D3 lazy fold, first-access
//! publication, the private cell file, and the §8 value-use forms (`Direct`,
//! `Cell`, `Fill`, `PlannedDelta`) on top of them. The u16 HEADER decode and the
//! arithmetic loop are Task 11, so nothing here runs a release executor. The
//! device side is driven through `ab_gkr_bwd_coeff_source_probe_kernel`, the
//! validation-only test kernel §12 sanctions: it calls the SAME typed resolvers
//! and writes out both projections of every operand instead of accumulating
//! them.
//!
//! **The oracle.** Each fixture is a real `EncodedProgram` built with the
//! compiler's own `encode_instrs`, so the words the GPU decodes are the words
//! the compiler would emit. `interpret_encoded_program` then runs that exact
//! stream on the CPU through a host source model, and the probe's per-operand
//! projections are accumulated with §4's role algebra and compared against it,
//! per row. That comparison covers the cell file and resolve-once implicitly;
//! the direct-source and publication assertions on top of it localize a failure
//! to the resolver that caused it.
//!
//! **Endpoint layout.** `s0 = V[row]`, `s1 = V[logical_rows + row]` — the
//! incumbent split-halves layout, mirrored in `coefficient_vm.cu`'s header
//! comment. The retired generic VM used the interleaved `(2*row, 2*row+1)`
//! convention of `gkr_eval_isa::bwd::interp::sumcheck_fold_point`; the fold
//! WEIGHTS coincide, only the backing offsets differ.

use std::collections::HashMap;
use std::mem::{align_of, size_of};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gkr_eval_isa::bwd::coeff::bind::{BoundColumn, BoundSourceWindow, CoeffSourceBinding};
use gkr_eval_isa::bwd::coeff::encode::{
    encode_instrs, opcode_of, DecodedCell, DecodedInstr, DecodedUse, EncodedProgram, SourceCoord,
};
use gkr_eval_isa::bwd::coeff::interp::{interpret_encoded_program, CoeffResolver};
use gkr_eval_isa::bwd::coeff::limits::TermCategory;
use gkr_eval_isa::bwd::coeff::model::{CoefficientRecipeId, SourceId};
use gkr_eval_isa::bwd::coeff::place::PlanAction;
use gkr_eval_isa::bwd::coeff::schedule::CellBudget;
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;

use super::desc::{
    bwd_coeff_arity, bwd_coeff_role, BwdCoeffDesc, BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT,
    BWD_COEFF_EXT_OP_C0_LINEAR_E4, BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4, BWD_COEFF_EXT_OP_MOVE_E4,
    BWD_COEFF_INPUT_COLUMN_SHIFT, BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT, BWD_COEFF_INPUT_WINDOW_SHIFT,
    BWD_COEFF_MODE_CELL, BWD_COEFF_MODE_DIRECT_SOURCE, BWD_COEFF_MODE_PLANNED_SOURCE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PLAN_DELTA_ACTION_SHIFT,
    BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT, BWD_COEFF_PROGRAM_WORD_CAP,
    BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_COEFF_ROLE_ENDPOINT0, BWD_COEFF_ROLE_PAIR,
    BWD_COEFF_THREADS_PER_BLOCK,
};
use super::lower::{lower_bwd_coeff, BwdCoeffRoundBinding, ResolvedBwdCoeffSourceWindow};
use super::{
    bwd_coeff_dynamic_smem_bytes, bwd_coeff_fold_depth, launch_fold_factor_prelude, BwdCoeffBank,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;
use crate::upstream::{BwdRegime, Field, FieldExtension, PrimeField, TIMESTAMP_COLUMNS_NUM_BITS};

// ── The validation-only probe binding ────────────────────────────────────────

/// Mirror of `bwd_coeff_probe_record` in `coefficient_vm.cuh`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct BwdCoeffProbeRecord {
    /// Regime opcode of the term whose operands this record resolves.
    opcode: u16,
    /// Index into `BwdCoeffDesc::program` of the FIRST input word.
    word: u16,
}

const _: () = {
    assert!(size_of::<BwdCoeffProbeRecord>() == 4);
    assert!(align_of::<BwdCoeffProbeRecord>() == 2);
};

/// Operand slots the probe reports per record (`BWD_COEFF_PROBE_OPERANDS`).
const PROBE_OPERANDS: usize = 2;

// Sticky error bits, mirrored from `coefficient_vm.cuh`.
const PROBE_ERR_DEAD_OPCODE: u32 = 1 << 0;
const PROBE_ERR_MOVE_OPCODE: u32 = 1 << 1;
const PROBE_ERR_PROGRAM_OUT_OF_RANGE: u32 = 1 << 2;
const PROBE_ERR_WINDOW_OUT_OF_RANGE: u32 = 1 << 3;
const PROBE_ERR_LANE_OUT_OF_BUDGET: u32 = 1 << 4;
const PROBE_ERR_MISALIGNED_E4_LANE: u32 = 1 << 5;
const PROBE_ERR_MODE_ILLEGAL_FOR_ROLE: u32 = 1 << 6;
const PROBE_ERR_PLAN_ACTION_INVALID: u32 = 1 << 7;
const PROBE_ERR_UNSUPPORTED_FOLD_DELTA: u32 = 1 << 8;

cuda_kernel_signature_arguments_and_function!(
    GkrBwdCoeffSourceProbe,
    desc: BwdCoeffDesc,
    regime_is_r0: u32,
    fold_depth: u32,
    records: *const BwdCoeffProbeRecord,
    n_records: u32,
    endpoint0_out: *mut E4,
    delta_out: *mut E4,
    error: *mut u32,
);
cuda_kernel_declaration!(
    ab_gkr_bwd_coeff_source_probe_kernel(
        desc: BwdCoeffDesc,
        regime_is_r0: u32,
        fold_depth: u32,
        records: *const BwdCoeffProbeRecord,
        n_records: u32,
        endpoint0_out: *mut E4,
        delta_out: *mut E4,
        error: *mut u32
    )
);

#[allow(clippy::too_many_arguments)]
fn launch_probe(
    desc: &BwdCoeffDesc,
    regime: BwdRegime,
    fold_depth: u8,
    records: *const BwdCoeffProbeRecord,
    n_records: usize,
    endpoint0_out: *mut E4,
    delta_out: *mut E4,
    error: *mut u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::builder()
        .grid_dim(
            desc.logical_rows
                .max(1)
                .div_ceil(BWD_COEFF_THREADS_PER_BLOCK),
        )
        .block_dim(BWD_COEFF_THREADS_PER_BLOCK)
        .dynamic_smem_bytes(bwd_coeff_dynamic_smem_bytes(desc.cell_budget))
        .stream(context.get_exec_stream())
        .build();
    let args = GkrBwdCoeffSourceProbeArguments::new(
        *desc,
        u32::from(regime == BwdRegime::R0),
        u32::from(fold_depth),
        records,
        n_records as u32,
        endpoint0_out,
        delta_out,
        error,
    );
    GkrBwdCoeffSourceProbeFunction(ab_gkr_bwd_coeff_source_probe_kernel).launch(&config, &args)
}

// ── Device helpers ───────────────────────────────────────────────────────────

fn upload<T: Copy>(values: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len().max(1), AllocationPlacement::Top)
        .expect("synthetic device allocation");
    if !values.is_empty() {
        memory_copy_async(
            &mut device[..values.len()],
            values,
            context.get_exec_stream(),
        )
        .expect("synthetic H2D");
    }
    device
}

fn download_e4(device: &DeviceAllocation<E4>, len: usize, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; len];
    memory_copy_async(&mut host[..], &device[..len], context.get_exec_stream())
        .expect("synthetic E4 D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("synthetic stream sync");
    host
}

fn download_error(device: &DeviceAllocation<u32>, context: &ProverContext) -> u32 {
    let mut host = [0u32];
    memory_copy_async(&mut host[..], &device[..1], context.get_exec_stream())
        .expect("synthetic error D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("synthetic stream sync");
    host[0]
}

fn bf(seed: u32) -> BF {
    BF::from_u32_with_reduction(seed.wrapping_mul(2_654_435_761) ^ 0x9e37_79b9)
}

fn e4(seed: u32) -> E4 {
    E4::from_array_of_base([
        bf(seed.wrapping_mul(4).wrapping_add(1)),
        bf(seed.wrapping_mul(4).wrapping_add(2)),
        bf(seed.wrapping_mul(4).wrapping_add(3)),
        bf(seed.wrapping_mul(4).wrapping_add(4)),
    ])
}

fn lift(value: BF) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(value)
}

fn e4_bits(value: E4) -> [u32; 4] {
    // SAFETY: E4 is the pinned four-u32 Rust/CUDA ABI field representation, and
    // this is a read-only reinterpretation for exact comparison and reporting.
    unsafe { std::mem::transmute(value) }
}

#[track_caller]
fn assert_e4(label: &str, got: E4, expected: E4) {
    assert_eq!(e4_bits(got), e4_bits(expected), "{label}");
}

// ── The host source model ────────────────────────────────────────────────────

/// What sits behind one synthetic source window.
#[derive(Clone, Debug)]
enum Backing {
    /// Column-major base-field matrix: `values[column * column_len + index]`.
    Base(Vec<BF>),
    /// Column-major extension-field matrix.
    Ext(Vec<E4>),
    /// A virtual-setup source, produced from the backing INDEX rather than read.
    Procedural(u8),
}

/// One synthetic source window: its backing, its depths and which of its columns
/// the program marks with a first access.
#[derive(Clone, Debug)]
struct HostWindow {
    index: usize,
    family: WindowFamily,
    columns: usize,
    backing_depth: u8,
    target_depth: u8,
    backing: Backing,
    /// A materializing column with no first access never catches up, so every
    /// use of it reads the publish buffer exactly as it was staged.
    first_accessed: Vec<bool>,
}

/// Deterministic pre-launch publish-buffer contents. A materializing column with
/// no first access must read these back verbatim, which is what proves a later
/// access reads the PUBLISHED backing instead of folding again.
fn staged_publication(window: usize, column: usize, index: usize) -> E4 {
    e4(0x0700_0000 + (window as u32) * 0x1_0000 + (column as u32) * 0x400 + index as u32)
}

/// `gkr_virtual_base_value`'s host twin, keyed by `BWD_COEFF_PROCEDURAL_*` /
/// `VirtualSetupKind` order.
fn procedural_value(kind: u8, index: usize) -> BF {
    let value = match kind {
        0 => (index < (1 << 16)).then_some(index as u32),
        1 => (index < (1usize << TIMESTAMP_COLUMNS_NUM_BITS)).then_some(index as u32),
        2 => Some(((index << 2) & 0xffff) as u32),
        3 => Some((index >> 14) as u32),
        other => panic!("unknown procedural kind {other}"),
    };
    value.map_or(Field::ZERO, BF::from_u32_unchecked)
}

fn one_minus(value: E4) -> E4 {
    let mut out = E4::ONE;
    out.sub_assign(&value);
    out
}

/// `prod_k (leaf_k ? ch[backing + k] : 1 - ch[backing + k])`, exactly what
/// `ab_gkr_bwd_coeff_build_fold_factors_kernel` writes into its bank.
fn fold_weight(leaf: usize, delta: u8, backing_depth: u8, challenges: &[E4]) -> E4 {
    let mut weight = E4::ONE;
    for k in 0..usize::from(delta) {
        let challenge = challenges[usize::from(backing_depth) + k];
        let factor = if (leaf >> k) & 1 == 1 {
            challenge
        } else {
            one_minus(challenge)
        };
        weight.mul_assign(&factor);
    }
    weight
}

/// Leaf bit `k` weights `challenges[backing_depth + k]` and fold step `k` halves
/// the level it starts from, so the leaf's backing offset is its bit-reversed
/// value times the target-depth span.
fn bit_reverse(leaf: usize, width: u8) -> usize {
    let width = usize::from(width);
    (0..width).fold(0, |acc, k| acc | (((leaf >> k) & 1) << (width - 1 - k)))
}

impl HostWindow {
    fn materialize(&self) -> bool {
        self.target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH
    }

    fn delta(&self) -> u8 {
        self.target_depth - self.backing_depth
    }

    /// Backing elements per column: the target-depth span, doubled once per fold
    /// the backing still owes.
    fn column_len(&self, rows: usize) -> usize {
        (2 * rows) << self.delta()
    }

    fn element(&self, column: usize, index: usize, rows: usize) -> E4 {
        let offset = column * self.column_len(rows) + index;
        match &self.backing {
            Backing::Base(values) => lift(values[offset]),
            Backing::Ext(values) => values[offset],
            Backing::Procedural(kind) => lift(procedural_value(*kind, index)),
        }
    }

    /// The two RAW target-depth endpoints of `column` at `row`.
    fn endpoints(&self, column: usize, row: usize, rows: usize, challenges: &[E4]) -> (E4, E4) {
        if self.materialize() && !self.first_accessed[column] {
            return (
                staged_publication(self.index, column, row),
                staged_publication(self.index, column, rows + row),
            );
        }
        let delta = self.delta();
        if delta == 0 {
            return (
                self.element(column, row, rows),
                self.element(column, rows + row, rows),
            );
        }
        let span = 2 * rows;
        let mut s0 = E4::ZERO;
        let mut s1 = E4::ZERO;
        for leaf in 0..(1usize << delta) {
            let weight = fold_weight(leaf, delta, self.backing_depth, challenges);
            let offset = bit_reverse(leaf, delta) * span;
            let mut low = self.element(column, row + offset, rows);
            low.mul_assign(&weight);
            s0.add_assign(&low);
            let mut high = self.element(column, rows + row + offset, rows);
            high.mul_assign(&weight);
            s1.add_assign(&high);
        }
        (s0, s1)
    }
}

/// The `CoeffResolver` the CPU oracle resolves through.
struct HostSources<'a> {
    windows: &'a [HostWindow],
    /// `SourceId` -> `(window, column)`.
    sources: &'a HashMap<u32, (usize, usize)>,
    rows: usize,
    challenges: &'a [E4],
}

impl CoeffResolver for HostSources<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        panic!("these fixtures use only the reserved +1 literal, never bank entry {id:?}")
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (E4, E4) {
        let (window, column) = self.sources[&id.0];
        let (s0, s1) = self.windows[window].endpoints(column, row, self.rows, self.challenges);
        let mut delta = s1;
        delta.sub_assign(&s0);
        (s0, delta)
    }
}

// ── Fixtures ─────────────────────────────────────────────────────────────────

struct Fixture {
    name: &'static str,
    rows: usize,
    regime: BwdRegime,
    round: u8,
    budget: CellBudget,
    challenges: Vec<E4>,
    windows: Vec<HostWindow>,
    instrs: Vec<DecodedInstr>,
}

/// Everything one fixture produced on the device.
struct ProbeRun {
    endpoint0: Vec<E4>,
    delta: Vec<E4>,
    /// One entry per MATERIALIZING window, in window order.
    published: Vec<Vec<E4>>,
    error: u32,
}

impl ProbeRun {
    fn operand(&self, record: usize, position: usize, row: usize, rows: usize) -> (E4, E4) {
        let slot = (record * PROBE_OPERANDS + position) * rows + row;
        (self.endpoint0[slot], self.delta[slot])
    }
}

/// Keeps every uploaded backing alive for the whole launch. Two typed vectors
/// rather than one tagged enum: an enum variant held purely for RAII has a field
/// nothing ever reads.
#[derive(Default)]
struct Backings {
    base: Vec<DeviceAllocation<BF>>,
    ext: Vec<DeviceAllocation<E4>>,
}

/// One probe record per term, pointing at the term's first INPUT word — the
/// probe does not decode headers (Task 11 does).
fn probe_records(fixture: &Fixture) -> Vec<BwdCoeffProbeRecord> {
    let mut records = Vec::new();
    let mut at = 0usize;
    for instr in &fixture.instrs {
        if let DecodedInstr::Term { category, .. } = instr {
            let opcode = opcode_of(fixture.regime, *category)
                .unwrap_or_else(|| panic!("{category:?} has no {:?} opcode", fixture.regime));
            records.push(BwdCoeffProbeRecord {
                opcode,
                word: (at + 1) as u16,
            });
        }
        at += instr.words();
    }
    records
}

struct RunOutcome {
    run: ProbeRun,
    program: EncodedProgram,
    binding: CoeffSourceBinding,
    sources: HashMap<u32, (usize, usize)>,
}

fn run_fixture(fixture: &Fixture, context: &ProverContext) -> RunOutcome {
    let rows = fixture.rows;
    let words = encode_instrs(fixture.regime, fixture.budget, &fixture.instrs)
        .unwrap_or_else(|error| panic!("{}: encode: {error:?}", fixture.name));
    let program = EncodedProgram {
        regime: fixture.regime,
        budget: fixture.budget,
        c_init: None,
        words,
    };

    // Bind every (window, column) to its own source, in wire order.
    let mut sources = HashMap::new();
    let mut next_source = 0u32;
    let bound_windows = fixture
        .windows
        .iter()
        .enumerate()
        .map(|(index, host)| BoundSourceWindow {
            family: host.family,
            first_column: 0,
            columns: (0..host.columns)
                .map(|column| {
                    let source = SourceId(next_source);
                    sources.insert(next_source, (index, column));
                    next_source += 1;
                    BoundColumn { column, source }
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    let binding = CoeffSourceBinding {
        target_depth: fixture.round,
        materialize: fixture.round >= BWD_COEFF_PUBLISH_TARGET_DEPTH,
        windows: bound_windows,
        uses: Vec::new(),
    };

    // Device storage. Every allocation below stays alive until the last download
    // has synchronized the stream.
    let mut backings = Backings::default();
    let mut publishes = Vec::new();
    let mut resolved = Vec::new();
    for (index, host) in fixture.windows.iter().enumerate() {
        let column_len = host.column_len(rows);
        let read = match &host.backing {
            Backing::Base(values) => {
                let device = upload(values, context);
                let column = ResolvedColumn {
                    is_e4: false,
                    ptr: device.as_ptr().cast(),
                    matrix_base: device.as_ptr() as *mut u8,
                    stride_bytes: (column_len * size_of::<BF>()) as u32,
                };
                backings.base.push(device);
                Some(column)
            }
            Backing::Ext(values) => {
                let device = upload(values, context);
                let column = ResolvedColumn {
                    is_e4: true,
                    ptr: device.as_ptr().cast(),
                    matrix_base: device.as_ptr() as *mut u8,
                    stride_bytes: (column_len * size_of::<E4>()) as u32,
                };
                backings.ext.push(device);
                Some(column)
            }
            Backing::Procedural(_) => None,
        };
        let publish = host.materialize().then(|| {
            let staged = (0..host.columns)
                .flat_map(|column| {
                    (0..2 * rows).map(move |slot| staged_publication(index, column, slot))
                })
                .collect::<Vec<_>>();
            let device = upload(&staged, context);
            let column = ResolvedColumn {
                is_e4: true,
                ptr: device.as_ptr().cast(),
                matrix_base: device.as_ptr() as *mut u8,
                stride_bytes: (2 * rows * size_of::<E4>()) as u32,
            };
            publishes.push(device);
            column
        });
        resolved.push(ResolvedBwdCoeffSourceWindow {
            read,
            publish,
            backing_depth: host.backing_depth,
            target_depth: host.target_depth,
            materialize: host.materialize(),
        });
    }

    let challenges_device = upload(&fixture.challenges, context);
    let eq_low = upload(&[E4::ZERO], context);
    let mut contributions = upload(&vec![E4::ZERO; 2 * rows], context);
    let runtime = BwdCoeffRoundBinding {
        round: fixture.round,
        rows: rows as u32,
        round_challenges: if fixture.challenges.is_empty() {
            std::ptr::null()
        } else {
            challenges_device.as_ptr()
        },
        n_round_challenges: fixture.challenges.len() as u32,
        windows: &resolved,
        eq_low: eq_low.as_ptr(),
        eq_sizes: GkrEqSizes::zeroed(),
        contributions: contributions.as_mut_ptr(),
    };
    let setup = lower_bwd_coeff(
        &program,
        &binding,
        &runtime,
        Vec::new(),
        std::ptr::null(),
        BwdCoeffBank::Constant,
    )
    .unwrap_or_else(|error| panic!("{}: lower: {error:?}", fixture.name));
    assert_eq!(setup.fold_depth, bwd_coeff_fold_depth(fixture.round));

    // The fold weights are derived from the device-resident transcript by the
    // incumbent prelude; the host never computes them.
    launch_fold_factor_prelude(&setup, context).expect("fold-factor prelude");

    let records = probe_records(fixture);
    let records_device = upload(&records, context);
    let slots = records.len() * PROBE_OPERANDS * rows;
    let mut endpoint0 = upload(&vec![E4::ZERO; slots], context);
    let mut delta = upload(&vec![E4::ZERO; slots], context);
    let mut error = upload(&[0u32], context);
    launch_probe(
        &setup.desc,
        fixture.regime,
        setup.fold_depth,
        records_device.as_ptr(),
        records.len(),
        endpoint0.as_mut_ptr(),
        delta.as_mut_ptr(),
        error.as_mut_ptr(),
        context,
    )
    .unwrap_or_else(|failure| panic!("{}: probe launch: {failure:?}", fixture.name));

    let run = ProbeRun {
        endpoint0: download_e4(&endpoint0, slots, context),
        delta: download_e4(&delta, slots, context),
        published: publishes
            .iter()
            .zip(fixture.windows.iter().filter(|host| host.materialize()))
            .map(|(device, host)| download_e4(device, host.columns * 2 * rows, context))
            .collect(),
        error: download_error(&error, context),
    };
    drop(backings);
    RunOutcome {
        run,
        program,
        binding,
        sources,
    }
}

// ── Assertions ───────────────────────────────────────────────────────────────

/// Accumulate the probe's per-operand projections with §4's role algebra. Every
/// fixture uses the reserved `+1` coefficient, so `k` drops out.
fn accumulate(fixture: &Fixture, run: &ProbeRun, row: usize) -> (E4, E4) {
    let regime_is_r0 = fixture.regime == BwdRegime::R0;
    let mut acc_c0 = E4::ZERO;
    let mut acc_c2 = E4::ZERO;
    let mut record = 0usize;
    for instr in &fixture.instrs {
        let DecodedInstr::Term { category, .. } = instr else {
            continue;
        };
        let opcode = opcode_of(fixture.regime, *category).expect("encodable category");
        let role = bwd_coeff_role(regime_is_r0, opcode);
        let arity = bwd_coeff_arity(regime_is_r0, opcode);
        let (lhs_endpoint0, lhs_delta) = run.operand(record, 0, row, fixture.rows);
        let (rhs_endpoint0, rhs_delta) = run.operand(record, arity - 1, row, fixture.rows);
        if role == BWD_COEFF_ROLE_ENDPOINT0 {
            acc_c0.add_assign(&lhs_endpoint0);
        } else {
            if role == BWD_COEFF_ROLE_PAIR {
                let mut c0 = lhs_endpoint0;
                c0.mul_assign(&rhs_endpoint0);
                acc_c0.add_assign(&c0);
            }
            let mut c2 = lhs_delta;
            c2.mul_assign(&rhs_delta);
            acc_c2.add_assign(&c2);
        }
        record += 1;
    }
    (acc_c0, acc_c2)
}

/// Rows compared against the CPU oracle. Every row is resolved on the device;
/// the oracle runs on a spread covering both blocks, the block boundary and the
/// partial tail.
fn oracle_rows(rows: usize) -> Vec<usize> {
    let block = BWD_COEFF_THREADS_PER_BLOCK as usize;
    let mut sample = vec![0, 1, rows / 2, rows - 1];
    if rows > block {
        sample.push(block - 1);
        sample.push(block);
    }
    sample.sort_unstable();
    sample.dedup();
    sample
}

fn assert_fixture(fixture: &Fixture, context: &ProverContext) {
    let outcome = run_fixture(fixture, context);
    let run = &outcome.run;
    assert_eq!(
        run.error, 0,
        "{}: the probe reported validation errors 0x{:x}",
        fixture.name, run.error
    );

    let resolver = HostSources {
        windows: &fixture.windows,
        sources: &outcome.sources,
        rows: fixture.rows,
        challenges: &fixture.challenges,
    };
    let regime_is_r0 = fixture.regime == BwdRegime::R0;

    for row in oracle_rows(fixture.rows) {
        // 1. The oracle: the encoded CPU interpreter over the SAME word stream.
        let (expected_c0, expected_c2) =
            interpret_encoded_program(&outcome.program, &outcome.binding, row, &resolver)
                .unwrap_or_else(|error| {
                    panic!("{}: CPU oracle row {row}: {error:?}", fixture.name)
                });
        let (got_c0, got_c2) = accumulate(fixture, run, row);
        assert_e4(
            &format!("{}: acc_c0 row {row}", fixture.name),
            got_c0,
            expected_c0,
        );
        assert_e4(
            &format!("{}: acc_c2 row {row}", fixture.name),
            got_c2,
            expected_c2,
        );

        // 2. Direct source uses, per operand, so a resolver bug localizes.
        let mut record = 0usize;
        for instr in &fixture.instrs {
            let DecodedInstr::Term { category, uses, .. } = instr else {
                continue;
            };
            let opcode = opcode_of(fixture.regime, *category).expect("encodable category");
            let role = bwd_coeff_role(regime_is_r0, opcode);
            for (position, use_) in uses.iter().enumerate() {
                let DecodedUse::Direct { coord } = *use_ else {
                    continue;
                };
                let source = outcome
                    .binding
                    .resolve(coord.window, coord.column)
                    .expect("bound coordinate");
                let (endpoint0, delta) = resolver.source_pair(source, row);
                let (got_endpoint0, got_delta) = run.operand(record, position, row, fixture.rows);
                assert_e4(
                    &format!(
                        "{}: record {record} operand {position} Endpoint0 row {row}",
                        fixture.name
                    ),
                    got_endpoint0,
                    endpoint0,
                );
                if role != BWD_COEFF_ROLE_ENDPOINT0 {
                    assert_e4(
                        &format!(
                            "{}: record {record} operand {position} Delta row {row}",
                            fixture.name
                        ),
                        got_delta,
                        delta,
                    );
                }
            }
            record += 1;
        }
    }

    // 3. Publication: a first access wrote both RAW target-depth endpoints, and
    //    a column with no first access still holds exactly what was staged.
    let mut materializing = 0usize;
    for host in &fixture.windows {
        if !host.materialize() {
            continue;
        }
        let published = &run.published[materializing];
        materializing += 1;
        for column in 0..host.columns {
            for row in oracle_rows(fixture.rows) {
                let (expected_s0, expected_s1) =
                    host.endpoints(column, row, fixture.rows, &fixture.challenges);
                let base = column * 2 * fixture.rows;
                assert_e4(
                    &format!(
                        "{}: window {} column {column} published s0 row {row}",
                        fixture.name, host.index
                    ),
                    published[base + row],
                    expected_s0,
                );
                assert_e4(
                    &format!(
                        "{}: window {} column {column} published s1 row {row}",
                        fixture.name, host.index
                    ),
                    published[base + fixture.rows + row],
                    expected_s1,
                );
            }
        }
    }
}

// ── Fixture construction ─────────────────────────────────────────────────────

fn base_backing(seed: u32, columns: usize, column_len: usize) -> Backing {
    Backing::Base(
        (0..columns * column_len)
            .map(|index| bf(seed + index as u32))
            .collect(),
    )
}

fn ext_backing(seed: u32, columns: usize, column_len: usize) -> Backing {
    Backing::Ext(
        (0..columns * column_len)
            .map(|index| e4(seed + index as u32))
            .collect(),
    )
}

fn host_window(
    index: usize,
    family: WindowFamily,
    columns: usize,
    backing_depth: u8,
    target_depth: u8,
    backing: Backing,
    first_accessed: Vec<bool>,
) -> HostWindow {
    HostWindow {
        index,
        family,
        columns,
        backing_depth,
        target_depth,
        backing,
        first_accessed,
    }
}

fn coord(window: u8, column: u8, first_access: bool) -> SourceCoord {
    SourceCoord {
        window,
        column,
        first_access,
    }
}

fn direct(window: u8, column: u8) -> DecodedUse {
    DecodedUse::Direct {
        coord: coord(window, column, false),
    }
}

fn direct_first(window: u8, column: u8) -> DecodedUse {
    DecodedUse::Direct {
        coord: coord(window, column, true),
    }
}

fn fill(window: u8, column: u8, dst_lane: u16) -> DecodedUse {
    DecodedUse::Fill {
        coord: coord(window, column, false),
        dst_lane,
    }
}

fn planned(window: u8, column: u8, endpoint0: PlanAction, delta: PlanAction) -> DecodedUse {
    DecodedUse::Planned {
        coord: coord(window, column, false),
        endpoint0,
        delta,
    }
}

fn cell(lane: u16) -> DecodedUse {
    DecodedUse::Cell(DecodedCell::Single { lane })
}

fn term(category: TermCategory, uses: Vec<DecodedUse>) -> DecodedInstr {
    DecodedInstr::Term {
        category,
        coefficient: CoefficientRecipeId::ONE,
        uses,
    }
}

/// R0: every typed source mode at fold depth zero.
fn r0_fixture(rows: usize) -> Fixture {
    let span = 2 * rows;
    Fixture {
        name: "R0",
        rows,
        regime: BwdRegime::R0,
        round: 0,
        budget: CellBudget::new(4).expect("c4"),
        challenges: Vec::new(),
        windows: vec![
            host_window(
                0,
                WindowFamily::BaseLayerWitness,
                3,
                0,
                0,
                base_backing(0x11, 3, span),
                vec![false; 3],
            ),
            host_window(
                1,
                WindowFamily::LayerOutput {
                    layer: 1,
                    ext: true,
                },
                2,
                0,
                0,
                ext_backing(0x21, 2, span),
                vec![false; 2],
            ),
            host_window(
                2,
                WindowFamily::VirtualSetup { kind: 0 },
                1,
                0,
                0,
                Backing::Procedural(0),
                vec![false],
            ),
        ],
        instrs: vec![
            // Plain BF Endpoint0: ONE base-field load, no lift.
            term(TermCategory::C0LinearBf, vec![direct(0, 0)]),
            // BF Delta: two base-field loads and a base-field subtract.
            term(
                TermCategory::C2ProductBfBf,
                vec![direct(0, 1), direct(0, 2)],
            ),
            // E4 Endpoint0 and E4 Delta, vectorized.
            term(TermCategory::C0LinearE4, vec![direct(1, 0)]),
            term(
                TermCategory::C2ProductE4E4,
                vec![direct(1, 0), direct(1, 1)],
            ),
            // A mixed product: BF first, E4 second, with the BF factor filled.
            term(
                TermCategory::C2ProductBfE4,
                vec![fill(0, 0, 1), direct(1, 1)],
            ),
            // Cell hit on the BF lane the fill just retained.
            term(TermCategory::C2ProductBfBf, vec![cell(1), direct(0, 2)]),
            // Procedural source: row-dependent, produced rather than read.
            term(TermCategory::C0LinearBf, vec![direct(2, 0)]),
            // A plan that retains the co-produced Endpoint0 in an E4 cell...
            term(
                TermCategory::C2ProductE4E4,
                vec![
                    planned(1, 0, PlanAction::Fill { lane: 4 }, PlanAction::Direct),
                    direct(1, 1),
                ],
            ),
            // ...and a plan that reads it back, so only endpoint ONE is loaded.
            term(
                TermCategory::C2ProductE4E4,
                vec![
                    planned(
                        1,
                        0,
                        PlanAction::UseResident { lane: 4 },
                        PlanAction::Fill { lane: 8 },
                    ),
                    direct(1, 1),
                ],
            ),
            // E4 cell hit on the retained Delta.
            term(TermCategory::C2ProductE4E4, vec![cell(8), direct(1, 1)]),
        ],
    }
}

/// Continuation at `round`: the bounded D0–D3 lazy fold, the native dual factor
/// and — from the threshold up — first-access publication.
fn continuation_fixture(round: u8, rows: usize) -> Fixture {
    let fold_depth = bwd_coeff_fold_depth(round);
    let span = 2 * rows;
    let materialize = round >= BWD_COEFF_PUBLISH_TARGET_DEPTH;
    let shallow = fold_depth.min(1);
    // Window 0 has never caught up (delta = the launch's fold depth); window 1
    // is exactly one fold behind when there is one to be behind by, and is BASE
    // backed, so a continuation program folds a base matrix into E4; window 2 is
    // procedural and exists only below the publication threshold, where a
    // window with no matrix also needs no publish backing.
    let mut windows = vec![
        host_window(
            0,
            WindowFamily::LayerOutput {
                layer: 2,
                ext: true,
            },
            3,
            round - fold_depth,
            round,
            ext_backing(0x31, 3, span << usize::from(fold_depth)),
            // Column 2 is deliberately never first-accessed.
            vec![true, true, false],
        ),
        host_window(
            1,
            WindowFamily::BaseLayerMemory,
            1,
            round - shallow,
            round,
            base_backing(0x41, 1, span << usize::from(shallow)),
            vec![true],
        ),
    ];
    if !materialize {
        windows.push(host_window(
            2,
            WindowFamily::VirtualSetup { kind: 2 },
            1,
            round - fold_depth,
            round,
            Backing::Procedural(2),
            vec![false],
        ));
    }

    let mut instrs = vec![
        // Folded Endpoint0, and the first access that publishes column 0.
        term(TermCategory::C0LinearE4, vec![direct_first(0, 0)]),
        // Native dual factor: ONE physical source-pair resolution per operand.
        term(
            TermCategory::DualProductE4,
            vec![direct(0, 0), direct_first(1, 0)],
        ),
        // A pair fill, then the packed pair `Cell` form reading both lanes back.
        term(
            TermCategory::DualProductE4,
            vec![
                planned(
                    0,
                    0,
                    PlanAction::Fill { lane: 0 },
                    PlanAction::Fill { lane: 4 },
                ),
                direct_first(0, 1),
            ],
        ),
        term(
            TermCategory::DualProductE4,
            vec![
                DecodedUse::Cell(DecodedCell::Pair {
                    endpoint0_lane: 0,
                    delta_lane: 4,
                }),
                direct(0, 1),
            ],
        ),
        // A SQUARED term: the two input records are byte-identical, so the
        // operand is resolved ONCE and consumed twice. Re-executing the second
        // copy would read lane 0 after this plan's fill overwrote it (§9.1).
        term(
            TermCategory::DualProductE4,
            vec![planned(
                0,
                0,
                PlanAction::UseResident { lane: 0 },
                PlanAction::Fill { lane: 0 },
            )],
        ),
        // Endpoint0 fill and its cell hit.
        term(TermCategory::C0LinearE4, vec![fill(1, 0, 8)]),
        term(TermCategory::C0LinearE4, vec![cell(8)]),
    ];
    if materialize {
        // A materializing column no record first-accesses never catches up, so
        // this use must read the staged publish buffer verbatim.
        instrs.push(term(TermCategory::C0LinearE4, vec![direct(0, 2)]));
    } else {
        instrs.push(term(
            TermCategory::DualProductE4,
            vec![direct(2, 0), direct(0, 2)],
        ));
    }

    Fixture {
        name: match round {
            0 => "Ext D0",
            1 => "Ext D1",
            2 => "Ext D2",
            _ => "Ext D3",
        },
        rows,
        regime: BwdRegime::Ext,
        round,
        budget: CellBudget::new(4).expect("c4"),
        challenges: (0..usize::from(round))
            .map(|index| e4(0x900 + index as u32))
            .collect(),
        windows,
        instrs,
    }
}

// ── Hand-built rejections ────────────────────────────────────────────────────

fn source_word(window: u16, column: u16, first_access: bool, mode: u16) -> u16 {
    (column << BWD_COEFF_INPUT_COLUMN_SHIFT)
        | (window << BWD_COEFF_INPUT_WINDOW_SHIFT)
        | (u16::from(first_access) << BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT)
        | mode
}

fn cell_word(lane: u16) -> u16 {
    (lane << BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT) | BWD_COEFF_MODE_CELL
}

fn plan_word(endpoint0_action: u16, delta_action: u16) -> u16 {
    (delta_action << BWD_COEFF_PLAN_DELTA_ACTION_SHIFT)
        | (endpoint0_action << BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT)
}

/// The probe rejects what the encoder would never emit.
///
/// None of these words can come out of `encode_instrs` — `check_lane`,
/// `bound_coord` and `check_plan` reject them — so they are written into the
/// descriptor by hand. A release kernel trusts its descriptor (§12); this is the
/// layer where "four-lane alignment is required, not assumed" is enforced.
fn assert_hand_built_words_are_rejected(context: &ProverContext) {
    let rows = 32usize;
    let backing = (0..2 * rows)
        .map(|index| e4(index as u32))
        .collect::<Vec<_>>();
    let device = upload(&backing, context);
    let mut endpoint0 = upload(&vec![E4::ZERO; PROBE_OPERANDS * rows], context);
    let mut delta = upload(&vec![E4::ZERO; PROBE_OPERANDS * rows], context);

    struct Case {
        label: &'static str,
        opcode: u16,
        word: u16,
        words: Vec<u16>,
        backing_depth: u8,
        expected: u32,
    }
    let direct_word = source_word(0, 0, false, BWD_COEFF_MODE_DIRECT_SOURCE);
    let cases = vec![
        Case {
            label: "misaligned E4 cell lane",
            opcode: BWD_COEFF_EXT_OP_C0_LINEAR_E4,
            word: 0,
            words: vec![cell_word(2)],
            backing_depth: 0,
            expected: PROBE_ERR_MISALIGNED_E4_LANE,
        },
        Case {
            label: "lane past the cell budget",
            opcode: BWD_COEFF_EXT_OP_C0_LINEAR_E4,
            word: 0,
            words: vec![cell_word(60)],
            backing_depth: 0,
            expected: PROBE_ERR_LANE_OUT_OF_BUDGET,
        },
        Case {
            label: "source window past the live count",
            opcode: BWD_COEFF_EXT_OP_C0_LINEAR_E4,
            word: 0,
            words: vec![source_word(5, 0, false, BWD_COEFF_MODE_DIRECT_SOURCE)],
            backing_depth: 0,
            expected: PROBE_ERR_WINDOW_OUT_OF_RANGE,
        },
        Case {
            label: "dead continuation opcode",
            opcode: 3,
            word: 0,
            words: vec![direct_word],
            backing_depth: 0,
            expected: PROBE_ERR_DEAD_OPCODE,
        },
        Case {
            label: "a move is not a term",
            opcode: BWD_COEFF_EXT_OP_MOVE_E4,
            word: 0,
            words: vec![direct_word],
            backing_depth: 0,
            expected: PROBE_ERR_MOVE_OPCODE,
        },
        Case {
            label: "record past the program array",
            opcode: BWD_COEFF_EXT_OP_C0_LINEAR_E4,
            word: (BWD_COEFF_PROGRAM_WORD_CAP - 2) as u16,
            words: vec![direct_word],
            backing_depth: 0,
            expected: PROBE_ERR_PROGRAM_OUT_OF_RANGE,
        },
        Case {
            label: "a plan on an Endpoint0-only role",
            opcode: BWD_COEFF_EXT_OP_C0_LINEAR_E4,
            word: 0,
            words: vec![
                source_word(0, 0, false, BWD_COEFF_MODE_PLANNED_SOURCE),
                plan_word(0, 2),
            ],
            backing_depth: 0,
            expected: PROBE_ERR_MODE_ILLEGAL_FOR_ROLE,
        },
        Case {
            label: "the format's fourth plan action",
            opcode: BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4,
            word: 0,
            words: vec![
                source_word(0, 0, false, BWD_COEFF_MODE_PLANNED_SOURCE),
                plan_word(3, 0),
                direct_word,
            ],
            backing_depth: 0,
            expected: PROBE_ERR_PLAN_ACTION_INVALID,
        },
        Case {
            label: "a catch-up distance the factor bank cannot weight",
            opcode: BWD_COEFF_EXT_OP_C0_LINEAR_E4,
            word: 0,
            words: vec![direct_word],
            // Two folds behind under a D3 launch: the bank holds only the
            // depth-one pair and one depth-three table.
            backing_depth: 1,
            expected: PROBE_ERR_UNSUPPORTED_FOLD_DELTA,
        },
    ];

    for case in cases {
        let mut desc = BwdCoeffDesc::empty();
        let at = case.word as usize;
        desc.program[at..at + case.words.len()].copy_from_slice(&case.words);
        desc.num_words = (at + case.words.len()) as u32;
        desc.n_source_windows = 1;
        desc.logical_rows = rows as u32;
        desc.cell_budget = 4;
        desc.source_windows[0].read_base = device.as_ptr().cast();
        desc.source_windows[0].read_stride_bytes = (2 * rows * size_of::<E4>()) as u32;
        desc.source_windows[0].origin = BWD_COEFF_ORIGIN_READ_EXT;
        desc.source_windows[0].backing_depth = case.backing_depth;
        desc.source_windows[0].target_depth = 3;

        let records = [BwdCoeffProbeRecord {
            opcode: case.opcode,
            word: case.word,
        }];
        let records_device = upload(&records, context);
        let mut error = upload(&[0u32], context);
        launch_probe(
            &desc,
            BwdRegime::Ext,
            3,
            records_device.as_ptr(),
            records.len(),
            endpoint0.as_mut_ptr(),
            delta.as_mut_ptr(),
            error.as_mut_ptr(),
            context,
        )
        .unwrap_or_else(|failure| panic!("{}: probe launch: {failure:?}", case.label));
        let reported = download_error(&error, context);
        assert_ne!(
            reported & case.expected,
            0,
            "{}: expected bit 0x{:x}, probe reported 0x{reported:x}",
            case.label,
            case.expected
        );
    }
}

// ── The test ─────────────────────────────────────────────────────────────────

#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_coeff_source_resolution_smoke() {
    let context = make_test_context(16, 16);

    // 200 rows: two blocks, the second partial, so the tail guard and the
    // per-warp transposed cell file are both exercised.
    assert_fixture(&r0_fixture(200), &context);
    for round in 0..=3u8 {
        assert_fixture(&continuation_fixture(round, 200), &context);
    }
    assert_hand_built_words_are_rejected(&context);
}

// ── Host-model unit tests (no GPU) ───────────────────────────────────────────

#[test]
fn the_fold_model_is_the_split_halves_recurrence() {
    // One fold of a four-element backing at rows = 1: the target-depth pair is
    // `(V[0] + c*(V[2] - V[0]), V[1] + c*(V[3] - V[1]))`, i.e. the incumbent
    // `(index, this_layer_size + index)` split, not an interleaving.
    let challenge = e4(7);
    let values = (0..4).map(e4).collect::<Vec<_>>();
    let host = host_window(
        0,
        WindowFamily::BaseLayerMemory,
        1,
        0,
        1,
        Backing::Ext(values.clone()),
        vec![true],
    );
    let (s0, s1) = host.endpoints(0, 0, 1, &[challenge]);
    let expect = |low: E4, high: E4| {
        let mut diff = high;
        diff.sub_assign(&low);
        diff.mul_assign(&challenge);
        let mut out = low;
        out.add_assign(&diff);
        out
    };
    assert_e4("split-halves s0", s0, expect(values[0], values[2]));
    assert_e4("split-halves s1", s1, expect(values[1], values[3]));
}

#[test]
fn a_never_first_accessed_materializing_column_reads_the_staged_publication() {
    let host = host_window(
        1,
        WindowFamily::LayerOutput {
            layer: 0,
            ext: true,
        },
        2,
        0,
        3,
        ext_backing(1, 2, 16),
        vec![true, false],
    );
    assert!(host.materialize());
    let (s0, s1) = host.endpoints(1, 0, 1, &[e4(1), e4(2), e4(3)]);
    assert_e4("staged s0", s0, staged_publication(1, 1, 0));
    assert_e4("staged s1", s1, staged_publication(1, 1, 1));
}

#[test]
fn bit_reversal_maps_a_leaf_to_its_split_halves_offset() {
    assert_eq!(bit_reverse(0b01, 2), 0b10);
    assert_eq!(bit_reverse(0b10, 2), 0b01);
    assert_eq!(bit_reverse(0b001, 3), 0b100);
    assert_eq!(bit_reverse(0b011, 3), 0b110);
    assert_eq!(bit_reverse(0, 1), 0);
    assert_eq!(bit_reverse(1, 1), 1);
}
