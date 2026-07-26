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

use std::collections::{HashMap, HashSet};
use std::mem::{align_of, size_of};

use cs::gkr_compiler::dag_ir::FieldKind;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::{memory_copy, memory_copy_async};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gkr_eval_isa::bwd::coeff::bind::{BoundColumn, BoundSourceWindow, CoeffSourceBinding};
use gkr_eval_isa::bwd::coeff::encode::{
    encode_instrs, opcode_of, DecodedCell, DecodedInstr, DecodedUse, EncodedProgram, SourceCoord,
};
use gkr_eval_isa::bwd::coeff::interp::{
    interpret_coeff_layer, interpret_encoded_program, CoeffResolver,
};
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
    BWD_COEFF_MAX_FOLD_DEPTH, BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_COEFF_ROLE_ENDPOINT0,
    BWD_COEFF_ROLE_PAIR, BWD_COEFF_THREADS_PER_BLOCK,
};
use super::compile::{
    load_add_sub_l0_coeff_case, pseudo_bank, AddSubCoeffCase, PROBED_BUDGETS,
};
use super::lower::{lower_bwd_coeff, BwdCoeffRoundBinding, ResolvedBwdCoeffSourceWindow};
use super::{
    bwd_coeff_dynamic_smem_bytes, bwd_coeff_fold_depth, launch_bwd_coeff,
    launch_fold_factor_prelude, BwdCoeffBank,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::gkr_ops::backward_sumcheck_round_update;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{
    get_eq_high_constant_device_ptr, launch_backward_dual_finalize_from_acc, make_eq_sizes,
    GkrEqSizes, GKR_EQ_GROUP_SIZE, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;
use crate::upstream::{
    BwdRegime, Field, FieldExtension, PrimeField, Seed, TIMESTAMP_COLUMNS_NUM_BITS,
};

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
    /// The evaluated coefficient bank, in index order — `None` for a fixture
    /// whose terms all carry the reserved `+1` literal, so that a bank lookup
    /// there is a test bug rather than a silently invented value.
    bank: Option<&'a [E4]>,
}

impl CoeffResolver for HostSources<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        let Some(bank) = self.bank else {
            panic!("this fixture uses only the reserved +1 literal, never bank entry {id:?}")
        };
        let slot = id
            .bank_index()
            .expect("a reserved literal never reaches the bank");
        bank[slot]
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
    name: String,
    rows: usize,
    regime: BwdRegime,
    round: u8,
    budget: CellBudget,
    challenges: Vec<E4>,
    windows: Vec<HostWindow>,
    instrs: Vec<DecodedInstr>,
    /// The evaluated coefficient bank. Empty for a probe fixture, whose terms all
    /// carry the reserved `+1`.
    bank: Vec<E4>,
    /// §9.3's per-thread `acc_c0` initializer, as a coefficient index.
    c_init: Option<CoefficientRecipeId>,
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

/// Encode a synthetic fixture and bind every `(window, column)` of it to its own
/// source, in wire order.
///
/// Shared by the probe path and the release path so both execute the same words
/// against the same binding.
fn encode_and_bind(
    fixture: &Fixture,
) -> (
    EncodedProgram,
    CoeffSourceBinding,
    HashMap<u32, (usize, usize)>,
) {
    let words = encode_instrs(fixture.regime, fixture.budget, &fixture.instrs)
        .unwrap_or_else(|error| panic!("{}: encode: {error:?}", fixture.name));
    let program = EncodedProgram {
        regime: fixture.regime,
        budget: fixture.budget,
        c_init: fixture.c_init,
        words,
    };

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
    (program, binding, sources)
}

fn run_fixture(fixture: &Fixture, context: &ProverContext) -> RunOutcome {
    let rows = fixture.rows;
    let (program, binding, sources) = encode_and_bind(fixture);

    // Device storage. Every allocation below stays alive until the last download
    // has synchronized the stream.
    let mut backings = Backings::default();
    let mut publishes = Vec::new();
    let resolved = upload_windows(
        &fixture.windows,
        rows,
        context,
        &mut backings,
        &mut publishes,
    );

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

/// Upload every window's read backing and, where §10.2 materializes, its staged
/// publish buffer, and return the per-window round geometry `lower_bwd_coeff`
/// takes.
///
/// `backings` and `publishes` own the allocations: they must outlive the launch
/// AND the downloads that synchronize the stream after it.
fn upload_windows(
    windows: &[HostWindow],
    rows: usize,
    context: &ProverContext,
    backings: &mut Backings,
    publishes: &mut Vec<DeviceAllocation<E4>>,
) -> Vec<ResolvedBwdCoeffSourceWindow> {
    let mut resolved = Vec::with_capacity(windows.len());
    for (index, host) in windows.iter().enumerate() {
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
    resolved
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
        bank: None,
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
    assert_eq!(
        run.published.len(),
        fixture
            .windows
            .iter()
            .filter(|host| host.materialize())
            .count(),
        "{}: every materializing window must have a downloaded publish buffer",
        fixture.name
    );
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
    term_k(category, CoefficientRecipeId::ONE, uses)
}

fn term_k(
    category: TermCategory,
    coefficient: CoefficientRecipeId,
    uses: Vec<DecodedUse>,
) -> DecodedInstr {
    DecodedInstr::Term {
        category,
        coefficient,
        uses,
    }
}

/// A cell-file move. §9.6: the OPCODE carries the width, both operands are bare
/// six-bit BF lanes, and the coefficient bits are canonical zero — which is what
/// `CoefficientRecipeId::ONE` encodes.
fn move_instr(category: TermCategory, from_lane: u16, to_lane: u16) -> DecodedInstr {
    DecodedInstr::Move {
        category,
        from_lane,
        to_lane,
    }
}

/// The lanes a fixture fills and reads back.
///
/// Chosen from the TOP of the cell file so a c16 run saturates the six-bit lane
/// field: at c16 `bf` is 63 — the largest value `BWD_COEFF_LANE_MASK` can
/// express — and the three E4 cells are the last three of the sixteen. At c4 the
/// same rule gives lane 15 and cells 1..3, so both budgets exercise the boundary
/// of whatever file they have.
struct LanePlan {
    bf: u16,
    e4: [u16; 3],
}

fn lane_plan(budget_cells: u8) -> LanePlan {
    let lanes = u16::from(budget_cells) * 4;
    LanePlan {
        bf: lanes - 1,
        e4: [lanes - 12, lanes - 8, lanes - 4],
    }
}

/// R0: every typed source mode at fold depth zero.
fn r0_fixture(rows: usize, budget_cells: u8) -> Fixture {
    let span = 2 * rows;
    let lane = lane_plan(budget_cells);
    Fixture {
        name: format!("R0 probe c{budget_cells}"),
        rows,
        regime: BwdRegime::R0,
        round: 0,
        budget: CellBudget::new(budget_cells).expect("legal budget"),
        bank: Vec::new(),
        c_init: None,
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
                vec![fill(0, 0, lane.bf), direct(1, 1)],
            ),
            // Cell hit on the BF lane the fill just retained.
            term(
                TermCategory::C2ProductBfBf,
                vec![cell(lane.bf), direct(0, 2)],
            ),
            // Procedural source: row-dependent, produced rather than read.
            term(TermCategory::C0LinearBf, vec![direct(2, 0)]),
            // A plan that retains the co-produced Endpoint0 in an E4 cell...
            term(
                TermCategory::C2ProductE4E4,
                vec![
                    planned(
                        1,
                        0,
                        PlanAction::Fill { lane: lane.e4[0] },
                        PlanAction::Direct,
                    ),
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
                        PlanAction::UseResident { lane: lane.e4[0] },
                        PlanAction::Fill { lane: lane.e4[1] },
                    ),
                    direct(1, 1),
                ],
            ),
            // E4 cell hit on the retained Delta.
            term(
                TermCategory::C2ProductE4E4,
                vec![cell(lane.e4[1]), direct(1, 1)],
            ),
        ],
    }
}

/// Continuation at `round`: the bounded D0–D3 lazy fold, the native dual factor
/// and — from the threshold up — first-access publication.
fn continuation_fixture(round: u8, rows: usize, budget_cells: u8) -> Fixture {
    let fold_depth = bwd_coeff_fold_depth(round);
    let span = 2 * rows;
    let shallow = fold_depth.min(1);
    let lane = lane_plan(budget_cells);
    // Window 0 has never caught up (delta = the launch's fold depth); window 1
    // is exactly one fold behind when there is one to be behind by, and is BASE
    // backed, so a continuation program folds a base matrix into E4; window 2 is
    // procedural, and it is present at EVERY round — including at and above the
    // publication threshold, where a procedural source must catch up and publish
    // like any other, from a backing it produces rather than reads.
    let windows = vec![
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
        host_window(
            2,
            WindowFamily::VirtualSetup { kind: 2 },
            1,
            round - fold_depth,
            round,
            Backing::Procedural(2),
            vec![true],
        ),
    ];

    let instrs = vec![
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
                    PlanAction::Fill { lane: lane.e4[0] },
                    PlanAction::Fill { lane: lane.e4[1] },
                ),
                direct_first(0, 1),
            ],
        ),
        term(
            TermCategory::DualProductE4,
            vec![
                DecodedUse::Cell(DecodedCell::Pair {
                    endpoint0_lane: lane.e4[0],
                    delta_lane: lane.e4[1],
                }),
                direct(0, 1),
            ],
        ),
        // A SQUARED term: the two input records are byte-identical, so the
        // operand is resolved ONCE and consumed twice. Re-executing the second
        // copy would read the Endpoint0 lane after this plan's fill overwrote it
        // with the Delta (§9.1).
        term(
            TermCategory::DualProductE4,
            vec![planned(
                0,
                0,
                PlanAction::UseResident { lane: lane.e4[0] },
                PlanAction::Fill { lane: lane.e4[0] },
            )],
        ),
        // Endpoint0 fill and its cell hit.
        term(TermCategory::C0LinearE4, vec![fill(1, 0, lane.e4[2])]),
        term(TermCategory::C0LinearE4, vec![cell(lane.e4[2])]),
        // The procedural source's own first access: at and above the threshold it
        // catches up from a backing it PRODUCES and publishes both endpoints, and
        // window 0 column 2 — which no record ever first-accesses — must still
        // read back exactly what was staged.
        term(
            TermCategory::DualProductE4,
            vec![direct_first(2, 0), direct(0, 2)],
        ),
        // ...and the published procedural value read back on a later access.
        term(TermCategory::C0LinearE4, vec![direct(2, 0)]),
    ];

    Fixture {
        name: format!("Ext probe D{fold_depth} round {round} c{budget_cells}"),
        rows,
        regime: BwdRegime::Ext,
        round,
        budget: CellBudget::new(budget_cells).expect("legal budget"),
        bank: Vec::new(),
        c_init: None,
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
    for budget_cells in [4u8, 16] {
        assert_fixture(&r0_fixture(200, budget_cells), &context);
    }
    for round in 0..=3u8 {
        assert_fixture(&continuation_fixture(round, 200, 4), &context);
    }
    // c16 is the six-bit lane field's boundary: cell 15 is lanes 60..63, and 63
    // is the largest lane index the format can express. Its dynamic shared memory
    // is 16 * 16 * 128 = 32,768 bytes per block, still under the 48 KB default
    // per-block limit, so it needs no opt-in attribute.
    assert_fixture(&continuation_fixture(3, 200, 16), &context);
    assert_hand_built_words_are_rejected(&context);
}

// ── The parity ladder over real add/sub layer-0 programs ────────────────────
//
// Everything above drives the validation-only probe over HAND-BUILT programs.
// This section drives the RELEASE executors over programs the production
// compiler emitted, and follows the whole chain §12.4 requires:
//
//   semantic CPU (acc_c0, acc_c2)
//     -> encoded CPU over the same u16 stream
//     -> GPU per-row contributions
//     -> the reduced (e_partial, c_partial) pair
//     -> the four round coefficients
//     -> the challenge and claim after the INCUMBENT round update.
//
// The incumbent enters at the last two rungs by construction: the reduction and
// the round update are `mega_finalize` / `ab_backward_sumcheck_round_update_kernel`
// and the upstream `output_univariate_monomial_form_max_quadratic`, all untouched.
// Nothing in this section compares the new path only against itself.

/// Rows every real-program run evaluates.
///
/// 200 is two blocks with a partial tail (so the row guard and the per-warp
/// transposed cell file are both exercised) and still <=
/// `MEGA_FINALIZE_BLOCK_THREADS`, which is what lets the incumbent
/// single-launch fused tail reduce the contribution buffer directly instead of
/// through a two-stage partials pass.
const COEFF_ROWS: usize = 200;

/// One realized add/sub layer-0 program plus the host model of its storage.
struct CoeffCase {
    name: String,
    case: AddSubCoeffCase,
    rows: usize,
    challenges: Vec<E4>,
    windows: Vec<HostWindow>,
    /// `SourceId` -> `(window, window-relative column)`.
    sources: HashMap<u32, (usize, usize)>,
    /// The evaluated coefficient bank both the CPU oracles and the launch use.
    bank: Vec<E4>,
    storage: BwdCoeffBank,
}

/// The catch-up distances the runtime factor bank can weight at `round` (§10.2).
///
/// `ab_gkr_bwd_coeff_build_fold_factors_kernel` fills the depth-one pair and one
/// depth-`fold_depth` table, so a window is either at target depth, one fold
/// behind, or has never caught up. `lower_bwd_coeff` rejects anything else, which
/// is exactly why the fixture assigns distances from this set rather than freely.
fn legal_catch_up_distances(round: u8) -> Vec<u8> {
    let fold_depth = bwd_coeff_fold_depth(round);
    let mut out = vec![0u8];
    if fold_depth >= 1 {
        out.push(1);
    }
    if fold_depth > 1 {
        out.push(fold_depth);
    }
    out
}

/// Build the host storage model for one realized program.
///
/// The windows, their families, their column spans and every first-access bit
/// come from the COMPILER's binding; only the backing VALUES and the per-window
/// catch-up distance are the fixture's, because a compiled program does not carry
/// device addresses or a round's fold state.
fn coeff_case(
    regime: BwdRegime,
    round: u8,
    budget_cells: u8,
    storage: BwdCoeffBank,
) -> CoeffCase {
    let case = load_add_sub_l0_coeff_case(regime, round, budget_cells);
    let rows = COEFF_ROWS;
    let distances = legal_catch_up_distances(round);

    // §10.3: the binding's own use list says which physical resolution of which
    // column carries the first-access bit.
    let mut first_accessed = HashSet::<(usize, usize)>::new();
    for use_ in &case.binding.uses {
        if use_.first_access {
            first_accessed.insert((usize::from(use_.window), usize::from(use_.column)));
        }
    }

    let mut sources = HashMap::new();
    let mut windows = Vec::with_capacity(case.binding.windows.len());
    for (index, window) in case.binding.windows.iter().enumerate() {
        let columns = window
            .columns
            .last()
            .map(|column| column.column - window.first_column)
            .expect("a bound window addresses at least one column")
            + 1;
        for column in &window.columns {
            let offset = column.column - window.first_column;
            assert!(
                sources.insert(column.source.0, (index, offset)).is_none(),
                "{regime:?} round {round} c{budget_cells}: source {:?} bound twice",
                column.source
            );
            // At R0 a source is read at its NATIVE width, so the operand width
            // the opcode carries must be the backing's field. In the Ext regime
            // every value is E4 regardless of what it is folded from, so the two
            // legitimately differ there.
            if regime == BwdRegime::R0 {
                assert_eq!(
                    case.layer.sources[column.source.0 as usize].field,
                    window.backing_field(),
                    "R0 c{budget_cells}: window {index} field disagrees with its source"
                );
            }
        }

        let delta = distances[index % distances.len()];
        let column_len = (2 * rows) << usize::from(delta);
        // Widely separated seeds, so a window that read another window's backing
        // would produce visibly wrong values rather than plausible ones.
        let seed = 0x0100_0000u32 + ((index as u32) << 20);
        let backing = match window.family {
            WindowFamily::VirtualSetup { kind } => Backing::Procedural(kind),
            _ => match window.backing_field() {
                FieldKind::Base => base_backing(seed, columns, column_len),
                FieldKind::Ext => ext_backing(seed, columns, column_len),
            },
        };
        windows.push(host_window(
            index,
            window.family,
            columns,
            round - delta,
            round,
            backing,
            (0..columns)
                .map(|column| first_accessed.contains(&(index, column)))
                .collect(),
        ));
    }

    CoeffCase {
        name: format!(
            "add/sub L0 {regime:?} round {round} c{budget_cells} {storage:?}"
        ),
        bank: pseudo_bank(&case.layer),
        case,
        rows,
        challenges: (0..usize::from(round))
            .map(|index| e4(0x0d00 + index as u32))
            .collect(),
        windows,
        sources,
        storage,
    }
}

/// E4 values the `__constant__` `ab_gkr_eq_high` symbol holds.
const EQ_HIGH_SLAB_LEN: usize = GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN;

/// The `__constant__` eq-high slab, as a device slice.
///
/// SAFETY: `get_eq_high_constant_device_ptr` returns the device address of the
/// `ab_gkr_eq_high` symbol, whose declared extent is exactly [`EQ_HIGH_SLAB_LEN`]
/// E4 values.
fn eq_high_slab() -> &'static mut DeviceSlice<E4> {
    unsafe { DeviceSlice::from_raw_parts_mut(get_eq_high_constant_device_ptr(), EQ_HIGH_SLAB_LEN) }
}

/// Owns the staged `ab_gkr_eq_high` sentinel and clears it again on drop.
///
/// The slab is a process-wide `__constant__` symbol that only the incumbent
/// factored-eq BUILD kernel writes in production, so a test that stages it and
/// walks away leaves state behind for whatever runs next — and because the
/// sentinel is `ONE`, a later test that forgot to stage would silently inherit a
/// working eq instead of failing. Restoring zero makes that omission loud: an
/// unstaged inline eq evaluates to zero and every contribution with it.
struct StagedEqHigh;

impl Drop for StagedEqHigh {
    fn drop(&mut self) {
        // Synchronous on purpose: `Drop` has no stream, and this must land before
        // the next test observes the symbol.
        memory_copy(eq_high_slab(), &[E4::ZERO; EQ_HIGH_SLAB_LEN]).expect("eq high restore");
    }
}

/// The staged factored-eq state one run needs.
struct StagedEq {
    /// Host twin of `eq(row)`: with all eight bits in the low slab and both high
    /// slabs at their `ONE` sentinel, `eq(row) == low[row]`.
    low: Vec<E4>,
    device_low: DeviceAllocation<E4>,
    sizes: GkrEqSizes,
    _guard: StagedEqHigh,
}

/// Stage the incumbent factored-eq state the release kernel reads inline.
///
/// `make_eq_sizes(GKR_EQ_GROUP_SIZE)` puts all eight bits in the LOW slab, so
/// both high slabs have size zero and `gkr_compute_eq_inline` reads their slot
/// ZERO as a sentinel — which the incumbent build kernel fills with `E::ONE()`.
/// Only that build kernel writes `ab_gkr_eq_high`, so the test writes the same
/// sentinel itself and `eq(row)` is exactly `eq_low[row]`. A per-row-varying
/// `eq_low` is the point: a constant one would let a kernel that dropped the eq
/// multiply entirely still pass.
fn stage_eq(rows: usize, context: &ProverContext) -> StagedEq {
    assert!(
        rows <= GKR_EQ_GROUP_TABLE_LEN,
        "one eq group covers {GKR_EQ_GROUP_TABLE_LEN} rows"
    );
    let guard = StagedEqHigh;
    memory_copy_async(
        eq_high_slab(),
        &[E4::ONE; EQ_HIGH_SLAB_LEN],
        context.get_exec_stream(),
    )
    .expect("eq high sentinel");

    let low = (0..GKR_EQ_GROUP_TABLE_LEN)
        .map(|slot| e4(0x00e0_0000 + slot as u32))
        .collect::<Vec<_>>();
    let device_low = upload(&low, context);
    StagedEq {
        low,
        device_low,
        sizes: make_eq_sizes(GKR_EQ_GROUP_SIZE),
        _guard: guard,
    }
}

/// What one release launch produced.
struct CoeffRun {
    /// `2 * rows` values: `eq * acc_c0` then `eq * acc_c2`.
    contributions: Vec<E4>,
    /// The host twin of the factored-eq low slab the launch read.
    eq_low: Vec<E4>,
    /// The incumbent fused tail's reduction plus round update, run straight off
    /// the contribution buffer the release kernel wrote.
    incumbent: RoundUpdate,
}

/// The five things a round update produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RoundUpdate {
    seed: Seed,
    claim: E4,
    eq_prefactor: E4,
    coeffs: [E4; 4],
    challenge: E4,
}

/// Fixed, non-degenerate round-update input state.
///
/// `prev_coord` and `eq_prefactor` are both inverted by the round update, so
/// neither may be zero.
fn round_update_inputs() -> (Seed, E4, E4, E4) {
    let seed = Seed([
        0x0123_4567,
        0x89ab_cdef,
        0xfedc_ba98,
        0x7654_3210,
        0x0f1e_2d3c,
        0x4b5a_6978,
        0xc3d2_e1f0,
        0x1122_3344,
    ]);
    let claim = e4(0x00c1_0000);
    let eq_prefactor = e4(0x00c1_0001);
    let prev_coord = e4(0x00c1_0002);
    assert_ne!(prev_coord, E4::ZERO);
    assert_ne!(eq_prefactor, E4::ZERO);
    (seed, claim, eq_prefactor, prev_coord)
}

/// The incumbent CPU round update, exactly as `crate::ops::gkr_ops`'s own parity
/// test runs it. This is upstream algebra plus the upstream transcript; nothing
/// in the coefficient ISA reimplements it.
fn cpu_round_update(e_partial: E4, c_partial: E4) -> RoundUpdate {
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
    use prover::gkr::sumcheck::{
        evaluate_eq_poly, evaluate_small_univariate_poly,
        output_univariate_monomial_form_max_quadratic,
    };

    let (mut seed, claim, eq_prefactor, prev_coord) = round_update_inputs();
    let mut normalized_claim = claim;
    normalized_claim.mul_assign(&eq_prefactor.inverse().expect("non-zero eq prefactor"));
    let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E4>(
        prev_coord,
        normalized_claim,
        e_partial,
        c_partial,
    );
    commit_field_els::<BF, E4>(&mut seed, &coeffs);
    let challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
    RoundUpdate {
        seed,
        claim: evaluate_small_univariate_poly::<BF, E4, 4>(&coeffs, &challenge),
        eq_prefactor: evaluate_eq_poly::<BF, E4>(&challenge, &prev_coord),
        coeffs,
        challenge,
    }
}

/// Device-resident round-update state, reused by both incumbent entry points.
struct RoundUpdateState {
    seed: DeviceAllocation<u32>,
    claim: DeviceAllocation<E4>,
    eq_prefactor: DeviceAllocation<E4>,
    coeffs: DeviceAllocation<E4>,
    challenge: DeviceAllocation<E4>,
    prev_coord: DeviceAllocation<E4>,
    /// The fold destination `mega_finalize` would write. Never used: the fixture
    /// passes `active_eq_size_before_fold = 0`, which skips the fold.
    eq_slot: DeviceAllocation<E4>,
}

fn round_update_state(context: &ProverContext) -> RoundUpdateState {
    let (seed, claim, eq_prefactor, prev_coord) = round_update_inputs();
    RoundUpdateState {
        seed: upload(&seed.0[..], context),
        claim: upload(&[claim], context),
        eq_prefactor: upload(&[eq_prefactor], context),
        coeffs: upload(&[E4::ZERO; 4], context),
        challenge: upload(&[E4::ZERO], context),
        prev_coord: upload(&[prev_coord], context),
        eq_slot: upload(&[E4::ZERO], context),
    }
}

fn download_round_update(state: &RoundUpdateState, context: &ProverContext) -> RoundUpdate {
    let mut seed = Seed::default();
    memory_copy_async(&mut seed.0[..], &state.seed[..STATE_SIZE], context.get_exec_stream())
        .expect("seed D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("round-update sync");
    let coeffs = download_e4(&state.coeffs, 4, context);
    RoundUpdate {
        seed,
        claim: download_e4(&state.claim, 1, context)[0],
        eq_prefactor: download_e4(&state.eq_prefactor, 1, context)[0],
        coeffs: [coeffs[0], coeffs[1], coeffs[2], coeffs[3]],
        challenge: download_e4(&state.challenge, 1, context)[0],
    }
}

/// Lower, launch the release executor, then run the INCUMBENT fused tail over the
/// contribution buffer it wrote.
fn run_coeff_case(case: &CoeffCase, context: &ProverContext) -> CoeffRun {
    let rows = case.rows;
    let mut backings = Backings::default();
    let mut publishes = Vec::new();
    let resolved = upload_windows(&case.windows, rows, context, &mut backings, &mut publishes);

    let eq = stage_eq(rows, context);
    let challenges = upload(&case.challenges, context);
    let mut contributions = upload(&vec![E4::ZERO; 2 * rows], context);
    let coefficients = upload(&case.bank, context);

    let runtime = BwdCoeffRoundBinding {
        round: case.case.round,
        rows: rows as u32,
        round_challenges: if case.challenges.is_empty() {
            std::ptr::null()
        } else {
            challenges.as_ptr()
        },
        n_round_challenges: case.challenges.len() as u32,
        windows: &resolved,
        eq_low: eq.device_low.as_ptr(),
        eq_sizes: eq.sizes,
        contributions: contributions.as_mut_ptr(),
    };
    let setup = lower_bwd_coeff(
        &case.case.program,
        &case.case.binding,
        &runtime,
        case.bank.clone(),
        match case.storage {
            BwdCoeffBank::Constant => std::ptr::null(),
            BwdCoeffBank::DevicePointer => coefficients.as_ptr(),
        },
        case.storage,
    )
    .unwrap_or_else(|error| panic!("{}: lower: {error:?}", case.name));
    assert_eq!(setup.fold_depth, bwd_coeff_fold_depth(case.case.round));

    setup
        .upload_constant_bank(context)
        .unwrap_or_else(|error| panic!("{}: constant bank: {error:?}", case.name));
    // `launch_bwd_coeff` runs the transcript-derived fold prelude itself.
    launch_bwd_coeff(&setup, context)
        .unwrap_or_else(|error| panic!("{}: release launch: {error:?}", case.name));

    let mut state = round_update_state(context);
    launch_backward_dual_finalize_from_acc(
        contributions.as_ptr(),
        rows,
        state.prev_coord.as_ptr(),
        state.seed.as_mut_ptr(),
        state.claim.as_mut_ptr(),
        state.eq_prefactor.as_mut_ptr(),
        state.coeffs.as_mut_ptr(),
        state.challenge.as_mut_ptr(),
        state.eq_slot.as_mut_ptr(),
        // Zero skips `mega_finalize`'s eq fold; only its reduction and round
        // update are under test here.
        0,
        context,
    )
    .unwrap_or_else(|error| panic!("{}: incumbent fused tail: {error:?}", case.name));

    let run = CoeffRun {
        contributions: download_e4(&contributions, 2 * rows, context),
        eq_low: eq.low.clone(),
        incumbent: download_round_update(&state, context),
    };
    drop(backings);
    drop(publishes);
    run
}

/// The whole ladder for one realized program.
fn assert_coeff_case(case: &CoeffCase, context: &ProverContext) {
    let name = &case.name;
    let rows = case.rows;
    let run = run_coeff_case(case, context);
    let resolver = HostSources {
        windows: &case.windows,
        sources: &case.sources,
        rows,
        challenges: &case.challenges,
        bank: Some(&case.bank),
    };

    // Rungs 1-3, per row: semantic CPU, encoded CPU, GPU contribution pair.
    let mut e_partial = E4::ZERO;
    let mut c_partial = E4::ZERO;
    for row in 0..rows {
        let semantic = interpret_coeff_layer(&case.case.layer, row, &resolver)
            .unwrap_or_else(|error| panic!("{name}: semantic row {row}: {error:?}"));
        let encoded = interpret_encoded_program(
            &case.case.program,
            &case.case.binding,
            row,
            &resolver,
        )
        .unwrap_or_else(|error| panic!("{name}: encoded row {row}: {error:?}"));
        assert_e4(&format!("{name}: semantic vs encoded acc_c0 row {row}"), encoded.0, semantic.0);
        assert_e4(&format!("{name}: semantic vs encoded acc_c2 row {row}"), encoded.1, semantic.1);

        let eq = run.eq_low[row & (GKR_EQ_GROUP_TABLE_LEN - 1)];
        let mut expected_c0 = eq;
        expected_c0.mul_assign(&encoded.0);
        let mut expected_c2 = eq;
        expected_c2.mul_assign(&encoded.1);
        assert_e4(
            &format!("{name}: GPU eq*acc_c0 row {row}"),
            run.contributions[row],
            expected_c0,
        );
        assert_e4(
            &format!("{name}: GPU eq*acc_c2 row {row}"),
            run.contributions[rows + row],
            expected_c2,
        );
        e_partial.add_assign(&expected_c0);
        c_partial.add_assign(&expected_c2);
    }

    // Rung 4: the two halves reduce INDEPENDENTLY. Each is summed over its own
    // slice of the GPU's contribution buffer and checked against the running total
    // the per-row loop above accumulated, so a half that leaked into the other —
    // or a stride error between them — shows up here.
    //
    // The INCUMBENT device reduction is not compared here; it is pinned one rung
    // later, where `run.incumbent` (which `launch_backward_dual_finalize_from_acc`
    // produced by reducing this same buffer on the device) is asserted equal to
    // the CPU round update fed the host-reduced pair. That comparison is what ties
    // the device reduction to these two values.
    let device_e_partial = run.contributions[..rows]
        .iter()
        .fold(E4::ZERO, |mut acc, value| {
            acc.add_assign(value);
            acc
        });
    let device_c_partial = run.contributions[rows..]
        .iter()
        .fold(E4::ZERO, |mut acc, value| {
            acc.add_assign(value);
            acc
        });
    assert_e4(&format!("{name}: reduced e_partial"), device_e_partial, e_partial);
    assert_e4(&format!("{name}: reduced c_partial"), device_c_partial, c_partial);

    // Rungs 5-6: the four round coefficients and the state after the round
    // update, against BOTH incumbent helpers.
    //
    // `(c0, c2) -> (e_partial, c_partial)`: the reduced X^0 half is the round
    // polynomial's CONSTANT coefficient and the reduced X^2 half its QUADRATIC
    // coefficient, which is the `(e, c)` pair
    // `compute_univariate_coeffs_max_quadratic` / the upstream
    // `output_univariate_monomial_form_max_quadratic` take in that order.
    let expected = cpu_round_update(e_partial, c_partial);
    assert_eq!(
        run.incumbent, expected,
        "{name}: the incumbent fused tail must reproduce the CPU round update"
    );
    let standalone = run_standalone_round_update(e_partial, c_partial, context);
    assert_eq!(
        standalone, expected,
        "{name}: the incumbent standalone round-update kernel must agree too"
    );

    // ...and the mapping stated as §4's algebra rather than taken on trust. `c1`
    // is recovered ONCE from the normalized claim, not per row.
    let (_, claim, eq_prefactor, prev_coord) = round_update_inputs();
    let mut normalized_claim = claim;
    normalized_claim.mul_assign(&eq_prefactor.inverse().expect("non-zero eq prefactor"));
    let mut b = E4::ONE;
    b.sub_assign(&prev_coord);
    let mut a = prev_coord;
    a.double();
    a.sub_assign(&E4::ONE);

    let mut c1 = normalized_claim;
    let mut b_e = b;
    b_e.mul_assign(&e_partial);
    c1.sub_assign(&b_e);
    c1.mul_assign(&prev_coord.inverse().expect("non-zero previous challenge"));
    c1.sub_assign(&c_partial);
    c1.sub_assign(&e_partial);

    let combine = |x: E4, y: E4, u: E4, v: E4| {
        let mut left = x;
        left.mul_assign(&y);
        let mut right = u;
        right.mul_assign(&v);
        left.add_assign(&right);
        left
    };
    let mut a_c = a;
    a_c.mul_assign(&c_partial);
    assert_e4(&format!("{name}: coeff[0] = b*acc_c0"), expected.coeffs[0], b_e);
    assert_e4(
        &format!("{name}: coeff[1] = a*acc_c0 + b*c1"),
        expected.coeffs[1],
        combine(a, e_partial, b, c1),
    );
    assert_e4(
        &format!("{name}: coeff[2] = a*c1 + b*acc_c2"),
        expected.coeffs[2],
        combine(a, c1, b, c_partial),
    );
    assert_e4(&format!("{name}: coeff[3] = a*acc_c2"), expected.coeffs[3], a_c);
}

/// The incumbent's OTHER round-update entry point: the standalone
/// `ab_backward_sumcheck_round_update_kernel`, fed the reduced pair directly.
///
/// Running both is what pins the `(c0, c2)` -> `(e_partial, c_partial)` mapping to
/// the pair's ORDER in the reduction buffer rather than to one kernel's reading
/// of it.
fn run_standalone_round_update(
    e_partial: E4,
    c_partial: E4,
    context: &ProverContext,
) -> RoundUpdate {
    let mut state = round_update_state(context);
    let reduction = upload(&[e_partial, c_partial], context);
    backward_sumcheck_round_update(
        &reduction[..2],
        &state.prev_coord[..1],
        &mut state.seed[..STATE_SIZE],
        &mut state.claim[..1],
        &mut state.eq_prefactor[..1],
        &mut state.coeffs[..4],
        &mut state.challenge[..1],
        context.get_exec_stream(),
    )
    .expect("standalone round update");
    download_round_update(&state, context)
}

/// R0, the first rung of the ladder: add/sub layer 0 at c2, c5 and c16, through
/// both coefficient banks.
#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_coeff_add_sub_l0_r0_spike() {
    let context = make_test_context(16, 16);
    for cells in PROBED_BUDGETS {
        for storage in [BwdCoeffBank::Constant, BwdCoeffBank::DevicePointer] {
            assert_coeff_case(&coeff_case(BwdRegime::R0, 0, cells, storage), &context);
        }
    }
}

/// Continuation: ONE Ext schedule, bound at each of D0-D3, at c2, c5 and c16.
///
/// The bank alternates with the round so both `CoeffBank` specializations run at
/// every fold depth across the two tests without doubling this one's launches.
#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_coeff_add_sub_l0_d0_d3_parity() {
    let context = make_test_context(16, 16);
    for round in 0..=BWD_COEFF_MAX_FOLD_DEPTH {
        let storage = if round % 2 == 0 {
            BwdCoeffBank::Constant
        } else {
            BwdCoeffBank::DevicePointer
        };
        for cells in PROBED_BUDGETS {
            assert_coeff_case(&coeff_case(BwdRegime::Ext, round, cells, storage), &context);
        }
    }
}

// ── Release-executor coverage of the forms the corpus does not emit ─────────
//
// `the_add_sub_l0_form_census_matches_what_the_gpu_tests_assume` measures what
// add/sub layer 0 actually emits. Two things it never does: a reserved `-1`
// coefficient, and a cell-file MOVE. Both are live parts of the format and of the
// decode loop, so they are covered here by hand-built programs run through the
// same release executors — and every arithmetic shape is additionally run at each
// of the three coefficient forms, so a sign or a width error in one shape cannot
// hide behind another shape's coverage.

/// Bank entries the arithmetic fixtures use; index `i` is coefficient index
/// `RESERVED + i`.
fn arithmetic_bank() -> Vec<E4> {
    vec![e4(0x000a_1100), e4(0x000a_1200)]
}

fn banked(slot: usize) -> CoefficientRecipeId {
    CoefficientRecipeId::from_bank_index(slot)
}

/// The lanes the arithmetic fixtures fill, move and read back.
///
/// Two BF lanes at the bottom of cell zero and three E4 cells at the TOP, so a
/// c16 run still saturates the six-bit lane field (cell 15 is lanes 60..63, and
/// 63 is the largest index `BWD_COEFF_LANE_MASK` can express) while the BF lanes
/// stay clear of every E4 range.
struct ArithLanes {
    bf: [u16; 2],
    e4: [u16; 3],
}

fn arith_lanes(budget_cells: u8) -> ArithLanes {
    let lanes = u16::from(budget_cells) * 4;
    ArithLanes {
        bf: [0, 1],
        e4: [lanes - 12, lanes - 8, lanes - 4],
    }
}

/// R0: every term shape at every coefficient form, plus both move widths.
fn r0_arithmetic_fixture(rows: usize, budget_cells: u8) -> Fixture {
    let span = 2 * rows;
    let lane = arith_lanes(budget_cells);
    Fixture {
        name: format!("R0 arithmetic c{budget_cells}"),
        rows,
        regime: BwdRegime::R0,
        round: 0,
        budget: CellBudget::new(budget_cells).expect("legal budget"),
        bank: arithmetic_bank(),
        // §5.3: R0 drops the spine `c_init` entirely, so a compiled R0 program
        // never carries one and neither does this fixture.
        c_init: None,
        challenges: Vec::new(),
        windows: vec![
            host_window(
                0,
                WindowFamily::BaseLayerWitness,
                3,
                0,
                0,
                base_backing(0x0071, 3, span),
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
                ext_backing(0x0081, 2, span),
                vec![false; 2],
            ),
            host_window(
                2,
                WindowFamily::VirtualSetup { kind: 1 },
                1,
                0,
                0,
                Backing::Procedural(1),
                vec![false],
            ),
        ],
        instrs: vec![
            // BF Endpoint0 into an E4 accumulator: add, subtract, mixed FMA.
            term_k(TermCategory::C0LinearBf, CoefficientRecipeId::ONE, vec![direct(0, 0)]),
            term_k(TermCategory::C0LinearBf, CoefficientRecipeId::NEG_ONE, vec![direct(0, 1)]),
            term_k(TermCategory::C0LinearBf, banked(0), vec![direct(0, 2)]),
            // E4 Endpoint0.
            term_k(TermCategory::C0LinearE4, CoefficientRecipeId::ONE, vec![direct(1, 0)]),
            term_k(TermCategory::C0LinearE4, CoefficientRecipeId::NEG_ONE, vec![direct(1, 1)]),
            term_k(TermCategory::C0LinearE4, banked(1), vec![direct(1, 0)]),
            // BF*BF: the product must be formed in BF and folded into limb zero.
            term_k(
                TermCategory::C2ProductBfBf,
                CoefficientRecipeId::ONE,
                vec![direct(0, 0), direct(0, 1)],
            ),
            term_k(
                TermCategory::C2ProductBfBf,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(0, 1), direct(0, 2)],
            ),
            term_k(
                TermCategory::C2ProductBfBf,
                banked(0),
                vec![direct(0, 2), direct(0, 0)],
            ),
            // ...and squared: ONE record, consumed twice (§9.1).
            term_k(
                TermCategory::C2ProductBfBf,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(0, 1)],
            ),
            // Mixed BF*E4, BF first and E4 second.
            term_k(
                TermCategory::C2ProductBfE4,
                CoefficientRecipeId::ONE,
                vec![direct(0, 0), direct(1, 0)],
            ),
            term_k(
                TermCategory::C2ProductBfE4,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(0, 1), direct(1, 1)],
            ),
            term_k(
                TermCategory::C2ProductBfE4,
                banked(1),
                vec![direct(0, 2), direct(1, 0)],
            ),
            // E4*E4, including a squared one.
            term_k(
                TermCategory::C2ProductE4E4,
                CoefficientRecipeId::ONE,
                vec![direct(1, 0), direct(1, 1)],
            ),
            term_k(
                TermCategory::C2ProductE4E4,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(1, 1), direct(1, 0)],
            ),
            term_k(
                TermCategory::C2ProductE4E4,
                banked(0),
                vec![direct(1, 0), direct(1, 1)],
            ),
            term_k(
                TermCategory::C2ProductE4E4,
                CoefficientRecipeId::ONE,
                vec![direct(1, 1)],
            ),
            // A procedural source, produced from the row rather than read.
            term_k(TermCategory::C0LinearBf, banked(1), vec![direct(2, 0)]),
            // MoveBF: retain a BF Delta, relocate it, read it back at the new
            // lane. A move is a local typed copy — nothing is dropped and no
            // source is touched — so the third term must see the same value.
            term_k(
                TermCategory::C2ProductBfBf,
                CoefficientRecipeId::ONE,
                vec![fill(0, 0, lane.bf[0]), direct(0, 1)],
            ),
            move_instr(TermCategory::MoveBf, lane.bf[0], lane.bf[1]),
            term_k(
                TermCategory::C2ProductBfBf,
                banked(0),
                vec![cell(lane.bf[1]), direct(0, 2)],
            ),
            // MoveE4, same shape one width up.
            term_k(
                TermCategory::C0LinearE4,
                CoefficientRecipeId::ONE,
                vec![fill(1, 0, lane.e4[0])],
            ),
            move_instr(TermCategory::MoveE4, lane.e4[0], lane.e4[1]),
            term_k(
                TermCategory::C0LinearE4,
                CoefficientRecipeId::NEG_ONE,
                vec![cell(lane.e4[1])],
            ),
            // A squared PLAN at BF width. Retain the co-produced Endpoint0 in a BF
            // lane, then square a `{UseResident l, Fill l}` plan on that SAME lane:
            // §9.1's resolve-once rule is what makes this legal, because
            // re-executing the second record would read lane `l` again after the
            // fill overwrote it with the Delta. The continuation fixture covers the
            // E4 width of the same hazard; both widths have their own resolver and
            // their own cell-file accessor, so both need the pin.
            term_k(
                TermCategory::C2ProductBfBf,
                CoefficientRecipeId::ONE,
                vec![
                    planned(
                        0,
                        0,
                        PlanAction::Fill { lane: lane.bf[0] },
                        PlanAction::Direct,
                    ),
                    direct(0, 1),
                ],
            ),
            term_k(
                TermCategory::C2ProductBfBf,
                banked(1),
                vec![planned(
                    0,
                    0,
                    PlanAction::UseResident { lane: lane.bf[0] },
                    PlanAction::Fill { lane: lane.bf[0] },
                )],
            ),
        ],
    }
}

/// Continuation at `round`: both live opcodes at every coefficient form, a native
/// dual factor's plan/packed-pair forms, a squared dual, a `MoveE4`, and a
/// `c_init` that alternates between a banked recipe and a reserved literal.
fn ext_arithmetic_fixture(round: u8, rows: usize, budget_cells: u8) -> Fixture {
    let fold_depth = bwd_coeff_fold_depth(round);
    let shallow = fold_depth.min(1);
    let span = 2 * rows;
    let lane = arith_lanes(budget_cells);
    Fixture {
        name: format!("Ext arithmetic D{fold_depth} round {round} c{budget_cells}"),
        rows,
        regime: BwdRegime::Ext,
        round,
        budget: CellBudget::new(budget_cells).expect("legal budget"),
        bank: arithmetic_bank(),
        // Both descriptor forms of §9.3's initializer: a bank entry, and a
        // reserved literal, which `lower_c_init` accepts and `coefficient_value`
        // resolves without touching the bank.
        c_init: Some(if round % 2 == 0 {
            banked(1)
        } else {
            CoefficientRecipeId::NEG_ONE
        }),
        challenges: (0..usize::from(round))
            .map(|index| e4(0x0b00 + index as u32))
            .collect(),
        windows: vec![
            host_window(
                0,
                WindowFamily::LayerOutput {
                    layer: 2,
                    ext: true,
                },
                2,
                round - fold_depth,
                round,
                ext_backing(0x0091, 2, span << usize::from(fold_depth)),
                vec![true, true],
            ),
            host_window(
                1,
                WindowFamily::BaseLayerMemory,
                1,
                round - shallow,
                round,
                base_backing(0x00a1, 1, span << usize::from(shallow)),
                vec![true],
            ),
        ],
        instrs: vec![
            term_k(
                TermCategory::C0LinearE4,
                CoefficientRecipeId::ONE,
                vec![direct_first(0, 0)],
            ),
            term_k(
                TermCategory::C0LinearE4,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(0, 0)],
            ),
            term_k(TermCategory::C0LinearE4, banked(0), vec![direct_first(0, 1)]),
            // One coefficient and one pair resolution per factor, BOTH accumulators.
            term_k(
                TermCategory::DualProductE4,
                CoefficientRecipeId::ONE,
                vec![direct(0, 0), direct_first(1, 0)],
            ),
            term_k(
                TermCategory::DualProductE4,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(0, 1), direct(1, 0)],
            ),
            term_k(
                TermCategory::DualProductE4,
                banked(1),
                vec![direct(0, 0), direct(0, 1)],
            ),
            // Squared dual: the plan below is the unsafe case §9.1 exists for, but
            // a squared DIRECT record is the cheap one, so cover both.
            term_k(
                TermCategory::DualProductE4,
                CoefficientRecipeId::NEG_ONE,
                vec![direct(0, 1)],
            ),
            // A pair fill, a move of the retained Endpoint0 lane, then the packed
            // pair `Cell` form reading the moved Endpoint0 and the original Delta.
            term_k(
                TermCategory::DualProductE4,
                banked(0),
                vec![
                    planned(
                        0,
                        0,
                        PlanAction::Fill { lane: lane.e4[0] },
                        PlanAction::Fill { lane: lane.e4[1] },
                    ),
                    direct(0, 1),
                ],
            ),
            move_instr(TermCategory::MoveE4, lane.e4[0], lane.e4[2]),
            term_k(
                TermCategory::DualProductE4,
                CoefficientRecipeId::ONE,
                vec![
                    DecodedUse::Cell(DecodedCell::Pair {
                        endpoint0_lane: lane.e4[2],
                        delta_lane: lane.e4[1],
                    }),
                    direct(0, 1),
                ],
            ),
            // A squared PLAN: `{UseResident l, Fill l}` on one lane. Re-executing
            // the second record would read lane `l` after the fill overwrote it.
            term_k(
                TermCategory::DualProductE4,
                banked(1),
                vec![planned(
                    0,
                    0,
                    PlanAction::UseResident { lane: lane.e4[2] },
                    PlanAction::Fill { lane: lane.e4[2] },
                )],
            ),
        ],
    }
}

/// Run the RELEASE executor over a synthetic fixture, through BOTH coefficient
/// banks, and compare its contributions against the encoded CPU interpreter.
fn assert_release_fixture(fixture: &Fixture, context: &ProverContext) {
    let rows = fixture.rows;
    let (program, binding, sources) = encode_and_bind(fixture);
    let mut backings = Backings::default();
    let mut publishes = Vec::new();
    let resolved = upload_windows(&fixture.windows, rows, context, &mut backings, &mut publishes);
    let eq = stage_eq(rows, context);
    let challenges = upload(&fixture.challenges, context);
    let coefficients = upload(&fixture.bank, context);
    let mut contributions = upload(&vec![E4::ZERO; 2 * rows], context);
    let runtime = BwdCoeffRoundBinding {
        round: fixture.round,
        rows: rows as u32,
        round_challenges: if fixture.challenges.is_empty() {
            std::ptr::null()
        } else {
            challenges.as_ptr()
        },
        n_round_challenges: fixture.challenges.len() as u32,
        windows: &resolved,
        eq_low: eq.device_low.as_ptr(),
        eq_sizes: eq.sizes,
        contributions: contributions.as_mut_ptr(),
    };

    let resolver = HostSources {
        windows: &fixture.windows,
        sources: &sources,
        rows,
        challenges: &fixture.challenges,
        bank: Some(&fixture.bank),
    };
    let expected = (0..rows)
        .map(|row| {
            interpret_encoded_program(&program, &binding, row, &resolver)
                .unwrap_or_else(|error| panic!("{}: CPU oracle row {row}: {error:?}", fixture.name))
        })
        .collect::<Vec<_>>();

    for storage in [BwdCoeffBank::Constant, BwdCoeffBank::DevicePointer] {
        let setup = lower_bwd_coeff(
            &program,
            &binding,
            &runtime,
            fixture.bank.clone(),
            match storage {
                BwdCoeffBank::Constant => std::ptr::null(),
                BwdCoeffBank::DevicePointer => coefficients.as_ptr(),
            },
            storage,
        )
        .unwrap_or_else(|error| panic!("{}: lower: {error:?}", fixture.name));
        setup
            .upload_constant_bank(context)
            .unwrap_or_else(|error| panic!("{}: constant bank: {error:?}", fixture.name));
        // Clear the buffer between banks so the second launch's result stands on
        // its own. Without this, a change that made the second launch skip a row
        // would read the FIRST launch's value there and the comparison would still
        // pass — the two banks must produce identical numbers, which is exactly
        // what makes a stale read invisible.
        memory_copy_async(
            &mut contributions[..2 * rows],
            &vec![E4::ZERO; 2 * rows],
            context.get_exec_stream(),
        )
        .expect("clear contributions between banks");
        launch_bwd_coeff(&setup, context)
            .unwrap_or_else(|error| panic!("{}: release launch: {error:?}", fixture.name));
        let got = download_e4(&contributions, 2 * rows, context);
        for (row, (expected_c0, expected_c2)) in expected.iter().enumerate() {
            let eq_row = eq.low[row & (GKR_EQ_GROUP_TABLE_LEN - 1)];
            let mut scaled_c0 = eq_row;
            scaled_c0.mul_assign(expected_c0);
            let mut scaled_c2 = eq_row;
            scaled_c2.mul_assign(expected_c2);
            assert_e4(
                &format!("{} {storage:?}: eq*acc_c0 row {row}", fixture.name),
                got[row],
                scaled_c0,
            );
            assert_e4(
                &format!("{} {storage:?}: eq*acc_c2 row {row}", fixture.name),
                got[rows + row],
                scaled_c2,
            );
        }
    }
    drop(backings);
    drop(publishes);
}

/// The release executors over every arithmetic shape, coefficient form, value-use
/// form and move width the ISA has.
#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_coeff_release_executor_covers_every_form() {
    let context = make_test_context(16, 16);
    // 200 rows: two blocks with a partial tail. c4 and c16 bracket the cell file;
    // the real-program ladder covers c2 and c5.
    for budget_cells in [4u8, 16] {
        assert_release_fixture(&r0_arithmetic_fixture(200, budget_cells), &context);
        for round in 0..=BWD_COEFF_MAX_FOLD_DEPTH {
            assert_release_fixture(&ext_arithmetic_fixture(round, 200, budget_cells), &context);
        }
    }
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

/// ONE split-halves fold of `values` with `challenge`:
/// `out[i] = v[i] + c * (v[i + len/2] - v[i])`, the incumbent
/// `(index, this_layer_size + index)` recurrence and nothing else. No leaf table,
/// no bit reversal, no span arithmetic.
fn fold_once(values: &[E4], challenge: E4) -> Vec<E4> {
    let half = values.len() / 2;
    (0..half)
        .map(|index| {
            let mut diff = values[half + index];
            diff.sub_assign(&values[index]);
            diff.mul_assign(&challenge);
            let mut out = values[index];
            out.add_assign(&diff);
            out
        })
        .collect()
}

/// The δ≥2 offset composition, derived from the recurrence rather than restated.
///
/// `HostWindow::endpoints` composes a δ-fold as one weighted sum over
/// `bit_reverse(leaf) * span` offsets, and so does the kernel. Both were derived
/// from the same reasoning, so a test that only re-states `bitrev * span` cannot
/// catch a shared misunderstanding — and at δ=1 bit reversal is the identity, so
/// `the_fold_model_is_the_split_halves_recurrence` cannot either. This applies
/// the single-fold recurrence δ times instead, which is the definition the
/// composition has to agree with.
#[test]
fn the_multi_fold_offsets_agree_with_the_recurrence_applied_delta_times() {
    for delta in 1..=3u8 {
        let rows = 3usize;
        let challenges = (0..u32::from(delta))
            .map(|round| e4(0x0500 + round))
            .collect::<Vec<_>>();
        let values = (0..(2 * rows) << delta)
            .map(|index| e4(0x0600 + index as u32))
            .collect::<Vec<_>>();

        // The reference: fold the whole column δ times, challenge k at step k —
        // the same order `ab_gkr_bwd_coeff_build_fold_factors_kernel` weights
        // `round_challenges[backing_depth + k]` in.
        let mut level = values.clone();
        for &challenge in &challenges {
            level = fold_once(&level, challenge);
        }
        assert_eq!(level.len(), 2 * rows, "D{delta} reference length");

        let host = host_window(
            0,
            WindowFamily::LayerOutput {
                layer: 0,
                ext: true,
            },
            1,
            0,
            delta,
            Backing::Ext(values),
            vec![true],
        );
        for row in 0..rows {
            let (s0, s1) = host.endpoints(0, row, rows, &challenges);
            assert_e4(&format!("D{delta} recurrence s0 row {row}"), s0, level[row]);
            assert_e4(
                &format!("D{delta} recurrence s1 row {row}"),
                s1,
                level[rows + row],
            );
        }
    }
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
